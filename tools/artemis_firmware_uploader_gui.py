"""
This is a simple firmware upload GUI designed for the Artemis platform.
Very handy for updating devices in the field without the need for compiling
and uploading through Arduino.

This is the "integrated" version which includes code from both ambiq_bin2board.py and artemis_svl.py

If you are building with a new version of artemis_svl.bin, remember to update BOOTLOADER_VERSION below.

Based on gist by Stefan Lehmann: https://gist.github.com/stlehmann/bea49796ad47b1e7f658ddde9620dff1

MIT license

Pyinstaller:
Windows:
pyinstaller --onefile --noconsole --distpath=. --icon=artemis_firmware_uploader_gui.ico --add-data="artemis_svl.bin;." --add-data="Artemis-Logo-Rounded.png;." artemis_firmware_uploader_gui.py
Linux:
pyinstaller --onefile --noconsole --distpath=. --icon=artemis_firmware_uploader_gui.ico --add-data="artemis_svl.bin:." --add-data="Artemis-Logo-Rounded.png:." artemis_firmware_uploader_gui.py

Pyinstaller needs:
artemis_firmware_uploader_gui.py (this file!)
artemis_firmware_uploader_gui.ico (icon file for the .exe)
Artemis-Logo-Rounded.png (icon for the GUI widget)
artemis_svl.bin (the bootloader binary)

"""

# Immediately upon reset the Artemis module will search for the timing character
#   to auto-detect the baud rate. If a valid baud rate is found the Artemis will
#   respond with the bootloader version packet
# If the computer receives a well-formatted version number packet at the desired
#   baud rate it will send a command to begin bootloading. The Artemis shall then
#   respond with the a command asking for the next frame.
# The host will then send a frame packet. If the CRC is OK the Artemis will write
#   that to memory and request the next frame. If the CRC fails the Artemis will
#   discard that data and send a request to re-send the previous frame.
# This cycle repeats until the Artemis receives a done command in place of the
#   requested frame data command.
# The initial baud rate determination must occur within some small timeout. Once
#   baud rate detection has completed all additional communication will have a
#   universal timeout value. Once the Artemis has begun requesting data it may no
#   no longer exit the bootloader. If the host detects a timeout at any point it
#   will stop bootloading.

# Notes about PySerial timeout:
# The timeout operates on whole functions - that is to say that a call to
#   ser.read(10) will return after ser.timeout, just as will ser.read(1) (assuming
#   that the necessary bytes were not found)
# If there are no incoming bytes (on the line or in the buffer) then two calls to
#   ser.read(n) will time out after 2*ser.timeout
# Incoming UART data is buffered behind the scenes, probably by the OS.

# Information about the firmware updater (taken from ambiq_bin2board.py):
#   This script performs the three main tasks:
#       1. Convert 'application.bin' to an OTA update blob
#       2. Convert the OTA blob into a wired update blob
#       3. Push the wired update blob into the Artemis module

from typing import Iterator, Tuple
from PyQt5.QtCore import QSettings, QObject, QProcess, QTimer, QThread, pyqtSignal, pyqtSlot
from PyQt5.QtWidgets import QWidget, QLabel, QComboBox, QGridLayout, \
    QPushButton, QApplication, QLineEdit, QFileDialog, QPlainTextEdit, \
    QAction, QActionGroup, QMenu, QMenuBar, QMainWindow
from PyQt5.QtGui import QCloseEvent, QTextCursor, QIcon, QFont
from PyQt5.QtSerialPort import QSerialPortInfo
import threading
import sys
import time
import datetime
import math
import os
import serial
from Crypto.Cipher import AES # pip install pycryptodome
import array
import hashlib
import hmac
import binascii

BOOTLOADER_VERSION = 6 # << Change this to match the version of artemis_svl.bin

# Setting constants
SETTING_PORT_NAME = 'port_name'
SETTING_FILE_LOCATION = 'file_location'
SETTING_BAUD_RATE = 'baud_rate' # Default to 115200 for upload
SETTING_ARTEMIS = 'artemis' # Default to Artemis-based boards

guiVersion = 'v3.0'

def trap_exc_during_debug(*args):
    # when app raises uncaught exception, print info
    print(args)


# install exception hook: without this, uncaught exception would cause application to exit
sys.excepthook = trap_exc_during_debug

def gen_serial_ports() -> Iterator[Tuple[str, str, str]]:
    """Return all available serial ports."""
    ports = QSerialPortInfo.availablePorts()
    return ((p.description(), p.portName(), p.systemLocation()) for p in ports)

#https://stackoverflow.com/a/50914550
def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    base_path = getattr(sys, '_MEIPASS', os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base_path, relative_path)

#https://stackoverflow.com/questions/20324804/how-to-use-qthread-correctly-in-pyqt-with-movetothread
def logthread(caller):
    print('%-25s:\t %s, %s,' % (caller, threading.current_thread().name,
                              threading.current_thread().ident))

# ///// START of code taken from artemis_svl.py
# Commands
SVL_CMD_VER     = 0x01  # version
SVL_CMD_BL      = 0x02  # enter bootload mode
SVL_CMD_NEXT    = 0x03  # request next chunk
SVL_CMD_FRAME   = 0x04  # indicate app data frame
SVL_CMD_RETRY   = 0x05  # request re-send frame
SVL_CMD_DONE    = 0x06  # finished - all data sent
SVL_CMD_MSG     = 0x07  # message
SVL_CMD_DATE    = 0x08  # update date/time

crcTable = (
       0x0000, 0x8005, 0x800F, 0x000A, 0x801B, 0x001E, 0x0014, 0x8011,
       0x8033, 0x0036, 0x003C, 0x8039, 0x0028, 0x802D, 0x8027, 0x0022,
       0x8063, 0x0066, 0x006C, 0x8069, 0x0078, 0x807D, 0x8077, 0x0072,
       0x0050, 0x8055, 0x805F, 0x005A, 0x804B, 0x004E, 0x0044, 0x8041,
       0x80C3, 0x00C6, 0x00CC, 0x80C9, 0x00D8, 0x80DD, 0x80D7, 0x00D2,
       0x00F0, 0x80F5, 0x80FF, 0x00FA, 0x80EB, 0x00EE, 0x00E4, 0x80E1,
       0x00A0, 0x80A5, 0x80AF, 0x00AA, 0x80BB, 0x00BE, 0x00B4, 0x80B1,
       0x8093, 0x0096, 0x009C, 0x8099, 0x0088, 0x808D, 0x8087, 0x0082,
       0x8183, 0x0186, 0x018C, 0x8189, 0x0198, 0x819D, 0x8197, 0x0192,
       0x01B0, 0x81B5, 0x81BF, 0x01BA, 0x81AB, 0x01AE, 0x01A4, 0x81A1,
       0x01E0, 0x81E5, 0x81EF, 0x01EA, 0x81FB, 0x01FE, 0x01F4, 0x81F1,
       0x81D3, 0x01D6, 0x01DC, 0x81D9, 0x01C8, 0x81CD, 0x81C7, 0x01C2,
       0x0140, 0x8145, 0x814F, 0x014A, 0x815B, 0x015E, 0x0154, 0x8151,
       0x8173, 0x0176, 0x017C, 0x8179, 0x0168, 0x816D, 0x8167, 0x0162,
       0x8123, 0x0126, 0x012C, 0x8129, 0x0138, 0x813D, 0x8137, 0x0132,
       0x0110, 0x8115, 0x811F, 0x011A, 0x810B, 0x010E, 0x0104, 0x8101,
       0x8303, 0x0306, 0x030C, 0x8309, 0x0318, 0x831D, 0x8317, 0x0312,
       0x0330, 0x8335, 0x833F, 0x033A, 0x832B, 0x032E, 0x0324, 0x8321,
       0x0360, 0x8365, 0x836F, 0x036A, 0x837B, 0x037E, 0x0374, 0x8371,
       0x8353, 0x0356, 0x035C, 0x8359, 0x0348, 0x834D, 0x8347, 0x0342,
       0x03C0, 0x83C5, 0x83CF, 0x03CA, 0x83DB, 0x03DE, 0x03D4, 0x83D1,
       0x83F3, 0x03F6, 0x03FC, 0x83F9, 0x03E8, 0x83ED, 0x83E7, 0x03E2,
       0x83A3, 0x03A6, 0x03AC, 0x83A9, 0x03B8, 0x83BD, 0x83B7, 0x03B2,
       0x0390, 0x8395, 0x839F, 0x039A, 0x838B, 0x038E, 0x0384, 0x8381,
       0x0280, 0x8285, 0x828F, 0x028A, 0x829B, 0x029E, 0x0294, 0x8291,
       0x82B3, 0x02B6, 0x02BC, 0x82B9, 0x02A8, 0x82AD, 0x82A7, 0x02A2,
       0x82E3, 0x02E6, 0x02EC, 0x82E9, 0x02F8, 0x82FD, 0x82F7, 0x02F2,
       0x02D0, 0x82D5, 0x82DF, 0x02DA, 0x82CB, 0x02CE, 0x02C4, 0x82C1,
       0x8243, 0x0246, 0x024C, 0x8249, 0x0258, 0x825D, 0x8257, 0x0252,
       0x0270, 0x8275, 0x827F, 0x027A, 0x826B, 0x026E, 0x0264, 0x8261,
       0x0220, 0x8225, 0x822F, 0x022A, 0x823B, 0x023E, 0x0234, 0x8231,
       0x8213, 0x0216, 0x021C, 0x8219, 0x0208, 0x820D, 0x8207, 0x0202)

def get_crc16(data) -> int:
    """Compute CRC on a byte array"""
    logthread('Uploader.get_crc16')

    #Table and code ported from Artemis SVL bootloader
    crc = 0x0000
    data = bytearray(data)
    for ch in data:
        tableAddr = ch ^ (crc >> 8)
        CRCH = (crcTable[tableAddr] >> 8) ^ (crc & 0xFF)
        CRCL = crcTable[tableAddr] & 0x00FF
        crc = CRCH << 8 | CRCL
    return crc

def wait_for_packet(ser) -> dict:
    """Wait for a packet"""
    logthread('Uploader.wait_for_packet')

    packet = {'len':0, 'cmd':0, 'data':0, 'crc':1, 'timeout':1}

    n = ser.read(2) # get the length bytes
    if(len(n) < 2):
        return packet

    packet['len'] = int.from_bytes(n, byteorder='big', signed=False)

    if(packet['len'] == 0): # Check for an empty packet
        return packet

    payload = ser.read(packet['len']) #read bytes (or timeout)

    if(len(payload) != packet['len']):
        return packet

    packet['timeout'] = 0                           # all bytes received, so timeout is not true
    packet['cmd'] = payload[0]                      # cmd is the first byte of the payload
    packet['data'] = payload[1:packet['len']-2]     # the data is the part of the payload that is not cmd or crc
    packet['crc'] = get_crc16(payload)         # performing the crc on the whole payload should return 0

    return packet


def send_packet(ser, cmd, data) -> None:
    """Send a packet"""
    logthread('Uploader.send_packet')
    data = bytearray(data)
    num_bytes = 3 + len(data)
    payload = bytearray(cmd.to_bytes(1,'big'))
    payload.extend(data)
    crc = get_crc16(payload)
    payload.extend(bytearray(crc.to_bytes(2,'big')))

    ser.write(num_bytes.to_bytes(2,'big'))
    ser.write(bytes(payload))

# ///// END of code taken from artemis_svl.py

# noinspection PyArgumentList

class MainWindow(QMainWindow):
    """Main Window"""
    def __init__(self, parent: QMainWindow = None) -> None:
        super().__init__(parent)

        self.ser = None
        self.isSerialSettingChanged = False

        ## ///// START of code taken from ambiq_bin2board.py

        ## Global Variables
        #self.loadTries = 0 #If we fail, try again. Tracks the number of tries we've attempted
        #self.loadSuccess = False
        #self.blob2wiredfile = ''
        #self.uploadbinfile = ''

        ## ARGS - these replace the actual args
        ## Maybe these should be in a JSON file?
        #self.abort = -1             # -a            Should it send abort command? (0 = abort, 1 = abort and quit, -1 = no abort)
        #self.authalgo = 0           # --authalgo    (0, AM_SECBOOT_AUTH_ALGO_MAX+1)
        #self.authI = 0              # --authI       Install Authentication check enabled (0,1)
        #self.authB = 0              # --authB       Boot Authentication check enabled (0,1)
        #self.authkey = 8            # --authkey     Authentication Key Idx (minHmacKeyIdx from keys_info.py)
        #self.appFile = 'bootloader_svl.bin'    # --bin Bootloader binary file
        #self.child0 = 0xFFFFFFFF    # --child0      (blobPtr#0 for Main / feature key for AM3P)
        #self.child1 = 0xFFFFFFFF    # --child1      (blobPtr#1 for Main)
        #self.crcI = 1               # --crcI        Install CRC check enabled (0,1)
        #self.crcB = 0               # --crcB        Boot CRC check enabled (0,1)
        #self.encalgo = 0            # --encalgo     (0, AM_SECBOOT_ENC_ALGO_MAX+1)
        #self.erasePrev = 0          # --erasePrev   (0,1)
        #self.image_type = 6         # -i            Image type (AM_SECBOOT_WIRED_IMAGETYPE_NONSECURE)
        #self.kek = 8                # --kek         KEK index (minAesKeyIdx from keys_info.py)
        #self.load_address_blob = 0xC000     # --load-address-wired  dest=loadaddress_blob   default=0x60000
        #self.load_address_image = 0x20000   # --load-address-blob   dest=loadaddress_image  default=AM_SECBOOT_DEFAULT_NONSECURE_MAIN=0xC000
        #self.magic_num = 0xCB       # --magic-num   Magic Num (AM_IMAGE_MAGIC_NONSECURE)
        #self.output_file = 'application'    # -o    Output filename (without the extension) [also used for intermediate filenames]
        #self.otadesc = 0xFE000      # -ota          OTA Descriptor Page address (hex) - (Default is 0xFE000 - at the end of main flash)
        #self.options = 0x1          # --options     (16b hex value) - bit0 instructs to perform OTA of the image after wired download
        #self.protection = 0         # -p            Protection info 2 bit C W (0,1,2,3)
        #self.reset_after = 2        # -r            Should it send reset command after image download? (0 = no reset, 1 = POI, 2 = POR)
        #self.split = 0x48000        # --split       MAX_DOWNLOAD_SIZE from am_defines.py
        #self.version = 0x0          # --version     version (15 bit)

        ## ///// START of defines taken from am_defines.py
        ## Really these should not be self.'globals'. It might be best to put them back into a separate file?
        #self.ivVal0 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        #self.FLASH_PAGE_SIZE                 = 0x2000                # 8K
        #self.MAX_DOWNLOAD_SIZE               = 0x48000               # 288K
        #self.AM_SECBOOT_AESCBC_BLOCK_SIZE_WORDS  = 4
        #self.AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES  = 4*self.AM_SECBOOT_AESCBC_BLOCK_SIZE_WORDS
        #self.AM_SECBOOT_MIN_KEYIDX_INFO0     = 8 ## KeyIdx 8 - 15
        #self.AM_SECBOOT_MAX_KEYIDX_INFO0     = 15
        #self.AM_SECBOOT_MIN_KEYIDX_INFO1     = 0 ## KeyIdx 0 - 7
        #self.AM_SECBOOT_MAX_KEYIDX_INFO1     = 7
        #self.AM_SECBOOT_KEYIDX_BYTES         = 16
        #self.AM_IMAGE_MAGIC_MAIN                    = 0xC0
        #self.AM_IMAGE_MAGIC_CHILD                   = 0xCC
        #self.AM_IMAGE_MAGIC_NONSECURE               = 0xCB
        #self.AM_IMAGE_MAGIC_INFO0                   = 0xCF
        #self.AM_IMAGE_MAGIC_CUSTPATCH               = 0xC1
        #self.AM_SECBOOT_WIRED_IMAGETYPE_SBL         = 0
        #self.AM_SECBOOT_WIRED_IMAGETYPE_AM3P        = 1
        #self.AM_SECBOOT_WIRED_IMAGETYPE_PATCH       = 2
        #self.AM_SECBOOT_WIRED_IMAGETYPE_MAIN        = 3
        #self.AM_SECBOOT_WIRED_IMAGETYPE_CHILD       = 4
        #self.AM_SECBOOT_WIRED_IMAGETYPE_CUSTPATCH   = 5
        #self.AM_SECBOOT_WIRED_IMAGETYPE_NONSECURE   = 6
        #self.AM_SECBOOT_WIRED_IMAGETYPE_INFO0       = 7
        #self.AM_SECBOOT_WIRED_IMAGETYPE_INFO0_NOOTA = 32
        #self.AM_SECBOOT_WIRED_IMAGETYPE_INVALID     = 0xFF
        #self.AM_SECBOOT_WIRED_MSGTYPE_HELLO         = 0
        #self.AM_SECBOOT_WIRED_MSGTYPE_STATUS        = 1
        #self.AM_SECBOOT_WIRED_MSGTYPE_OTADESC       = 2
        #self.AM_SECBOOT_WIRED_MSGTYPE_UPDATE        = 3
        #self.AM_SECBOOT_WIRED_MSGTYPE_ABORT         = 4
        #self.AM_SECBOOT_WIRED_MSGTYPE_RECOVER       = 5
        #self.AM_SECBOOT_WIRED_MSGTYPE_RESET         = 6
        #self.AM_SECBOOT_WIRED_MSGTYPE_ACK           = 7
        #self.AM_SECBOOT_WIRED_MSGTYPE_DATA          = 8
        #self.AM_SECBOOT_WIRED_ACK_STATUS_SUCCESS              = 0
        #self.AM_SECBOOT_WIRED_ACK_STATUS_FAILURE              = 1
        #self.AM_SECBOOT_WIRED_ACK_STATUS_INVALID_INFO0        = 2
        #self.AM_SECBOOT_WIRED_ACK_STATUS_CRC                  = 3
        #self.AM_SECBOOT_WIRED_ACK_STATUS_SEC                  = 4
        #self.AM_SECBOOT_WIRED_ACK_STATUS_MSG_TOO_BIG          = 5
        #self.AM_SECBOOT_WIRED_ACK_STATUS_UNKNOWN_MSGTYPE      = 6
        #self.AM_SECBOOT_WIRED_ACK_STATUS_INVALID_ADDR         = 7
        #self.AM_SECBOOT_WIRED_ACK_STATUS_INVALID_OPERATION    = 8
        #self.AM_SECBOOT_WIRED_ACK_STATUS_INVALID_PARAM        = 9
        #self.AM_SECBOOT_WIRED_ACK_STATUS_SEQ                  = 10
        #self.AM_SECBOOT_WIRED_ACK_STATUS_TOO_MUCH_DATA        = 11
        #self.AM_HMAC_SIG_SIZE                = 32
        #self.AM_KEK_SIZE                     = 16
        #self.AM_CRC_SIZE                     = 4
        #self.AM_MAX_UART_MSG_SIZE            = 8192  # 8K buffer in SBL
        #self.AM_WU_IMAGEHDR_OFFSET_SIG       = 16
        #self.AM_WU_IMAGEHDR_OFFSET_IV        = 48
        #self.AM_WU_IMAGEHDR_OFFSET_KEK       = 64
        #self.AM_WU_IMAGEHDR_OFFSET_IMAGETYPE = (self.AM_WU_IMAGEHDR_OFFSET_KEK + self.AM_KEK_SIZE)
        #self.AM_WU_IMAGEHDR_OFFSET_OPTIONS   = (self.AM_WU_IMAGEHDR_OFFSET_IMAGETYPE + 1)
        #self.AM_WU_IMAGEHDR_OFFSET_KEY       = (self.AM_WU_IMAGEHDR_OFFSET_IMAGETYPE + 4)
        #self.AM_WU_IMAGEHDR_OFFSET_ADDR      = (self.AM_WU_IMAGEHDR_OFFSET_KEY + 4)
        #self.AM_WU_IMAGEHDR_OFFSET_SIZE      = (self.AM_WU_IMAGEHDR_OFFSET_ADDR + 4)
        #self.AM_WU_IMAGEHDR_START_HMAC       = (self.AM_WU_IMAGEHDR_OFFSET_SIG + self.AM_HMAC_SIG_SIZE)
        #self.AM_WU_IMAGEHDR_START_ENCRYPT    = (self.AM_WU_IMAGEHDR_OFFSET_KEK + self.AM_KEK_SIZE)
        #self.AM_WU_IMAGEHDR_SIZE             = (self.AM_WU_IMAGEHDR_OFFSET_KEK + self.AM_KEK_SIZE + 16)
        #self.AM_IMAGEHDR_SIZE_MAIN           = 256
        #self.AM_IMAGEHDR_SIZE_AUX            = (112 + self.AM_KEK_SIZE)
        #self.AM_IMAGEHDR_OFFSET_CRC          = 4
        #self.AM_IMAGEHDR_OFFSET_SIG          = 16
        #self.AM_IMAGEHDR_OFFSET_IV           = 48
        #self.AM_IMAGEHDR_OFFSET_KEK          = 64
        #self.AM_IMAGEHDR_OFFSET_SIGCLR       = (self.AM_IMAGEHDR_OFFSET_KEK + self.AM_KEK_SIZE)
        #self.AM_IMAGEHDR_START_CRC           = (self.AM_IMAGEHDR_OFFSET_CRC + self.AM_CRC_SIZE)
        #self.AM_IMAGEHDR_START_HMAC_INST     = (self.AM_IMAGEHDR_OFFSET_SIG + self.AM_HMAC_SIG_SIZE)
        #self.AM_IMAGEHDR_START_ENCRYPT       = (self.AM_IMAGEHDR_OFFSET_KEK + self.AM_KEK_SIZE)
        #self.AM_IMAGEHDR_START_HMAC          = (self.AM_IMAGEHDR_OFFSET_SIGCLR + self.AM_HMAC_SIG_SIZE)
        #self.AM_IMAGEHDR_OFFSET_ADDR         = self.AM_IMAGEHDR_START_HMAC
        #self.AM_IMAGEHDR_OFFSET_VERKEY       = (self.AM_IMAGEHDR_OFFSET_ADDR + 4)
        #self.AM_IMAGEHDR_OFFSET_CHILDPTR     = (self.AM_IMAGEHDR_OFFSET_VERKEY + 4)
        #self.INFO_SIZE_BYTES                 = (8 * 1024)
        #self.INFO_MAX_AUTH_KEY_WORDS         = 32
        #self.INFO_MAX_ENC_KEY_WORDS          = 32
        ## ///// END of defines taken from am_defines.py

        ## ///// START of defines taken from keys_info.py
        ## Really these should not be self.'globals'. It might be best to put them back into a separate file?
        #self.minAesKeyIdx = 8
        #self.maxAesKeyIdx = 15
        #self.minHmacKeyIdx = 8
        #self.maxHmacKeyIdx = 15
        ####### Following are just dummy keys - Should be substituted with real keys #######
        #self.keyTblAes = [
        #        # Info0 Keys - Starting at index 8
        #        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        #        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        #        0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
        #        0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
        #        0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
        #        0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5, 0xA5,
        #        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        #        0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE,
        #    ]
        #self.keyTblHmac = [
        #        # Info0 Keys - Starting at index 8
        #        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        #        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        #        0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55, 0xAA, 0x55,
        #        0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE, 0xEF, 0xBE, 0xAD, 0xDE,
        #    ]
        #self.INFO_KEY                    = 0xd894e09e
        #self.FLASH_KEY                   = 0x12344321
        ## ///// END of defines taken from keys_info.py

        ## ///// END of code taken from ambiq_bin2board.py

        # File location line edit
        msg_label = QLabel(self.tr('Firmware File:'))
        self.fileLocation_lineedit = QLineEdit()
        msg_label.setBuddy(self.fileLocation_lineedit)
        self.fileLocation_lineedit.setEnabled(False)
        self.fileLocation_lineedit.returnPressed.connect(
            self.on_browse_btn_pressed)

        # Browse for new file button
        self.browse_btn = QPushButton(self.tr('Browse'))
        self.browse_btn.setEnabled(True)
        self.browse_btn.pressed.connect(self.on_browse_btn_pressed)

        # Port Combobox
        self.isCOMPortsUpdated = False
        port_label = QLabel(self.tr('COM Port:'))
        self.port_combobox = QComboBox()
        port_label.setBuddy(self.port_combobox)
        self.port_combobox.currentIndexChanged.connect(self.on_combobox_changed)
        self.update_com_ports()

        # Refresh Button
        self.refresh_btn = QPushButton(self.tr('Refresh'))
        self.refresh_btn.pressed.connect(self.on_refresh_btn_pressed)

        # Clear Button
        self.clear_btn = QPushButton(self.tr('Clear Log'))
        self.clear_btn.pressed.connect(self.on_clear_btn_pressed)

        # Baudrate Combobox
        self.isBaudUpdated = False
        baud_label = QLabel(self.tr('Baud Rate:'))
        self.baud_combobox = QComboBox()
        baud_label.setBuddy(self.baud_combobox)
        self.baud_combobox.currentIndexChanged.connect(self.on_combobox_changed)
        self.update_baud_rates()

        myFont=QFont()
        myFont.setBold(True)
        # Update Datetime Button
        self.update_dt_btn = QPushButton(self.tr('  Update Date/Time  '))
        self.update_dt_btn.setFont(myFont)
        self.update_dt_btn.setFixedWidth(150)
        self.update_dt_btn.pressed.connect(self.on_update_dt_btn_pressed)

        # Upload Button
        self.upload_btn = QPushButton(self.tr('  Upload Firmware  '))
        self.upload_btn.setFont(myFont)
        self.upload_btn.setFixedWidth(150)
        self.upload_btn.pressed.connect(self.on_upload_btn_pressed)

        # Connect UART Button
        self.connect_btn = QPushButton(self.tr('  Connect  '))
        self.connect_btn.setFont(myFont)
        self.connect_btn.setFixedWidth(150)
        self.connect_btn.pressed.connect(self.on_connect_btn_pressed)

        ## Upload Bootloader Button
        #self.updateBootloader_btn = QPushButton(self.tr(' Update Bootloader '))
        #self.updateBootloader_btn.pressed.connect(self.on_update_bootloader_btn_pressed)

        # Messages Bar
        messages_label = QLabel(self.tr('Status / Warnings:'))

        # Messages Window
        self.messages = QPlainTextEdit()
        # Attempting to reduce window size
        #self.messages.setMinimumSize(1, 2)
        #self.messages.resize(1, 2)

        # Remote Messages Bar
        messages_label_remote = QLabel(self.tr('Remote Status / Warnings:'))

        # Remote Messages Window
        self.messages_remote = QPlainTextEdit()
        # Attempting to reduce window size
        #self.messages_remote.setMinimumSize(1, 2)
        #self.messages_remote.resize(1, 2)

        # Menu Bar
        menubar = self.menuBar()
        boardMenu = menubar.addMenu('Board Type')
        
        boardGroup = QActionGroup(self)

        self.artemis = QAction('Artemis', self, checkable=True)
        self.artemis.setStatusTip('Artemis-based boards including the OLA and AGT')
        self.artemis.setChecked(True) # Default to artemis
        a = boardGroup.addAction(self.artemis)
        boardMenu.addAction(a)
        
        self.apollo3 = QAction('Apollo3', self, checkable=True)
        self.apollo3.setStatusTip('Apollo3 Blue development boards including the SparkFun Edge')
        a = boardGroup.addAction(self.apollo3)
        boardMenu.addAction(a)

        # Status Bar
        self.statusBar()

        # Arrange Layout
        layout = QGridLayout()
        
        layout.addWidget(msg_label, 1, 0)
        layout.addWidget(self.fileLocation_lineedit, 1, 1)
        layout.addWidget(self.browse_btn, 1, 2)

        layout.addWidget(port_label, 2, 0)
        layout.addWidget(self.port_combobox, 2, 1)
        layout.addWidget(self.refresh_btn, 2, 2)

        layout.addWidget(baud_label, 3, 0)
        layout.addWidget(self.baud_combobox, 3, 1)
        layout.addWidget(self.clear_btn, 3, 2)

        layout.addWidget(messages_label, 4, 0)
        layout.addWidget(self.messages, 5, 0, 5, 3)

        layout.addWidget(messages_label_remote, 15, 0)
        layout.addWidget(self.messages_remote, 16, 0, 16, 3)

        layout.addWidget(self.update_dt_btn, 36, 0)
        layout.addWidget(self.upload_btn, 36, 1)
        layout.addWidget(self.connect_btn, 36, 2)
        #layout.addWidget(self.updateBootloader_btn, 36, 1)

        widget = QWidget()
        widget.setLayout(layout)
        self.setCentralWidget(widget)

        #self._clean_settings() # This will delete all existing settings! Use with caution!
        
        self._load_settings()

        # Make the text edit window read-only
        self.messages.setReadOnly(True)
        self.messages.clear()  # Clear the message window
        self.messages_remote.setReadOnly(True)
        self.messages_remote.clear()  # Clear the message window

        self.showDatetime()
        logthread('mainwin.__init__')

    def showDatetime(self):
        currentDT = datetime.datetime.now()
        self.addMessage(currentDT.strftime("%Y-%m-%d %H:%M:%S"))

    def addMessage(self, msg: str) -> None:
        """Add msg to the messages window, ensuring that it is visible"""
        #logthread('mainwin.addMessage')
        self.messages.moveCursor(QTextCursor.End)
        #self.messages.ensureCursorVisible()
        self.messages.appendPlainText(msg)
        #self.messages.ensureCursorVisible()
        self.messages.repaint() # Update/refresh the message window
    
    def addMessageRemote(self, msg: str) -> None:
        """Add msg to the remote messages window, ensuring that it is visible"""
        #logthread('mainwin.addMessageRemote')
        self.messages_remote.moveCursor(QTextCursor.End)
        #self.messages_remote.ensureCursorVisible()
        self.messages_remote.appendPlainText(msg)
        #self.messages_remote.ensureCursorVisible()
        self.messages_remote.repaint() # Update/refresh the remote message window

    def _load_settings(self) -> None:
        """Load settings on startup."""
        logthread('mainwin._load_settings')
        settings = QSettings()

        port_name = settings.value(SETTING_PORT_NAME)
        if port_name is not None:
            index = self.port_combobox.findData(port_name)
            if index > -1:
                self.port_combobox.setCurrentIndex(index)

        lastFile = settings.value(SETTING_FILE_LOCATION)
        if lastFile is not None:
            self.fileLocation_lineedit.setText(lastFile)

        baud = settings.value(SETTING_BAUD_RATE)
        if baud is not None:
            index = self.baud_combobox.findData(baud)
            if index > -1:
                self.baud_combobox.setCurrentIndex(index)

        checked = settings.value(SETTING_ARTEMIS)
        if checked is not None:
            if (checked == 'True'):
                self.artemis.setChecked(True)
                self.apollo3.setChecked(False)
            else:
                self.artemis.setChecked(False)
                self.apollo3.setChecked(True)

    def _save_settings(self) -> None:
        """Save settings on shutdown."""
        logthread('mainwin._save_settings')
        settings = QSettings()
        settings.setValue(SETTING_PORT_NAME, self.port)
        settings.setValue(SETTING_FILE_LOCATION, self.fileLocation_lineedit.text())
        settings.setValue(SETTING_BAUD_RATE, self.baudRate)
        if (self.artemis.isChecked()): # Convert isChecked to str
            checkedStr = 'True'
        else:
            checkedStr = 'False'
        settings.setValue(SETTING_ARTEMIS, checkedStr)

    def _clean_settings(self) -> None:
        """Clean (remove) all existing settings."""
        logthread('mainwin._clean_settings')
        settings = QSettings()
        settings.clear()

    def show_error_message(self, msg: str) -> None:
        """Show a Message Box with the error message."""
        logthread('mainwin.show_error_message')
        QMessageBox.critical(self, QApplication.applicationName(), str(msg))

    def update_com_ports(self) -> None:
        """Update COM Port list in GUI."""
        logthread('mainwin.update_com_ports')
        previousPort = self.port # Record the previous port before we clear the combobox

        self.port_combobox.clear()

        index = 0
        indexOfCH340 = -1
        indexOfPrevious = -1
        for desc, name, sys in gen_serial_ports():
            longname = desc + " (" + name + ")"
            self.port_combobox.addItem(longname, sys)
            if("CH340" in longname):
                # Select the first available CH340
                # This is likely to only work on Windows. Linux port names are different.
                if (indexOfCH340 == -1):
                    indexOfCH340 = index
                    # it could be too early to call
                    #self.addMessage("CH340 found at index " + str(indexOfCH340))
                    # as the GUI might not exist yet
            if(sys == previousPort): # Previous port still exists so record it
                indexOfPrevious = index
            index = index + 1

        if indexOfPrevious > -1: # Restore the previous port if it still exists
            self.port_combobox.setCurrentIndex(indexOfPrevious)
        if indexOfCH340 > -1: # If we found a CH340, let that take priority
            self.port_combobox.setCurrentIndex(indexOfCH340)

    def update_baud_rates(self) -> None:
        """Update baud rate list in GUI."""
        logthread('mainwin.update_baud_rates')
        # Lowest speed first so code defaults to that
        # if settings.value(SETTING_BAUD_RATE) is None
        self.baud_combobox.clear()
        self.baud_combobox.addItem("115200", 115200)
        self.baud_combobox.addItem("460800", 460800)
        self.baud_combobox.addItem("921600", 921600)

    @property
    def port(self) -> str:
        logthread('mainwin.port')
        """Return the current serial port."""
        return self.port_combobox.currentData()

    @property
    def baudRate(self) -> str:
        logthread('mainwin.baudRate')
        """Return the current baud rate."""
        return self.baud_combobox.currentData()

    def closeEvent(self, event: QCloseEvent) -> None:
        """Handle Close event of the Widget."""
        logthread('mainwin.closeEvent')
        self._save_settings()

        event.accept()

    def on_combobox_changed(self):
        self.isSerialSettingChanged = True
        if ((self.ser != None) and (self.ser.is_open == True)):
            self.addMessage("Port " + self.port + " is open, going to close it\n")
            self.ser.close()
            self.connect_btn.setText("Connect")

    def on_browse_btn_pressed(self) -> None:
        """Open dialog to select bin file."""
        logthread('mainwin.on_browse_btn_pressed')
        options = QFileDialog.Options()
        fileName, _ = QFileDialog.getOpenFileName(
            None,
            "Select Firmware to Upload",
            "",
            "Firmware Files (*.bin);;All Files (*)",
            options=options)
        if fileName:
            self.fileLocation_lineedit.setText(fileName)

    def on_refresh_btn_pressed(self) -> None:
        logthread('mainwin.on_refresh_btn_pressed')
        self.update_com_ports()
        self.addMessage("Ports Refreshed\n")

    def on_clear_btn_pressed(self) -> None:
        logthread('mainwin.on_refresh_btn_pressed')
        self.messages.clear()
        self.messages_remote.clear()
        self.showDatetime()

    def on_connect_btn_pressed(self) -> None:
        logthread('mainwin.on_connect_btn_pressed')
        if ((self.ser == None) or (self.isSerialSettingChanged == True)):
            self.addMessage("Updated settings of port " + str(self.port))
            self.ser = serial.Serial(None, self.baudRate, timeout=1)
            self.ser.port = self.port
            self.isSerialSettingChanged = False
        try:
                if (self.ser.is_open == True):
                    self.addMessage("Closed port " + self.port)
                    self.ser.close()
                    self.connect_btn.setText("Connect")
                else:
                     # Open the serial port
                    self.addMessage("Opened port " + self.port + " at " + str(self.baudRate) + " Baud")
                    self.ser.open()
                    self.connect_btn.setText("Disconnect")
        except IOError:
            self.addMessage("Failed to connect to port " + str(self.port))

    def on_update_dt_btn_pressed(self) -> None:
        logthread('mainwin.on_update_dt_btn_pressed')
        currDT = datetime.datetime.now()
        if (self.ser != None):
            if (self.ser.is_open == True):
                self.addMessage("Updated remote date/time to " + currDT.strftime("%Y-%m-%d %H:%M:%S"))
                DT = str(currDT.year - 2000) + " " + \
                     str(currDT.month) + " " + \
                     str(currDT.day) + " " + \
                     str(currDT.hour) + " " + \
                     str(currDT.minute) + " " + \
                     str(currDT.second)
                payload = bytes('DateTime ' + DT, encoding='utf8')
                self.ser.write(payload) 
                #remoteReply = self.ser.read(30)
                #self.addMessage("Received reply " + str(remoteReply))
            else:
                self.addMessage("Serial port is not open, connect a port first")
        else:
                self.addMessage("Serial port is not open, connect a port first")

    def on_upload_btn_pressed(self) -> None:
        """Check if port is available"""
        logthread('mainwin.on_update_dt_btn_pressed')
        portAvailable = False
        for desc, name, sys in gen_serial_ports():
            if (sys == self.port):
                portAvailable = True
        if (portAvailable == False):
            self.addMessage("Port No Longer Available")
            return

        """Check if file exists"""
        fileExists = False
        try:
            f = open(self.fileLocation_lineedit.text())
            fileExists = True
        except IOError:
            fileExists = False
        finally:
            if (fileExists == False):
                self.addMessage("File Not Found")
                return
            f.close()

        self.addMessage("\nUploading firmware")

        self.uploader = Uploader(self.ser, self.fileLocation_lineedit.text())
        self.upload_thread = QThread()
        self.uploader.moveToThread(self.upload_thread)
        self.uploader.addMessage[str].connect(self.addMessage)
        self.uploader.addMessageRemote[str].connect(self.addMessageRemote)
        self.uploader.finished.connect(self.done)

        # start uploader
        self.upload_thread.started.connect(self.uploader.upload_main)
        self.upload_thread.start()

        self.browse_btn.setEnabled(False)
        self.refresh_btn.setEnabled(False)
        self.clear_btn.setEnabled(False)
        self.upload_btn.setEnabled(False)

        #self.upload_main() # Call artemis_svl.py (previously this spawned a QProcess)

    def done(self):
        """
        Enable buttons when done
        """
        logthread('mainwin.done')
        self.browse_btn.setEnabled(True)
        self.refresh_btn.setEnabled(True)
        self.clear_btn.setEnabled(True)
        self.upload_btn.setEnabled(True)

#    def on_update_bootloader_btn_pressed(self) -> None:
#        """Check if port is available"""
#        portAvailable = False
#        for desc, name, sys in gen_serial_ports():
#            if (sys == self.port):
#                portAvailable = True
#        if (portAvailable == False):
#            self.addMessage("Port No Longer Available")
#            return

#        """Check if file exists"""
#        fileExists = False
#        try:
#            f = open(resource_path(self.appFile))
#            fileExists = True
#        except IOError:
#            fileExists = False
#        finally:
#            if (fileExists == False):
#                self.addMessage("Bootloader file Not Found")
#                return
#            f.close()

#        self.addMessage("\nUpdating bootloader")

#        self.update_main() # Call ambiq_bin2board.py (previously this spawned a QProcess)

#    # ///// START of code taken from am_defines.py

#    def crc32(self, L):
#        """CRC using ethernet poly, as used by Corvette hardware for validation"""
#        return (binascii.crc32(L) & 0xFFFFFFFF)

#    def pad_to_block_size(self, text, block_size, bZeroPad):
#        """Pad the text to the block_size."""
#        text_length = len(text)
#        amount_to_pad = block_size - (text_length % block_size)
#        if (amount_to_pad == block_size):
#            if (bZeroPad == 0):
#                amount_to_pad = 0
#        for i in range(0, amount_to_pad, 1):
#            text += bytes(chr(amount_to_pad), 'ascii')
#        return text


#    def encrypt_app_aes(self, cleartext, encKey, iv):
#        """AES CBC encryption"""
#        key = array.array('B', encKey).tostring()
#        ivVal = array.array('B', iv).tostring()
#        plaintext = array.array('B', cleartext).tostring()

#        encryption_suite = AES.new(key, AES.MODE_CBC, ivVal)
#        cipher_text = encryption_suite.encrypt(plaintext)
        
#        return cipher_text


#    def encrypt_app_aes128(self, cleartext, encKey, iv):
#        """AES 128 CBC encryption"""
#        key = array.array('B', encKey).tostring()
#        ivVal = array.array('B', iv).tostring()
#        plaintext = array.array('B', cleartext).tostring()

#        encryption_suite = AES.new(key, AES.MODE_CBC, ivVal)
#        cipher_text = encryption_suite.encrypt(plaintext)
        
#        return cipher_text

    
#    def compute_hmac(self, key, data):
#        """SHA256 HMAC"""
#        sig = hmac.new(array.array('B', key).tostring(), array.array('B', data).tostring(), hashlib.sha256).digest()
#        return sig


#    def fill_word(self, barray, offset, w):
#        """Fill one word in bytearray"""
#        # I guess barray must be mutable?
#        barray[offset + 0]  = (w >>  0) & 0x000000ff;
#        barray[offset + 1]  = (w >>  8) & 0x000000ff;
#        barray[offset + 2]  = (w >> 16) & 0x000000ff;
#        barray[offset + 3]  = (w >> 24) & 0x000000ff;


#    def int_to_bytes(self, n) -> bytes:
#        """Turn a 32-bit number into a series of bytes for transmission."""
#        A = [n & 0xFF,
#             (n >> 8) & 0xFF,
#             (n >> 16) & 0xFF,
#             (n >> 24) & 0xFF]

#        return A


#    def word_from_bytes(self, B, n):
#        """Extract a word from a byte array"""
#        return (B[n] + (B[n + 1] << 8) + (B[n + 2] << 16) + (B[n + 3] << 24))


#    def auto_int(self, x) -> int:
#        """automatically figure out the integer format (base 10 or 16)"""
#        return int(x, 0)

#    # ///// END of code taken from am_defines.py

#    # ///// START of code taken from ambiq_bin2board.py

#    def bin2blob_process(self) -> None:
## was:       def bin2blob_process(loadaddress, appFile, magicNum, crcI, crcB, authI, authB, protection, authKeyIdx, output, encKeyIdx, version, erasePrev, child0, child1, authalgo, encalgo):
## was called as: bin2blob_process(args.loadaddress_blob, args.appFile, args.magic_num, args.crcI, args.crcB, args.authI, args.authB, args.protection, args.authkey, args.output, args.kek, args.version, args.erasePrev, args.child0, args.child1, args.authalgo, args.encalgo)
#        """Generate the image blob as per command line parameters"""

#        loadaddress = self.load_address_blob

#        app_binarray = bytearray()
#        # Open the file, and read it into an array of integers.
#        with open(resource_path(self.appFile),'rb') as f_app:
#            app_binarray.extend(f_app.read())
#            f_app.close()

#        encKeyIdx = self.kek

#        encVal = 0
#        if (self.encalgo != 0):
#            encVal = 1
#            if ((encKeyIdx < self.minAesKeyIdx) or (encKeyIdx > self.maxAesKeyIdx)):
#                self.addMessage("Invalid encKey Idx " + str(encKeyIdx))
#                return
#            if (self.encalgo == 2):
#                if (encKeyIdx & 0x1):
#                    self.addMessage("Invalid encKey Idx " + str(encKeyIdx))
#                    return
#                keySize = 32
#            else:
#                keySize = 16

#        authKeyIdx = self.authkey

#        if (self.authalgo != 0):
#            if ((authKeyIdx < self.minHmacKeyIdx) or (authKeyIdx > self.maxHmacKeyIdx) or (authKeyIdx & 0x1)):
#                self.addMessage("Invalid authKey Idx " + str(authKeyIdx))
#                return

#        if (self.magic_num == self.AM_IMAGE_MAGIC_MAIN):
#            hdr_length  = self.AM_IMAGEHDR_SIZE_MAIN;   #fixed header length
#        elif ((self.magic_num == self.AM_IMAGE_MAGIC_CHILD) or (self.magic_num == self.AM_IMAGE_MAGIC_CUSTPATCH) or (self.magic_num == self.AM_IMAGE_MAGIC_NONSECURE) or (self.magic_num == self.AM_IMAGE_MAGIC_INFO0)):
#            hdr_length  = self.AM_IMAGEHDR_SIZE_AUX;   #fixed header length
#        else:
#            self.addMessage("magic number" +str(hex(self.magic_num)) + " not supported")
#            return
#        self.addMessage("Header Size = " + str(hex(hdr_length)))

#        #generate mutable byte array for the header
#        hdr_binarray = bytearray([0x00]*hdr_length);

#        orig_app_length  = (len(app_binarray))
#        self.addMessage("original app_size " + str(orig_app_length))

#        self.addMessage("load_address " + str(hex(loadaddress)))
#        if (loadaddress & 0x3):
#            self.addMessage("load address needs to be word aligned")
#            return

#        if (self.magic_num == self.AM_IMAGE_MAGIC_INFO0):
#            if (orig_app_length & 0x3):
#                self.addMessage("INFO0 blob length needs to be multiple of 4")
#                return
#            if ((loadaddress + orig_app_length) > self.INFO_SIZE_BYTES):
#                self.addMessage("INFO0 Offset and length exceed size")
#                return

#        if (encVal == 1):
#            block_size = self.AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES
#            app_binarray = self.pad_to_block_size(app_binarray, block_size, 1)
#        else:
#            # Add Padding
#            app_binarray = self.pad_to_block_size(app_binarray, 4, 0)

#        app_length  = (len(app_binarray))
#        self.addMessage("app_size " + str(app_length))

#        # Create Image blobs

#        # w0
#        blobLen = hdr_length + app_length
#        w0 = (self.magic_num << 24) | ((encVal & 0x1) << 23) | blobLen

#        self.addMessage("w0 = " + str(hex(w0)))
#        self.fill_word(hdr_binarray, 0, w0)

#        # w2
#        securityVal = ((self.authI << 1) | self.crcI) << 4 | (self.authB << 1) | self.crcB
#        self.addMessage("Security Value " + str(hex(securityVal)))
#        w2 = ((securityVal << 24) & 0xff000000) | ((self.authalgo) & 0xf) | ((authKeyIdx << 4) & 0xf0) | ((self.encalgo << 8) & 0xf00) | ((encKeyIdx << 12) & 0xf000)
#        self.fill_word(hdr_binarray, 8, w2)
#        self.addMessage("w2 = " + str(hex(w2)))


#        if (self.magic_num == self.AM_IMAGE_MAGIC_INFO0):
#            # Insert the INFO0 size and offset
#            addrWord = ((orig_app_length>>2) << 16) | ((loadaddress>>2) & 0xFFFF)
#            versionKeyWord = self.INFO_KEY
#        else:
#            # Insert the application binary load address.
#            addrWord = loadaddress | (self.protection & 0x3)
#            # Initialize versionKeyWord
#            versionKeyWord = (self.version & 0x7FFF) | ((self.erasePrev & 0x1) << 15)

#        self.addMessage("addrWord = " + str(hex(addrWord)))
#        self.fill_word(hdr_binarray, self.AM_IMAGEHDR_OFFSET_ADDR, addrWord)

#        self.addMessage("versionKeyWord = " + str(hex(versionKeyWord)))
#        self.fill_word(hdr_binarray, self.AM_IMAGEHDR_OFFSET_VERKEY, versionKeyWord)

#        # Initialize child (Child Ptr/ Feature key)
#        self.addMessage("child0/feature = " + str(hex(self.child0)))
#        self.fill_word(hdr_binarray, self.AM_IMAGEHDR_OFFSET_CHILDPTR, self.child0)
#        self.addMessage("child1 = " + str(hex(self.child1)))
#        self.fill_word(hdr_binarray, self.AM_IMAGEHDR_OFFSET_CHILDPTR + 4, self.child1)

#        authKeyIdx = authKeyIdx - self.minHmacKeyIdx
#        if (self.authB != 0): # Authentication needed
#            self.addMessage("Boot Authentication Enabled")
#    #        am_print("Key used for HMAC")
#    #        am_print([hex(keyTblHmac[authKeyIdx*AM_SECBOOT_KEYIDX_BYTES + n]) for n in range (0, AM_HMAC_SIG_SIZE)])
#            # Initialize the clear image HMAC
#            sigClr = self.compute_hmac(self.keyTblHmac[authKeyIdx*self.AM_SECBOOT_KEYIDX_BYTES:(authKeyIdx*self.AM_SECBOOT_KEYIDX_BYTES+self.AM_HMAC_SIG_SIZE)], (hdr_binarray[self.AM_IMAGEHDR_START_HMAC:hdr_length] + app_binarray))
#            self.addMessage("HMAC Clear")
#            #am_print([hex(n) for n in sigClr])
#            # Fill up the HMAC
#            for x in range(0, self.AM_HMAC_SIG_SIZE):
#                hdr_binarray[self.AM_IMAGEHDR_OFFSET_SIGCLR + x]  = sigClr[x]

#        # All the header fields part of the encryption are now final
#        if (encVal == 1):
#            self.addMessage("Encryption Enabled")
#            encKeyIdx = encKeyIdx - self.minAesKeyIdx
#            ivValAes = os.urandom(self.AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES)
#            self.addMessage("Initialization Vector")
#            #am_print([hex(ivValAes[n]) for n in range (0, AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES)])
#            keyAes = os.urandom(keySize)
#            self.addMessage("AES Key used for encryption")
#            #am_print([hex(keyAes[n]) for n in range (0, keySize)])
#            # Encrypted Part
#            self.addMessage("Encrypting blob of size " + str((hdr_length - self.AM_IMAGEHDR_START_ENCRYPT + app_length)))
#            enc_binarray = self.encrypt_app_aes((hdr_binarray[self.AM_IMAGEHDR_START_ENCRYPT:hdr_length] + app_binarray), keyAes, ivValAes)
#    #        am_print("Key used for encrypting AES Key")
#    #        am_print([hex(keyTblAes[encKeyIdx*keySize + n]) for n in range (0, keySize)])
#            # Encrypted Key
#            enc_key = self.encrypt_app_aes(keyAes, self.keyTblAes[encKeyIdx*keySize:encKeyIdx*keySize + keySize], ivVal0)
#            self.addMessage("Encrypted Key")
#            #am_print([hex(enc_key[n]) for n in range (0, keySize)])
#            # Fill up the IV
#            for x in range(0, self.AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES):
#                hdr_binarray[self.AM_IMAGEHDR_OFFSET_IV + x]  = ivValAes[x]
#            # Fill up the Encrypted Key
#            for x in range(0, keySize):
#                hdr_binarray[self.AM_IMAGEHDR_OFFSET_KEK + x]  = enc_key[x]
#        else:
#            enc_binarray = hdr_binarray[self.AM_IMAGEHDR_START_ENCRYPT:hdr_length] + app_binarray


#        if (self.authI != 0): # Install Authentication needed
#            self.addMessage("Install Authentication Enabled")
#    #        am_print("Key used for HMAC")
#    #        am_print([hex(keyTblHmac[authKeyIdx*AM_SECBOOT_KEYIDX_BYTES + n]) for n in range (0, AM_HMAC_SIG_SIZE)])
#            # Initialize the top level HMAC
#            sig = self.compute_hmac(self.keyTblHmac[authKeyIdx*self.AM_SECBOOT_KEYIDX_BYTES:(authKeyIdx*self.AM_SECBOOT_KEYIDX_BYTES+self.AM_HMAC_SIG_SIZE)], (hdr_binarray[self.AM_IMAGEHDR_START_HMAC_INST:self.AM_IMAGEHDR_START_ENCRYPT] + enc_binarray))
#            self.addMessage("Generated Signature")
#            #am_print([hex(n) for n in sig])
#            # Fill up the HMAC
#            for x in range(0, self.AM_HMAC_SIG_SIZE):
#                hdr_binarray[self.AM_IMAGEHDR_OFFSET_SIG + x]  = sig[x]
#        # compute the CRC for the blob - this is done on a clear image
#        crc = self.crc32(hdr_binarray[self.AM_IMAGEHDR_START_CRC:hdr_length] + app_binarray)
#        self.addMessage("crc =  " + str(hex(crc)))
#        w1 = crc
#        self.fill_word(hdr_binarray, self.AM_IMAGEHDR_OFFSET_CRC, w1)

#        # now output all three binary arrays in the proper order
#        output = self.output_file + '_OTA_blob.bin'
#        self.blob2wiredfile = output # save the output of bin2blob for use by blob2wired
#        self.addMessage("Writing to file " + str(output))
#        with open(output, mode = 'wb') as out:
#            out.write(hdr_binarray[0:self.AM_IMAGEHDR_START_ENCRYPT])
#            out.write(enc_binarray)


#    def blob2wired_process(self, appFile) -> None:
## was:       def blob2wired_process(appFile, imagetype, loadaddress, authalgo, encalgo, authKeyIdx, encKeyIdx, optionsVal, maxSize, output):
## was called as: blob2wired_process( blob2wiredfile, args.imagetype, args.loadaddress_image, args.authalgo, args.encalgo, args.authkey, args.kek, args.options, args.split, args.output)

#        """Generate the image blob as per command line parameters"""

#        loadaddress = self.load_address_image

#        app_binarray = bytearray()
#        # Open the file, and read it into an array of integers.
#        self.addMessage("testing: " + appFile )
#        with open(appFile,'rb') as f_app:
#            app_binarray.extend(f_app.read())
#            f_app.close()

#        # Make sure it is page multiple
#        if ((self.split & (self.FLASH_PAGE_SIZE - 1)) != 0):
#            self.addMessage("Split needs to be multiple of flash page size")
#            return

#        encKeyIdx = self.kek

#        if (self.encalgo != 0):
#            if ((encKeyIdx < self.minAesKeyIdx) or (encKeyIdx > self.maxAesKeyIdx)):
#                self.addMessage("Invalid encKey Idx " + str(encKeyIdx))
#                return
#            if (self.encalgo == 2):
#                if (encKeyIdx & 0x1):
#                    self.addMessage("Invalid encKey Idx " + str(encKeyIdx))
#                    return
#                keySize = 32
#            else:
#                keySize = 16

#        authKeyIdx = self.authkey

#        if (self.authalgo != 0):
#            if ((authKeyIdx < self.minHmacKeyIdx) or (authKeyIdx > self.maxHmacKeyIdx) or (authKeyIdx & 0x1)):
#                self.addMessage("Invalid authKey Idx " + str(authKeyIdx))
#                return

#        hdr_length  = self.AM_WU_IMAGEHDR_SIZE;   #fixed header length
#        self.addMessage("Header Size = " + str(hex(hdr_length)))

#        orig_app_length  = (len(app_binarray))

#        if (self.encalgo != 0):
#            block_size = keySize
#            app_binarray = self.pad_to_block_size(app_binarray, block_size, 1)
#        else:
#            # Add Padding
#            app_binarray = self.pad_to_block_size(app_binarray, 4, 0)

#        app_length  = (len(app_binarray))
#        self.addMessage("app_size = " + str(app_length))

#        if (app_length + hdr_length > self.split):
#            self.addMessage("Image size bigger than max - Creating Split image")

#        start = 0
#        # now output all three binary arrays in the proper order
#        output = self.output_file + '_Wired_OTA_blob.bin'
#        self.uploadbinfile = output # save the name of the output from blob2wired
#        out = open(output, mode = 'wb')

#        while (start < app_length):
#            #generate mutable byte array for the header
#            hdr_binarray = bytearray([0x00]*hdr_length);

#            if (app_length - start > self.split):
#                end = start + self.split
#            else:
#                end = app_length

#            if (self.image_type == self.AM_SECBOOT_WIRED_IMAGETYPE_INFO0_NOOTA):
#                key = self.INFO_KEY
#                # word offset
#                self.fill_word(hdr_binarray, self.AM_WU_IMAGEHDR_OFFSET_ADDR, loadaddress>>2)
#            else:
#                key = self.FLASH_KEY
#                # load address
#                self.fill_word(hdr_binarray, self.AM_WU_IMAGEHDR_OFFSET_ADDR, loadaddress)
#            # Create imageType & options
#            hdr_binarray[self.AM_WU_IMAGEHDR_OFFSET_IMAGETYPE] = self.image_type
#            # Set the options only for the first block
#            if (start == 0):
#                hdr_binarray[self.AM_WU_IMAGEHDR_OFFSET_OPTIONS] = self.options
#            else:
#                hdr_binarray[self.AM_WU_IMAGEHDR_OFFSET_OPTIONS] = 0

#            # Create Info0 Update Blob for wired update
#            self.fill_word(hdr_binarray, self.AM_WU_IMAGEHDR_OFFSET_KEY, key)
#            # update size
#            self.fill_word(hdr_binarray, self.AM_WU_IMAGEHDR_OFFSET_SIZE, end-start)

#            w0 = ((self.authalgo & 0xf) | ((authKeyIdx << 8) & 0xf00) | ((self.encalgo << 16) & 0xf0000) | ((encKeyIdx << 24) & 0x0f000000))

#            self.fill_word(hdr_binarray, 0, w0)

#            if (self.encalgo != 0):
#                keyIdx = encKeyIdx - self.minAesKeyIdx
#                ivValAes = os.urandom(self.AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES)
#                self.addMessage("Initialization Vector")
#                #am_print([hex(n) for n in ivValAes])
#                keyAes = os.urandom(keySize)
#                self.addMessage("AES Key used for encryption")
#                #am_print([hex(keyAes[n]) for n in range (0, keySize)])
#                # Encrypted Part - after security header
#                enc_binarray = self.encrypt_app_aes((hdr_binarray[self.AM_WU_IMAGEHDR_START_ENCRYPT:hdr_length] + app_binarray[start:end]), keyAes, ivValAes)
#    #            am_print("Key used for encrypting AES Key")
#    #            am_print([hex(keyTblAes[keyIdx*AM_SECBOOT_KEYIDX_BYTES + n]) for n in range (0, keySize)])
#                # Encrypted Key
#                enc_key = self.encrypt_app_aes(keyAes, self.keyTblAes[keyIdx*self.AM_SECBOOT_KEYIDX_BYTES:(keyIdx*self.AM_SECBOOT_KEYIDX_BYTES + keySize)], ivVal0)
#                self.addMessage("Encrypted Key")
#                #am_print([hex(enc_key[n]) for n in range (0, keySize)])
#                # Fill up the IV
#                for x in range(0, self.AM_SECBOOT_AESCBC_BLOCK_SIZE_BYTES):
#                    hdr_binarray[self.AM_WU_IMAGEHDR_OFFSET_IV + x]  = ivValAes[x]
#                # Fill up the Encrypted Key
#                for x in range(0, keySize):
#                    hdr_binarray[self.AM_WU_IMAGEHDR_OFFSET_KEK + x]  = enc_key[x]
#            else:
#                enc_binarray = hdr_binarray[self.AM_WU_IMAGEHDR_START_ENCRYPT:hdr_length] + app_binarray[start:end]


#            if (self.authalgo != 0): # Authentication needed
#                keyIdx = authKeyIdx - self.minHmacKeyIdx
#    #            am_print("Key used for HMAC")
#    #            am_print([hex(keyTblHmac[keyIdx*AM_SECBOOT_KEYIDX_BYTES + n]) for n in range (0, AM_HMAC_SIG_SIZE)])
#                # Initialize the HMAC - Sign is computed on image following the signature
#                sig = self.compute_hmac(self.keyTblHmac[keyIdx*self.AM_SECBOOT_KEYIDX_BYTES:(keyIdx*self.AM_SECBOOT_KEYIDX_BYTES+self.AM_HMAC_SIG_SIZE)], hdr_binarray[self.AM_WU_IMAGEHDR_START_HMAC:self.AM_WU_IMAGEHDR_START_ENCRYPT] + enc_binarray)
#                self.addMessage("HMAC")
#                #am_print([hex(n) for n in sig])
#                # Fill up the HMAC
#                for x in range(0, self.AM_HMAC_SIG_SIZE):
#                    hdr_binarray[self.AM_WU_IMAGEHDR_OFFSET_SIG + x]  = sig[x]

#            self.addMessage("Writing to file " + str(output))
#            self.addMessage("Image from " + str(hex(start)) + " to " + str(hex(end)) + " will be loaded at " + str(hex(loadaddress)))
#            out.write(hdr_binarray[0:self.AM_WU_IMAGEHDR_START_ENCRYPT])
#            out.write(enc_binarray)

#            # Reset start for next chunk
#            start = end
#            loadaddress = loadaddress + self.split


#    def updater(self) -> None:
#        """Updater main function"""

#        # Open a serial port, and communicate with Device
#        #
#        # Max flashing time depends on the amount of SRAM available.
#        # For very large images, the flashing happens page by page.
#        # However if the image can fit in the free SRAM, it could take a long time
#        # for the whole image to be flashed at the end.
#        # The largest image which can be stored depends on the max SRAM.
#        # Assuming worst case ~100 ms/page of flashing time, and allowing for the
#        # image to be close to occupying full SRAM (256K) which is 128 pages.

#        connection_timeout = 5

#        self.addMessage("Connecting over serial port...")

#        # Artemis-base boards need 115200 baud
#        if (self.artemis.isChecked()):
#            if (self.baudRate > 115200):
#                index = self.baud_combobox.findData(115200)
#                if index > -1:
#                    self.baud_combobox.setCurrentIndex(index)
#                    self.addMessage("Changing Baud Rate to 115200")
#        # Apollo3 dev boards (SparkFun Edge) need 921600
#        else:
#            if (self.baudRate < 921600):
#                index = self.baud_combobox.findData(921600)
#                if index > -1:
#                    self.baud_combobox.setCurrentIndex(index)
#                    self.addMessage("Changing Baud Rate to 921600")

#        #Check to see if the com port is available
#        try:
#            with serial.Serial(self.port, self.baudRate, timeout=connection_timeout) as self.ser:
#                pass
#        except:
#            self.addMessage("Could not open serial port!")
#            return

#        #Begin talking over com port

#        #The auto-bootload sequence is good but not fullproof. The bootloader
#        #fails to correctly catch the BOOT signal about 1 out of ten times.
#        #Auto-retry this number of times before we give up.

#        self.loadTries = 0

#        while self.loadTries < 3:
#            self.loadSuccess = False

#            with serial.Serial(self.port, self.baudRate, timeout=connection_timeout) as self.ser:
#                #DTR is driven low when serial port open. DTR has now pulled RST low.

#                # time.sleep(0.005) #3ms and 10ms work well. Not 50, and not 0.
#                time.sleep(0.008) #3ms and 10ms work well. Not 50, and not 0.

#                #Setting RTS/DTR high causes the bootload pin to go high, then fall across 100ms
#                self.ser.setDTR(0) #Set DTR high
#                self.ser.setRTS(0) #Set RTS high - support the CH340E

#                #Give bootloader a chance to run and check bootload pin before communication begins. But must initiate com before bootloader timeout of 250ms.
#                time.sleep(0.100) #100ms works well

#                self.ser.reset_input_buffer()    # reset the input bufer to discard any UART traffic that the device may have generated

#                self.connect_device()

#                if(self.loadSuccess == True):
#                    self.addMessage("Tries = " + str(self.loadTries))
#                    self.addMessage("Bootloader updated to version " + str(BOOTLOADER_VERSION))
#                    return
#                else:
#                    self.addMessage("Fail")

#                self.loadTries = self.loadTries + 1

#        self.addMessage("Tries = " + str(self.loadTries))
#        self.addMessage("Upload failed!")

#        try:
#            self.ser.close()
#        except:
#            pass

#        return


#    def connect_device(self) -> None:
#        """Communicate with Device. Given a serial port, connects to the target device using the UART."""

#        # Send Hello
#        #generate mutable byte array for the header
#        hello = bytearray([0x00]*4)
#        self.fill_word(hello, 0, ((8 << 16) | self.AM_SECBOOT_WIRED_MSGTYPE_HELLO))
#        self.addMessage("Sending Hello.")
#        response, success = self.send_command(hello, 88)

#        #Check if response failed
#        if success == False:
#            self.addMessage("Failed to respond")
#            return

#        self.addMessage("Received response for Hello")
#        word = self.word_from_bytes(response, 4)
#        if ((word & 0xFFFF) == self.AM_SECBOOT_WIRED_MSGTYPE_STATUS):
#            # Received Status
#            self.addMessage("Bootloader connected")

#            self.addMessage("Received Status")
#            self.addMessage("Length = " + str(hex((word >> 16))))
#            self.addMessage("Version = " + str(hex(self.word_from_bytes(response, 8))))
#            self.addMessage("Max Storage = " + str(hex(self.word_from_bytes(response, 12))))
#            self.addMessage("Status = " + str(hex(self.word_from_bytes(response, 16))))
#            self.addMessage("State = " + str(hex(self.word_from_bytes(response, 20))))
###            verboseprint("AMInfo = ")
###            for x in range(24, 88, 4):
###                verboseprint(hex(self.word_from_bytes(response, x)))

#            if (self.abort != -1):
#                # Send OTA Desc
#                self.addMessage("Sending Abort command.")
#                abortMsg = bytearray([0x00]*8);
#                self.fill_word(abortMsg, 0, ((12 << 16) | self.AM_SECBOOT_WIRED_MSGTYPE_ABORT))
#                self.fill_word(abortMsg, 4, self.abort)
#                response, success = self.send_ackd_command(abortMsg)
#                if success == False:
#                    self.addMessage("Failed to ack command")
#                    return

#            otadescaddr = self.otadesc
#            if (otadescaddr != 0xFFFFFFFF):
#                # Send OTA Desc
#                self.addMessage("Sending OTA Descriptor = " + str(hex(otadescaddr)))
#                otaDesc = bytearray([0x00]*8);
#                self.fill_word(otaDesc, 0, ((12 << 16) | self.AM_SECBOOT_WIRED_MSGTYPE_OTADESC))
#                self.fill_word(otaDesc, 4, otadescaddr)
#                response, success = self.send_ackd_command(otaDesc)
#                if success == False:
#                    self.addMessage("Failed to ack command")
#                    return


#            imageType = self.image_type
#            if (self.uploadbinfile != ''):

#                # Read the binary file from the command line.
#                with open(self.uploadbinfile, mode='rb') as binfile:
#                    application = binfile.read()
#                # Gather the important binary metadata.
#                totalLen = len(application)
#                # Send Update command
#                self.addMessage("Sending Update Command.")

#                # It is assumed that maxSize (self.split) is 256b multiple
#                maxImageSize = self.split
#                if ((maxImageSize & (self.FLASH_PAGE_SIZE - 1)) != 0):
#                    self.addMessage("Split needs to be multiple of flash page size")
#                    return

#                # Each Block of image consists of AM_WU_IMAGEHDR_SIZE Bytes Image header and the Image blob
#                maxUpdateSize = self.AM_WU_IMAGEHDR_SIZE + maxImageSize
#                numUpdates = (totalLen + maxUpdateSize - 1) // maxUpdateSize # Integer division
#                self.addMessage("Number of updates needed = " + str(numUpdates))

#                end = totalLen
#                for numUpdates in range(numUpdates, 0 , -1):
#                    start = (numUpdates-1)*maxUpdateSize
#                    crc = self.crc32(application[start:end])
#                    applen = end - start
#                    self.addMessage("Sending block of size " + str(hex(applen)) + " from " + str(hex(start)) + " to " + str(hex(end)))
#                    end = end - applen

#                    update = bytearray([0x00]*16);
#                    self.fill_word(update, 0, ((20 << 16) | self.AM_SECBOOT_WIRED_MSGTYPE_UPDATE))
#                    self.fill_word(update, 4, applen)
#                    self.fill_word(update, 8, crc)
#                    # Size = 0 => We're not piggybacking any data to IMAGE command
#                    self.fill_word(update, 12, 0)

#                    response, success = self.send_ackd_command(update)
#                    if success == False:
#                        self.addMessage("Failed to ack command")
#                        return

#                    # Loop over the bytes in the image, and send them to the target.
#                    resp = 0
#                    # Max chunk size is AM_MAX_UART_MSG_SIZE adjusted for the header for Data message
#                    maxChunkSize = self.AM_MAX_UART_MSG_SIZE - 12
#                    for x in range(0, applen, maxChunkSize):
#                        # Split the application into chunks of maxChunkSize bytes.
#                        # This is the max chunk size supported by the UART bootloader
#                        if ((x + maxChunkSize) > applen):
#                            chunk = application[start+x:start+applen]
#    #                        print(str(hex(start+x)), " to ", str(hex(applen)))
#                        else:
#                            chunk = application[start+x:start+x+maxChunkSize]
#    #                        print(str(hex(start+x)), " to ", str(hex(start + x + maxChunkSize)))

#                        chunklen = len(chunk)

#                        # Build a data packet with a "data command" a "length" and the actual
#                        # payload bytes, and send it to the target.
#                        dataMsg = bytearray([0x00]*8);
#                        self.fill_word(dataMsg, 0, (((chunklen + 12) << 16) | self.AM_SECBOOT_WIRED_MSGTYPE_DATA))
#                        # seqNo
#                        self.fill_word(dataMsg, 4, x)

#                        self.addMessage("Sending Data Packet of length " + str(chunklen))
#                        response, success = self.send_ackd_command(dataMsg + chunk)
#                        if success == False:
#                            self.addMessage("Failed to ack command")
#                            return

###            if (args.raw != ''):
###
###                # Read the binary file from the command line.
###                with open(args.raw, mode='rb') as rawfile:
###                    blob = rawfile.read()
###                # Send Raw command
###                verboseprint('Sending Raw Command.')
###                ser.write(blob)

#            if (self.reset_after != 0):
#                # Send reset
#                self.addMessage("Sending Reset Command.")
#                resetmsg = bytearray([0x00]*8);
#                self.fill_word(resetmsg, 0, ((12 << 16) | self.AM_SECBOOT_WIRED_MSGTYPE_RESET))
#                # options
#                self.fill_word(resetmsg, 4, self.reset_after)
#                response, success = self.send_ackd_command(resetmsg)
#                if success == False:
#                    self.addMessage("Failed to ack command")
#                    return


#            # Success! We're all done
#            self.loadSuccess = True
#        else:
#            # Received Wrong message
#            self.addMessage("Received Unknown Message")
#            word = self.word_from_bytes(response, 4)
#            self.addMessage("msgType = " + str(hex(word & 0xFFFF)))
#            self.addMessage("Length = " + str(hex(word >> 16)))


#    def send_ackd_command(self, command) -> (bytes, bool):
#        """Send ACK'd command. Sends a command, and waits for an ACK."""

#        response, success = self.send_command(command, 20)

#        #Check if response failed
#        if success == False:
#            self.addMessage("Response not valid")
#            return (b'',False) #Return error

#        word = self.word_from_bytes(response, 4)
#        if ((word & 0xFFFF) == self.AM_SECBOOT_WIRED_MSGTYPE_ACK):
#            # Received ACK
#            if (self.word_from_bytes(response, 12) != self.AM_SECBOOT_WIRED_ACK_STATUS_SUCCESS):
#                self.addMessage("Received NACK")
#                self.addMessage("msgType = " + str(hex(self.word_from_bytes(response, 8))))
#                self.addMessage("error = " + str(hex(self.word_from_bytes(response, 12))))
#                self.addMessage("seqNo = " + str(hex(self.word_from_bytes(response, 16))))
#                self.addMessage("Upload failed: No ack to command")

#                return (b'',False) #Return error

#        return (response, True)


#    def send_command(self, params, response_len) -> (bytes, bool):
#        """Send command. Sends a command, and waits for the response."""

#        # Compute crc
#        crc = self.crc32(params)
#    #    print([hex(n) for n in int_to_bytes(crc)])
#    #    print([hex(n) for n in params])
#        # send crc first
#        self.ser.write(self.int_to_bytes(crc))

#        # Next, send the parameters.
#        self.ser.write(params)

#        response = b''
#        response = self.ser.read(response_len)

#        # Make sure we got the number of bytes we asked for.
#        if len(response) != response_len:
#            self.addMessage("No response for command " + str(params))
#            n = len(response)
#            if (n != 0):
#                self.addMessage("received " + str(len(response)) + " bytes")
#            return (b'',False)

#        return (response, True)


#    def send_bytewise_command(self, command, params, response_len) -> (bytes, bool):
#        """Send a command that uses an array of bytes as its parameters."""

#        # Send the command first.
#        ser.write(self.int_to_bytes(command))

#        # Next, send the parameters.
#        ser.write(params)

#        response = b''
#        response = self.ser.read(response_len)

#        # Make sure we got the number of bytes we asked for.
#        if len(response) != response_len:
#            self.addMessage("Upload failed: No reponse to command")
#            return (b'',False)

#        return (response, True)


#    def update_main(self) -> None:
#        """Updater main function"""

#        #self.messages.clear() # Clear the message window

#        self.addMessage("\nArtemis Bootloader Update\n")
#        self.addMessage("Installing bootloader version " + str(BOOTLOADER_VERSION))

#        self.bin2blob_process()
#        self.blob2wired_process(self.blob2wiredfile)
#        self.updater()


#    # ///// END of code taken from ambiq_bin2board.py

class Uploader(QObject):
    addMessage = pyqtSignal(str)
    addMessageRemote = pyqtSignal(str)
    finished = pyqtSignal()

    def __init__(self, ser, fileLocation):
        #QThread.__init__(self)
        super().__init__()
        logthread('Uploader.__init__')
        
        self.ser = ser
        self.fileLocation = fileLocation
        self.installed_bootloader = -1 # Use this to record the bootloader version

        # ///// START of code taken from artemis_svl.py
        
        # Really these should not be self.'globals'. It might be best to put them back into a separate file?
            
    #    # Commands
    #    self.SVL_CMD_VER     = 0x01  # version
    #    self.SVL_CMD_BL      = 0x02  # enter bootload mode
    #    self.SVL_CMD_NEXT    = 0x03  # request next chunk
    #    self.SVL_CMD_FRAME   = 0x04  # indicate app data frame
    #    self.SVL_CMD_RETRY   = 0x05  # request re-send frame
    #    self.SVL_CMD_DONE    = 0x06  # finished - all data sent
    #    self.SVL_CMD_MSG     = 0x07  # message

        self.barWidthInCharacters = 50  # Width of progress bar, ie [###### % complete (NOT USED)

    #    self.crcTable = (
    #        0x0000, 0x8005, 0x800F, 0x000A, 0x801B, 0x001E, 0x0014, 0x8011,
    #        0x8033, 0x0036, 0x003C, 0x8039, 0x0028, 0x802D, 0x8027, 0x0022,
    #        0x8063, 0x0066, 0x006C, 0x8069, 0x0078, 0x807D, 0x8077, 0x0072,
    #        0x0050, 0x8055, 0x805F, 0x005A, 0x804B, 0x004E, 0x0044, 0x8041,
    #        0x80C3, 0x00C6, 0x00CC, 0x80C9, 0x00D8, 0x80DD, 0x80D7, 0x00D2,
    #        0x00F0, 0x80F5, 0x80FF, 0x00FA, 0x80EB, 0x00EE, 0x00E4, 0x80E1,
    #        0x00A0, 0x80A5, 0x80AF, 0x00AA, 0x80BB, 0x00BE, 0x00B4, 0x80B1,
    #        0x8093, 0x0096, 0x009C, 0x8099, 0x0088, 0x808D, 0x8087, 0x0082,
    #        0x8183, 0x0186, 0x018C, 0x8189, 0x0198, 0x819D, 0x8197, 0x0192,
    #        0x01B0, 0x81B5, 0x81BF, 0x01BA, 0x81AB, 0x01AE, 0x01A4, 0x81A1,
    #        0x01E0, 0x81E5, 0x81EF, 0x01EA, 0x81FB, 0x01FE, 0x01F4, 0x81F1,
    #        0x81D3, 0x01D6, 0x01DC, 0x81D9, 0x01C8, 0x81CD, 0x81C7, 0x01C2,
    #        0x0140, 0x8145, 0x814F, 0x014A, 0x815B, 0x015E, 0x0154, 0x8151,
    #        0x8173, 0x0176, 0x017C, 0x8179, 0x0168, 0x816D, 0x8167, 0x0162,
    #        0x8123, 0x0126, 0x012C, 0x8129, 0x0138, 0x813D, 0x8137, 0x0132,
    #        0x0110, 0x8115, 0x811F, 0x011A, 0x810B, 0x010E, 0x0104, 0x8101,
    #        0x8303, 0x0306, 0x030C, 0x8309, 0x0318, 0x831D, 0x8317, 0x0312,
    #        0x0330, 0x8335, 0x833F, 0x033A, 0x832B, 0x032E, 0x0324, 0x8321,
    #        0x0360, 0x8365, 0x836F, 0x036A, 0x837B, 0x037E, 0x0374, 0x8371,
    #        0x8353, 0x0356, 0x035C, 0x8359, 0x0348, 0x834D, 0x8347, 0x0342,
    #        0x03C0, 0x83C5, 0x83CF, 0x03CA, 0x83DB, 0x03DE, 0x03D4, 0x83D1,
    #        0x83F3, 0x03F6, 0x03FC, 0x83F9, 0x03E8, 0x83ED, 0x83E7, 0x03E2,
    #        0x83A3, 0x03A6, 0x03AC, 0x83A9, 0x03B8, 0x83BD, 0x83B7, 0x03B2,
    #        0x0390, 0x8395, 0x839F, 0x039A, 0x838B, 0x038E, 0x0384, 0x8381,
    #        0x0280, 0x8285, 0x828F, 0x028A, 0x829B, 0x029E, 0x0294, 0x8291,
    #        0x82B3, 0x02B6, 0x02BC, 0x82B9, 0x02A8, 0x82AD, 0x82A7, 0x02A2,
    #        0x82E3, 0x02E6, 0x02EC, 0x82E9, 0x02F8, 0x82FD, 0x82F7, 0x02F2,
    #        0x02D0, 0x82D5, 0x82DF, 0x02DA, 0x82CB, 0x02CE, 0x02C4, 0x82C1,
    #        0x8243, 0x0246, 0x024C, 0x8249, 0x0258, 0x825D, 0x8257, 0x0252,
    #        0x0270, 0x8275, 0x827F, 0x027A, 0x826B, 0x026E, 0x0264, 0x8261,
    #        0x0220, 0x8225, 0x822F, 0x022A, 0x823B, 0x023E, 0x0234, 0x8231,
    #        0x8213, 0x0216, 0x021C, 0x8219, 0x0208, 0x820D, 0x8207, 0x0202)

    #    # ///// END of code taken from artemis_svl.py

    def __del__(self):
        logthread('Uploader.__del__')
        self.wait()

    ## ///// START of code taken from artemis_svl.py

    #def get_crc16(self, data) -> int:
    #    """Compute CRC on a byte array"""
    #    logthread('Uploader.get_crc16')

    #    #Table and code ported from Artemis SVL bootloader
    #    crc = 0x0000
    #    data = bytearray(data)
    #    for ch in data:
    #        tableAddr = ch ^ (crc >> 8)
    #        CRCH = (self.crcTable[tableAddr] >> 8) ^ (crc & 0xFF)
    #        CRCL = self.crcTable[tableAddr] & 0x00FF
    #        crc = CRCH << 8 | CRCL
    #    #self.addMessage.emit("\tcrc is " + str(crc))
    #    return crc

    #def wait_for_packet(self) -> dict:
    #    """Wait for a packet"""
    #    logthread('Uploader.wait_for_packet')

    #    packet = {'len':0, 'cmd':0, 'data':0, 'crc':1, 'timeout':1}

    #    n = self.ser.read(2) # get the length bytes
    #    if(len(n) < 2):
    #        #self.addMessage.emit("\tpacket length < 2")
    #        return packet

    #    packet['len'] = int.from_bytes(n, byteorder='big', signed=False)
    #    #self.addMessage.emit("\tpacket length " + str(packet['len']))

    #    if(packet['len'] == 0): # Check for an empty packet
    #        return packet

    #    payload = self.ser.read(packet['len']) #read bytes (or timeout)

    #    if(len(payload) != packet['len']):
    #        #self.addMessage("\tincorrect payload length")
    #        return packet

    #    packet['timeout'] = 0                           # all bytes received, so timeout is not true
    #    packet['cmd'] = payload[0]                      # cmd is the first byte of the payload
    #    packet['data'] = payload[1:packet['len']-2]     # the data is the part of the payload that is not cmd or crc
    #    packet['crc'] = self.get_crc16(payload)         # performing the crc on the whole payload should return 0

    #    return packet


    #def send_packet(self, cmd, data) -> None:
    #    """Send a packet"""
    #    logthread('Uploader.send_packet')
    #    data = bytearray(data)
    #    num_bytes = 3 + len(data)
    #    #self.addMessage("\tsending packet length " + str(num_bytes))
    #    payload = bytearray(cmd.to_bytes(1,'big'))
    #    payload.extend(data)
    #    crc = self.get_crc16(payload)
    #    payload.extend(bytearray(crc.to_bytes(2,'big')))
    #    #self.addMessage.emit("\tsending packet crc " + str(crc))

    #    self.ser.write(num_bytes.to_bytes(2,'big'))
    #    #self.addMessage.emit("\t" + str(num_bytes.to_bytes(2,'big')))
    #    self.ser.write(bytes(payload))
    #    #self.addMessage.emit("\t" + str(bytes(payload)))

    def phase_setup(self) -> bool:
        """Setup: signal baud rate, get version, and command BL enter"""
        logthread('Uploader.phase_setup')
        upgrade_cmd = b'Upgrade'
        baud_detect_byte = b'U'


        vesion_pkg_received = False
        setup_failed = False
        packet_counter = 0

        self.addMessage.emit("Phase:\tSetup")

        self.ser.write(bytes(upgrade_cmd))          # send the upgrade command

        self.addMessage.emit("\tSent upgrade_cmd")
        time.sleep(5)                               # wait five seconds for ama3 to go to be bootloader mode

        self.ser.reset_input_buffer()               # Handle the serial startup blip
        self.addMessage.emit("\tCleared startup blip")

        self.ser.write(baud_detect_byte)            # send the baud detection character
        self.addMessage.emit("\tSent baud_detect_byte")

        while((not vesion_pkg_received) and (not setup_failed)):

            packet = wait_for_packet(self.ser)

            if(packet['timeout']):
                self.addMessage.emit("\twait_for_packet timeout")
                setup_failed = True
                break 
            if(packet['crc']):
                self.addMessage.emit("\twait_for_packet crc error")
                setup_failed = True
                break
        
            if(packet['cmd'] == SVL_CMD_VER):
                self.addMessage.emit("\twait_for_packet complete")
                self.installed_bootloader = int.from_bytes(packet['data'], 'big')
                self.addMessage.emit("\tGot SVL Bootloader Version: " + str(self.installed_bootloader))
                self.addMessage.emit("\tSending \'enter bootloader\' command")

                vesion_pkg_received = True

                send_packet(self.ser, SVL_CMD_BL, b'')
                #self.addMessage.emit("\tfinished send_packet")
                break

            if(packet['cmd'] == SVL_CMD_MSG):
                self.addMessageRemote.emit(packet['data'].decode('ascii'))

            packet_counter += 1
            if(packet_counter > 10):    # There should be less than 10 message packets before the version packet
                self.addMessage.emit("\tNo version packet received in time")
                setup_failed = True
                break
        
        return setup_failed
        # Now enter the bootload phase

    def phase_bootload(self) -> bool:
        """Bootloader phase (Artemis is locked in)"""
        logthread('Uploader.phase_bootload')
        startTime = time.time()
        frame_size = 512*4

        resend_max = 4
        resend_count = 0

        self.addMessage.emit("Phase:\tBootload")

        with open(self.fileLocation, mode='rb') as binfile:
            application = binfile.read()
            total_len = len(application)

            total_frames = math.ceil(total_len/frame_size)
            curr_frame = 0
            progressChars = 0

            self.addMessage.emit("\tSending " + str(total_len) +
                         " bytes in " + str(total_frames) + " frames")

            bl_done = False
            bl_failed = False
            done_sent = False

            while((not bl_done) and (not bl_failed)):

                packet = wait_for_packet(self.ser)               # wait for indication by Artemis

                #print(packet)

                if( packet['cmd'] == SVL_CMD_MSG ):
                    self.addMessageRemote.emit(packet['data'].decode('ascii'))
                elif( packet['cmd'] == SVL_CMD_DONE ):
                            bl_done = True
                            break
                elif( not done_sent ):
                    if((packet['timeout'] or packet['crc'])):
                        self.addMessage.emit("\tError receiving packet")
                        bl_failed = True
                        bl_done = True
                        break

                    if( packet['cmd'] == SVL_CMD_NEXT ):
                        self.addMessage.emit("\tGot frame request")
                        curr_frame += 1
                        resend_count = 0
                    elif( packet['cmd'] == SVL_CMD_RETRY ):
                        self.addMessage.emit("\tRetrying...")
                        resend_count += 1
                        if( resend_count >= resend_max ):
                            bl_failed = True
                            bl_done = True
                            break
                    else:
                        self.addMessage.emit("\tUnknown error")
                        bl_failed = True
                        bl_done = True
                        break

                    if( curr_frame <= total_frames ):
                        frame_data = application[((curr_frame-1)*frame_size):((curr_frame-1+1)*frame_size)]
                        self.addMessage.emit("\tSending frame #" + str(curr_frame) + ", length: " + str(len(frame_data)))
                        send_packet(self.ser, SVL_CMD_FRAME, frame_data)
                    else:
                        send_packet(self.ser, SVL_CMD_DONE, b'')
                        done_sent = True

            if( bl_failed == False ):
                self.addMessage.emit("Upload complete!")
                endTime = time.time()
                bps = total_len / (endTime - startTime)
                self.addMessage.emit("Nominal bootload " + str(round(bps, 2)) + " bytes/sec\n")
            else:
                self.addMessage.emit("Upload failed!\n")
                if (self.baudRate > 115200):
                    self.addMessage.emit("Please try a slower Baud Rate\n")

            return bl_failed

    @pyqtSlot()
    def upload_main(self) -> None:
    #def run(self) -> None:
        """SparkFun Variable Loader (Variable baud rate bootloader for Artemis Apollo3 modules)"""
        logthread('Uploader.upload_main')
        try:
            num_tries = 3

            #self.messages.clear() # Clear the message window

            self.addMessage.emit("\nArtemis SVL Uploader\n")

            for _ in range(num_tries):

                bl_failed = False

                bl_failed = self.phase_setup()      # Perform baud rate negotiation
                if( bl_failed == False ):
                    bl_failed = self.phase_bootload()     # Bootload

                if( bl_failed == False ):
                    break
            if ((self.installed_bootloader >= 0) and (self.installed_bootloader < BOOTLOADER_VERSION)):
                self.addMessage.emit("\nYour bootloader is out of date.\nPlease click Update Bootloader.")

        except:
            self.addMessage.emit("Could not communicate with board!")

        #try:
        #    self.ser.close()
        #except:
        #    self.addMessage.emit("Failed to close serial port!")
        #    pass

        self.finished.emit()

    # ///// END of code taken from artemis_svl.py

if __name__ == '__main__':
    import sys
    app = QApplication([sys.argv])
    app.setOrganizationName('SparkFun')
    app.setApplicationName('Artemis Firmware Uploader ' + guiVersion)
    app.setWindowIcon(QIcon(resource_path("Artemis-Logo-Rounded.png")))
    w = MainWindow()
    w.show()
    sys.exit(app.exec_())
