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
#SETTING_ARTEMIS = 'artemis' # Default to Artemis-based boards

guiVersion = 'v1.3'

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
    #logthread('Global.get_crc16')

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
    #logthread('Global.wait_for_packet')

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
    #logthread('Global.send_packet')
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
        self.setupUi()
        self.showDatetime()

        ## Create uploader object and thread
        #self.uploader = Uploader()
        #self.upload_thread = QThread()
        #self.uploader.moveToThread(self.upload_thread)
        #self.uploader.addMessage[str].connect(self.addMessage)
        #self.uploader.addMessageRemote[str].connect(self.addMessageRemote)
        #self.upload_thread.started.connect(self.uploader.upload_main)
        #self.uploader.finished.connect(self.done)

        logthread('mainwin.__init__')
    
    def setupUi(self):
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

        ## Menu Bar
        #menubar = self.menuBar()
        #boardMenu = menubar.addMenu('Board Type')
        
        #boardGroup = QActionGroup(self)

        #self.artemis = QAction('Artemis', self, checkable=True)
        #self.artemis.setStatusTip('Artemis-based boards including the OLA and AGT')
        #self.artemis.setChecked(True) # Default to artemis
        #a = boardGroup.addAction(self.artemis)
        #boardMenu.addAction(a)
        
        #self.apollo3 = QAction('Apollo3', self, checkable=True)
        #self.apollo3.setStatusTip('Apollo3 Blue development boards including the SparkFun Edge')
        #a = boardGroup.addAction(self.apollo3)
        #boardMenu.addAction(a)

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

        #checked = settings.value(SETTING_ARTEMIS)
        #if checked is not None:
        #    if (checked == 'True'):
        #        self.artemis.setChecked(True)
        #        self.apollo3.setChecked(False)
        #    else:
        #        self.artemis.setChecked(False)
        #        self.apollo3.setChecked(True)

    def _save_settings(self) -> None:
        """Save settings on shutdown."""
        logthread('mainwin._save_settings')
        settings = QSettings()
        settings.setValue(SETTING_PORT_NAME, self.port)
        settings.setValue(SETTING_FILE_LOCATION, self.fileLocation_lineedit.text())
        settings.setValue(SETTING_BAUD_RATE, self.baudRate)
        #if (self.artemis.isChecked()): # Convert isChecked to str
        #    checkedStr = 'True'
        #else:
        #    checkedStr = 'False'
        #settings.setValue(SETTING_ARTEMIS, checkedStr)

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
                     str(currDT.second) + "\r\n"
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
        logthread('mainwin.on_upload_btn_pressed')
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

        # Create uploader and thread
        self.uploader = Uploader(self.ser, self.fileLocation_lineedit.text())
        self.upload_thread = QThread()
        self.uploader.moveToThread(self.upload_thread)

        #self.uploader.set_serial_connection(self.ser)
        #self.uploader.set_file_location(self.fileLocation_lineedit.text())

        # Connect signals and slots
        self.uploader.addMessage[str].connect(self.addMessage)
        self.uploader.addMessageRemote[str].connect(self.addMessageRemote)
        self.upload_thread.started.connect(self.uploader.upload_main)
        self.uploader.finished.connect(self.done)

        # start uploader
        self.upload_thread.start()

        self.browse_btn.setEnabled(False)
        self.refresh_btn.setEnabled(False)
        self.clear_btn.setEnabled(False)
        self.upload_btn.setEnabled(False)
        self.update_dt_btn.setEnabled(False)

    def done(self):
        logthread('mainwin.done')

        # Enable buttons when done
        self.browse_btn.setEnabled(True)
        self.refresh_btn.setEnabled(True)
        self.clear_btn.setEnabled(True)
        self.upload_btn.setEnabled(True)
        self.update_dt_btn.setEnabled(True)

        self.upload_thread.quit()
        self.uploader.deleteLater()
        self.upload_thread.deleteLater()

class Uploader(QObject):
    addMessage = pyqtSignal(str)
    addMessageRemote = pyqtSignal(str)
    finished = pyqtSignal()

    def __init__(self, ser, fileLocation):
        #QThread.__init__(self)
        super(QObject, self).__init__()
        logthread('Uploader.__init__')
        
        self.ser = ser
        self.fileLocation = fileLocation
        self.installed_bootloader = -1 # Use this to record the bootloader version
        self.barWidthInCharacters = 50  # Width of progress bar, ie [###### % complete (NOT USED)

    #def __del__(self):
    #    logthread('Uploader.__del__')
    #    self.upload_thread.wait()

    def set_serial_connection(self, ser):
        self.ser = ser

    def set_file_location(self, fileLocation):
        self.fileLocation = fileLocation

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
        """SparkFun Variable Loader (Variable baud rate bootloader for Artemis Apollo3 modules)"""
        logthread('Uploader.upload_main')
        try:
            num_tries = 3

            #self.messages.clear() # Clear the message window

            self.addMessage.emit("\nLocaSafe UT221 SVL Uploader\n")

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
    app.setOrganizationName('Locatechs')
    app.setApplicationName('LocaSafe UT221 Firmware Uploader ' + guiVersion)
    app.setWindowIcon(QIcon(resource_path("Artemis-Logo-Rounded.png")))
    w = MainWindow()
    w.show()
    sys.exit(app.exec_())
