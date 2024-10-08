# recorder.py : Basic class for packet reading from the frame recorder component.
#
# Copyright (C) 2017 CESNET z. s. p. o.
# Author(s): Pavel Benacek <benacek@cesnet.cz>

import scapy.all as scapy
import math
import pickle
import signal
import time


# Implementation of dummy handlers for reading/writing of MI32 transactions.
# These handlers are not required and are used for testing purposes only.
# The real implementation should call the csbus or appropriate tool.
# Notice that real handles has to match with the provided prototypes.

# NOTE: This variable is filled with data in the main function.
memory  = None


def load_memory(path):
    """
    Load the pickled memory.
    """
    # Reconstruct the memory object from the player code
    global memory
    f = open(path)
    del memory

    global memory
    memory = pickle.load(f)
    f.close()


def write32(addr, data):
    """
    Write the 32-bit transaction. The function throws the instance of
    IOError class when the write operation fails.

    Parametrs:
        - addr - write address
        - data - 32-bit data to write.
    """
    print("Data write: 0x%05X ==> 0x%02X" % (addr, data))


def read32(addr):
    """
    Read the 32-bit transaction. The function returns 32-bit number.
    The function throws the instance of IOError class when the
    read operation fails.

    The type of returned vaue has to be long.
    """
    global memory
    # Implementation of the read statement
    if addr >= RecorderReader.DATA_OFFSET:
        # Read 32bit data word from the memory
        try:
            return memory[0]["WORD"][addr]
        except KeyError:
            raise IOError("Reading a data word from bad address!")
    elif addr == RecorderReader.STATUS_OFFSET:
        # Read the status register setup just used bits
        if len(memory):
            # Some data are available, return the destination bit enabled.
            return 0x2
        else:
            # No data available, return false
            return 0x0
    elif addr  == RecorderReader.EOF_POS_OFFSET:
        # Read the EOF_POS register
        return memory[0]["EOF_POS"]
    elif addr == RecorderReader.SOF_POS_OFFSET:
        # Read the SOF_POS register
        return memory[0]["SOF_POS"]
    elif addr == RecorderReader.VLD_OFFSET:
        # Data with block validity. Remove the front element.
        ret = memory[0]["VLD"]
        memory.pop(0)
        return ret
    else:
        # Some read operation
        print("Data read from the unknown address 0x%02X" % (addr))
        raise IOError("Reading from the unknown memory address!")


class RecorderReader(object):
    """
    This class implements the control functionality for packet reading from the packet record
    component. The output data are stored in the form of the packet.
    """

    # Variables with address space
    DATA_OFFSET    = 0x14
    STATUS_OFFSET  = 0x00
    EOF_POS_OFFSET = 0x10
    SOF_POS_OFFSET = 0x0C
    VLD_OFFSET     = 0x08
    CONTROL_OFFSET = 0x04

    # Helping masks
    FIFO_SRC_RDY_MASK = 0x2

    # Command constants
    CMD_FIFO_EN   = 0x1
    CMD_FIFO_DIS  = 0x0

    def __init__(
            self, regions,
            region_size,
            block_size,
            item_width,
            write_handler,
            read_handler,
            pcap,
            base=0x0,
            sigterm=False,
            pkt_num=0):
        """
        Initilization of the recorder class. The class should be initialized
        with the MFB configuration, read/write device handlers and output pcap file.
        Parameters:
            - regions       - the number of MFB regions
            - region_size   - the width of one region
            - block_size    - size of one block
            - item_width    - number of items in a block
            - write_handler - handler on the write function (capable to write a 32-bit transaction)
            - read_handler  - handler on the read function (capable to read a 32-bit transaction)
            - pcap          - path to the PCAP file
            - base          - base component address
            - sigterm       - enable the signal termination mode (disabled by default)
            - pkt_num       - number of packets to capture (disabled when pkt_num = 0)

        Note: See the read32 and write32 function for the identification of basic function prototypes.
        """
        # MFB configuration
        self.regions = regions
        self.region_size = region_size
        self.block_size = block_size
        self.item_width = item_width
        # Remember the function handlers
        self.writeh = write_handler
        self.readh = read_handler
        # Remember the PCAP file
        self.pcap = pcap
        # Store the base pointer
        self.base = base
        # Some saniti check of the input, the minimal item_width is 8 bits
        is_power2 = True if item_width & (item_width - 1) == 0 else False
        if item_width < 8 or not is_power2:
            raise ValueError("Miminal allowed item_width is 8 bits and the size should be a multiple of 2!")
        # Control capture variable and register the handler
        self.sigterm = sigterm
        # Number of packets to capture
        self.pkt_num = pkt_num
        self.capture = True
        if sigterm:
            # Register the signal handling if the sigterm mode is enabled
            signal.signal(signal.SIGINT, self._stop_capture)
        # Compute the number of 32-bit elements in the data word
        self.word_count = int(math.ceil((regions * region_size * block_size * item_width) / 32.0))
        # Compute the widhth of sof and eof pos elements
        self.sof_elem_width = int(math.ceil(max(1, math.log(region_size, 2))))
        self.eof_elem_width = int(math.ceil(max(1, math.log(region_size * block_size, 2))))

    def _wait_for_data(self):
        """
        Wait untill data are ready.
        """
        while not self._check_destination_ready() and self.sigterm and self.capture:
            time.sleep(1)
            print("Waiting for data ...")

    def _continue_capture(self):
        """
        Function to check if is required to continue the capture process. This function
        returns true or false.
        """
        # Check if the packet numeber mode is enabeld
        if self.pkt_num > 0 and not self.capture:
            return False
        # Check if the "until data" mode is enabled
        if not self.sigterm and not self._check_destination_ready():
            return False
        # Check if the user mode is enabled
        if self.sigterm and not self.capture:
            return False
        return True

    def read(self):
        """
        The main function for the PCAP reconstruction from the MI32 stream. This function should be
        ended with a CTRL+C signal.
        """
        # Enabling the capture and waiting for a small amount of time
        self.writeh(self.base + self.CONTROL_OFFSET, self.CMD_FIFO_EN)
        time.sleep(1)
        print("Starting the PCAP capture to %s." % (self.pcap))
        # The capture is running in two situations:
        #  1) The signal handling is required and thereofre, we are capturing packets to PCAP untill the CTRL+C is detected
        #  2) The signal handling is not used and we are reading untill some data are available.
        # Before that, prepare some helping variables
        try:
            packets = []
            mfb_words = []
            # Check the state
            while self._continue_capture():
                # Wait for a valid word
                self._wait_for_data()
                if self.sigterm and not self.capture:
                    # Escape from the recording
                    break
                # Read the MFB word from the device
                mfb_word_bus = 0x0
                data_addr = self.DATA_OFFSET + (self.word_count - 1) * 4
                for i in range(0, self.word_count):
                    # We need to get data in multiples of 4. Starting from 0x14)
                    mfb_word_bus = (mfb_word_bus << 32) | self.readh(self.base + data_addr)
                    data_addr -= 0x4
                # Divide them into mfb blocks and regions
                mfb = {}
                blk_size = self.block_size * self.item_width
                mfb["WORD"] = []
                for reg in range(0, self.regions):
                    reg_blk = []
                    for blk in range(0, self.region_size):
                        # Preapre the mask (based on the block width)
                        blk_mask = int('1' * (blk_size), 2)
                        tmp_val  = mfb_word_bus & blk_mask
                        # Append it to the region block and prepare the next block
                        reg_blk.append(tmp_val)
                        mfb_word_bus = mfb_word_bus >> blk_size
                    # Append the block into the region list
                    mfb["WORD"].append(reg_blk)
                # Read {SOF,EOF}_POS
                mfb["SOF_POS"] = self.readh(self.base + self.SOF_POS_OFFSET)
                mfb["EOF_POS"] = self.readh(self.base + self.EOF_POS_OFFSET)
                # Read the valid blocks
                mfb["VLD"] = self.readh(self.base + self.VLD_OFFSET)
                # Append the read MFB word
                mfb_words.append(mfb)
                # Decore the packet if available
                while True:
                    packet = self._decode_packet(mfb_words)
                    if packet:
                        # Prepare the MFB for next iteration
                        mfb_words = self._initialize_mfb(mfb_words)
                        # Store the packet
                        packets.append(packet)
                        print("%d packets have been captured." % (len(packets)))
                        # Be paranoid and check that the number of packets is higher than 0
                        if (len(packets) == self.pkt_num and self.pkt_num > 0):
                            self.capture = False
                    else:
                        # No packet, break.
                        break

            # Disable the capture
            self.writeh(self.base + self.CONTROL_OFFSET, self.CMD_FIFO_DIS)
            # Write the output pcap
            if len(packets):
                print("Storing packet in the %s file." % (self.pcap))
                scapy.wrpcap(self.pcap, packets)
            else:
                print("No packets were captured.")

        except IOError as e:
            print("Error during read/write operation:", str(e))

    def _initialize_mfb(self, mfb_words):
        """
        Prepare the MFB structure for the next packet.

        Parameters:
            - mfb_words - structure with captured MFB words.

        Returns new MFB structure.
        """
        # Remove all words but let the last one
        mfb_words = [mfb_words[-1]]
        # Check if the MFB word contains SOP, remove it if not.
        sop_data = self._det_start(mfb_words[0])
        eop_data = self._det_end(mfb_words[0])
        # Compute the SOP and EOP position in bytes
        sop_offset = (sop_data[1] * self.region_size + sop_data[2]) * self.block_size * self.item_width / 8
        eop_offset = (eop_data[1] * self.region_size * self.block_size) * self.item_width / 8 + eop_data[2]
        # Remove SOP and EOP if detected SOP is before EOP
        if sop_data[0] and eop_data[0] and (sop_offset < eop_offset):
            # SOP before EOP, remove bothr
            tmp_mfb_words = self._remove_sop(mfb_words, sop_data)
            tmp_mfb_words = self._remove_eop(tmp_mfb_words, eop_data)
            # Check if the remaining word contans SOP. If not, return empty list
            sop_data = self._det_start(tmp_mfb_words[0])
            if not sop_data[0]:
                return []
            else:
                return tmp_mfb_words
        elif (sop_data[0]):
            # SOP is after EOP, remove EOP.
            return self._remove_eop(mfb_words, eop_data)
        else:
            # The SOP is not in the current word
            return []

    def _remove_sop(self, mfb_words, sop_data):
        """
        Remove the SOP information from the MFB.

        Parameters:
            - mfb_words - structure with captured MFB words.
            - sop_data -  structure for detected SOP
        """
        # Invalidate the SOP in region
        sof_str_mask              = list('1' * self.regions)
        sof_str_mask[sop_data[1]] = '0'
        # Reverse the mask and create a number from it (LSB is on the left)
        sof_mask  = int(''.join(sof_str_mask[::-1]), 2)
        tmp_mask  = sof_mask << (self.regions + 1) | int('1' * self.regions, 2) << 1 | 0x1
        mfb_words[0]["VLD"] &= tmp_mask
        return mfb_words

    def _remove_eop(self, mfb_words, eop_data):
        """
        Remove the EOP information from the MFB.

        Parameters:
            - mfb_words - structure with captured MFB words.
            - sop_data -  structure for detected SOP
        """
        # Invalidate the EOF in region
        eof_str_mask              = list('1' * self.regions)
        eof_str_mask[eop_data[1]] = '0'
        # Reverse the mask and create a number from it (LSB is on the left)
        eof_mask  = int(''.join(eof_str_mask[::-1]), 2)
        tmp_mask  = int('1' * self.regions, 2) << (self.regions + 1) | eof_mask << 1 | 0x1
        mfb_words[0]["VLD"] &= tmp_mask
        return mfb_words

    def _det_start(self, mfb):
        """
        Detect the start in the MFB word.

        Parameters:
            - mfb - mfb word structure

        The function returns a tuple which encodes the right start of the packet.
        """
        # Default values
        det = False
        reg = 0
        pos = 0
        sof_vld = (mfb["VLD"] >> (1 + self.regions)) & int('1' * self.regions, 2)
        if sof_vld != 0:
            # The start is detected
            det = True
            # Extract the start region (we are indexing from 0). This function removes the
            # 0b on the beginning,reverse it and searches for the index of 1
            reg = bin(sof_vld)[2:][::-1].index('1')
            # Extract the starting block in a region
            pos = (mfb["SOF_POS"] >> (reg * self.sof_elem_width)) & int('1' * self.sof_elem_width, 2)
        return (det, reg, pos)

    def _det_end(self, mfb_word):
        """
        Detect the end of the MFB word.

        Parameters:
            - mfb - mfb word structure

        The function returns a tuple which encodes the right end of the packet.
        """
        # Default values
        det = False
        reg = 0
        pos = 0
        eof_vld = (mfb_word["VLD"] >> 1) & int('1' * self.regions, 2)
        if eof_vld != 0:
            # The end is detected
            det = True
            # Extract the end region (we are indexing from 0)
            reg = bin(eof_vld)[2:][::-1].index('1')
            # Extract the eof_pos in a region
            pos = (mfb_word["EOF_POS"] >> (reg * self.eof_elem_width)) & int('1' * self.eof_elem_width, 2)
        return (det, reg, pos)

    def _get_item(self, data, item_num):
        """
        This method extracts items in a byte oriented way.

        Parameters:
            - data - block data
            - item_num - number of the item (indexed from 0)

        Return: Item's hexadecimal form.
        """
        # Compute the number of bytes to extract
        extr_bytes = self.item_width / 8
        blk = data >> (item_num * self.item_width)
        raw_pkt = ""
        for i in range(0, extr_bytes):
            it = blk & 0xFF
            raw_pkt += chr(it)
            blk = blk >> 8
        return raw_pkt

    def _serialize_data(self, mfb_word, start_reg, start_blk, end_reg, end_item):
        """
        This method perfomrs the data serialization from the MFB WORD which is the list
        of lists (i.e, regions and blocks).

        Parameters:
            - mfb_word - list of lists
            - start_reg - start region
            - start_blk - start block
            - end_reg - end region
            - end_item - offset in the region

        Return the hexadecimal string of the packet.
        """
        raw_pkt = ""
        # Initialize start block data
        tmp_start_blk  = start_blk
        for c_reg in range(start_reg, self.regions):
            # For each region (starting from the start region)
            for c_blk in range(tmp_start_blk, self.region_size):
                # And for the starting block
                blk = mfb_word[c_reg][c_blk]
                # Extract one item
                for i in range(0, self.block_size):
                    raw_pkt += self._get_item(blk, i)
                    # Check if we reached the last item
                    curr_item = c_blk * self.block_size + i
                    if c_reg == end_reg and end_item == curr_item:
                        # We are done, return the result
                        return raw_pkt
            # Ok, block captured, restart the block pointer at the end
            # of the region cycle.
            tmp_start_blk = 0

        raise RuntimeError("Error during the data serialization")

    def _decode_packet(self, mfb_words):
        """
        Decode the packet from captured MFB words. Function also prepares the
        mfb_words structure for the next iteration (it removes the part of the
        list which was identified as a packet, the EOF_POS signalization is also removed).

        Parameters:
            - mfb_words - list of MFB word configuration which is represented as a dictionary.

        The function returns the instance of scapy Packet or None
        """
        # Check if the packet contains the EOF_POS block. If yes, data for the whole packet are
        # presented.
        if len(mfb_words) == 0:
            return None
        end_det, end_reg, end_pos = self._det_end(mfb_words[-1])
        if not end_det:
            # No end was detected.
            return None
        # Detect the starting information
        start_det, start_reg, start_pos  = self._det_start(mfb_words[0])
        # The caputured dump contains a packet. Iterate over words, regions, blocks and dump
        # blocks into the hexadecimal representation (per bytes)
        if start_det is False and end_det is True:
            # Error ... start and end are expected
            raise RuntimeError("Error during the packet decoding! No start has been detected.")

        # Detect if first and last words are same --> one word transfewr
        one_word = True if mfb_words[0] == mfb_words[-1] else False
        # Decode the packet
        raw_pkt = ""
        # Prepare some helping extraction variables for the whole MFB word
        last_reg_item_num = self.region_size * self.block_size - 1
        last_reg_num      = self.regions - 1
        # Check if the we have one word transfer. If not, setup the maximal end signal values
        for i in range(0, len(mfb_words)):
            if i == 0 and one_word:
                # We are working with one word MFB transaction
                raw_pkt += self._serialize_data(mfb_words[i]["WORD"], start_reg, start_pos, end_reg, end_pos)
            elif i == 0:
                # We are working with first MFB word --> start from the detected SOF and serialize untill the end of the word
                raw_pkt += self._serialize_data(mfb_words[i]["WORD"], start_reg, start_pos, last_reg_num, last_reg_item_num)
            elif i == len(mfb_words) - 1:
                # We are working with last MFB word
                raw_pkt += self._serialize_data(mfb_words[i]["WORD"], 0, 0, end_reg, end_pos)
            else:
                # We are working with data MFB word (serialize the whole word)
                raw_pkt += self._serialize_data(mfb_words[i]["WORD"], 0, 0, last_reg_num, last_reg_item_num)

        # Create a packet
        ret = scapy.Ether(_pkt=raw_pkt)
        mfb_words = []
        return ret

    def _check_destination_ready(self):
        """
        The method reads the status register and check the validity of TX source ready
        signal.

        The True is returned when the source ready is active.
        """
        ret = self.readh(self.base + self.STATUS_OFFSET)
        return (ret & self.FIFO_SRC_RDY_MASK) != 0

    def _stop_capture(self, signum, frame):
        """
        Handler for capture stop
        """
        self.capture = False


# Main starting function for a simulatino purposes
def main():
    try:
        # Create a reader block to reconstruc
        load_memory("../../frame_player/sw/memory.pickle")
        reader = RecorderReader(4, 8, 8, 8, write32, read32, "recorded.pcap", 0x0, False, 0)
        reader.read()
    except IOError as e:
        print("Error during read/write operation: ", str(e))


if __name__ == "__main__":
    main()
