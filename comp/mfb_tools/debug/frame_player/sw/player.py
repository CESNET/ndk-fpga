#!/usr/bin/env python3
# player.py : Basic script for generation of the MI32 configuration
#             stream
#
# Copyright (C) 2017 CESNET z. s. p. o.
# Author(s): Pavel Benacek <benacek@cesnet.cz>

import scapy.all as scapy
import math
# import pickle
import nfb

# Implementation of dummy handlers for reading/writing of MI32 transactions.
# These handlers are not required and are used for testing purposes only.
# The real implementation should call the csbus or appropriate tool.
# Notice that real handles has to match with the provided prototypes.
memory = None
mfb    = {"WORD": {}, "VLD": 0, "SOF_POS": 0, "EOF_POS": 0}


def write32(addr, data):
    """
    Write the 32-bit transaction. The function throws the instance of
    IOError class when the write operation fails.

    Parametrs:
        - addr - write address
        - data - 32-bit data to write. They are encoded as the long.
    """
    global memory
    global mfb
    print("Data write: 0x%05X ==> 0x%02X" % (addr, data))
    if addr >= PlayerConfigurator.DATA_OFFSET:
        # We are writting data, append them into the list of MI32 transactions
        mfb["WORD"][addr] = data
        print("Write DATA")
    elif addr == PlayerConfigurator.VLD_OFFSET:
        # Writting of VLD signals --> in this case, check the LSB bit, append it into the memory
        # and reset the mfb dictionary
        mfb["VLD"] = data
        print("Write VLD")
        if data & 0x1:
            # Write data and reset the structure
            memory.append(mfb)
            mfb = {"WORD": {}, "VLD": 0, "SOF_POS": 0, "EOF_POS": 0}
    elif addr == PlayerConfigurator.SOF_POS_OFFSET:
        # Writting of shared sof_pos
        mfb["SOF_POS"] = data
        print("Write SOF_POS")
    elif addr == PlayerConfigurator.EOF_POS_OFFSET:
        # Writtig of shared eof_pos
        mfb["EOF_POS"] = data
        print("Write EOF_POS")
    elif addr == PlayerConfigurator.CTRL_OFFSET:
        if data == PlayerConfigurator.CMD_STORE_DIS:
            #f = open("memory.pickle","w")
            #pickle.dump(str(memory),f)
            #f.close()
            print("All data were written into memory")
        elif data == PlayerConfigurator.CMD_STORE_EN:
            # Output dictionary with mapping data (this contains the representation of
            # recorder fifo memory)
            memory = []
            # Helping variables
            mfb = {"WORD": {}, "VLD": 0, "SOF_POS": 0, "EOF_POS": 0}
            print("All memory structures were initialized.")
    else:
        # Just print information about the write operation
        print("Data write: 0x%05X ==> 0x%02X" % (addr, data))


def read32(addr):
    """
    Read the 32-bit transaction. The function returns 32-bit number.
    The function throws the instance of IOError class when the
    read operation fails
    """
    pass


class PlayerConfigurator(object):
    """
    This class implements the configuration process of the frame player component via a 32bit configuration
    interface. This class can be runned from this script (you have to just implement the read/write handlers)
    or  you can use it in your own projects where the appropriate read/write operations are passed.
    """
    # Constants for the address space and commands
    DATA_OFFSET    = 0x14
    VLD_OFFSET     = 0x08
    SOF_POS_OFFSET = 0x0C
    EOF_POS_OFFSET = 0x10
    CTRL_OFFSET    = 0x04

    # Commands
    CMD_STORE_EN   = 0x1
    CMD_STORE_DIS  = 0x2
    CMD_STORE_RPT  = 0xB

    def __init__(self, regions, region_size, block_size, item_width, fifo_depth, write_handler, read_handler, pcap, base=0x0):
        """
        Initilization of the player configurator class. The class should be initialized
        with the MFB configuration, depth of the FIFO memory and read/write device handlers.

        Parameters:
            - regions       - the number of MFB regions
            - region_size   - the width of one region
            - block_size    - size of one block
            - item_width    - number of items in a block
            - fifo_depth    - number of items which can be stored in a FIFO memory
            - write_handler - handler on the write function (capable to write a 32-bit transaction)
            - read_handler  - handler on the read function (capable to read a 32-bit transaction)
            - pcap          - path to the PCAP file
            - base          - base address which is used for the MI32 component. The default value is 0x0

        Note: See the read32 and write32 function for the identification of basic function prototypes.
        """
        # MFB configuration
        self.regions = regions
        self.region_size = region_size
        self.block_size = block_size
        self.item_width = item_width
        # Remember the configuration of the FIFO memory
        self.fifo_depth = fifo_depth
        # Remember the function handlers
        self.writeh = write_handler
        self.readh = read_handler
        # Remember the PCAP file
        self.pcap = pcap
        # Store the base address
        self.base = base
        # Some saniti check of the input, the minimal item_width is 8 bits
        is_power2 = True if item_width & (item_width - 1) == 0 else False
        if item_width < 8 or not is_power2:
            raise ValueError("Miminal allowed item_width is 8 bits and the size should be a multiple of 2!")
        # Compute the number of 32 bit transactions
        self.mi32_transactions = int(math.ceil(float(regions * region_size * block_size * item_width) / 32.0))
        #print("MI words per MFB word " + str(self.mi32_transactions))
        # Compute the width of one SOF element on shared bus
        self.sof_elem_width = int(math.ceil(max(1, math.log(region_size, 2))))
        self.eof_elem_width = int(math.ceil(max(1, math.log(region_size * block_size, 2))))
        #print("SOF_POS width " + str(self.sof_elem_width))
        #print("EOF_POS width " + str(self.eof_elem_width))
        self.words_cnt = 0

    def configure(self, repeate_en=False):
        """
        The main function for the configuration of the frame_player component

        Parameters:
            - repeate_en - enable of player repeate mode
        """
        # Switch the component to the storage mode, feed it with data and start the reply mode.
        self.writeh(self.base + self.CTRL_OFFSET, self.CMD_STORE_EN)
        self._generate()

        if repeate_en is True:
            self.writeh(self.base + self.CTRL_OFFSET, self.CMD_STORE_RPT)
        else:
            self.writeh(self.base + self.CTRL_OFFSET, self.CMD_STORE_DIS)

    def _reset_mfb_struct(self):
        """
        Method for resetting of MFB stuff.
        """
        return {
            "WORD":     self.regions * [[]],
            "SOF":      self.regions * [False],
            "SOF_POS":  self.regions * [0],
            "EOF":      self.regions * [False],
            "EOF_POS":  self.regions * [0],
        }

    def _generate(self):
        """
        Generate the configuration stream for the MFB player component. This component reads a packet
        and generates the configuration stream for the MFB player component
        """
        # Open the PCAP file in scapy, get the first packet and transform it into 32 bit configuration
        # stream.
        packets = scapy.rdpcap(self.pcap)
        # Prepare the MFB stuff
        mfb = self._reset_mfb_struct()
        reg = 0
        # Helping variables
        fifo_ptr      = 0
        pkt_cnt       = 0
        mfb_blk = 0
        while True:
            # Check if we have any packets to send
            if not len(packets):
                # No packet is available, therefore, send the rest and end.
                self._send_mfb_word(mfb)
                print("All packets were processed!")
                break
            # Convert to packet to the serioes of numbers which are than splitted into chunks. The conversion
            # produces a list of numbers from 0-255
            packet = packets.pop()
            print("Converting the packet number %d." % (pkt_cnt))
            pkt_cnt += 1
            #content = map(ord,bytes(packet))
            content = bytes(packet)
            # Now we need to split a frame into blocks. Therefore, we need to create an n-tuples where
            # n is the number of items in one block
            block_elements = self.block_size * self.item_width / 8
            # print(block_elements)
            block_list = self._split(content, block_elements)
            # Check if we have a place in the FIFO
            mfb_words_req = math.ceil(float(len(block_list)) / self.region_size)
            # print("mfb_words_req: " + str(mfb_words_req))
            if fifo_ptr + mfb_words_req > self.fifo_depth:
                # print("fifo_ptr: " + str(fifo_ptr))
                # print("fifo_depth: " + str(self.fifo_depth))
                # Finish frame sending (if it wasn't already finished)
                self._send_mfb_word(mfb)
                print("There isn't space for a next packet in the FIFO memory.")
                break
            # Insert segments into the MFB word
            segment = 0
            # print(len(block_list))
            for block in block_list:
                #print("PKT block " + str(segment))
                #print("MFB block " + str(mfb_blk))
                # First and last signalization
                first = True if segment == 0 else False
                last  = True if segment == (len(block_list) - 1) else False
                # Check if the MFB word is completed. The MFB is considered to be completed iff:
                #   * 1) All regions and slots are filled
                #   * 2) All regions are filled and start of new frame is detected. In such situation we
                #        need to fill the remaining place with zeros.
                if ((reg + 1) == self.regions and len(mfb["WORD"][-1]) == self.region_size) or ((reg + 1) == self.regions and (first and mfb["SOF"][reg])):
                    # Fill the remaining place with zeros
                    self._fill_mfb_word(mfb, block_elements)
                    # Send prepared data and restart the MFB structures
                    self._send_mfb_word(mfb)
                    # Update the transactions by one
                    fifo_ptr   += 1
                    # Restart the MFB stuff
                    mfb = self._reset_mfb_struct()
                    reg = 0
                    mfb_blk = 0
                    # print("MFB word completed")
                # Update the region counter because we need to fill the next
                # region. The counter is update if the end of the reqion was
                # detected or one beginning is already presented.
                if len(mfb["WORD"][reg]) == self.region_size or (mfb["SOF"][reg] and first):
                    reg += 1
                    mfb_blk = 0
                    # print("MFB new region")
                # Add blocks into the MFB region and also deal with the sop/eop signalization
                if first:
                    # Remember the start block
                    #print("MFB block SOF")
                    mfb["SOF"][reg] = True
                    mfb["SOF_POS"][reg] = len(mfb["WORD"][reg])
                if last:
                    # Remember the last item. The block element is built from
                    # independet items.
                    #print("MFB block EOF")
                    mfb["EOF"][reg] = True
                    eop_pos = len(mfb["WORD"][reg]) * self.block_size + len(block) - 1
                    mfb["EOF_POS"][reg] = eop_pos
                # Append the data block extend the data before appending
                self._fill_zeros(block, block_elements)
                mfb["WORD"][reg].append(block)
                segment += 1
                mfb_blk += 1
                #print("MFB block done")
            # print(self.words_cnt)

    def _send_mfb_word(self, mfb):
        """
        Program the MFB word into the component.

        Parameters:
            - mfb -  dictionary with the MFB stuff
        """
        # Take blocks and divede them into 32 bit transactions.
        # First of all, we serialize all the bits into one long vector because long integer
        # in Python has unlimited precission. All elements are appended in reversed order.
        # print(mfb)
        mfb_bus = 0
        for region in mfb["WORD"][::-1]:
            # Inverse the block list
            for block in region[::-1]:
                # Inverse the item list
                for item in block[::-1]:
                    mfb_bus = (mfb_bus << 8) | item
        # Split the serialized transaction into independent write transactions. Generate the
        # write transactions for the MFB
        data_offset = self.DATA_OFFSET
        for i in range(0, self.mi32_transactions):
            # Generate the write transaction
            data = mfb_bus & 0xFFFFFFFF
            self.writeh(self.base + data_offset, int(data))
            # data_offset  += 0x4
            # Shift the data
            mfb_bus = mfb_bus >> 32
        # Write informations about {SOF,EOF}_POS to achieve it, find the start index
        sof = 0
        eof = 0
        sof_pos = 0
        eof_pos = 0
        for i in reversed(range(0, self.regions)):
            # Check if the SOP is available
            if mfb["SOF"][i]:
                sof_pos = sof_pos | mfb["SOF_POS"][i]
                sof     = sof | 0x1
            # Check if the EOF is available
            if mfb["EOF"][i]:
                eof_pos = eof_pos | mfb["EOF_POS"][i]
                eof     = eof | 0x1
            # Go to the next bit (if we have something to process)
            if i > 0:
                sof = sof << 1
                eof = eof << 1
                sof_pos = sof_pos << self.sof_elem_width
                eof_pos = eof_pos << self.eof_elem_width
        # Write the SOF and EOF positions
        self.writeh(self.base + self.SOF_POS_OFFSET, int(sof_pos))
        self.writeh(self.base + self.EOF_POS_OFFSET, int(eof_pos))

        # Prepare the valid signals | SOF_VEC (REGIONS) | EOF_VEC (REGIONS | VLD (1b) |
        vld_sig = (sof << (self.regions + 1)) | (eof << 1) | 0x1
        self.writeh(self.base + self.VLD_OFFSET, int(vld_sig))
        self.words_cnt += 1

    def _split(self, data, n):
        """
        This function splits a list elements into chunks of length n. Unused place
        is filled with zeros.

        Parameters:
            - data - data to split (it is typically a list)
            - n  - legth of the stride
        """
        #print(len(list(data)))
        #print(int(n))
        data_list = list(data)
        return [data_list[i:i + int(n)] for i in range(0, len(data_list), int(n))]

    def _fill_zeros(self, data, n):
        """
        Fill the remaining place with zeros to fullfill the lenght constraint

        Parameters:
            - data - block to fill
            - n    - required lenght of the stride

        Returns: The stride with filled zeros.
        """
        if len(data) < n:
            # We need to fill data
            data.extend([0] * (int(n) - len(data)))

    def _fill_mfb_word(self, mfb, n):
        """
        Iterate over the MFB bus and fill remaining blocks with zeros.

        Parameters:
            - mfb      - the MFB structure
            - n        - length of the stride
        """
        for region in mfb["WORD"]:
            # Check if the region contains the required number of blocks. Before that,
            # extend the last know block with zeros
            if len(region) > 0:
                self._fill_zeros(region[-1], n)
            if len(region) < self.region_size:
                # We need to add more regions
                region.extend([[0] * int(n)] * (self.region_size - len(region)))


# Main starting function for a simulatino purposes
def main():
    # TODO: Implement the parameter parsing using the optparse (https://docs.python.org/2/library/optparse.html)
    # Create the instance of player configurator and run the generator

    dev = nfb.open()
    comp = dev.comp_open("netcope,bus,mi", 0) # cesnet,ofm,gen_loop_switch

    try:
        player_config = PlayerConfigurator(4, 8, 8, 8, 2**15, comp.write32, comp.read32, "./pcaps/pkts512-1024.pcap", 0x51c0)
        player_config.configure(True)
        # Pickle the memory structure. It will be used in the second reader script. The stored data format
        # should match with the frame_reader format.
    except IOError as e:
        print("Error during read/write operation: ", str(e))


if __name__ == "__main__":
    main()
