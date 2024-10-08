# test_frame_software.py : Script for testing of frame_player and
#                          frame_recorder software.
#
# Copyright (C) 2017 CESNET z. s. p. o.
# Author(s): Pavel Benacek <benacek@cesnet.cz>

import sys
import os
import scapy.all as scapy

# Testing stuff ###############################################################
# Import the tested code
import player
import recorder

# Extend the path and insert python modules
sys.path.append(os.path.join(os.path.abspath("../.."), "frame_player", "sw"))
sys.path.append(os.path.join(os.path.abspath("../.."), "frame_recorder", "sw"))

# Configuration ###############################################################
# MFB configurations to test
configs_list = (
    (1, 8, 8, 8),
    (2, 8, 8, 8),
    (4, 8, 8, 8),
    (8, 8, 8, 8),
)

# Folder with testing pcaps
pcap_path   = os.path.abspath("./test_pcaps/")

# Player FIFO
fifo_depth  = 1024

# Output pcap file
out_pcap    = os.path.abspath("./output.pcap")

# Path with test PCAPs
pcaps = os.listdir(pcap_path)


def compare_pcaps(input_file, output_file):
    """
    Compare two pcap files if the content is same.
    """
    print("Comparing %s with %s file." % (input_file, output_file))
    # Opent both pcaps in scapy
    in_packets = scapy.rdpcap(input_file)
    out_packets = scapy.rdpcap(output_file)

    # Search for all input packets in the output pcap file
    for in_pkt in in_packets:
        # I know, this is not efficient but it is enough for testing purposes
        if in_pkt not in out_packets:
            print("Following packet wasn't find in the %s!" % (output_file))
            in_pkt.display()
            return False

    print("Both PCAP files contain same packets!")
    return True


def main():
    """
    Main testing process.
    """
    # Iterate over all test scenarios and test the serialization and deserialization for
    # each file.
    for regs, reg_size, block_size, item_width in configs_list:
        for pcap in pcaps:
            print("Testing MFB configuration (%d,%d,%d,%d)" % (regs, reg_size, block_size, item_width))
            print("Input PCAP file:  %s" % (pcap))
            # Absolute PCAP path
            abs_pcap_path = os.path.join(pcap_path, pcap)
            # Prepare the player object and use read/write function in the player module
            play = player.PlayerConfigurator(regs, reg_size, block_size, item_width, fifo_depth, player.write32, player.read32, abs_pcap_path, 0x0)
            # Prepare the recorder object and use read/wrute function in the recorder module
            rec  = recorder.RecorderReader(regs, reg_size, block_size, item_width, recorder.write32, recorder.read32, out_pcap, 0x0, False, 0)
            # Remove old pickle file
            if os.path.exists("memory.pickle"):
                os.remove("memory.pickle")
            # Remove the pcap file and
            if os.path.exists(out_pcap):
                os.remove(out_pcap)
            # Run the configuration. The output is serialized and catched in the
            # memory.pickle file.
            play.configure()
            # Restore the memory and run the packet capture
            try:
                recorder.load_memory("memory.pickle")
                rec.read()
            except IOError:
                print("Error during the loading of pickled memory!")
                return 0x1
            except Exception as e:
                print("Error during the de-serialization!")
                print(str(e))
                return 0x1

            # Compare both pcaps
            if not compare_pcaps(abs_pcap_path, out_pcap):
                return 0x1

    # End the function
    print("\n\n======================")
    print("All tests are OK")
    print("======================\n")

    return 0x0


if __name__ == "__main__":
    ret = main()
    sys.exit(ret)
