import cocotb
from cocotb.triggers import Timer, RisingEdge, Combine

from ndk_core import NFBDevice

import sys
sys.stderr = None # disable warnings from Scapy
from scapy.all import TCP, Ether, IP, raw
sys.stderr = sys.__stderr__

def s2b(pkt):
    return list(bytes(raw(pkt)))

@cocotb.test()
async def cocotb_test_idcomp_invert(dut):
    nfb = NFBDevice(dut)
    await nfb.init()

    mi, dma = nfb.mi[0], nfb.dma

    node = [nfb._fdt.get_node(path) for path in nfb.fdt_get_compatible("netcope,idcomp")][0]
    mi_base = node.get_property('reg')[0]

    await mi.write32(mi_base, 0x12345678)
    assert await mi.read32(mi_base) == 0x12345678 ^ 0xFFFFFFFF

@cocotb.test()
async def cocotb_test_rx_scapy_packet(dut):
    nfb = NFBDevice(dut)
    await nfb.init()

    mac = nfb.eth[0].rxmac
    await mac.enable()
    # Sync the enable command
    await Timer(1, units='us')

    for i in range(2):
        await nfb.dma.rx[0]._push_desc()
    await Timer(1, units='us')

    pkt = Ether()/IP(dst="127.0.0.1")/TCP()/"GET /index.html HTTP/1.0 \n\n"
    await nfb._eth_rx_driver[0].write_packet(s2b(pkt))

    p = await nfb.dma.rx[0].read()
    assert list(p) == s2b(pkt)

    stats = await mac.read_stats()
    assert stats['received'] == 1

@cocotb.test()
async def cocotb_test_tx_scapy_packet(dut):
    nfb = NFBDevice(dut)
    await nfb.init()

    mac = nfb.eth[0].txmac
    await mac.enable()

    pkt = Ether()/IP(dst="127.0.0.1")/TCP()/"GET /index.html HTTP/1.0 \n\n"

    def eth_tx_monitor_cb(p):
        assert p == s2b(pkt)
    nfb._eth_tx_monitor[0].add_callback(eth_tx_monitor_cb)

    await nfb.dma.tx[0].send(s2b(pkt))
    await Timer(10, units='us')
    
    stats = await mac.read_stats()
    assert stats['sent'] == 1
