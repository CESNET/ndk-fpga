import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer, RisingEdge, ClockCycles


async def read_mi(dut, addr):
    dut.MI_ADDR.value = addr
    dut.MI_RD.value = 1
    while dut.MI_ARDY.value == 0:
        await RisingEdge(dut.CLK)
    dut.MI_RD.value = 0

    while dut.MI_DRDY.value == 0:
        await RisingEdge(dut.CLK)

    data = dut.MI_DRD.value
    await RisingEdge(dut.CLK)

    return data


async def send_mfb(dut, byte_cnt):
    bytes_in_word = 2**len(dut.RX_EOF_POS)

    dut.RX_SOF_POS.value = 0
    dut.RX_EOF_POS.value = (byte_cnt - 1) % (bytes_in_word)
    dut.RX_SOF.value = 1

    dut.RX_SRC_RDY.value = 1
    for i in range(byte_cnt):
        dut.RX_SOF.value = 1 if i < bytes_in_word else 0
        dut.RX_EOF.value = 1 if i == byte_cnt - 1 else 0

        if i % bytes_in_word == bytes_in_word - 1 or i == byte_cnt - 1:
            await RisingEdge(dut.CLK)

    dut.RX_SRC_RDY.value = 0


async def init(dut):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 10, 'ns').start())

    # Do a reset
    dut.RST.value = 1
    await ClockCycles(dut.CLK, 2)
    dut.RST.value = 0
    await RisingEdge(dut.CLK)

    dut.RX_DST_RDY.value = 1


@cocotb.test()
async def test_bytes_conut(dut):
    """Send transaction and check byte counter with MI READ"""
    await init(dut)

    for i in range(1650):
        await send_mfb(dut, i + 1)
    # MI latency of DUT is 3 CLK cycles
    await Timer(30, 'ns')

    # Check that transaction last 5 CLK cycles
    assert await read_mi(dut, 0) == 5
    # Check that transaction have 193 bytes
    assert await read_mi(dut, 8) == 16543


@cocotb.test()
async def test_reset(dut):
    """Check zero ticks after issuing reset"""
    await init(dut)

    await send_mfb(dut, 1987)

    dut.RST.value = 1
    await ClockCycles(dut.CLK, 1)
    dut.RST.value = 0
    # MI latency of DUT is 3 CLK cycles
    await ClockCycles(dut.CLK, 3)

    # Check that counter of ticks was zeroed
    assert await read_mi(dut, 0) == 0
