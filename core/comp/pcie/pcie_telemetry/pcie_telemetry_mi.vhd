-- pcie_telemetry_mi.vhd: PCIe infrastructure telemetry with MI access
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The PCIE_TELEMETRY_MI collects performance data of the PCIe infrastructure of
-- the NDK and makes it readable over the MI bus. It observes, for every PCIe
-- endpoint, the four MFB buses around the PTC module and the sources that stop
-- the PCIe transfer.
--
-- A BRAKE is one input signal of this module. It is active in every cycle in
-- which one named reason stopped the data flow of the PTC.
--
-- **What is measured**
--
-- - the PCIe settings negotiated with the host: maximum payload size (MPS),
--   maximum read request size (MRRS), extended tag, 10-bit tag, read completion
--   boundary (RCB) and link up,
-- - the free PCIe tags of the PTC and the free words of its downstream storage
--   FIFO. Each of them is reported twice, as the value now and as the lowest
--   value reached,
-- - per MFB bus: transferred words, transferred MFB items, started transactions
--   and the cycles the bus was stalled by its consumer. The cycles in which each
--   region carried data are counted separately,
-- - the MVB items of the buses between the DMA and the PTC. These buses carry
--   the headers of the transactions on a separate MVB,
-- - the cycles in which a BRAKE signal stopped the transfer, one counter per
--   reason. The reasons are those listed at the PCIE_PTC_BRAKE port. A firmware
--   that does not report a reason leaves that counter at zero,
-- - how long the PCIe tags and the storage FIFO words were short. Each of the
--   two is a histogram of four bands, from exhausted to more than half free.
--
-- Every clock domain has its own counter of elapsed cycles, so every share can
-- be computed from one measurement window. The counters of the PCIe clock and
-- the BRAKE signals are measured on that same clock, so they describe the same
-- cycles.
--
-- **Structure**
--
-- The module instantiates two :ref:`PCIE_TELEMETRY_PROBE <pcie_telemetry_probe>`
-- units per PCIe endpoint, one for the PCIe clock domain and one for the DMA
-- clock domain. :ref:`PCIE_TELEMETRY_ACC <pcie_telemetry_acc>` sums what the
-- probes report into the wide counters that software reads.
--
-- **Reading the counters**
--
-- Reading all counters takes many MI transactions, so software must first issue
-- the SNAPSHOT command. It copies all counters into a second memory. The counter
-- window then returns that second memory. All values read after one SNAPSHOT
-- therefore belong to the same moment.
--
-- **Register map** (byte offsets, all registers are 32-bit)
--
-- .. code-block:: text
--
--     0x0000 RO MAGIC        = 0x50544C4D
--     0x0004 RO VERSION      [31:16] major, [15:0] minor
--     0x0008 RO CFG_TOPOLOGY [7:0] PCIe endpoints, [15:8] DMA ports per endpoint,
--                            [23:16] probes
--     0x000C RO CFG_LAYOUT   [15:0] counters, [23:16] counter width,
--                            [31:24] counters per endpoint
--     0x0010 RO CFG_PCIE     [7:0] channels, [15:8] buses, [23:16] regions of
--                            the probe, [31:24] BRAKE signals of the PCIe probe
--     0x0014 RO CFG_DMA      the same for the DMA clock probe
--     0x0018 RO CFG_DRAIN    [15:0] DRAIN_PERIOD in cycles,
--                            [23:16] bytes per MFB item
--     0x001C RO CNT_BASE     byte offset of the counter window
--     0x0020 WO COMMAND      bit0 snapshot, bit1 clear counters, bit2 clear flags,
--                            bit3 clear the lowest values in PCIE_TAGS and PCIE_STFIFO
--     0x0024 RO STATUS       bit0 busy, bit1 a delta was lost,
--                            bit2 a read-out started too early
--     0x0028 RW READ_SEL     bit0 0 = read snapshot copy, 1 = read live copy
--     0x002C RO CFG_REGIONS  regions each bus really has, [7:0] RQ, [15:8] RC,
--                            [23:16] UP, [31:24] DOWN. A bus narrower than its
--                            probe is padded, its extra regions never carry data.
--     0x0030 RO CFG_WIDTH    [15:0] bytes per region of the RQ bus,
--                            [31:16] bytes per region of the RC bus
--     0x003C RO CFG_WIDTH_DMA [15:0] bytes per region of the UP bus,
--                            [31:16] bytes per region of the DOWN bus
--     0x0034 RO CFG_HIST     [7:0] bands per histogram, [15:8] histograms of the
--                            PCIe clock probe, [23:16] of the DMA clock probe.
--                            The bands are the last BRAKE channels of a probe,
--                            in the order of the signals they belong to: the tags
--                            first, then the storage FIFO.
--     0x0038 RO CFG_CAPACITY [15:0] PCIe tags, [31:16] storage FIFO words. The
--                            band thresholds are an eighth and a half of these.
--     0x0040 RO PCIE_STATUS  one register per endpoint
--                            [2:0] MPS, [5:3] MRRS, [6] extended tag enable,
--                            [7] 10-bit tag enable, [8] RCB, [9] link up
--     0x0080 RO PCIE_TAGS    one register per endpoint
--                            [15:0] free tags, [31:16] lowest free tags
--     0x00C0 RO PCIE_STFIFO  one register per endpoint
--                            [15:0] free FIFO words, [31:16] lowest free words
--     0x8000 RO counters, two 32-bit words per counter, low word first
--
-- Counter numbering is described at :ref:`PCIE_TELEMETRY_PROBE
-- <pcie_telemetry_probe>`. Counters of one endpoint are stored together. The
-- counters of its PCIe clock probe come first, those of its DMA clock probe
-- second.
--
entity PCIE_TELEMETRY_MI is
    generic (
        -- Number of monitored PCIe endpoints.
        PCIE_ENDPOINTS            : natural := 1;
        -- Number of DMA ports (PTC DMA side streams) per PCIe endpoint.
        DMA_PORTS                 : natural := 1;
        -- Number of MFB regions of the RQ bus, that is PTC to PCIe. The RQ and
        -- RC buses are measured together with the larger of the two values. Tie
        -- the unused SOF and EOF bits of the narrower bus to zero.
        PCIE_RQ_MFB_REGIONS       : natural := 2;
        -- Number of MFB regions of the RC bus, that is PCIe to PTC.
        PCIE_RC_MFB_REGIONS       : natural := 2;
        -- Number of MFB regions of the UP bus, that is DMA to PTC.
        DMA_UP_MFB_REGIONS        : natural := 2;
        -- Number of MFB regions of the DOWN bus, that is PTC to DMA.
        DMA_DOWN_MFB_REGIONS      : natural := 2;
        -- Number of bytes in one MFB region of the RQ bus. The value is only
        -- reported to software and changes nothing in this module.
        PCIE_RQ_MFB_REGION_BYTES  : natural := 32;
        -- Number of bytes in one MFB region of the RC bus.
        PCIE_RC_MFB_REGION_BYTES  : natural := 32;
        -- Number of bytes in one MFB region of the UP bus.
        DMA_UP_MFB_REGION_BYTES   : natural := 32;
        -- Number of bytes in one MFB region of the DOWN bus.
        DMA_DOWN_MFB_REGION_BYTES : natural := 32;
        -- Number of bytes in one MFB item. It converts the region sizes into
        -- item counts. The EOF_POS fields address items, not bytes.
        MFB_ITEM_BYTES            : natural := 4;
        -- Width of one EOF_POS field of the PCIe side buses. It is the log2 of
        -- the item count of the larger region of the two.
        PCIE_EOF_POS_WIDTH        : natural := 3;
        -- The same for the DMA side buses.
        DMA_EOF_POS_WIDTH         : natural := 3;
        -- Width of the counters that software reads, allowed range is 33 to 64.
        CNT_WIDTH                 : natural := 48;
        -- Number of cycles between two read-outs of the probe counters. It must
        -- be a power of two. A longer period costs more flip-flops in the fast
        -- clock domains, but it leaves more time for the MI clock domain.
        DRAIN_PERIOD              : natural := 4096;
        -- Number of PCIe tags the PTC can use at the same time. It only sets the
        -- thresholds of the tag histogram, which are an eighth and a half of it.
        TAG_CAPACITY              : natural := 256;
        -- Number of words the PTC storage FIFO holds. It sets the thresholds of
        -- the storage FIFO histogram, which are an eighth and a half of it.
        STFIFO_CAPACITY           : natural := 1024;
        -- FPGA device
        DEVICE                    : string  := "AGILEX"
    );
    port (
        -- =====================================================================
        --  MI INTERFACE (MI_CLK)
        -- =====================================================================
        MI_CLK              : in  std_logic;
        MI_RESET            : in  std_logic;

        MI_DWR              : in  std_logic_vector(32-1 downto 0);
        MI_ADDR             : in  std_logic_vector(32-1 downto 0);
        MI_BE               : in  std_logic_vector(4-1 downto 0);
        MI_RD               : in  std_logic;
        MI_WR               : in  std_logic;
        MI_DRD              : out std_logic_vector(32-1 downto 0);
        MI_ARDY             : out std_logic;
        MI_DRDY             : out std_logic;

        -- =====================================================================
        --  PCIE CLOCK DOMAIN OF EACH ENDPOINT
        -- =====================================================================
        PCIE_CLK            : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_RESET          : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- Observed buses, bus 0 = PTC to PCIe (RQ), bus 1 = PCIe to PTC (RC).
        PCIE_MFB_SOF        : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*max(PCIE_RQ_MFB_REGIONS,PCIE_RC_MFB_REGIONS)-1 downto 0);
        PCIE_MFB_EOF        : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*max(PCIE_RQ_MFB_REGIONS,PCIE_RC_MFB_REGIONS)-1 downto 0);
        -- Item of the region in which the frame ends, valid with PCIE_MFB_EOF.
        PCIE_MFB_EOF_POS    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*max(PCIE_RQ_MFB_REGIONS,PCIE_RC_MFB_REGIONS)*PCIE_EOF_POS_WIDTH-1 downto 0) := (others => (others => '0'));
        PCIE_MFB_SRC_RDY    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
        PCIE_MFB_DST_RDY    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);

        -- BRAKE signals of the PTC, one bit per reason:
        --   bit 0 = the pool of free PCIe tags is too small,
        --   bit 1 = the tag FIFO had no tag ready, although the pool is deep enough,
        --   bit 2 = no free space in the downstream storage FIFO,
        --   bit 3 = no free entry in the Completion Header buffer of the PCIe Hard IP,
        --   bit 4 = the MFB is held before the split between the DMA ports,
        --   bit 5 = the MVB is held before that same split.
        -- Bits 0 to 3 stop the stream towards PCIe. Bits 4 and 5 stop the stream
        -- towards the DMA module. A firmware that does not report a reason leaves
        -- its bit at zero. Software reads the number of reasons from CFG_PCIE.
        PCIE_PTC_BRAKE      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(6-1 downto 0) := (others => (others => '0'));
        -- Free words of the PTC downstream storage FIFO.
        PCIE_STFIFO_FREE    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(16-1 downto 0);

        -- Negotiated PCIe configuration.
        PCIE_MPS            : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
        PCIE_MRRS           : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
        PCIE_EXT_TAG_EN     : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_10B_TAG_REQ_EN : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_RCB_SIZE       : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_LINK_UP        : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        --  DMA CLOCK DOMAIN
        -- =====================================================================
        DMA_CLK             : in  std_logic;
        DMA_RESET           : in  std_logic;

        -- Observed buses, bus 2*p = DMA to PTC (UP), bus 2*p+1 = PTC to DMA
        -- (DOWN) of the DMA port p.
        DMA_MFB_SOF         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS*max(DMA_UP_MFB_REGIONS,DMA_DOWN_MFB_REGIONS)-1 downto 0);
        DMA_MFB_EOF         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS*max(DMA_UP_MFB_REGIONS,DMA_DOWN_MFB_REGIONS)-1 downto 0);
        -- Item of the region in which the frame ends, valid with DMA_MFB_EOF.
        DMA_MFB_EOF_POS     : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS*max(DMA_UP_MFB_REGIONS,DMA_DOWN_MFB_REGIONS)*DMA_EOF_POS_WIDTH-1 downto 0) := (others => (others => '0'));
        DMA_MFB_SRC_RDY     : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS-1 downto 0);
        DMA_MFB_DST_RDY     : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS-1 downto 0);

        -- The headers of the DMA side are carried on separate MVB buses. Every
        -- request has an item here, but only a request with payload also reaches
        -- the MFB.
        DMA_MVB_VLD         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS*max(DMA_UP_MFB_REGIONS,DMA_DOWN_MFB_REGIONS)-1 downto 0) := (others => (others => '0'));
        DMA_MVB_SRC_RDY     : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS-1 downto 0) := (others => (others => '0'));
        DMA_MVB_DST_RDY     : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2*DMA_PORTS-1 downto 0) := (others => (others => '0'));

        -- Number of free PCIe tags in the PTC, on the PCIe clock. The PTC also
        -- provides this value resynchronised to the DMA clock. It is measured
        -- here so that it shares the clock with the BRAKE signal that becomes
        -- active when the tags run out.
        PCIE_TAG_FREE       : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11-1 downto 0)
    );
end entity;

architecture FULL of PCIE_TELEMETRY_MI is

    constant VERSION_MAJOR   : natural := 2;
    constant VERSION_MINOR   : natural := 0;
    constant MAGIC           : std_logic_vector(32-1 downto 0) := X"5054_4C4D";
    -- Byte offset of the counter window, decoded by MI_ADDR(15).
    constant CNT_BASE        : std_logic_vector(32-1 downto 0) := X"0000_8000";

    -- Each probe observes the two buses of its clock domain with one region
    -- count. The narrower bus is padded with regions that never carry data.
    constant PCIE_MFB_REGIONS : natural := max(PCIE_RQ_MFB_REGIONS,PCIE_RC_MFB_REGIONS);
    constant DMA_MFB_REGIONS  : natural := max(DMA_UP_MFB_REGIONS,DMA_DOWN_MFB_REGIONS);

    constant STFIFO_WIDTH    : natural := 16;
    constant TAG_WIDTH       : natural := 11;

    -- Number of bands of one histogram of a resource that can run out.
    constant HIST_LEVELS     : natural := 4;
    -- Both histograms are measured by the probe of the PCIe clock domain, one
    -- for the storage FIFO and one for the PCIe tags. The probe of the DMA clock
    -- domain measures no histogram.
    constant PCIE_HISTS      : natural := 2;
    constant DMA_HISTS       : natural := 0;

    constant PCIE_BUSES      : natural := 2;
    -- The six BRAKE signals of the PTC, then the bands of the tag histogram and
    -- of the storage FIFO histogram, in the order of the signals they belong to.
    constant PCIE_BRAKES     : natural := 6 + PCIE_HISTS*HIST_LEVELS;
    constant DMA_BUSES       : natural := 2*DMA_PORTS;
    constant DMA_BRAKES      : natural := DMA_HISTS*HIST_LEVELS;

    constant PCIE_CHANNELS   : natural := 1 + PCIE_BUSES*(6+PCIE_MFB_REGIONS) + PCIE_BRAKES;
    constant DMA_CHANNELS    : natural := 1 + DMA_BUSES*(6+DMA_MFB_REGIONS) + DMA_BRAKES;

    -- Items in one region of each observed bus, in the order in which the probes
    -- observe them. The PCIe probe takes RQ and then RC. The DMA probe takes UP
    -- and then DOWN of every port.
    function pcie_region_items_f return i_array_t is
        variable items_v : i_array_t(PCIE_BUSES-1 downto 0);
    begin
        items_v(0) := PCIE_RQ_MFB_REGION_BYTES/MFB_ITEM_BYTES;
        items_v(1) := PCIE_RC_MFB_REGION_BYTES/MFB_ITEM_BYTES;
        return items_v;
    end function;

    function dma_region_items_f return i_array_t is
        variable items_v : i_array_t(DMA_BUSES-1 downto 0);
    begin
        for p in 0 to DMA_PORTS-1 loop
            items_v(2*p)   := DMA_UP_MFB_REGION_BYTES/MFB_ITEM_BYTES;
            items_v(2*p+1) := DMA_DOWN_MFB_REGION_BYTES/MFB_ITEM_BYTES;
        end loop;
        return items_v;
    end function;
    constant EP_CHANNELS     : natural := PCIE_CHANNELS + DMA_CHANNELS;

    constant STREAMS         : natural := 2*PCIE_ENDPOINTS;
    constant ENTRIES         : natural := 2**log2(PCIE_ENDPOINTS*EP_CHANNELS);
    constant ENTRY_AWIDTH    : natural := log2(ENTRIES);

    constant PCIE_IDX_WIDTH  : natural := log2(PCIE_CHANNELS);
    constant DMA_IDX_WIDTH   : natural := log2(DMA_CHANNELS);
    constant IDX_WIDTH       : natural := max(PCIE_IDX_WIDTH,DMA_IDX_WIDTH);
    constant PCIE_ITEMS_MAX  : natural := max(PCIE_RQ_MFB_REGION_BYTES,PCIE_RC_MFB_REGION_BYTES)/MFB_ITEM_BYTES;
    constant DMA_ITEMS_MAX   : natural := max(DMA_UP_MFB_REGION_BYTES,DMA_DOWN_MFB_REGION_BYTES)/MFB_ITEM_BYTES;
    constant PCIE_DELTA_W    : natural := log2(DRAIN_PERIOD*max(1,PCIE_MFB_REGIONS*PCIE_ITEMS_MAX)+1);
    constant DMA_DELTA_W     : natural := log2(DRAIN_PERIOD*max(1,DMA_MFB_REGIONS*DMA_ITEMS_MAX)+1);
    constant DELTA_WIDTH     : natural := max(PCIE_DELTA_W,DMA_DELTA_W);

    -- Status word that crosses from the PCIe clock domain of one endpoint. It
    -- holds the link configuration, then the current and the lowest value of both
    -- resources.
    constant PCIE_AUX_WIDTH  : natural := 10 + 2*STFIFO_WIDTH + 2*TAG_WIDTH;
    constant CFG_LO          : natural := 0;
    constant STF_NOW_LO      : natural := CFG_LO + 10;
    constant STF_MIN_LO      : natural := STF_NOW_LO + STFIFO_WIDTH;
    constant TAG_NOW_LO      : natural := STF_MIN_LO + STFIFO_WIDTH;
    constant TAG_MIN_LO      : natural := TAG_NOW_LO + TAG_WIDTH;

    -- One hot band of a resource that can run out. Band 0 means the resource is
    -- exhausted and already blocks the transfer. Band 3 means that more than half
    -- of it is free. The thresholds are an eighth and a half of the capacity.
    function hist_level_f (free : std_logic_vector; capacity : natural) return std_logic_vector is
        variable value_v : unsigned(free'length-1 downto 0);
        variable band_v  : std_logic_vector(HIST_LEVELS-1 downto 0);
    begin
        value_v := unsigned(free);
        band_v  := (others => '0');
        if (value_v = 0) then
            band_v(0) := '1';
        elsif (value_v <= capacity/8) then
            band_v(1) := '1';
        elsif (value_v <= capacity/2) then
            band_v(2) := '1';
        else
            band_v(3) := '1';
        end if;
        return band_v;
    end function;

    -- Counters of one endpoint are stored together. Those of its PCIe clock
    -- probe come first.
    function stream_base_f return i_array_t is
        variable base_v : i_array_t(STREAMS-1 downto 0);
    begin
        for ep in 0 to PCIE_ENDPOINTS-1 loop
            base_v(2*ep)   := ep*EP_CHANNELS;
            base_v(2*ep+1) := ep*EP_CHANNELS + PCIE_CHANNELS;
        end loop;
        return base_v;
    end function;

    constant STREAM_BASE : i_array_t(STREAMS-1 downto 0) := stream_base_f;

    signal probe_index    : slv_array_t(STREAMS-1 downto 0)(IDX_WIDTH-1 downto 0);
    signal probe_delta    : slv_array_t(STREAMS-1 downto 0)(DELTA_WIDTH-1 downto 0);
    signal probe_vld      : std_logic_vector(STREAMS-1 downto 0);
    signal probe_rd       : std_logic_vector(STREAMS-1 downto 0);
    signal probe_fifo_ovf : std_logic_vector(STREAMS-1 downto 0);
    signal probe_overrun  : std_logic_vector(STREAMS-1 downto 0);

    signal pcie_aux_dout  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(PCIE_AUX_WIDTH-1 downto 0);
    signal pcie_aux_vld   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal cfg_reg        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(10-1 downto 0);
    signal stfifo_now     : u_array_t(PCIE_ENDPOINTS-1 downto 0)(STFIFO_WIDTH-1 downto 0);
    signal stfifo_min     : u_array_t(PCIE_ENDPOINTS-1 downto 0)(STFIFO_WIDTH-1 downto 0);
    signal tag_now        : u_array_t(PCIE_ENDPOINTS-1 downto 0)(TAG_WIDTH-1 downto 0);
    signal tag_min        : u_array_t(PCIE_ENDPOINTS-1 downto 0)(TAG_WIDTH-1 downto 0);

    signal cmd_snapshot   : std_logic;
    signal cmd_clear      : std_logic;
    signal cmd_clear_mark : std_logic;
    signal flag_clr_tgl   : std_logic;
    signal read_live      : std_logic;
    signal acc_busy       : std_logic;

    signal acc_rd_addr    : std_logic_vector(ENTRY_AWIDTH+1-1 downto 0);
    signal acc_rd_data    : std_logic_vector(CNT_WIDTH-1 downto 0);

    signal reg_dout       : std_logic_vector(32-1 downto 0);
    signal reg_dout_reg   : std_logic_vector(32-1 downto 0);
    signal mi_addr_reg    : std_logic_vector(32-1 downto 0);
    signal mi_rd_reg      : std_logic;
    signal mi_rd_reg2     : std_logic;
    signal mi_drd_reg     : std_logic_vector(32-1 downto 0);

begin

    assert (CNT_WIDTH > 32 and CNT_WIDTH <= 64)
        report "PCIE_TELEMETRY_MI: Set CNT_WIDTH between 33 and 64."
        severity failure;

    assert (PCIE_EOF_POS_WIDTH = log2(max(PCIE_RQ_MFB_REGION_BYTES,PCIE_RC_MFB_REGION_BYTES)/MFB_ITEM_BYTES))
        report "PCIE_TELEMETRY_MI: Set PCIE_EOF_POS_WIDTH to the log2 of the items in the larger PCIe side region."
        severity failure;

    assert (DMA_EOF_POS_WIDTH = log2(max(DMA_UP_MFB_REGION_BYTES,DMA_DOWN_MFB_REGION_BYTES)/MFB_ITEM_BYTES))
        report "PCIE_TELEMETRY_MI: Set DMA_EOF_POS_WIDTH to the log2 of the items in the larger DMA side region."
        severity failure;

    assert (PCIE_ENDPOINTS <= 16)
        report "PCIE_TELEMETRY_MI: The register map holds at most 16 PCIe endpoints."
        severity failure;

    assert (PCIE_ENDPOINTS*EP_CHANNELS*8 <= 16#8000#)
        report "PCIE_TELEMETRY_MI: The counter window is too small for this configuration."
        severity failure;

    -- =========================================================================
    --  1. PROBES
    -- =========================================================================

    ep_g : for ep in 0 to PCIE_ENDPOINTS-1 generate

        signal pcie_tick       : std_logic;
        signal dma_tick        : std_logic;
        signal pcie_index      : std_logic_vector(PCIE_IDX_WIDTH-1 downto 0);
        signal pcie_delta      : std_logic_vector(PCIE_DELTA_W-1 downto 0);
        signal dma_index       : std_logic_vector(DMA_IDX_WIDTH-1 downto 0);
        signal dma_delta       : std_logic_vector(DMA_DELTA_W-1 downto 0);

        signal stfifo_win_min  : unsigned(STFIFO_WIDTH-1 downto 0);
        signal pcie_aux_din    : std_logic_vector(PCIE_AUX_WIDTH-1 downto 0);
        signal tag_win_min     : unsigned(TAG_WIDTH-1 downto 0);

        signal stfifo_band     : std_logic_vector(HIST_LEVELS-1 downto 0);
        signal tag_band        : std_logic_vector(HIST_LEVELS-1 downto 0);

    begin

        -- Each decode gets a register of its own, so that the compares never
        -- stand between the observed signal and the counters of the probe.
        process (PCIE_CLK(ep))
        begin
            if (rising_edge(PCIE_CLK(ep))) then
                stfifo_band <= hist_level_f(PCIE_STFIFO_FREE(ep),STFIFO_CAPACITY);
                if (PCIE_RESET(ep) = '1') then
                    stfifo_band <= (others => '0');
                end if;
            end if;
        end process;

        process (PCIE_CLK(ep))
        begin
            if (rising_edge(PCIE_CLK(ep))) then
                tag_band <= hist_level_f(PCIE_TAG_FREE(ep),TAG_CAPACITY);
                if (PCIE_RESET(ep) = '1') then
                    tag_band <= (others => '0');
                end if;
            end if;
        end process;

        pcie_probe_i : entity work.PCIE_TELEMETRY_PROBE
        generic map (
            BUSES            => PCIE_BUSES,
            REGIONS          => PCIE_MFB_REGIONS,
            REGION_ITEMS     => pcie_region_items_f,
            EOF_POS_WIDTH    => PCIE_EOF_POS_WIDTH,
            REGION_ITEMS_MAX => PCIE_ITEMS_MAX,
            BRAKES           => PCIE_BRAKES,
            DRAIN_PERIOD     => DRAIN_PERIOD,
            DEVICE           => DEVICE
        )
        port map (
            CLK         => PCIE_CLK(ep),
            RESET       => PCIE_RESET(ep),

            RX_SOF      => PCIE_MFB_SOF(ep),
            RX_EOF      => PCIE_MFB_EOF(ep),
            RX_EOF_POS  => PCIE_MFB_EOF_POS(ep),
            RX_SRC_RDY  => PCIE_MFB_SRC_RDY(ep),
            RX_DST_RDY  => PCIE_MFB_DST_RDY(ep),
            RX_BRAKE    => stfifo_band & tag_band & PCIE_PTC_BRAKE(ep),

            DRAIN_TICK  => pcie_tick,

            MI_CLK      => MI_CLK,
            MI_RESET    => MI_RESET,

            TX_INDEX    => pcie_index,
            TX_DELTA    => pcie_delta,
            TX_VLD      => probe_vld(2*ep),
            TX_RD       => probe_rd(2*ep),

            MI_FLAG_CLR => flag_clr_tgl,
            TX_FIFO_OVF => probe_fifo_ovf(2*ep),
            TX_OVERRUN  => probe_overrun(2*ep)
        );

        probe_index(2*ep) <= std_logic_vector(resize(unsigned(pcie_index),IDX_WIDTH));
        probe_delta(2*ep) <= std_logic_vector(resize(unsigned(pcie_delta),DELTA_WIDTH));

        dma_probe_i : entity work.PCIE_TELEMETRY_PROBE
        generic map (
            BUSES            => DMA_BUSES,
            REGIONS          => DMA_MFB_REGIONS,
            REGION_ITEMS     => dma_region_items_f,
            EOF_POS_WIDTH    => DMA_EOF_POS_WIDTH,
            REGION_ITEMS_MAX => DMA_ITEMS_MAX,
            BRAKES           => DMA_BRAKES,
            DRAIN_PERIOD     => DRAIN_PERIOD,
            DEVICE           => DEVICE
        )
        port map (
            CLK         => DMA_CLK,
            RESET       => DMA_RESET,

            RX_SOF      => DMA_MFB_SOF(ep),
            RX_EOF      => DMA_MFB_EOF(ep),
            RX_EOF_POS  => DMA_MFB_EOF_POS(ep),
            RX_SRC_RDY  => DMA_MFB_SRC_RDY(ep),
            RX_DST_RDY  => DMA_MFB_DST_RDY(ep),
            RX_BRAKE    => (others => '0'),

            RX_MVB_VLD     => DMA_MVB_VLD(ep),
            RX_MVB_SRC_RDY => DMA_MVB_SRC_RDY(ep),
            RX_MVB_DST_RDY => DMA_MVB_DST_RDY(ep),

            DRAIN_TICK  => dma_tick,

            MI_CLK      => MI_CLK,
            MI_RESET    => MI_RESET,

            TX_INDEX    => dma_index,
            TX_DELTA    => dma_delta,
            TX_VLD      => probe_vld(2*ep+1),
            TX_RD       => probe_rd(2*ep+1),

            MI_FLAG_CLR => flag_clr_tgl,
            TX_FIFO_OVF => probe_fifo_ovf(2*ep+1),
            TX_OVERRUN  => probe_overrun(2*ep+1)
        );

        probe_index(2*ep+1) <= std_logic_vector(resize(unsigned(dma_index),IDX_WIDTH));
        probe_delta(2*ep+1) <= std_logic_vector(resize(unsigned(dma_delta),DELTA_WIDTH));

        -- ---------------------------------------------------------------------
        -- STATUS OF THE PCIE CLOCK DOMAIN
        -- ---------------------------------------------------------------------

        -- The lowest value inside one DRAIN_PERIOD is kept here. The lowest value
        -- over the whole measurement is kept in the MI clock domain.
        process (PCIE_CLK(ep))
        begin
            if (rising_edge(PCIE_CLK(ep))) then
                if (pcie_tick = '1') then
                    stfifo_win_min <= unsigned(PCIE_STFIFO_FREE(ep));
                    tag_win_min    <= unsigned(PCIE_TAG_FREE(ep));
                else
                    if (unsigned(PCIE_STFIFO_FREE(ep)) < stfifo_win_min) then
                        stfifo_win_min <= unsigned(PCIE_STFIFO_FREE(ep));
                    end if;
                    if (unsigned(PCIE_TAG_FREE(ep)) < tag_win_min) then
                        tag_win_min <= unsigned(PCIE_TAG_FREE(ep));
                    end if;
                end if;
                if (PCIE_RESET(ep) = '1') then
                    stfifo_win_min <= (others => '1');
                    tag_win_min    <= (others => '1');
                end if;
            end if;
        end process;

        pcie_aux_din <= std_logic_vector(tag_win_min) & PCIE_TAG_FREE(ep) &
                        std_logic_vector(stfifo_win_min) & PCIE_STFIFO_FREE(ep) &
                        PCIE_LINK_UP(ep) & PCIE_RCB_SIZE(ep) & PCIE_10B_TAG_REQ_EN(ep) &
                        PCIE_EXT_TAG_EN(ep) & PCIE_MRRS(ep) & PCIE_MPS(ep);

        pcie_aux_i : entity work.ASYNC_BUS_HANDSHAKE
        generic map (
            DATA_WIDTH => PCIE_AUX_WIDTH
        )
        port map (
            ACLK     => PCIE_CLK(ep),
            ARST     => PCIE_RESET(ep),
            ADATAIN  => pcie_aux_din,
            ASEND    => pcie_tick,
            AREADY   => open,

            BCLK     => MI_CLK,
            BRST     => MI_RESET,
            BDATAOUT => pcie_aux_dout(ep),
            BLOAD    => '1',
            BVALID   => pcie_aux_vld(ep)
        );

        -- ---------------------------------------------------------------------
        -- STATUS REGISTERS IN THE MI CLOCK DOMAIN
        -- ---------------------------------------------------------------------

        -- The probes report the lowest value of every DRAIN_PERIOD. The lowest of
        -- the reported values is therefore the lowest value since the last clear.
        process (MI_CLK)
        begin
            if (rising_edge(MI_CLK)) then
                if (pcie_aux_vld(ep) = '1') then
                    cfg_reg(ep)    <= pcie_aux_dout(ep)(CFG_LO+10-1 downto CFG_LO);
                    stfifo_now(ep) <= unsigned(pcie_aux_dout(ep)(STF_NOW_LO+STFIFO_WIDTH-1 downto STF_NOW_LO));
                    tag_now(ep)    <= unsigned(pcie_aux_dout(ep)(TAG_NOW_LO+TAG_WIDTH-1 downto TAG_NOW_LO));
                    if (unsigned(pcie_aux_dout(ep)(STF_MIN_LO+STFIFO_WIDTH-1 downto STF_MIN_LO)) < stfifo_min(ep)) then
                        stfifo_min(ep) <= unsigned(pcie_aux_dout(ep)(STF_MIN_LO+STFIFO_WIDTH-1 downto STF_MIN_LO));
                    end if;
                    if (unsigned(pcie_aux_dout(ep)(TAG_MIN_LO+TAG_WIDTH-1 downto TAG_MIN_LO)) < tag_min(ep)) then
                        tag_min(ep) <= unsigned(pcie_aux_dout(ep)(TAG_MIN_LO+TAG_WIDTH-1 downto TAG_MIN_LO));
                    end if;
                end if;

                if (cmd_clear = '1' or cmd_clear_mark = '1') then
                    stfifo_min(ep) <= (others => '1');
                    tag_min(ep)    <= (others => '1');
                end if;

                if (MI_RESET = '1') then
                    cfg_reg(ep)    <= (others => '0');
                    stfifo_now(ep) <= (others => '0');
                    stfifo_min(ep) <= (others => '1');
                    tag_now(ep)    <= (others => '0');
                    tag_min(ep)    <= (others => '1');
                end if;
            end if;
        end process;

    end generate;

    -- =========================================================================
    --  2. COUNTER MEMORY
    -- =========================================================================

    acc_i : entity work.PCIE_TELEMETRY_ACC
    generic map (
        STREAMS     => STREAMS,
        STREAM_BASE => STREAM_BASE,
        ENTRIES     => ENTRIES,
        IDX_WIDTH   => IDX_WIDTH,
        DELTA_WIDTH => DELTA_WIDTH,
        CNT_WIDTH   => CNT_WIDTH
    )
    port map (
        CLK      => MI_CLK,
        RESET    => MI_RESET,

        RX_INDEX => probe_index,
        RX_DELTA => probe_delta,
        RX_VLD   => probe_vld,
        RX_RD    => probe_rd,

        SNAPSHOT => cmd_snapshot,
        CLEAR    => cmd_clear,
        BUSY     => acc_busy,

        RD_ADDR  => acc_rd_addr,
        RD_EN    => MI_RD,
        RD_DATA  => acc_rd_data
    );

    acc_rd_addr <= (not read_live) & MI_ADDR(ENTRY_AWIDTH+3-1 downto 3);

    -- =========================================================================
    --  3. MI REGISTERS
    -- =========================================================================

    MI_ARDY <= MI_RD or MI_WR;

    process (MI_CLK)
    begin
        if (rising_edge(MI_CLK)) then
            cmd_snapshot   <= '0';
            cmd_clear      <= '0';
            cmd_clear_mark <= '0';

            if (MI_WR = '1' and MI_ADDR(15) = '0') then
                case (MI_ADDR(7 downto 2)) is
                    when "001000" =>
                        cmd_snapshot   <= MI_DWR(0);
                        cmd_clear      <= MI_DWR(1);
                        cmd_clear_mark <= MI_DWR(3);
                        if (MI_DWR(2) = '1') then
                            flag_clr_tgl <= not flag_clr_tgl;
                        end if;
                    when "001010" =>
                        read_live <= MI_DWR(0);
                    when others =>
                        null;
                end case;
            end if;

            if (MI_RESET = '1') then
                cmd_snapshot   <= '0';
                cmd_clear      <= '0';
                cmd_clear_mark <= '0';
                flag_clr_tgl   <= '0';
                read_live      <= '0';
            end if;
        end if;
    end process;

    reg_dout_p : process (all)
        variable ep_v : natural;
    begin
        reg_dout <= (others => '0');
        ep_v     := to_integer(unsigned(MI_ADDR(5 downto 2)));
        if (ep_v > PCIE_ENDPOINTS-1) then
            ep_v := 0;
        end if;

        case (MI_ADDR(7 downto 6)) is
            when "01" =>
                if (to_integer(unsigned(MI_ADDR(5 downto 2))) < PCIE_ENDPOINTS) then
                    reg_dout(10-1 downto 0) <= cfg_reg(ep_v);
                end if;

            when "10" =>
                if (to_integer(unsigned(MI_ADDR(5 downto 2))) < PCIE_ENDPOINTS) then
                    reg_dout(TAG_WIDTH-1 downto 0)     <= std_logic_vector(tag_now(ep_v));
                    reg_dout(16+TAG_WIDTH-1 downto 16) <= std_logic_vector(tag_min(ep_v));
                end if;

            when "11" =>
                if (to_integer(unsigned(MI_ADDR(5 downto 2))) < PCIE_ENDPOINTS) then
                    reg_dout(STFIFO_WIDTH-1 downto 0)     <= std_logic_vector(stfifo_now(ep_v));
                    reg_dout(16+STFIFO_WIDTH-1 downto 16) <= std_logic_vector(stfifo_min(ep_v));
                end if;

            when others =>
                case (MI_ADDR(5 downto 2)) is
                    when "0000" =>
                        reg_dout <= MAGIC;
                    when "0001" =>
                        reg_dout(31 downto 16) <= std_logic_vector(to_unsigned(VERSION_MAJOR,16));
                        reg_dout(15 downto  0) <= std_logic_vector(to_unsigned(VERSION_MINOR,16));
                    when "0010" =>
                        reg_dout( 7 downto  0) <= std_logic_vector(to_unsigned(PCIE_ENDPOINTS,8));
                        reg_dout(15 downto  8) <= std_logic_vector(to_unsigned(DMA_PORTS,8));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(STREAMS,8));
                    when "0011" =>
                        reg_dout(15 downto  0) <= std_logic_vector(to_unsigned(ENTRIES,16));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(CNT_WIDTH,8));
                        reg_dout(31 downto 24) <= std_logic_vector(to_unsigned(EP_CHANNELS,8));
                    when "0100" =>
                        reg_dout( 7 downto  0) <= std_logic_vector(to_unsigned(PCIE_CHANNELS,8));
                        reg_dout(15 downto  8) <= std_logic_vector(to_unsigned(PCIE_BUSES,8));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(PCIE_MFB_REGIONS,8));
                        reg_dout(31 downto 24) <= std_logic_vector(to_unsigned(PCIE_BRAKES,8));
                    when "0101" =>
                        reg_dout( 7 downto  0) <= std_logic_vector(to_unsigned(DMA_CHANNELS,8));
                        reg_dout(15 downto  8) <= std_logic_vector(to_unsigned(DMA_BUSES,8));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(DMA_MFB_REGIONS,8));
                        reg_dout(31 downto 24) <= std_logic_vector(to_unsigned(DMA_BRAKES,8));
                    when "0110" =>
                        reg_dout(15 downto  0) <= std_logic_vector(to_unsigned(DRAIN_PERIOD,16));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(MFB_ITEM_BYTES,8));
                    when "0111" =>
                        reg_dout <= CNT_BASE;
                    when "1011" =>
                        reg_dout( 7 downto  0) <= std_logic_vector(to_unsigned(PCIE_RQ_MFB_REGIONS,8));
                        reg_dout(15 downto  8) <= std_logic_vector(to_unsigned(PCIE_RC_MFB_REGIONS,8));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(DMA_UP_MFB_REGIONS,8));
                        reg_dout(31 downto 24) <= std_logic_vector(to_unsigned(DMA_DOWN_MFB_REGIONS,8));
                    when "1100" =>
                        reg_dout(15 downto  0) <= std_logic_vector(to_unsigned(PCIE_RQ_MFB_REGION_BYTES,16));
                        reg_dout(31 downto 16) <= std_logic_vector(to_unsigned(PCIE_RC_MFB_REGION_BYTES,16));
                    when "1111" =>
                        reg_dout(15 downto  0) <= std_logic_vector(to_unsigned(DMA_UP_MFB_REGION_BYTES,16));
                        reg_dout(31 downto 16) <= std_logic_vector(to_unsigned(DMA_DOWN_MFB_REGION_BYTES,16));
                    when "1101" =>
                        reg_dout( 7 downto  0) <= std_logic_vector(to_unsigned(HIST_LEVELS,8));
                        reg_dout(15 downto  8) <= std_logic_vector(to_unsigned(PCIE_HISTS,8));
                        reg_dout(23 downto 16) <= std_logic_vector(to_unsigned(DMA_HISTS,8));
                    when "1110" =>
                        reg_dout(15 downto  0) <= std_logic_vector(to_unsigned(TAG_CAPACITY,16));
                        reg_dout(31 downto 16) <= std_logic_vector(to_unsigned(STFIFO_CAPACITY,16));
                    when "1001" =>
                        reg_dout(0) <= acc_busy;
                        reg_dout(1) <= or probe_fifo_ovf;
                        reg_dout(2) <= or probe_overrun;
                    when "1010" =>
                        reg_dout(0) <= read_live;
                    when others =>
                        null;
                end case;
        end case;
    end process;

    -- The read answer needs two cycles, one for the counter memory and one for
    -- the output multiplexer.
    process (MI_CLK)
    begin
        if (rising_edge(MI_CLK)) then
            mi_addr_reg  <= MI_ADDR;
            reg_dout_reg <= reg_dout;
            mi_rd_reg    <= MI_RD;
            mi_rd_reg2   <= mi_rd_reg;

            if (mi_addr_reg(15) = '0') then
                mi_drd_reg <= reg_dout_reg;
            elsif (mi_addr_reg(2) = '0') then
                mi_drd_reg <= acc_rd_data(32-1 downto 0);
            else
                mi_drd_reg                          <= (others => '0');
                mi_drd_reg(CNT_WIDTH-32-1 downto 0) <= acc_rd_data(CNT_WIDTH-1 downto 32);
            end if;

            if (MI_RESET = '1') then
                mi_rd_reg  <= '0';
                mi_rd_reg2 <= '0';
            end if;
        end if;
    end process;

    MI_DRD  <= mi_drd_reg;
    MI_DRDY <= mi_rd_reg2;

end architecture;
