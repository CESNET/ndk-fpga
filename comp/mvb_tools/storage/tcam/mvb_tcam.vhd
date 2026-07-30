-- mvb_tcam.vhd: MVB TCAM component
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author: Tomas Fukac <fukac@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =====================================================================
--                            Entity declaration
-- =====================================================================
-- MVB wrapper around ``TCAM2``: instantiates one full, independent
-- TCAM2 core **per MVB item** (MVB_ITEMS instances), each holding its own
-- complete, identical copy of the table content. This is what makes it
-- possible to match MVB_ITEMS independent keys against the table in the
-- same clock cycle, but it also means **FPGA resource usage scales linearly
-- with MVB_ITEMS** - a wide MVB bus with a large or wide TCAM table can
-- become very expensive; consider whether the use case really needs a full
-- MVB_ITEMS-way replicated TCAM.
--
-- .. WARNING::
--    Only TCAM2 instance 0 is built with READ_FROM_TCAM enabled; the
--    READ_* interface always reads through that single instance
--    (WRITE_* is broadcast identically to every instance, so all copies
--    stay in sync regardless).
--
-- .. WARNING::
--    MATCH_OUT_ADDR is **not** a binary address like READ_ADDR/WRITE_ADDR.
--    For each MVB item it is an ITEMS-bit one-hot/bitmap vector, one bit per
--    stored TCAM row, since a TCAM can match multiple (or zero) rows at
--    once; MATCH_OUT_HIT for that item is simply the OR of its bits.
--
-- .. NOTE::
--    A single WRITE_EN request and a match never overlap - the hardware
--    always finishes one before starting the other - so a match always sees
--    that one row's complete old or complete new content, never a mix. You
--    don't need to add anything yourself for that.
--
--    This only covers a single row, though. Updating several rows is just a
--    sequence of separate writes, and matches can happen in between them -
--    seeing some rows already updated and others not yet. If your
--    application needs the whole table to look consistent during a
--    multi-row update, that's up to you to arrange (e.g. by holding off
--    match traffic for the duration).
--
entity MVB_TCAM is
    generic (
        -- Number of MVB items transferred in one word. Directly multiplies
        -- FPGA resource usage, see the WARNING above.
        MVB_ITEMS          : natural := 4;

        -- Width of one TCAM item (and of WRITE_DATA/WRITE_MASK/MATCH_DATA/READ_DATA/READ_MASK per item), in bits.
        DATA_WIDTH         : integer := 36;

        -- Number of rows (entries) in the TCAM table.
        -- For optimal resource usage should be a multiple of
        -- 2*L*(2^RESOURCES_SAVING) on Xilinx (where L is the number of
        -- LUTRAMs in one SLICEM), or of 16*(2^RESOURCES_SAVING) on Intel
        -- (32*(2^RESOURCES_SAVING) when USE_FRAGMENTED_MEM is set).
        ITEMS              : integer := 16;

        -- Trade-off between FPGA resources and matching speed. Possible
        -- values are 0-4 on all devices. Higher values save resources
        -- and speed up writes, but cost both matching throughput and latency:
        --
        -- * Throughput (how often a new match can be started): one match
        --   every CLK cycle at RESOURCES_SAVING = 0 (MATCH_DST_RDY stays
        --   asserted, one result per clock back-to-back); only one match
        --   every 2^RESOURCES_SAVING cycles for higher values (MATCH_DST_RDY
        --   drops after each accepted match until that many cycles pass).
        -- * RX-to-TX latency of one result (MATCH_OUT_* after the matching
        --   MATCH_DATA is accepted): a fixed 3 + (2^RESOURCES_SAVING - 1)
        --   CLK cycles - i.e. 3 cycles at RESOURCES_SAVING = 0, growing by
        --   2^RESOURCES_SAVING - 1 for higher values.
        --
        -- Write speed (time until WRITE_RDY returns after a write) is
        -- 2^(5-RESOURCES_SAVING)+1 CLK cycles, the same on all devices.
        RESOURCES_SAVING   : integer := 0;

        -- When true, a WRITE_EN request presented in the same cycle as a
        -- MATCH_EN request is served first (match is delayed); when false,
        -- match has priority over write. A read request is only ever
        -- deprioritized against a concurrent write (READ_RDY is simply
        -- "not WRITE_EN") - it is not affected by match activity at all,
        -- regardless of this generic's value.
        WRITE_BEFORE_MATCH : boolean := true;

        -- Enables the READ_* interface (through TCAM2 instance 0 only, see
        -- the WARNING above) by adding extra internal storage that mirrors
        -- WRITE_DATA/WRITE_MASK. Costs extra resources; leave false if the
        -- table content never needs to be read back.
        READ_FROM_TCAM     : boolean := true;

        -- Adds an output register stage on the READ_DATA/READ_MASK/READ_DATA_VLD
        -- path for better timing, at the cost of one extra CLK cycle of read
        -- latency. Has no effect unless READ_FROM_TCAM = true (that extra
        -- storage is what this register stage sits on).
        OUTPUT_READ_REGS   : boolean := true;

        -- Changes the meaning of a masked-out bit (WRITE_MASK bit = '0'):
        --
        -- * false - a masked bit is always don't-care (matches both '0' and '1').
        -- * true  - a masked bit is don't-care only if the corresponding
        --   WRITE_DATA bit is '0'; if that WRITE_DATA bit is '1', the whole
        --   row becomes permanently UNMATCHABLE.
        USE_UNMATCHABLE    : boolean := false;

        -- Trade higher memory-primitive utilization for a discontinuous row
        -- address space: uses the full Intel MLAB width (20 instead of 16
        -- bits, rows 21-32 unused per block) or the full Xilinx SLICEM width
        -- (14 instead of 8 on ULTRASCALE/VERSAL, 6 instead of 4 on 7SERIES,
        -- rows 15-16/7-8 unused per block).
        USE_FRAGMENTED_MEM : boolean := false;

        -- Target FPGA device.
        -- "7SERIES", "ULTRASCALE", "VERSAL", "ARRIA10", "STRATIX10", "AGILEX"
        DEVICE             : string  := "ULTRASCALE";

        -- Manufacturer of the FPGA device, derived from DEVICE by default;
        -- only override together with DEVICE.
        IS_XILINX          : boolean := (DEVICE = "7SERIES" or DEVICE = "ULTRASCALE" or DEVICE = "VERSAL");
        IS_INTEL           : boolean := (DEVICE = "ARRIA10" or DEVICE = "STRATIX10" or DEVICE = "AGILEX");

        -- The following generics are derived automatically from the
        -- generics above and are not meant to be overridden directly.
        INTEL_DATA_WIDTH   : integer := tsel(USE_FRAGMENTED_MEM, 20, 16);
        XILINX_DATA_WIDTH  : integer := tsel(DEVICE = "ULTRASCALE" or DEVICE = "VERSAL", tsel(USE_FRAGMENTED_MEM, 14, 8), tsel(USE_FRAGMENTED_MEM, 6, 4));
        MEMORY_DATA_WIDTH  : integer := tsel(IS_XILINX, XILINX_DATA_WIDTH, INTEL_DATA_WIDTH);
        ALIGNED_DATA_WIDTH : integer := 2**log2(MEMORY_DATA_WIDTH);
        ITEMS_ALIGNED      : natural := tsel(USE_FRAGMENTED_MEM, div_roundup(ITEMS,MEMORY_DATA_WIDTH)*ALIGNED_DATA_WIDTH, ITEMS);
        ADDR_WIDTH         : natural := max(1, log2(ITEMS_ALIGNED))
    );
    port (
        -- CLOCK AND RESET
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        -- =====================================================================
        -- READ INTERFACE (functional only when READ_FROM_TCAM = true; reads
        -- through TCAM2 instance 0, see the WARNING above)
        -- =====================================================================

        -- Row address to read; any value in 0 to ITEMS_ALIGNED-1.
        READ_ADDR          : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        READ_EN            : in  std_logic;
        -- Equivalent to "not WRITE_EN" (combinational); deasserted only
        -- while WRITE_EN is currently asserted, independent of any match
        -- activity or of WRITE_BEFORE_MATCH.
        READ_RDY           : out std_logic;
        READ_DATA          : out std_logic_vector(DATA_WIDTH-1 downto 0);
        READ_MASK          : out std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Valid one CLK cycle after a request accepted with READ_RDY = '1'
        -- (plus one more CLK cycle when OUTPUT_READ_REGS = true).
        READ_DATA_VLD      : out std_logic;

        -- =====================================================================
        -- WRITE INTERFACE (broadcast identically to every one of the
        -- MVB_ITEMS replicated TCAM2 instances)
        -- =====================================================================

        WRITE_DATA         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- '0' bit = don't-care (or UNMATCHABLE, see USE_UNMATCHABLE); '1' bit = must match WRITE_DATA.
        WRITE_MASK         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Row address to write; any value in 0 to ITEMS_ALIGNED-1.
        WRITE_ADDR         : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        WRITE_EN           : in  std_logic;
        -- Asserted only when every one of the MVB_ITEMS replicated instances is ready to accept a write.
        WRITE_RDY          : out std_logic;

        -- =====================================================================
        -- MATCH INTERFACE
        -- =====================================================================

        MATCH_DATA         : in  std_logic_vector(MVB_ITEMS*DATA_WIDTH-1 downto 0);
        MATCH_VLD          : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        MATCH_SRC_RDY      : in  std_logic;
        -- Asserted only when every one of the MVB_ITEMS replicated instances
        -- is ready to match (i.e. the whole MVB word is matched together, or not at all).
        MATCH_DST_RDY      : out std_logic;

        -- =====================================================================
        -- MATCH_OUT INTERFACE - result of a MATCH interface request, 3 CLK
        -- cycles later (plus the RESOURCES_SAVING match latency, see above)
        -- =====================================================================

        -- Per MVB item: '1' if the table held at least one matching row for that item's MATCH_DATA.
        MATCH_OUT_HIT      : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- Per MVB item: one-hot/bitmap of matching rows (ITEMS bits), see the WARNING above - not a binary address.
        MATCH_OUT_ADDR     : out std_logic_vector(MVB_ITEMS*ITEMS-1 downto 0);
        MATCH_OUT_VLD      : out std_logic_vector(MVB_ITEMS-1 downto 0);
        MATCH_OUT_SRC_RDY  : out std_logic
    );
end entity;

-- =====================================================================
--                       Architecture declaration
-- =====================================================================
architecture FULL of MVB_TCAM is

    signal tcam_write_rdy     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal tcam_match_en      : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal tcam_match_rdy     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal tcam_match_out_vld : std_logic_vector(MVB_ITEMS-1 downto 0);

    signal tcam_read_rdy      : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal tcam_read_data     : std_logic_vector(MVB_ITEMS*DATA_WIDTH-1 downto 0);
    signal tcam_read_mask     : std_logic_vector(MVB_ITEMS*DATA_WIDTH-1 downto 0);
    signal tcam_read_data_vld : std_logic_vector(MVB_ITEMS-1 downto 0);

begin

    tcam_g: for i in 0 to MVB_ITEMS-1 generate

        tcam_i: entity work.TCAM2
        generic map (
            DATA_WIDTH         => DATA_WIDTH,
            ITEMS              => ITEMS,
            RESOURCES_SAVING   => RESOURCES_SAVING,
            WRITE_BEFORE_MATCH => WRITE_BEFORE_MATCH,
            READ_FROM_TCAM     => (READ_FROM_TCAM and (i = 0)),
            OUTPUT_READ_REGS   => OUTPUT_READ_REGS,
            USE_UNMATCHABLE    => USE_UNMATCHABLE,
            USE_FRAGMENTED_MEM => USE_FRAGMENTED_MEM,
            DEVICE             => DEVICE
        ) port map (
            CLK            => CLK,
            RST            => RESET,

            READ_ADDR      => READ_ADDR,
            READ_EN        => READ_EN,
            READ_RDY       => tcam_read_rdy(i),
            READ_DATA      => tcam_read_data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            READ_MASK      => tcam_read_mask((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            READ_DATA_VLD  => tcam_read_data_vld(i),

            WRITE_DATA     => WRITE_DATA,
            WRITE_MASK     => WRITE_MASK,
            WRITE_ADDR     => WRITE_ADDR,
            WRITE_EN       => WRITE_EN,
            WRITE_RDY      => tcam_write_rdy(i),

            MATCH_DATA     => MATCH_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            MATCH_EN       => tcam_match_en(i),
            MATCH_RDY      => tcam_match_rdy(i),

            MATCH_OUT_HIT  => MATCH_OUT_HIT(i),
            MATCH_OUT_ADDR => MATCH_OUT_ADDR((i+1)*ITEMS-1 downto i*ITEMS),
            MATCH_OUT_VLD  => tcam_match_out_vld(i)
        );

    end generate;

    -- write interface
    WRITE_RDY <= and tcam_write_rdy;

    -- read interface
    READ_RDY      <= tcam_read_rdy(0);
    READ_DATA     <= tcam_read_data(DATA_WIDTH-1 downto 0);
    READ_MASK     <= tcam_read_mask(DATA_WIDTH-1 downto 0);
    READ_DATA_VLD <= tcam_read_data_vld(0);

    -- match interface
    MATCH_DST_RDY <= and tcam_match_rdy;

    tcam_match_en_p : process (MATCH_SRC_RDY, MATCH_VLD, tcam_match_rdy)
    begin
        for i in 0 to MVB_ITEMS-1 loop
            tcam_match_en(i) <= MATCH_SRC_RDY and MATCH_VLD(i) and (and tcam_match_rdy);
        end loop;
    end process;

    -- match out interface
    MATCH_OUT_VLD     <= tcam_match_out_vld;
    MATCH_OUT_SRC_RDY <= or tcam_match_out_vld;

end architecture;
