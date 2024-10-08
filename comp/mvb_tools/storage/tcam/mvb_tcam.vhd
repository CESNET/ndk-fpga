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
entity MVB_TCAM is
    Generic (
        -- Number of MVB items in word
        MVB_ITEMS          : natural := 4;

        -- TCAM item width in bits
        DATA_WIDTH         : integer := 36;

        -- TCAM2 storage capacity
        --     for XILINX (7SERIES, ULTRASCALE) optimal is a multiple of 1*(2^RS)
        --     for INTEL (ARRIA10, STRATIX10) optimal is a multiple of 16*(2^RS), if memory fragmentation is not enabled, otherwise a multiple of 32*(2^RS)
        ITEMS              : integer := 16;

        -- TCAM2 resources saving
        --     higher level of resources saving means fewer FPGA resources involved and faster item write but slower matching
        --     item write speed is 2^(6-RS) cycles for XILINX and 2^(5-RS)+1 cycles for INTEL FPGAs
        --     maximum level of resources saving is 6 for XILINX and 5 for INTEL FPGAs
        --     matching speed corresponds to 2^RS cycles
        RESOURCES_SAVING   : integer := 0;

        -- set as true if item write should have higher priority when requested in the same cycle as match
        -- TCAM2 read has lower priority than write
        WRITE_BEFORE_MATCH : boolean := true;

        -- set as true to enable read from TCAM2 by adding extra WRITE_DATA and WRITE_MASK storage
        READ_FROM_TCAM     : boolean := true;

        -- set as true to enable output registers for READ INTERFACE
        --     READ_FROM_TCAM must be set as true
        --     otherwise (false) READ_DATA and READ_MASK are ready in the next clock cycle after request
        OUTPUT_READ_REGS   : boolean := true;

        -- If true, writing a masked bit (mask=0) has two different meanings:
        --    If the bit is 0, then it is don't care
        --    But if the bit is 1, then it is UNMATCHABLE!
        USE_UNMATCHABLE    : boolean := false;

        -- set as true to use the entire Intel MLAB data width (20 instead of 16), but TCAM rows are addressed discontinuously (rows 21-32 are unused)
        USE_FRAGMENTED_MEM : boolean := false;

        -- FPGA device
        --    available are "7SERIES", "ULTRASCALE", "ARRIA10", "STRATIX10", "AGILEX"
        DEVICE             : string := "ULTRASCALE"
    );
    Port (
        -- CLOCK AND RESET
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        -- READ INTERFACE (READ_FROM_TCAM must be set as true)
        READ_ADDR          : in  std_logic_vector(max(1,log2(ITEMS))-1 downto 0);
        READ_EN            : in  std_logic;
        READ_RDY           : out std_logic;
        READ_DATA          : out std_logic_vector(DATA_WIDTH-1 downto 0);
        READ_MASK          : out std_logic_vector(DATA_WIDTH-1 downto 0);
        READ_DATA_VLD      : out std_logic;

        -- WRITE INTERFACE
        WRITE_DATA         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        WRITE_MASK         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        WRITE_ADDR         : in  std_logic_vector(max(1,log2(ITEMS))-1 downto 0);
        WRITE_EN           : in  std_logic;
        WRITE_RDY          : out std_logic;

        -- MATCH INTERFACE
        MATCH_DATA         : in  std_logic_vector(MVB_ITEMS*DATA_WIDTH-1 downto 0);
        MATCH_VLD          : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        MATCH_SRC_RDY      : in  std_logic;
        MATCH_DST_RDY      : out std_logic;

        -- MATCH_OUT INTERFACE (Output match latency is 3 cycles)
        MATCH_OUT_HIT      : out std_logic_vector(MVB_ITEMS-1 downto 0);
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
