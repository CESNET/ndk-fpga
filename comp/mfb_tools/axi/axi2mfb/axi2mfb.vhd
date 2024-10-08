-- axi2mfb.vhd: AXI to MFB bridge
-- Copyright (C) 2024 BrnoLogic, Ltd.
-- Author(s): Radek Hajek <hajek@brnologic.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- -------------------------------------------------------------------------
--                             Description
-- -------------------------------------------------------------------------

-- This component implements AXI stream to MFB bridge
--
entity AXI2MFB is
    generic(
        -- =========================================================================
        -- input/output reg. config
        -- =========================================================================
        -- enables input register stage
        USE_IN_PIPE          : boolean := false;
        -- enables output register stage
        USE_OUT_PIPE         : boolean := false;

        -- =========================================================================
        -- MFB parameters
        --
        -- Frame size restrictions:
        -- regions: any positive number
        -- regison_size: power of 2
        -- block_size: power of 2
        -- item_width: 8
        -- =========================================================================
        REGIONS             : natural := 1;
        REGION_SIZE         : natural := 1;
        BLOCK_SIZE          : natural := 32;
        ITEM_WIDTH          : natural := 8;

        -- =========================================================================
        -- AXI STREAM parameters
        --
        -- restrictions:
        -- size of AXI stream data needs to match MFB data size
        -- =========================================================================
        -- AXI stream data width
        AXI_DATA_WIDTH          : natural := 256;

        -- =============================
        -- Others (PIPE config)
        -- =============================
        -- "SHREG" or "REG"
        PIPE_TYPE      : string  := "SHREG";
        DEVICE         : string  := "7SERIES"
    );
    port(
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================

        CLK              : in  std_logic;
        RST              : in  std_logic;

        -- =========================================================================
        -- AXI INTERFACE
        -- =========================================================================

        RX_AXI_TDATA     : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- =========================================================================
        -- TX MFB INTERFACE
        -- =========================================================================

        TX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic
    );
end AXI2MFB;

architecture behavioral of AXI2MFB is

    constant MFB_DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant MFB_SOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE));
    constant MFB_EOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant TKEEP_SPLIT_WIDTH : natural := (AXI_DATA_WIDTH/8) / REGIONS;
    constant REG_EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

    -- function
    function is_powerof2 (n : natural) return boolean is
    begin
        return (2 ** log2(n)) = n;
    end is_powerof2;

    --signals
    type t_tkeep_split_array is array (0 to REGIONS) of std_logic_vector(TKEEP_SPLIT_WIDTH - 1 downto 0);
    signal tkeep_split  : t_tkeep_split_array;
    signal frame_start_q : std_logic;

    -- s0 => s1
    signal axi_tlast_s1 : std_logic;
    signal axi_tdata_s1 : std_logic_vector(RX_AXI_TDATA'RANGE);
    signal axi_tkeep_s1 : std_logic_vector(RX_AXI_TKEEP'RANGE);
    signal src_rdy_s1   : std_logic;
    signal dst_rdy_s1   : std_logic;

    -- s1 => s2
    signal mfb_eof_pos_s1 : std_logic_vector(TX_MFB_EOF_POS'RANGE);
    signal mfb_sof_s1     : std_logic_vector(TX_MFB_SOF'RANGE);
    signal mfb_eof_s1     : std_logic_vector(TX_MFB_EOF'RANGE);


begin
    -----------------------------------------------------------------------------
    -- valid parameters checks
    -----------------------------------------------------------------------------
    -- 1. MFB ITEM needs to be byte - EOF is item aligned & AXI stream use TKEEP by byte
    assert (ITEM_WIDTH = 8)   report "AXI2MFB: ITEM_WIDTH != 8"   severity FAILURE;

    -- 2. MFB REGIONS_SIZE is expected to be 2^n
    assert (is_powerof2(REGION_SIZE))   report "AXI2MFB: REGION_SIZE is not power of 2"   severity FAILURE;

    -- 3. MFB BLOCK_SIZE is expected to be 2^n
    assert (is_powerof2(BLOCK_SIZE))   report "AXI2MFB: BLOCK_SIZE is not power of 2"   severity FAILURE;

    -- 4. MFB and AXI stream data width needs to be equal
    assert (MFB_DATA_WIDTH = AXI_DATA_WIDTH)   report "AXI2MFB: MFB and AXIs data width is not matching"   severity FAILURE;

    -----------------------------------------------------------------------------
    -- input stage (s0 => s1)
    -----------------------------------------------------------------------------
    input_pipe_i :  entity  work.AXI_PIPE
        generic map(
            AXI_DATA_WIDTH  => AXI_DATA_WIDTH,
            FAKE_PIPE       => not USE_IN_PIPE,
            USE_DST_RDY     => true,
            PIPE_TYPE       => PIPE_TYPE,
            DEVICE          => DEVICE
        )
        port map(
            CLK           => CLK,
            RESET         => RST,

            RX_AXI_TDATA   => RX_AXI_TDATA,
            RX_AXI_TKEEP   => RX_AXI_TKEEP,
            RX_AXI_TLAST   => RX_AXI_TLAST,
            RX_AXI_TVALID  => RX_AXI_TVALID,
            RX_AXI_TREADY  => RX_AXI_TREADY,

            TX_AXI_TDATA   => axi_tdata_s1,
            TX_AXI_TKEEP   => axi_tkeep_s1,
            TX_AXI_TLAST   => axi_tlast_s1,
            TX_AXI_TVALID  => src_rdy_s1,
            TX_AXI_TREADY  => dst_rdy_s1
        );

    -----------------------------------------------------------------------------
    -- stage s1
    -----------------------------------------------------------------------------

    -----------------------------------------------------------------------------
    -- start frame detection register
    -----------------------------------------------------------------------------
    -- seq. logic
    frame_start_seq_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                frame_start_q <= '1';
            elsif (src_rdy_s1 = '1' AND dst_rdy_s1 = '1') then
                frame_start_q <= axi_tlast_s1;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    -- output comb. logic
    -----------------------------------------------------------------------------
    -- TX_MFB_SOF is asserted after last packet has ended (start_frame flag)
    mfb_sof_s1 <= (0 => frame_start_q, others => '0');

    -- default assignemnt for virtual region
    tkeep_split(REGIONS) <= (others => '0');

    -- TX_MFB_EOF and TX_MFB_EOF_POS logic
    reg_split_g: for r in 0 to REGIONS-1 generate
        -- split TKEEP to vector per region
        tkeep_split(r) <= axi_tkeep_s1(TKEEP_SPLIT_WIDTH*(r+1)-1 downto TKEEP_SPLIT_WIDTH * r);

        -- EOF bit when TKEEPs ends in region
        mfb_eof_s1(r) <= axi_tlast_s1 and (not tkeep_split(r+1)(0)) and tkeep_split(r)(0);

        -- TX_MFB_EOF_POS is counted based on TKEEP
        mfb_eof_pos_p : process (all)
            variable ms_one_index : std_logic_vector(REG_EOF_POS_WIDTH-1 downto 0);
        begin
            ms_one_index := (others => '0');
            one_l : for index in TKEEP_SPLIT_WIDTH - 1 downto 1 loop
                if (tkeep_split(r)(index) = '1') then
                    ms_one_index := std_logic_vector(to_unsigned(index, REG_EOF_POS_WIDTH));
                    exit one_l;
                end if;
            end loop;

            mfb_eof_pos_s1(REG_EOF_POS_WIDTH*(r+1) - 1 downto REG_EOF_POS_WIDTH*r) <= ms_one_index;
        end process;
    end generate;

    -----------------------------------------------------------------------------
    -- output stage (s1 => s2)
    -----------------------------------------------------------------------------
    output_pipe_i :  entity  work.MFB_PIPE
        generic map(
            REGIONS       => REGIONS,
            REGION_SIZE   => REGION_SIZE,
            BLOCK_SIZE    => BLOCK_SIZE,
            ITEM_WIDTH    => ITEM_WIDTH,
            META_WIDTH    => 0,

            FAKE_PIPE     => not USE_OUT_PIPE,
            USE_DST_RDY   => true,
            PIPE_TYPE     => PIPE_TYPE,
            DEVICE        => DEVICE
        )
        port map(
            CLK           => CLK,
            RESET         => RST,

            RX_DATA       => axi_tdata_s1,
            RX_META       => (others => '0'),
            RX_SOF_POS    => (others => '0'), -- SOF POS is fixed to 0
            RX_EOF_POS    => mfb_eof_pos_s1,
            RX_SOF        => mfb_sof_s1,
            RX_EOF        => mfb_eof_s1,
            RX_SRC_RDY    => src_rdy_s1,
            RX_DST_RDY    => dst_rdy_s1,

            TX_DATA       => TX_MFB_DATA,
            TX_META       => open,
            TX_SOF_POS    => TX_MFB_SOF_POS,
            TX_EOF_POS    => TX_MFB_EOF_POS,
            TX_SOF        => TX_MFB_SOF,
            TX_EOF        => TX_MFB_EOF,
            TX_SRC_RDY    => TX_MFB_SRC_RDY,
            TX_DST_RDY    => TX_MFB_DST_RDY
        );

    -----------------------------------------------------------------------------
    -- run-time checks for unsupported protocol
    -----------------------------------------------------------------------------
    -- pragma synthesis_off
    -- TKEEP invalid format
    axi_check_p: process(CLK)
        variable ls_zero_index : natural;
        variable ms_one_index : natural;
        variable TKEEP_tmp : std_logic_vector(RX_AXI_TKEEP'LEFT + 1 downto 0);
    begin
        if (rising_edge(CLK)) then
            if (RX_AXI_TVALID = '1') then
                -- AXI stream empty data transaction
                assert (OR(RX_AXI_TKEEP) /= '0')   report "AXI2MFB: RX_AXI_TKEEP == 0 while RX_AXI_TVALID == 1"   severity FAILURE;

                ls_zero_index := 0;
                ms_one_index := 0;

                -- count index of least significant zero -1
                TKEEP_tmp := '0' & RX_AXI_TKEEP;
                zero_l : for i in 0 to RX_AXI_TKEEP'LEFT loop
                if (TKEEP_tmp(i+1) = '0') then
                    ls_zero_index := i;
                    exit zero_l;
                end if;
                end loop;

                -- count index of most significant one
                one_l : for i in RX_AXI_TKEEP'LEFT downto 1 loop
                if (TKEEP_tmp(i) = '1') then
                    ms_one_index := i;
                    exit one_l;
                end if;
                end loop;

                -- for b0~01~1 pattern the indexes has to be the same
                assert (ms_one_index = ls_zero_index)   report "AXI2MFB: TKEEP unsupported format while RX_AXI_TVALID == 1"   severity FAILURE;
            end if;
        end if;
    end process;
    -- pragma synthesis_on

end architecture;
