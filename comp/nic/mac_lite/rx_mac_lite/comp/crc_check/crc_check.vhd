-- crc_check.vhd: CRC check
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture FULL of RX_MAC_LITE_CRC_CHECK is

    constant REGION_WIDTH : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant EOF_POS_SIZE : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant CRC_REG_CONF : natural := tsel(INBANDFCS,254,255);

    signal s_ext_crc32         : std_logic_vector(REGIONS*32-1 downto 0);
    signal s_ext_crc32_vld     : std_logic_vector(REGIONS-1 downto 0);

    signal s_shreg_din         : std_logic_vector(REGIONS*33-1 downto 0);
    signal s_shreg_dout        : std_logic_vector(REGIONS*33-1 downto 0);

    signal s_ext_crc32_dly_arr : slv_array_t(REGIONS-1 downto 0)(32-1 downto 0);
    signal s_ext_crc32_dly_vld : std_logic_vector(REGIONS-1 downto 0);

    signal cut_data            : std_logic_vector(REGIONS*REGION_WIDTH-1 downto 0);
    signal cut_sof_pos         : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal cut_eof_pos         : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
    signal cut_sof             : std_logic_vector(REGIONS-1 downto 0);
    signal cut_eof             : std_logic_vector(REGIONS-1 downto 0);
    signal cut_src_rdy         : std_logic;

    signal s_calc_crc_n        : std_logic_vector(REGIONS*32-1 downto 0);
    signal s_calc_crc_arr      : slv_array_t(REGIONS-1 downto 0)(32-1 downto 0);
    signal s_calc_crc_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal s_calc_crc_src_rdy  : std_logic;

    signal s_calc_crc_arr_vld  : std_logic_vector(REGIONS-1 downto 0);
    signal s_calc_crc_lva_reg  : std_logic_vector(32-1 downto 0);
    signal s_calc_crc_lva      : slv_array_t(REGIONS-1 downto 0)(32-1 downto 0);

    signal s_crc_error         : std_logic_vector(REGIONS-1 downto 0);
    signal s_crc_error_vld     : std_logic_vector(REGIONS-1 downto 0);

begin

    assert (ITEM_WIDTH = 8)
        report "RX_MAC_LITE_CRC_CHECK: ITEM_WIDTH must be 8, other values are not supported!!!"
        severity failure;

    -- extraction of CRC32 from Ethernet frames (latency = 2 cycles)
    get_crc32_i : entity work.RX_MAC_LITE_GET_CRC32
    generic map(
        REGIONS     => REGIONS,
        REGION_SIZE => REGION_SIZE,
        BLOCK_SIZE  => BLOCK_SIZE,
        ITEM_WIDTH  => ITEM_WIDTH,
        INBANDFCS   => INBANDFCS
    )
    port map(
        -- CLOCK AND RESET
        CLK          => CLK,
        RESET        => RESET,
        -- INPUT DATA INTERFACE
        RX_DATA      => RX_DATA,
        RX_EOF_POS   => RX_EOF_POS,
        RX_EOF       => RX_EOF,
        RX_SRC_RDY   => RX_SRC_RDY,
        -- OUTPUT CRC32 INTERFACE
        CRC32        => s_ext_crc32,
        CRC32_VLD    => s_ext_crc32_vld
    );

    -- pack SHREG input data
    s_shreg_din <= s_ext_crc32 & s_ext_crc32_vld;

    sh_reg_meta_i : entity work.SH_REG_BASE_STATIC
    generic map(
        DATA_WIDTH => REGIONS*33,
        NUM_BITS   => 6,
        DEVICE     => DEVICE
    )
    port map(
        CLK  => CLK,
        CE   => '1',
        DIN  => s_shreg_din,
        DOUT => s_shreg_dout
    );

    shreg_unpack_g : for r in 0 to REGIONS-1 generate
        -- unpack SHREG output data
        s_ext_crc32_dly_arr(r) <= s_shreg_dout((r+1)*32+REGIONS-1 downto r*32+REGIONS);
        s_ext_crc32_dly_vld(r) <= s_shreg_dout(r);
    end generate;

    crc_cutter_g : if INBANDFCS generate
        -- CRC CUTTER (MFB_CRC32_ETHERNET expected frame without CRC)
        crc_cutter_i : entity work.RX_MAC_LITE_CRC_CUTTER
        generic map(
            REGIONS        => REGIONS,
            REGION_SIZE    => REGION_SIZE,
            BLOCK_SIZE     => BLOCK_SIZE,
            ITEM_WIDTH     => ITEM_WIDTH,
            OUTPUT_REG     => False --> latency = 1 cycle
        )
        port map(
            CLK            => CLK,
            RESET          => RESET,

            RX_DATA        => RX_DATA,
            RX_SOF_POS     => RX_SOF_POS,
            RX_EOF_POS     => RX_EOF_POS,
            RX_SOF         => RX_SOF,
            RX_EOF         => RX_EOF,
            RX_ADAPTER_ERR => (others => '0'),
            RX_SRC_RDY     => RX_SRC_RDY,

            TX_DATA        => cut_data,
            TX_SOF_POS     => cut_sof_pos,
            TX_EOF_POS     => cut_eof_pos,
            TX_SOF         => cut_sof,
            TX_EOF         => cut_eof,
            TX_SRC_RDY     => cut_src_rdy,
            TX_ADAPTER_ERR => open,
            TX_CRC_CUT_ERR => open
        );
    end generate;

    no_crc_cutter_g : if not INBANDFCS generate
        cut_data    <= RX_DATA;
        cut_sof_pos <= RX_SOF_POS;
        cut_eof_pos <= RX_EOF_POS;
        cut_sof     <= RX_SOF;
        cut_eof     <= RX_EOF;
        cut_src_rdy <= RX_SRC_RDY;
    end generate;

    -- calculation of CRCs from Ethernet frames
    mfb_crc32_ethernet_i : entity work.MFB_CRC32_ETHERNET
    generic map(
        REGIONS        => REGIONS,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE,
        ITEM_WIDTH     => ITEM_WIDTH,
        USE_DST_RDY    => False,
        IMPLEMENTATION => "PARALLEL", -- best value, don't edit!
        CRC_END_IMPL   => "TREE", -- best value, don't edit!
        REG_BITMAP     => std_logic_vector(to_unsigned(CRC_REG_CONF,32)) -- latency = 8 or 7 cycles
    )
    port map(
        -- CLOCK AND RESET
        CLK           => CLK,
        RESET         => RESET,
        -- INPUT MFB DATA INTERFACE
        RX_DATA       => cut_data,
        RX_SOF_POS    => cut_sof_pos,
        RX_EOF_POS    => cut_eof_pos,
        RX_SOF        => cut_sof,
        RX_EOF        => cut_eof,
        RX_SRC_RDY    => cut_src_rdy,
        RX_DST_RDY    => open,
        -- OUTPUT CRC32 INTERFACE
        CRC32_DATA    => s_calc_crc_n,
        CRC32_VLD     => s_calc_crc_vld,
        CRC32_SRC_RDY => s_calc_crc_src_rdy,
        CRC32_DST_RDY => '1'
    );

    -- unpack calculated CRCs to array
    calc_crc_arr_g : for r in 0 to REGIONS-1 generate
        s_calc_crc_arr(r) <= not s_calc_crc_n((r+1)*32-1 downto r*32);
        s_calc_crc_arr_vld(r) <= s_calc_crc_src_rdy and s_calc_crc_vld(r);
    end generate;

    -- last valid array of computed CRC
    s_calc_crc_lva(0) <= s_calc_crc_arr(0) when (s_calc_crc_arr_vld(0) = '1') else s_calc_crc_lva_reg;
    calc_crc_lva_g : for r in 1 to REGIONS-1 generate
        s_calc_crc_lva(r) <= s_calc_crc_arr(r) when (s_calc_crc_arr_vld(r) = '1') else s_calc_crc_lva(r-1);
    end generate;

    -- last valid register of computed CRC
    calc_crc_lva_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_calc_crc_src_rdy = '1') then
                s_calc_crc_lva_reg <= s_calc_crc_lva(regions-1);
            end if;
        end if;
    end process;

    crc_err_g : for r in 0 to REGIONS-1 generate
        -- compare CRCs
        s_crc_error(r) <= '0' when (s_calc_crc_lva(r) = s_ext_crc32_dly_arr(r)) else '1';
        -- valid flag of CRCs error
        s_crc_error_vld(r) <= s_ext_crc32_dly_vld(r);
    end generate;

    -- output registers
    crc_err_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            CRC_ERR     <= s_crc_error;
            CRC_ERR_VLD <= s_crc_error_vld;
        end if;
    end process;

    crc_err_src_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                CRC_ERR_SRC_RDY <= '0';
            else
                CRC_ERR_SRC_RDY <= or s_crc_error_vld;
            end if;
        end if;
    end process;

end architecture;
