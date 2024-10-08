-- metadata_insertor.vhd: DUT Wrapper
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

entity DUT_WRAPPER is
    generic(
        CX_USE_CLK2           : boolean := true;
        CX_USE_CLK_ARB        : boolean := false;
        OBUF_META_EQ_OUTPUT   : boolean := false;
        OBUF_INPUT_EQ_OUTPUT  : boolean := false;

        MFB_REGIONS           : natural := 4;
        MFB_REGION_SIZE       : natural := 8;
        MFB_BLOCK_SIZE        : natural := 8;
        MFB_ITEM_WIDTH        : natural := 8;
        MFB_META_WIDTH        : natural := 128;

        PKT_MTU               : natural := 1024;
        TRANS_FIFO_SIZE       : natural := 64;

        F_GAP_ADJUST_EN       : boolean := false;
        F_GAP_ADJUST_SIZE_AVG : natural := 24;
        F_GAP_ADJUST_SIZE_MIN : natural := 24;

        F_EXTEND_START_EN     : boolean := true;
        F_EXTEND_START_SIZE   : integer := -4;

        F_EXTEND_END_EN       : boolean := true;
        F_EXTEND_END_SIZE     : integer := -5;

        DEVICE                : string := "STRATIX10"
    );
    port(
        RX_CLK         : in  std_logic;
        RX_CLK2        : in  std_logic;
        RX_RESET       : in  std_logic;
        TX_CLK         : in  std_logic;
        TX_RESET       : in  std_logic;
        CX_CLK_ARB     : in  std_logic;
        CX_RESET_ARB   : in  std_logic;

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  std_logic_vector(MFB_REGIONS*(MFB_META_WIDTH+1)-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0); -- valid with EOF
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic

    );
end entity;

architecture FULL of DUT_WRAPPER is

    signal rx_meta_all_arr : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_META_WIDTH+1-1 downto 0);
    signal rx_meta_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal rx_discard_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(0 downto 0);

begin

    rx_meta_all_arr <= slv_array_deser(RX_MFB_META,MFB_REGIONS,MFB_META_WIDTH+1);
    -- Merges metadata with discard
    rx_unpack_g : for i in 0 to MFB_REGIONS-1 generate
        rx_discard_arr(i) <= rx_meta_all_arr(i)(0 downto 0);
        rx_meta_arr(i) <= rx_meta_all_arr(i)(MFB_META_WIDTH+1-1 downto 1);
    end generate;

    dut_i : entity work.CROSSBARX_STREAM
    generic map(
        CX_USE_CLK2           => CX_USE_CLK2,
        CX_USE_CLK_ARB        => CX_USE_CLK_ARB,
        OBUF_META_EQ_OUTPUT   => OBUF_META_EQ_OUTPUT,
        OBUF_INPUT_EQ_OUTPUT  => OBUF_INPUT_EQ_OUTPUT,
        MFB_REGIONS           => MFB_REGIONS,
        MFB_REGION_SIZE       => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE        => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH        => MFB_ITEM_WIDTH,
        MFB_META_WIDTH        => MFB_META_WIDTH,
        PKT_MTU               => PKT_MTU,
        TRANS_FIFO_SIZE       => TRANS_FIFO_SIZE,
        F_GAP_ADJUST_EN       => F_GAP_ADJUST_EN,
        F_GAP_ADJUST_SIZE_AVG => F_GAP_ADJUST_SIZE_AVG,
        F_GAP_ADJUST_SIZE_MIN => F_GAP_ADJUST_SIZE_MIN,
        F_EXTEND_START_EN     => F_EXTEND_START_EN,
        F_EXTEND_START_SIZE   => F_EXTEND_START_SIZE,
        F_EXTEND_END_EN       => F_EXTEND_END_EN,
        F_EXTEND_END_SIZE     => F_EXTEND_END_SIZE,
        DEVICE                => DEVICE
    )
    port map(
        RX_CLK         => RX_CLK,
        RX_CLK2        => RX_CLK2,
        RX_RESET       => RX_RESET,
        TX_CLK         => TX_CLK,
        TX_RESET       => TX_RESET,
        CX_CLK_ARB     => CX_CLK_ARB,
        CX_RESET_ARB   => CX_RESET_ARB,

        RX_MFB_DATA    => RX_MFB_DATA,
        RX_MFB_META    => slv_array_ser(rx_meta_arr,MFB_REGIONS,MFB_META_WIDTH),
        RX_MFB_DISCARD => slv_array_ser(rx_discard_arr,MFB_REGIONS,1),
        RX_MFB_SOF_POS => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS => RX_MFB_EOF_POS,
        RX_MFB_SOF     => RX_MFB_SOF,
        RX_MFB_EOF     => RX_MFB_EOF,
        RX_MFB_SRC_RDY => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY => RX_MFB_DST_RDY,

        TX_MFB_DATA    => TX_MFB_DATA,
        TX_MFB_META    => TX_MFB_META,
        TX_MFB_SOF_POS => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS => TX_MFB_EOF_POS,
        TX_MFB_SOF     => TX_MFB_SOF,
        TX_MFB_EOF     => TX_MFB_EOF,
        TX_MFB_SRC_RDY => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
