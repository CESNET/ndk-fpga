-- mfb_pd_asfifo_simple.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

entity MFB_PD_ASFIFO_SIMPLE is
    generic(
        -- ==================
        -- MFB parameters
        -- ==================
        MFB_REGIONS     : natural := 4;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;
        MFB_META_WIDTH  : natural := 2;
        -- ==================
        -- FIFO PARAMETERS
        -- ==================
        -- FIFO depth in number of data words, must be power of two!
        FIFO_ITEMS      : natural := 512;
        -- Sets the maximum number of remaining free data words in the FIFO
        -- that triggers the RX_AFULL signal.
        AFULL_OFFSET    : natural := FIFO_ITEMS/2;
        -- Defines target FPGA device.
        DEVICE          : string  := "AGILEX"
    );
    port(
        -- ==================
        -- RX MFB interface
        --
        -- Runs on RX_CLK
        -- ==================

        RX_CLK        : in  std_logic;
        RX_RESET      : in  std_logic;

        RX_DATA       : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_META       : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
        RX_SOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_EOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_SOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_EOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY    : in  std_logic;
        RX_DST_RDY    : out std_logic;
        -- Discard flag valid with each EOF
        RX_DISCARD    : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Almost full flag
        RX_AFULL      : out std_logic;
        -- FIFO status
        RX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0);

        -- ==================
        -- TX MFB interface
        --
        -- Runs on TX_CLK
        -- ==================

        TX_CLK        : in  std_logic;
        TX_RESET      : in  std_logic;

        TX_DATA       : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_META       : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_SOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_EOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_SOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_EOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY    : out std_logic;
        TX_DST_RDY    : in  std_logic
    );
end entity;

architecture FULL of MFB_PD_ASFIFO_SIMPLE is

    signal tx_pfifo_data     : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal tx_pfifo_meta     : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal tx_pfifo_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_pfifo_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_pfifo_sof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_pfifo_eof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal tx_pfifo_src_rdy  : std_logic;
    signal tx_pfifo_dst_rdy  : std_logic;

    signal rx_dfifo_data     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_dfifo_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_dfifo_src_rdy  : std_logic;
    signal rx_dfifo_dst_rdy  : std_logic;

    signal tx_dfifo_data     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_dfifo_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_dfifo_src_rdy  : std_logic;
    signal tx_dfifo_dst_rdy  : std_logic;

    signal dfifo_ovf_err_reg : std_logic;

    signal tx_mins_data      : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal tx_mins_meta      : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal tx_mins_discard   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_mins_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_mins_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_mins_sof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_mins_eof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal tx_mins_src_rdy   : std_logic;
    signal tx_mins_dst_rdy   : std_logic;

    signal tx_dst_rdy_fix    : std_logic;

    signal dbg_rx_cnt  : unsigned(32-1 downto 0);
    signal dbg_mid_cnt : unsigned(32-1 downto 0);

begin

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_SRC_RDY = '1' and RX_DST_RDY = '1') then
                dbg_rx_cnt <= dbg_rx_cnt + 1;
            end if;
            if (RX_RESET = '1') then
                dbg_rx_cnt <= (others => '0');
            end if;
        end if;
    end process;

    pfifo_i : entity work.MFB_ASFIFOX
    generic map (
        MFB_REGIONS         => MFB_REGIONS,
        MFB_REG_SIZE        => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
        FIFO_ITEMS          => FIFO_ITEMS,
        RAM_TYPE            => "BRAM",
        FWFT_MODE           => True,
        OUTPUT_REG          => False,
        METADATA_WIDTH      => MFB_META_WIDTH,
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => AFULL_OFFSET,
        ALMOST_EMPTY_OFFSET => FIFO_ITEMS/2
    ) port map (
        RX_CLK     => RX_CLK,
        RX_RESET   => RX_RESET,

        RX_DATA    => RX_DATA,
        RX_META    => RX_META,
        RX_SOF     => RX_SOF,
        RX_EOF     => RX_EOF,
        RX_SOF_POS => RX_SOF_POS,
        RX_EOF_POS => RX_EOF_POS,
        RX_SRC_RDY => RX_SRC_RDY,
        RX_DST_RDY => RX_DST_RDY,
        RX_AFULL   => RX_AFULL,
        RX_STATUS  => RX_STATUS,

        TX_CLK     => TX_CLK,
        TX_RESET   => TX_RESET,

        TX_DATA    => tx_pfifo_data,
        TX_META    => tx_pfifo_meta,
        TX_SOF     => tx_pfifo_sof,
        TX_EOF     => tx_pfifo_eof,
        TX_SOF_POS => tx_pfifo_sof_pos,
        TX_EOF_POS => tx_pfifo_eof_pos,
        TX_SRC_RDY => tx_pfifo_src_rdy,
        TX_DST_RDY => tx_pfifo_dst_rdy,
        TX_AEMPTY  => open,
        TX_STATUS  => open
    );

    process (TX_CLK)
    begin
        if (rising_edge(TX_CLK)) then
            if (tx_pfifo_src_rdy = '1' and tx_pfifo_dst_rdy = '1') then
                dbg_mid_cnt <= dbg_mid_cnt + 1;
            end if;
            if (TX_RESET = '1') then
                dbg_mid_cnt <= (others => '0');
            end if;
        end if;
    end process;

    rx_dfifo_data    <= RX_DISCARD;
    rx_dfifo_vld     <= RX_EOF;
    rx_dfifo_src_rdy <= (or RX_EOF) and RX_SRC_RDY and RX_DST_RDY;

    dfifo_i : entity work.MVB_ASFIFOX
    generic map(
        MVB_ITEMS           => MFB_REGIONS,
        MVB_ITEM_WIDTH      => 1,
        FIFO_ITEMS          => 2*FIFO_ITEMS,
        RAM_TYPE            => "AUTO",
        FWFT_MODE           => True,
        OUTPUT_REG          => False,
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 1
    )
    port map(
        RX_CLK     => RX_CLK,
        RX_RESET   => RX_RESET,
        RX_DATA    => rx_dfifo_data,
        RX_VLD     => rx_dfifo_vld,
        RX_SRC_RDY => rx_dfifo_src_rdy,
        RX_DST_RDY => rx_dfifo_dst_rdy,
        RX_AFULL   => open,
        RX_STATUS  => open,

        TX_CLK     => TX_CLK,
        TX_RESET   => TX_RESET,
        TX_DATA    => tx_dfifo_data,
        TX_VLD     => tx_dfifo_vld,
        TX_SRC_RDY => tx_dfifo_src_rdy,
        TX_DST_RDY => tx_dfifo_dst_rdy,
        TX_AEMPTY  => open,
        TX_STATUS  => open
    );

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (rx_dfifo_dst_rdy = '0' and rx_dfifo_src_rdy = '1') then
                dfifo_ovf_err_reg <= '1';
            end if;
            if (RX_RESET = '1') then
                dfifo_ovf_err_reg <= '0';
            end if;
        end if;
    end process;

    assert (dfifo_ovf_err_reg /= '1')
       report "MFB_PD_ASFIFO_SIMPLE: Illegal write to full dfifo_i FIFO!"
       severity failure;

    mins_i : entity work.METADATA_INSERTOR
    generic map(
        MVB_ITEMS       => MFB_REGIONS,
        MVB_ITEM_WIDTH  => 1,

        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        MFB_META_WIDTH  => MFB_META_WIDTH,

        INSERT_MODE     => 0, -- insert to SOF region
        MVB_FIFO_SIZE   => 16,
        MVB_FIFOX_MULTI => True, -- we need also MVB_ASFIFOX
        DEVICE          => DEVICE
    )
    port map(
        CLK             => TX_CLK,
        RESET           => TX_RESET,

        RX_MVB_DATA     => tx_dfifo_data,
        RX_MVB_VLD      => tx_dfifo_vld,
        RX_MVB_SRC_RDY  => tx_dfifo_src_rdy,
        RX_MVB_DST_RDY  => tx_dfifo_dst_rdy,

        RX_MFB_DATA     => tx_pfifo_data,
        RX_MFB_META     => tx_pfifo_meta,
        RX_MFB_SOF_POS  => tx_pfifo_sof_pos,
        RX_MFB_EOF_POS  => tx_pfifo_eof_pos,
        RX_MFB_SOF      => tx_pfifo_sof,
        RX_MFB_EOF      => tx_pfifo_eof,
        RX_MFB_SRC_RDY  => tx_pfifo_src_rdy,
        RX_MFB_DST_RDY  => tx_pfifo_dst_rdy,

        TX_MFB_DATA     => tx_mins_data,
        TX_MFB_META     => tx_mins_meta,
        TX_MFB_META_NEW => tx_mins_discard,
        TX_MFB_SOF_POS  => tx_mins_sof_pos,
        TX_MFB_EOF_POS  => tx_mins_eof_pos,
        TX_MFB_SOF      => tx_mins_sof,
        TX_MFB_EOF      => tx_mins_eof,
        TX_MFB_SRC_RDY  => tx_mins_src_rdy,
        TX_MFB_DST_RDY  => tx_mins_dst_rdy
    );

    drop_i : entity work.MFB_DROPPER
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => MFB_META_WIDTH
    )
    port map (
        CLK        => TX_CLK,
        RESET      => TX_RESET,

        RX_DATA    => tx_mins_data,
        RX_META    => tx_mins_meta,
        RX_SOF_POS => tx_mins_sof_pos,
        RX_EOF_POS => tx_mins_eof_pos,
        RX_SOF     => tx_mins_sof,
        RX_EOF     => tx_mins_eof,
        RX_SRC_RDY => tx_mins_src_rdy,
        RX_DST_RDY => tx_mins_dst_rdy,
        RX_DROP    => tx_mins_discard,

        TX_DATA    => TX_DATA,
        TX_META    => TX_META,
        TX_SOF_POS => TX_SOF_POS,
        TX_EOF_POS => TX_EOF_POS,
        TX_SOF     => TX_SOF,
        TX_EOF     => TX_EOF,
        TX_SRC_RDY => TX_SRC_RDY,
        TX_DST_RDY => tx_dst_rdy_fix
    );

    tx_dst_rdy_fix <= TX_DST_RDY or not TX_SRC_RDY;

end architecture;
