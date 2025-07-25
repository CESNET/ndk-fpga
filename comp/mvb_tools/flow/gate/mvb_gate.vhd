-- mvb_gate.vhd: Gating for MVB
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

-- Simple gate for MVB bus. Has option for instation of FIFO,
-- which can smooth out stopping of the bus.
entity MVB_GATE is
    generic (
        ITEMS           : natural := 4;
        ITEM_WIDTH      : natural := 8;
        RX_FIFO_EN      : boolean := false;
        RX_FIFO_DEPTH   : natural := 32;
        DEVICE          : string  := "AGILEX"
    );
    port (
        CLK             : in    std_logic;
        RESET           : in    std_logic;

        -- ===============================================
        -- RX MVB interface
        -- ===============================================
        RX_DATA         : in    std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        RX_VLD          : in    std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY      : in    std_logic;
        RX_DST_RDY      : out   std_logic;

        -- ===============================================
        -- TX MVB interface
        -- ===============================================
        TX_DATA         : out   std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD          : out   std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY      : out   std_logic;
        TX_DST_RDY      : in    std_logic;

        -- ===============================================
        -- Control interface
        -- ===============================================
        -- When this signal is asserted, transmission from RX -> TX
        -- is disabled.
        STOP_EN         : in    std_logic
    );
end entity;

architecture FULL of MVB_GATE is

    signal rx_fifox_tx_data     : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal rx_fifox_tx_vld      : std_logic_vector(ITEMS-1 downto 0);
    signal rx_fifox_tx_src_rdy  : std_logic;
    signal rx_fifox_tx_dst_rdy  : std_logic;

begin

    rx_fifo_i : entity work.MVB_FIFOX
    generic map (
        ITEMS       => ITEMS,
        ITEM_WIDTH  => ITEM_WIDTH,
        FIFO_DEPTH  => RX_FIFO_DEPTH,
        RAM_TYPE    => "AUTO",
        DEVICE      => DEVICE,
        FAKE_FIFO   => not RX_FIFO_EN
    ) port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => RX_DATA,
        RX_VLD      => RX_VLD,
        RX_SRC_RDY  => RX_SRC_RDY,
        RX_DST_RDY  => RX_DST_RDY,

        TX_DATA     => rx_fifox_tx_data,
        TX_VLD      => rx_fifox_tx_vld,
        TX_SRC_RDY  => rx_fifox_tx_src_rdy,
        TX_DST_RDY  => rx_fifox_tx_dst_rdy
    );

    TX_DATA              <= rx_fifox_tx_data;
    TX_VLD               <= rx_fifox_tx_vld;
    TX_SRC_RDY           <= rx_fifox_tx_src_rdy and not STOP_EN;
    rx_fifox_tx_dst_rdy  <= TX_DST_RDY and not STOP_EN;

end architecture;
