-- mux.vhd: General width MVB MUX
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Multi-value bus multiplexer. Selects, which input MVB interface  will be transmitting to output MVB.
-- The selection is done base on received select transactions. For each RX transaction,
-- there must be exactly one select transaction. If there is none, the component will wait until one is received.
entity GEN_MVB_MUX is
    generic (
        MVB_ITEMS       : natural := 1;
        -- One MVB item width
        DATA_WIDTH      : natural := 64;
        -- Number of RX MVB interfaces
        MUX_WIDTH       : natural := 2;

        -- Depth of select FIFO
        FIFO_DEPTH      : natural := 2;
        DEVICE          : string  := "ULTRASCALE"
    );
    port (
        -- Clock signal
        CLK             : in    std_logic;
        -- Synchronous reset with CLK
        RESET           : in    std_logic;

        -- MUX_WIDTH of RX MVB interfaces
        RX_DATA         : in    std_logic_vector(MUX_WIDTH * MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        RX_VLD          : in    std_logic_vector(MUX_WIDTH * MVB_ITEMS - 1 downto 0);
        RX_SRC_RDY      : in    std_logic_vector(MUX_WIDTH - 1 downto 0);
        RX_DST_RDY      : out   std_logic_vector(MUX_WIDTH - 1 downto 0);

        -- TX MVB interface
        TX_DATA         : out   std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        TX_VLD          : out   std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX_SRC_RDY      : out   std_logic;
        TX_DST_RDY      : in    std_logic;

        -- MVB interface for select signal, for each RX transaction one wants
        -- to multiplex, there must be one select transaction.
        RX_SEL_DATA     : in    std_logic_vector(max(log2(MUX_WIDTH), 1) - 1 downto 0);
        RX_SEL_VLD      : in    std_logic_vector(0 downto 0);
        RX_SEL_SRC_RDY  : in    std_logic;
        RX_SEL_DST_RDY  : out   std_logic
    );
end entity;

architecture behavioral of GEN_MVB_MUX is

    constant SEL_WIDTH      : natural := max(1, log2(MUX_WIDTH));

    signal tx_src_rdy_int   : std_logic_vector(1-1 downto 0);
    signal rx_dst_rdies_int : std_logic_vector(MUX_WIDTH-1 downto 0);

    signal sel_fifo_data    : std_logic_vector(SEL_WIDTH - 1 downto 0);
    signal sel_fifo_vld     : std_logic_vector(0 downto 0);
    signal sel_fifo_src_rdy : std_logic;
    signal sel_fifo_dst_rdy : std_logic;

    signal rx_data_arr      : slv_array_t(MUX_WIDTH - 1 downto 0)(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
    signal rx_vld_arr       : slv_array_t(MUX_WIDTH - 1 downto 0)(MVB_ITEMS - 1 downto 0);

begin  -- architecture behavioral

    TX_SRC_RDY <= tx_src_rdy_int(0) and sel_fifo_src_rdy;
    RX_DST_RDY <= rx_dst_rdies_int;
    sel_fifo_dst_rdy <= tx_src_rdy_int(0) and TX_DST_RDY;

    rx_data_arr <= slv_array_deser(RX_DATA, MUX_WIDTH);
    rx_vld_arr <= slv_array_deser(RX_VLD, MUX_WIDTH);

    data_mux_e : entity work.GEN_MUX
    generic map (
        DATA_WIDTH      => MVB_ITEMS * DATA_WIDTH,
        MUX_WIDTH       => MUX_WIDTH
    ) port map (
        DATA_IN         => RX_DATA,
        SEL             => sel_fifo_data,
        DATA_OUT        => TX_DATA
    );

    vld_mux_e : entity work.GEN_MUX
    generic map (
        DATA_WIDTH      => MVB_ITEMS,
        MUX_WIDTH       => MUX_WIDTH
    ) port map (
        DATA_IN         => RX_VLD,
        SEL             => sel_fifo_data,
        DATA_OUT        => TX_VLD
    );

    srdy_mux_e : entity work.GEN_MUX
    generic map (
        DATA_WIDTH  => 1,
        MUX_WIDTH   => MUX_WIDTH
    ) port map (
        DATA_IN     => RX_SRC_RDY,
        SEL         => sel_fifo_data,
        DATA_OUT    => tx_src_rdy_int
    );

    drdy_demux_e : entity work.GEN_DEMUX
    generic map (
        DATA_WIDTH  => 1,
        DEMUX_WIDTH => MUX_WIDTH
    ) port map (
        DATA_IN     => "" & TX_DST_RDY and sel_fifo_src_rdy,
        SEL         => sel_fifo_data,
        DATA_OUT    => rx_dst_rdies_int
    );

    sel_fifo_i : entity work.MVB_FIFOX
    generic map (
        ITEMS       => 1,
        ITEM_WIDTH  => SEL_WIDTH,
        FIFO_DEPTH  => FIFO_DEPTH,
        DEVICE      => DEVICE
    ) port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => RX_SEL_DATA,
        RX_VLD      => RX_SEL_VLD,
        RX_SRC_RDY  => RX_SEL_SRC_RDY,
        RX_DST_RDY  => RX_SEL_DST_RDY,

        TX_DATA     => sel_fifo_data,
        TX_VLD      => sel_fifo_vld,
        TX_SRC_RDY  => sel_fifo_src_rdy,
        TX_DST_RDY  => sel_fifo_dst_rdy,

        STATUS      => open,
        AFULL       => open,
        AEMPTY      => open
    );
end architecture behavioral;
