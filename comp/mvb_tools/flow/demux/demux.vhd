-- demux.vhd: General width item MVB DEMUX
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Multi-value bus item demultiplexer. For each item, there is a select signal,
-- which determines to which TX port the item will be transmitted.
-- Transaction on RX MVB is executed, when all ports, to which at least one item will be transmitted,
-- have DST_RDY asserted. Ports, which will not receive any item, do not have to have DST_RDY asserted.
entity GEN_MVB_DEMUX is
    generic (
        -- Any positive value
        MVB_ITEMS       : natural := 1;
        -- Any positive value
        DATA_WIDTH      : natural := 64;
        -- TX interfaces count
        DEMUX_WIDTH     : natural := 2;

        VERSION         : string := "register";

        OUTPUT_REG      : boolean := False;

        -- Input register. This component will
        -- break, when connected to output of MVB_MERGE,
        -- since it can RX_VLD signal before transmission.
        -- In that case, enable this input register.
        INPUT_REG       : boolean := false
    );
    port (
        -- Clock signal
        CLK             : in    std_logic;
        -- Synchronous reset with CLK
        RESET           : in    std_logic;

        -- ================================================
        -- RX MVB interface
        --
        -- Receive MVB interface with items to demultiplex.
        -- ================================================

        -- This signal contains items, which will be demultiplexed
        RX_DATA         : in    std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        -- This signal contains select signal for each item.
        RX_SEL          : in    std_logic_vector(MVB_ITEMS * max(1, log2(DEMUX_WIDTH)) - 1 downto 0);
        RX_VLD          : in    std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX_SRC_RDY      : in    std_logic;
        RX_DST_RDY      : out   std_logic;

        -- ================================================
        -- TX MVB interfaces
        --
        -- DEMUX_WIDTH (amount) of transmit interfaces.
        -- ================================================

        -- This signal contains demultiplexed items.
        TX_DATA         : out   std_logic_vector(DEMUX_WIDTH * MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        TX_VLD          : out   std_logic_vector(DEMUX_WIDTH * MVB_ITEMS - 1 downto 0);
        TX_SRC_RDY      : out   std_logic_vector(DEMUX_WIDTH - 1 downto 0);
        TX_DST_RDY      : in    std_logic_vector(DEMUX_WIDTH - 1 downto 0)
    );
end entity;

architecture behavioral of GEN_MVB_DEMUX is

    constant SEL_WIDTH          : natural := max(1, log2(DEMUX_WIDTH));

    signal rx_data_arr          : slv_array_t(MVB_ITEMS - 1 downto 0)(DATA_WIDTH - 1 downto 0);
    signal rx_sel_arr           : slv_array_t(MVB_ITEMS - 1 downto 0)(SEL_WIDTH - 1 downto 0);
    signal rx_vld_int           : std_logic_vector(MVB_ITEMS - 1 downto 0);
    signal rx_srdy_int          : std_logic;
    signal rx_sel_dec_arr       : slv_array_t(MVB_ITEMS - 1 downto 0)(DEMUX_WIDTH - 1 downto 0);

    signal fork_rx_data_arr     : slv_array_t(MVB_ITEMS - 1 downto 0)(DATA_WIDTH + DEMUX_WIDTH - 1 downto 0);
    signal fork_rx_dst_rdy      : std_logic;
    signal fork_tx_data         : std_logic_vector(DEMUX_WIDTH * MVB_ITEMS * (DATA_WIDTH + DEMUX_WIDTH) - 1 downto 0);
    signal fork_tx_data_arr     : slv_array_t(DEMUX_WIDTH - 1 downto 0)(MVB_ITEMS * (DATA_WIDTH + DEMUX_WIDTH) - 1 downto 0);
    signal fork_tx_vld          : std_logic_vector(DEMUX_WIDTH * MVB_ITEMS - 1 downto 0);
    signal fork_tx_vld_arr      : slv_array_t(DEMUX_WIDTH - 1 downto 0)(MVB_ITEMS - 1 downto 0);
    signal fork_tx_src_rdy      : std_logic_vector(DEMUX_WIDTH - 1 downto 0);
    signal fork_tx_dst_rdy      : std_logic_vector(DEMUX_WIDTH - 1 downto 0);

    signal tx_data_arr          : slv_array_t(DEMUX_WIDTH - 1 downto 0)(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
    signal tx_vld_arr           : slv_array_t(DEMUX_WIDTH - 1 downto 0)(MVB_ITEMS - 1 downto 0);

begin
    RX_DST_RDY <= fork_rx_dst_rdy;

    in_reg_g : if INPUT_REG generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                if RESET = '1' then
                    rx_srdy_int <= '0';
                elsif fork_rx_dst_rdy = '1' then
                    rx_sel_arr  <= slv_array_deser(RX_SEL, MVB_ITEMS);
                    rx_data_arr <= slv_array_deser(RX_DATA, MVB_ITEMS);
                    rx_vld_int  <= RX_VLD;
                    rx_srdy_int <= RX_SRC_RDY;
                end if;
            end if;
        end process;
    else generate
        rx_sel_arr  <= slv_array_deser(RX_SEL, MVB_ITEMS);
        rx_data_arr <= slv_array_deser(RX_DATA, MVB_ITEMS);
        rx_vld_int  <= RX_VLD;
        rx_srdy_int <= RX_SRC_RDY;
    end generate;

    dec_g  : for i in 0 to MVB_ITEMS - 1 generate
        dec_i : entity work.DEC1FN
        generic map (
            ITEMS   => DEMUX_WIDTH
        )
        port map (
            ADDR    => rx_sel_arr(i),
            DO      => rx_sel_dec_arr(i)
        );
    end generate;

    fork_rx_data_g  : for i in 0 to MVB_ITEMS - 1 generate
        fork_rx_data_arr(i) <= rx_sel_dec_arr(i) & rx_data_arr(i);
    end generate;

    fork_i : entity work.MVB_FORK
    generic map (
        OUTPUT_PORTS    => DEMUX_WIDTH,
        ITEMS           => MVB_ITEMS,
        ITEM_WIDTH      => DATA_WIDTH + DEMUX_WIDTH,
        USE_DST_RDY     => true,
        VERSION         => VERSION
    ) port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_DATA         => slv_array_ser(fork_rx_data_arr),
        RX_VLD          => rx_vld_int,
        RX_SRC_RDY      => rx_srdy_int,
        RX_DST_RDY      => fork_rx_dst_rdy,

        TX_DATA         => fork_tx_data,
        TX_VLD          => fork_tx_vld,
        TX_SRC_RDY      => fork_tx_src_rdy,
        TX_DST_RDY      => fork_tx_dst_rdy
    );

    fork_tx_data_arr    <= slv_array_deser(fork_tx_data, DEMUX_WIDTH);
    fork_tx_vld_arr     <= slv_array_deser(fork_tx_vld, DEMUX_WIDTH);

    discard_g : for i in 0 to DEMUX_WIDTH - 1 generate
        signal discard_rx_all  : slv_array_t(MVB_ITEMS - 1 downto 0)(DATA_WIDTH + DEMUX_WIDTH - 1 downto 0);
        signal discard_rx_data  : slv_array_t(MVB_ITEMS - 1 downto 0)(DATA_WIDTH - 1 downto 0);
        signal discard_rx_sel   : slv_array_t(MVB_ITEMS - 1 downto 0)(DEMUX_WIDTH - 1 downto 0);
        signal dicard_rx_disc   : std_logic_vector(MVB_ITEMS - 1 downto 0);
    begin

        discard_rx_all <= slv_array_deser(fork_tx_data_arr(i), MVB_ITEMS);

        rx_data_g : for x in 0 to MVB_ITEMS - 1 generate
            discard_rx_data(x) <= discard_rx_all(x)(DATA_WIDTH - 1 downto 0);
            discard_rx_sel(x)  <= discard_rx_all(x)(DATA_WIDTH + DEMUX_WIDTH - 1 downto DATA_WIDTH);
            dicard_rx_disc(x)  <= discard_rx_sel(x)(i);
        end generate;

        dicsard_i : entity work.MVB_DISCARD
        generic map (
            ITEMS       => MVB_ITEMS,
            ITEM_WIDTH  => DATA_WIDTH,
            OUTPUT_REG  => OUTPUT_REG
        ) port map (
            CLK         => CLK,
            RESET       => RESET,

            RX_DATA     => slv_array_ser(discard_rx_data),
            RX_DISCARD  => not dicard_rx_disc,
            RX_VLD      => fork_tx_vld_arr(i),
            RX_SRC_RDY  => fork_tx_src_rdy(i),
            RX_DST_RDY  => fork_tx_dst_rdy(i),

            TX_DATA     => tx_data_arr(i),
            TX_VLD      => tx_vld_arr(i),
            TX_SRC_RDY  => TX_SRC_RDY(i),
            TX_DST_RDY  => TX_DST_RDY(i)
        );
    end generate;

    TX_DATA <= slv_array_ser(tx_data_arr);
    TX_VLD  <= slv_array_ser(tx_vld_arr);

end architecture behavioral;
