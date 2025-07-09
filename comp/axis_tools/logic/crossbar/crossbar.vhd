-- crossbar.vhd: AXIS_CROSSBAR component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

entity AXIS_CROSSBAR is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH : natural := 512;
        -- AXI-Stream user data width in bits.
        AXI_TUSER_WIDTH : natural := 0;
        -- Number of input/output ports.
        NUM_PORTS       : natural := 2
    );
    port (
        -- =========================================================================
        -- RX AXI STREAM INTERFACES
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER    : in  std_logic_vector(NUM_PORTS*AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST    : in  std_logic_vector(NUM_PORTS-1 downto 0);
        RX_AXI_TVALID   : in  std_logic_vector(NUM_PORTS-1 downto 0);
        RX_AXI_TREADY   : out std_logic_vector(NUM_PORTS-1 downto 0);

        -- =========================================================================
        -- TX AXI STREAM INTERFACES
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER    : out std_logic_vector(NUM_PORTS*AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        TX_AXI_TLAST    : out std_logic_vector(NUM_PORTS-1 downto 0);
        TX_AXI_TVALID   : out std_logic_vector(NUM_PORTS-1 downto 0);
        TX_AXI_TREADY   : in  std_logic_vector(NUM_PORTS-1 downto 0);

        -- =========================================================================
        -- CONTROL INTERFACE
        -- =========================================================================
        OP_CONN_VLD     : in  std_logic_vector(NUM_PORTS-1 downto 0);
        OP_CONN_SEL     : in  std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0)
    );
end entity;

architecture FULL of AXIS_CROSSBAR is

    signal s_tx_axi_tdata_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_tx_axi_tkeep_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_tx_axi_tuser_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TUSER_WIDTH-1 downto 0);
    signal s_rx_axi_tready_arr : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_conn_sel_arr      : slv_array_t(NUM_PORTS-1 downto 0)(log2(NUM_PORTS)-1 downto 0);
    signal s_conn_sel_hot_arr  : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);

    signal s_ip_tx_dst_rdy_arr : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_ip_drives_hot_arr : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);

begin

    s_conn_sel_arr <= slv_array_deser(OP_CONN_SEL, NUM_PORTS);

    op_mux_g : for i in 0 to NUM_PORTS-1 generate
        op_mux_i : entity work.AXIS_MUX
        generic map (
            AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
            AXI_TUSER_WIDTH => AXI_TUSER_WIDTH,
            MUX_WIDTH       => NUM_PORTS
        )
        port map (
            RX_AXI_TDATA  => RX_AXI_TDATA,
            RX_AXI_TKEEP  => RX_AXI_TKEEP,
            RX_AXI_TUSER  => RX_AXI_TUSER,
            RX_AXI_TLAST  => RX_AXI_TLAST,
            RX_AXI_TVALID => RX_AXI_TVALID,
            RX_AXI_TREADY => s_rx_axi_tready_arr(i),
            TX_AXI_TDATA  => s_tx_axi_tdata_arr(i),
            TX_AXI_TKEEP  => s_tx_axi_tkeep_arr(i),
            TX_AXI_TUSER  => s_tx_axi_tuser_arr(i),
            TX_AXI_TLAST  => TX_AXI_TLAST(i),
            TX_AXI_TVALID => TX_AXI_TVALID(i),
            TX_AXI_TREADY => TX_AXI_TREADY(i),
            MUX_EN        => OP_CONN_VLD(i),
            MUX_SEL       => s_conn_sel_arr(i)
        );

        addr_dec_i : entity work.DEC1FN_ENABLE
        generic map (
            ITEMS => NUM_PORTS
        )
        port map (
            ADDR   => s_conn_sel_arr(i),
            ENABLE => OP_CONN_VLD(i),
            DO     => s_conn_sel_hot_arr(i)
        );

        ip_transpose_hot_g : for j in 0 to NUM_PORTS-1 generate
            s_ip_tx_dst_rdy_arr(i)(j) <= s_rx_axi_tready_arr(j)(i);
            s_ip_drives_hot_arr(i)(j) <= s_conn_sel_hot_arr(j)(i);
        end generate;

        RX_AXI_TREADY(i) <= and (not s_ip_drives_hot_arr(i) or (s_ip_drives_hot_arr(i) and s_ip_tx_dst_rdy_arr(i)));

    end generate;

    TX_AXI_TDATA <= slv_array_ser(s_tx_axi_tdata_arr);
    TX_AXI_TKEEP <= slv_array_ser(s_tx_axi_tkeep_arr);
    TX_AXI_TUSER <= slv_array_ser(s_tx_axi_tuser_arr);

end architecture;
