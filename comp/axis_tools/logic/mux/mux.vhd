-- mux.vhd: AXIS_MUX component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Authors(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

entity AXIS_MUX is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH : natural := 512;
        -- AXI-Stream user data width in bits.
        AXI_TUSER_WIDTH : natural := 0;
        -- Number of input streams.
        MUX_WIDTH       : natural := 16
    );
    port (
        -- =========================================================================
        -- RX AXI STREAM INTERFACES
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(MUX_WIDTH*AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector(MUX_WIDTH*AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER    : in  std_logic_vector(MUX_WIDTH*AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST    : in  std_logic_vector(MUX_WIDTH-1 downto 0);
        RX_AXI_TVALID   : in  std_logic_vector(MUX_WIDTH-1 downto 0);
        RX_AXI_TREADY   : out std_logic_vector(MUX_WIDTH-1 downto 0);

        -- =========================================================================
        -- TX AXI STREAM INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER    : out std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        TX_AXI_TLAST    : out std_logic;
        TX_AXI_TVALID   : out std_logic;
        TX_AXI_TREADY   : in  std_logic;

        -- =========================================================================
        -- MUX INTERFACE
        -- =========================================================================
        -- Blocks traffic if not enabled.
        MUX_EN          : in  std_logic;
        -- Input stream select.
        MUX_SEL         : in  std_logic_vector(max(1,log2(MUX_WIDTH))-1 downto 0)
    );
end entity;

architecture FULL of AXIS_MUX is

    constant AXI_DATA_WIDTH : natural := AXI_TDATA_WIDTH + (AXI_TDATA_WIDTH/8) + AXI_TUSER_WIDTH + 1 + 1;
    constant MUX_DATA_WIDTH : natural := MUX_WIDTH * AXI_DATA_WIDTH;

    subtype AXI_TDATA_R is natural range  AXI_TDATA_WIDTH                           -1 downto 0;
    subtype AXI_TKEEP_R is natural range (AXI_TDATA_R'high+1) + (AXI_TDATA_WIDTH/8) -1 downto (AXI_TDATA_R'high+1);
    subtype AXI_TUSER_R is natural range (AXI_TKEEP_R'high+1) +  AXI_TUSER_WIDTH    -1 downto (AXI_TKEEP_R'high+1);

    signal s_rx_axi_tdata_arr      : slv_array_t(MUX_WIDTH-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_rx_axi_tkeep_arr      : slv_array_t(MUX_WIDTH-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_rx_axi_tuser_arr      : slv_array_t(MUX_WIDTH-1 downto 0)(AXI_TUSER_WIDTH-1 downto 0);
    signal s_rx_axi_ifc_packed_arr : slv_array_t(MUX_WIDTH-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal s_tx_axi_ifc_packed     : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);

    signal s_demux_rx_rdy : std_logic_vector(MUX_WIDTH-1 downto 0);
    signal s_mux_tx_vld   : std_logic;

begin

    s_rx_axi_tdata_arr <= slv_array_deser(RX_AXI_TDATA, MUX_WIDTH);
    s_rx_axi_tkeep_arr <= slv_array_deser(RX_AXI_TKEEP, MUX_WIDTH);
    s_rx_axi_tuser_arr <= slv_array_deser(RX_AXI_TUSER, MUX_WIDTH);

    rx_axi_ifc_pack_g : for i in 0 to MUX_WIDTH-1 generate
        s_rx_axi_ifc_packed_arr(i) <= RX_AXI_TVALID(i) & RX_AXI_TLAST(i) & s_rx_axi_tuser_arr(i) & s_rx_axi_tkeep_arr(i) & s_rx_axi_tdata_arr(i);
    end generate;
    (s_mux_tx_vld, TX_AXI_TLAST, TX_AXI_TUSER, TX_AXI_TKEEP, TX_AXI_TDATA) <= s_tx_axi_ifc_packed;

    data_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => AXI_DATA_WIDTH,
        MUX_WIDTH  => MUX_WIDTH
    )
    port map (
        DATA_IN  => slv_array_ser(s_rx_axi_ifc_packed_arr),
        SEL      => MUX_SEL,
        DATA_OUT => s_tx_axi_ifc_packed
    );

    ready_mux_i : entity work.GEN_DEMUX
    generic map (
        DATA_WIDTH  => 1,
        DEMUX_WIDTH => MUX_WIDTH
    )
    port map (
        DATA_IN(0) => TX_AXI_TREADY,
        SEL        => MUX_SEL,
        DATA_OUT   => s_demux_rx_rdy
    );

    RX_AXI_TREADY <= s_demux_rx_rdy and (RX_AXI_TREADY'range => MUX_EN);
    TX_AXI_TVALID <= s_mux_tx_vld and MUX_EN;

end architecture;
