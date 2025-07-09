-- demux.vhd: AXIS_DEMUX component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Authors(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

entity AXIS_DEMUX is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH : natural := 512;
        -- AXI-Stream user data width in bits.
        AXI_TUSER_WIDTH : natural := 0;
        -- Number of output streams.
        DEMUX_WIDTH     : natural := 16
    );
    port (
        -- =========================================================================
        -- RX AXI STREAM INTERFACE
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER    : in  std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST    : in  std_logic;
        RX_AXI_TVALID   : in  std_logic;
        RX_AXI_TREADY   : out std_logic;

        -- =========================================================================
        -- TX AXI STREAM INTERFACES
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(DEMUX_WIDTH*AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(DEMUX_WIDTH*AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER    : out std_logic_vector(DEMUX_WIDTH*AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        TX_AXI_TLAST    : out std_logic_vector(DEMUX_WIDTH-1 downto 0);
        TX_AXI_TVALID   : out std_logic_vector(DEMUX_WIDTH-1 downto 0);
        TX_AXI_TREADY   : in  std_logic_vector(DEMUX_WIDTH-1 downto 0);

        -- =========================================================================
        -- MUX INTERFACE
        -- =========================================================================
        -- Blocks traffic if not enabled.
        DEMUX_EN        : in  std_logic;
        -- Output stream select.
        DEMUX_SEL       : in  std_logic_vector(max(1,log2(DEMUX_WIDTH))-1 downto 0)
    );
end entity;

architecture FULL of AXIS_DEMUX is

    signal s_tx_axi_tdata_arr    : slv_array_t(DEMUX_WIDTH-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_tx_axi_tkeep_arr    : slv_array_t(DEMUX_WIDTH-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_tx_axi_tuser_arr    : slv_array_t(DEMUX_WIDTH-1 downto 0)(AXI_TUSER_WIDTH-1 downto 0);

    signal s_rx_axi_tvalid_demux : std_logic_vector(DEMUX_WIDTH-1 downto 0);
    signal s_tx_axi_tready_mux   : std_logic;

begin

    demux_output_logic_g : for i in 0 to DEMUX_WIDTH-1 generate
        s_tx_axi_tdata_arr(i) <= RX_AXI_TDATA;
        s_tx_axi_tkeep_arr(i) <= RX_AXI_TKEEP;
        s_tx_axi_tuser_arr(i) <= RX_AXI_TUSER;
        TX_AXI_TLAST(i)       <= RX_AXI_TLAST;
        TX_AXI_TVALID(i)      <= s_rx_axi_tvalid_demux(i) and DEMUX_EN;
    end generate;
    TX_AXI_TDATA  <= slv_array_ser(s_tx_axi_tdata_arr);
    TX_AXI_TKEEP  <= slv_array_ser(s_tx_axi_tkeep_arr);
    TX_AXI_TUSER  <= slv_array_ser(s_tx_axi_tuser_arr);
    RX_AXI_TREADY <= s_tx_axi_tready_mux and DEMUX_EN;

    rx_axi_tvalid_demux_i : entity work.GEN_DEMUX
    generic map (
        DATA_WIDTH  => 1,
        DEMUX_WIDTH => DEMUX_WIDTH,
        DEF_VALUE   => '0'
    )
    port map (
        DATA_IN(0) => RX_AXI_TVALID,
        SEL        => DEMUX_SEL,
        DATA_OUT   => s_rx_axi_tvalid_demux
    );

    tx_axi_tready_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => 1,
        MUX_WIDTH  => DEMUX_WIDTH
    )
    port map (
        DATA_IN     => TX_AXI_TREADY,
        SEL         => DEMUX_SEL,
        DATA_OUT(0) => s_tx_axi_tready_mux
    );

end architecture;
