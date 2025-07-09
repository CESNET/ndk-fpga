-- voq_manager.vhd: AXIS_VOQ_MANAGER component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

entity AXIS_VOQ_MANAGER is
    generic (
        -- Number of output ports.
        NUM_PORTS          : natural        := 2;
        -- Depth of individual virtual output queues.
        NUM_ITEMS_PER_PORT : integer_vector := (0 => 16, 1 => 16);
        -- Maximum capacity width in bits.
        MAX_STATUS_WIDTH   : integer        := log2(max(NUM_ITEMS_PER_PORT))+1;
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH    : natural        := 512;
        -- AXI-Stream destination width in bits (switch purposes only).
        AXI_TDEST_WIDTH    : natural        := log2(NUM_PORTS);
        -- Target device.
        DEVICE             : string         := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- =========================================================================
        -- RX AXI INTERFACE
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TDEST    : in  std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);
        RX_AXI_TLAST    : in  std_logic;
        RX_AXI_TVALID   : in  std_logic;
        RX_AXI_TREADY   : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST    : out std_logic;
        TX_AXI_TVALID   : out std_logic;
        TX_AXI_TREADY   : in  std_logic;

        -- =========================================================================
        -- iSLIP CONTROL INTERFACE
        -- =========================================================================
        DEST_REQ_VEC    : out std_logic_vector(NUM_PORTS-1 downto 0);
        DEST_REQ_SIZES  : out std_logic_vector(NUM_PORTS*MAX_STATUS_WIDTH-1 downto 0) := (others => '0');
        VOQ_CONN_VLD    : in  std_logic;
        VOQ_CONN_SEL    : in  std_logic_vector(AXI_TDEST_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of AXIS_VOQ_MANAGER is

    signal s_voq_rx_axi_tdata      : std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH-1 downto 0);
    signal s_voq_rx_axi_tkeep      : std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_voq_rx_axi_tdata_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_voq_rx_axi_tkeep_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_voq_rx_axi_tlast_arr  : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_voq_rx_axi_tvalid_arr : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_voq_rx_axi_tready_arr : std_logic_vector(NUM_PORTS-1 downto 0);

    signal s_voq_tx_axi_tdata_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_voq_tx_axi_tkeep_arr  : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_voq_tx_axi_tlast_arr  : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_voq_tx_axi_tvalid_arr : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_voq_tx_axi_tready_arr : std_logic_vector(NUM_PORTS-1 downto 0);

begin

    voq_demux_i : entity work.AXIS_DEMUX
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        AXI_TUSER_WIDTH => 0,
        DEMUX_WIDTH     => NUM_PORTS
    )
    port map (
        RX_AXI_TDATA  => RX_AXI_TDATA,
        RX_AXI_TKEEP  => RX_AXI_TKEEP,
        RX_AXI_TLAST  => RX_AXI_TLAST,
        RX_AXI_TVALID => RX_AXI_TVALID,
        RX_AXI_TREADY => RX_AXI_TREADY,
        TX_AXI_TDATA  => s_voq_rx_axi_tdata,
        TX_AXI_TKEEP  => s_voq_rx_axi_tkeep,
        TX_AXI_TLAST  => s_voq_rx_axi_tlast_arr,
        TX_AXI_TVALID => s_voq_rx_axi_tvalid_arr,
        TX_AXI_TREADY => s_voq_rx_axi_tready_arr,
        DEMUX_EN      => '1',
        DEMUX_SEL     => RX_AXI_TDEST
    );

    s_voq_rx_axi_tdata_arr <= slv_array_deser(s_voq_rx_axi_tdata, NUM_PORTS);
    s_voq_rx_axi_tkeep_arr <= slv_array_deser(s_voq_rx_axi_tkeep, NUM_PORTS);

    virtual_output_queues_g : for i in 0 to NUM_PORTS-1 generate
        constant VOQ_STATUS_WIDTH : natural := log2(NUM_ITEMS_PER_PORT(i))+1;
        signal voq_empty          : std_logic;
        signal voq_status         : std_logic_vector(VOQ_STATUS_WIDTH-1 downto 0);
    begin

        -- TODO: optimize using some kind of DP memory?
        voq_i : entity work.AXIS_FIFO
        generic map (
            AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
            AXI_TUSER_WIDTH => 0,
            ITEMS           => NUM_ITEMS_PER_PORT(i), -- TODO: measure how much is needed
            DEVICE          => DEVICE,
            FIFO_TYPE       => 1
        )
        port map (
            CLK           => CLK,
            RESET         => RESET,
            RX_AXI_TDATA  => s_voq_rx_axi_tdata_arr(i),
            RX_AXI_TKEEP  => s_voq_rx_axi_tkeep_arr(i),
            RX_AXI_TLAST  => s_voq_rx_axi_tlast_arr(i),
            RX_AXI_TVALID => s_voq_rx_axi_tvalid_arr(i),
            RX_AXI_TREADY => s_voq_rx_axi_tready_arr(i),
            TX_AXI_TDATA  => s_voq_tx_axi_tdata_arr(i),
            TX_AXI_TKEEP  => s_voq_tx_axi_tkeep_arr(i),
            TX_AXI_TLAST  => s_voq_tx_axi_tlast_arr(i),
            TX_AXI_TVALID => s_voq_tx_axi_tvalid_arr(i),
            TX_AXI_TREADY => s_voq_tx_axi_tready_arr(i),
            FULL          => open,
            AFULL         => open,
            STATUS        => voq_status,
            EMPTY         => voq_empty,
            AEMPTY        => open
        );

        DEST_REQ_VEC(i) <= not voq_empty;
        DEST_REQ_SIZES(i*MAX_STATUS_WIDTH+VOQ_STATUS_WIDTH-1 downto i*MAX_STATUS_WIDTH) <= voq_status;
    end generate;

    voq_mux_i : entity work.AXIS_MUX
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        AXI_TUSER_WIDTH => 0,
        MUX_WIDTH       => NUM_PORTS
    )
    port map (
        RX_AXI_TDATA  => slv_array_ser(s_voq_tx_axi_tdata_arr),
        RX_AXI_TKEEP  => slv_array_ser(s_voq_tx_axi_tkeep_arr),
        RX_AXI_TLAST  => s_voq_tx_axi_tlast_arr,
        RX_AXI_TVALID => s_voq_tx_axi_tvalid_arr,
        RX_AXI_TREADY => s_voq_tx_axi_tready_arr,
        TX_AXI_TDATA  => TX_AXI_TDATA,
        TX_AXI_TKEEP  => TX_AXI_TKEEP,
        TX_AXI_TLAST  => TX_AXI_TLAST,
        TX_AXI_TVALID => TX_AXI_TVALID,
        TX_AXI_TREADY => TX_AXI_TREADY,
        MUX_EN        => VOQ_CONN_VLD,
        MUX_SEL       => VOQ_CONN_SEL
    );

end architecture;
