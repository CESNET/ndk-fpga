-- switch.vhd: top-level AXIS_SWITCH component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;
use work.proto_match_pack.all;
use work.config_pack.all;

entity AXIS_SWITCH is
    generic (
        -- Configuration array object.
        CONFIG           : config_array_t := CONFIG;
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH  : natural        := 512;
        -- MI data bus width in bits.
        MI_DATA_WIDTH    : natural        := 32;
        -- MI address bus width in bits.
        MI_ADDR_WIDTH    : natural        := 32;
        -- Blocks traffic if not enabled (configurable via CSR).
        MI_ENABLE_AXI    : boolean        := true;
        -- Number of actions.
        NUM_ACTIONS      : natural        := CONFIG_NUM_ACTIONS;
        -- Number of ports.
        NUM_PORTS        : natural        := CONFIG_NUM_PORTS;
        -- Depth of individual virtual output queues.
        NUM_ITEMS_PER_IP : integer_vector := (CONFIG_NUM_PORTS-1 downto 0 => CONFIG_VOQ_ITEMS);
        -- Depth of individual virtual input queues.
        NUM_ITEMS_PER_OP : integer_vector := (CONFIG_NUM_PORTS-1 downto 0 => CONFIG_OP_ITEMS);
        -- Enable read from match-action tables.
        MAT_READ_ENABLE  : boolean        := true;
        -- Target device.
        DEVICE           : string         := "AGILEX"
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
        RX_AXI_TDATA    : in  slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST    : in  std_logic_vector(NUM_PORTS-1 downto 0);
        RX_AXI_TVALID   : in  std_logic_vector(NUM_PORTS-1 downto 0);
        RX_AXI_TREADY   : out std_logic_vector(NUM_PORTS-1 downto 0);

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST    : out std_logic_vector(NUM_PORTS-1 downto 0);
        TX_AXI_TVALID   : out std_logic_vector(NUM_PORTS-1 downto 0);
        TX_AXI_TREADY   : in  std_logic_vector(NUM_PORTS-1 downto 0);

        -- =========================================================================
        -- MI CONTROL INTERFACE
        -- =========================================================================
        MI_DWR          : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ADDR         : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        MI_RD           : in  std_logic;
        MI_WR           : in  std_logic;
        MI_BE           : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
        MI_DRD          : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ARDY         : out std_logic;
        MI_DRDY         : out std_logic
    );
end entity;

architecture FULL of AXIS_SWITCH is

    signal s_rx_switch_tdata         : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_rx_switch_tkeep         : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_rx_switch_tlast         : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_rx_switch_tvalid        : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_rx_switch_tready        : std_logic_vector(NUM_PORTS-1 downto 0);

    signal s_tx_switch_tdata_deser   : std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH-1 downto 0);
    signal s_tx_switch_tkeep_deser   : std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_tx_switch_tdata         : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal s_tx_switch_tkeep         : slv_array_t(NUM_PORTS-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal s_tx_switch_tlast         : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_tx_switch_tvalid        : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_tx_switch_tready        : std_logic_vector(NUM_PORTS-1 downto 0);

    constant MAX_STATUS_WIDTH        : integer := log2(max(NUM_ITEMS_PER_IP))+1;
    signal s_switch_dst_req_arr      : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_switch_dst_req_size_arr : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS*MAX_STATUS_WIDTH-1 downto 0);

    signal s_switch_ip_conn_vld      : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_switch_ip_conn_sel      : std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0);
    signal s_switch_op_conn_vld      : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_switch_op_conn_sel      : std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0);

    constant NUM_MATS                : natural := tsel(CONFIG(0).match_num_fields = 0, 0, CONFIG'length);
    constant MAT_MAX_ITEMS           : natural := config_array_get_max(CONFIG, MAT_CONFIG_ITEMS);
    constant MAT_MAX_ADDR_WIDTH      : natural := log2(MAT_MAX_ITEMS);
    constant MAT_MAX_DATA_WIDTH      : natural := config_array_get_max(CONFIG, MAT_CONFIG_MATCH_WIDTH);

    signal s_mat_read_addr           : std_logic_vector(MAT_MAX_ADDR_WIDTH-1 downto 0);
    signal s_mat_read_en             : std_logic_vector(NUM_PORTS*NUM_MATS-1 downto 0);
    signal s_mat_read_rdy            : std_logic_vector(NUM_PORTS*NUM_MATS-1 downto 0);
    signal s_mat_read_vld            : std_logic_vector(NUM_PORTS*NUM_MATS-1 downto 0);
    signal s_mat_read_data           : std_logic_vector(NUM_PORTS*NUM_MATS*MAT_MAX_DATA_WIDTH-1 downto 0);
    signal s_mat_read_mask           : std_logic_vector(NUM_PORTS*NUM_MATS*MAT_MAX_DATA_WIDTH-1 downto 0);
    signal s_mat_read_action         : std_logic_vector(NUM_PORTS*NUM_MATS*log2(NUM_ACTIONS)-1 downto 0);
    signal s_mat_write_addr          : std_logic_vector(MAT_MAX_ADDR_WIDTH-1 downto 0);
    signal s_mat_write_en            : std_logic_vector(NUM_PORTS*NUM_MATS-1 downto 0);
    signal s_mat_write_rdy           : std_logic_vector(NUM_PORTS*NUM_MATS-1 downto 0);
    signal s_mat_write_data          : std_logic_vector(MAT_MAX_DATA_WIDTH-1 downto 0);
    signal s_mat_write_mask          : std_logic_vector(MAT_MAX_DATA_WIDTH-1 downto 0);
    signal s_mat_write_action        : std_logic_vector(log2(NUM_ACTIONS)-1 downto 0);
    signal s_ctrl_axi_enable         : std_logic;

begin

    rx_pipelines_g : for i in 0 to NUM_PORTS-1 generate
        constant MATS_READ_DATA_WIDTH   : natural := NUM_MATS*MAT_MAX_DATA_WIDTH;
        constant MATS_READ_ACTION_WIDTH : natural := NUM_MATS*log2(NUM_ACTIONS);
        signal s_rx_tready              : std_logic;
    begin
        rx_pipeline_i : entity work.AXIS_RX_PIPELINE
        generic map (
            CONFIG             => CONFIG,
            AXI_TDATA_WIDTH    => AXI_TDATA_WIDTH,
            AXI_TDEST_WIDTH    => log2(NUM_ACTIONS),
            MAT_READ_ENABLE    => MAT_READ_ENABLE,
            NUM_PORTS          => NUM_PORTS,
            NUM_ITEMS_PER_PORT => NUM_ITEMS_PER_IP,
            DEVICE             => DEVICE
        )
        port map (
            CLK              => CLK,
            RESET            => RESET,
            RX_AXI_TDATA     => RX_AXI_TDATA(i),
            RX_AXI_TKEEP     => RX_AXI_TKEEP(i),
            RX_AXI_TLAST     => RX_AXI_TLAST(i),
            RX_AXI_TVALID    => RX_AXI_TVALID(i),
            RX_AXI_TREADY    => s_rx_tready,
            TX_AXI_TDATA     => s_rx_switch_tdata(i),
            TX_AXI_TKEEP     => s_rx_switch_tkeep(i),
            TX_AXI_TLAST     => s_rx_switch_tlast(i),
            TX_AXI_TVALID    => s_rx_switch_tvalid(i),
            TX_AXI_TREADY    => s_rx_switch_tready(i),
            MAT_READ_ADDR    => s_mat_read_addr,
            MAT_READ_EN      => s_mat_read_en((i+1)*NUM_MATS-1 downto i*NUM_MATS),
            MAT_READ_RDY     => s_mat_read_rdy((i+1)*NUM_MATS-1 downto i*NUM_MATS),
            MAT_READ_VLD     => s_mat_read_vld((i+1)*NUM_MATS-1 downto i*NUM_MATS),
            MAT_READ_DATA    => s_mat_read_data((i+1)*MATS_READ_DATA_WIDTH-1 downto i*MATS_READ_DATA_WIDTH),
            MAT_READ_MASK    => s_mat_read_mask((i+1)*MATS_READ_DATA_WIDTH-1 downto i*MATS_READ_DATA_WIDTH),
            MAT_READ_ACTION  => s_mat_read_action((i+1)*MATS_READ_ACTION_WIDTH-1 downto i*MATS_READ_ACTION_WIDTH),
            MAT_WRITE_ADDR   => s_mat_write_addr,
            MAT_WRITE_EN     => s_mat_write_en((i+1)*NUM_MATS-1 downto i*NUM_MATS),
            MAT_WRITE_RDY    => s_mat_write_rdy((i+1)*NUM_MATS-1 downto i*NUM_MATS),
            MAT_WRITE_DATA   => s_mat_write_data,
            MAT_WRITE_MASK   => s_mat_write_mask,
            MAT_WRITE_ACTION => s_mat_write_action,
            DEST_REQ_VEC     => s_switch_dst_req_arr(i),
            DEST_REQ_SIZES   => s_switch_dst_req_size_arr(i),
            VOQ_CONN_VLD     => s_switch_ip_conn_vld(i),
            VOQ_CONN_SEL     => s_switch_ip_conn_sel((i+1)*log2(NUM_PORTS)-1 downto i*log2(NUM_PORTS))
        );
        RX_AXI_TREADY(i) <= s_rx_tready and s_ctrl_axi_enable;
    end generate;

    switch_fabric_i : entity work.AXIS_SWITCH_FABRIC
    generic map (
        NUM_PORTS       => NUM_PORTS,
        STATUS_WIDTH    => MAX_STATUS_WIDTH,
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,
        RX_AXI_TDATA   => slv_array_ser(s_rx_switch_tdata),
        RX_AXI_TKEEP   => slv_array_ser(s_rx_switch_tkeep),
        RX_AXI_TLAST   => s_rx_switch_tlast,
        RX_AXI_TVALID  => s_rx_switch_tvalid,
        RX_AXI_TREADY  => s_rx_switch_tready,
        TX_AXI_TDATA   => s_tx_switch_tdata_deser,
        TX_AXI_TKEEP   => s_tx_switch_tkeep_deser,
        TX_AXI_TLAST   => s_tx_switch_tlast,
        TX_AXI_TVALID  => s_tx_switch_tvalid,
        TX_AXI_TREADY  => s_tx_switch_tready,
        DEST_REQ_VEC   => slv_array_ser(s_switch_dst_req_arr),
        DEST_REQ_SIZES => slv_array_ser(s_switch_dst_req_size_arr),
        IP_CONN_VLD    => s_switch_ip_conn_vld,
        IP_CONN_SEL    => s_switch_ip_conn_sel,
        OP_CONN_VLD    => s_switch_op_conn_vld,
        OP_CONN_SEL    => s_switch_op_conn_sel
    );
    s_tx_switch_tdata <= slv_array_deser(s_tx_switch_tdata_deser, NUM_PORTS);
    s_tx_switch_tkeep <= slv_array_deser(s_tx_switch_tkeep_deser, NUM_PORTS);

    -- TODO: tx_pipeline_i
    tx_pipelines_g : for i in 0 to NUM_PORTS-1 generate
        op_manager_i : entity work.AXIS_OP_MANAGER
        generic map (
            NUM_PORTS          => NUM_PORTS,
            NUM_ITEMS_PER_PORT => NUM_ITEMS_PER_OP,
            AXI_TDATA_WIDTH    => AXI_TDATA_WIDTH,
            DEVICE             => DEVICE
        )
        port map (
            CLK           => CLK,
            RESET         => RESET,
            RX_AXI_TDATA  => s_tx_switch_tdata(i),
            RX_AXI_TKEEP  => s_tx_switch_tkeep(i),
            RX_AXI_TLAST  => s_tx_switch_tlast(i),
            RX_AXI_TVALID => s_tx_switch_tvalid(i),
            RX_AXI_TREADY => s_tx_switch_tready(i),
            TX_AXI_TDATA  => TX_AXI_TDATA(i),
            TX_AXI_TKEEP  => TX_AXI_TKEEP(i),
            TX_AXI_TLAST  => TX_AXI_TLAST(i),
            TX_AXI_TVALID => TX_AXI_TVALID(i),
            TX_AXI_TREADY => TX_AXI_TREADY(i),
            OP_CONN_VLD   => s_switch_op_conn_vld(i),
            OP_CONN_SEL   => s_switch_op_conn_sel((i+1)*log2(NUM_PORTS)-1 downto i*log2(NUM_PORTS))
        );
    end generate;

    switch_ctrl_i : entity work.SWITCH_CONTROLLER
    generic map (
        CONFIG             => CONFIG,
        CONFIG_NUM_ACTIONS => NUM_ACTIONS,
        CONFIG_NUM_PORTS   => NUM_PORTS,
        MAT_READ_ENABLE    => MAT_READ_ENABLE,
        MI_DATA_WIDTH      => MI_DATA_WIDTH,
        MI_ADDR_WIDTH      => MI_ADDR_WIDTH,
        MI_ENABLE_AXI      => MI_ENABLE_AXI,
        DEVICE             => DEVICE
    )
    port map (
        CLK              => CLK,
        RESET            => RESET,
        MI_DWR           => MI_DWR,
        MI_ADDR          => MI_ADDR,
        MI_RD            => MI_RD,
        MI_WR            => MI_WR,
        MI_BE            => MI_BE,
        MI_DRD           => MI_DRD,
        MI_ARDY          => MI_ARDY,
        MI_DRDY          => MI_DRDY,
        MAT_READ_ADDR    => s_mat_read_addr,
        MAT_READ_EN      => s_mat_read_en,
        MAT_READ_RDY     => s_mat_read_rdy,
        MAT_READ_VLD     => s_mat_read_vld,
        MAT_READ_DATA    => s_mat_read_data,
        MAT_READ_MASK    => s_mat_read_mask,
        MAT_READ_ACTION  => s_mat_read_action,
        MAT_WRITE_ADDR   => s_mat_write_addr,
        MAT_WRITE_EN     => s_mat_write_en,
        MAT_WRITE_RDY    => s_mat_write_rdy,
        MAT_WRITE_DATA   => s_mat_write_data,
        MAT_WRITE_MASK   => s_mat_write_mask,
        MAT_WRITE_ACTION => s_mat_write_action,
        AXI_ENABLE       => s_ctrl_axi_enable
    );

end architecture;
