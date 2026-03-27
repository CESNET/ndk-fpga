-- dispatcher.vhd: AXIS_DISPATCHER component
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

use work.proto_hdr_pack.all;
use work.proto_match_pack.all;
use work.config_pack.all;

entity AXIS_DISPATCHER is
    generic (
        -- Configuration array object.
        CONFIG                : config_array_t := CONFIG_NONE;
        -- >>>> DO NOT MODIFY => EXPLANATORY PURPOSE ONLY!
        -- Number of match-action tables per port.
        CONFIG_SIZE           : natural        := tsel(CONFIG(0).match_num_fields = 0, 0, CONFIG'length);
        -- Max capacity of the match-action tables.
        CONFIG_MAX_ITEMS      : natural        := config_array_get_max(CONFIG, MAT_CONFIG_ITEMS);
        -- Max address width in bits.
        CONFIG_MAX_ADDR_WIDTH : natural        := log2(CONFIG_MAX_ITEMS);
        -- Max data vector width in bits.
        CONFIG_MAX_DATA_WIDTH : natural        := config_array_get_max(CONFIG, MAT_CONFIG_MATCH_WIDTH);
        -- <<<<
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH       : natural        := 512;
        -- AXI-Stream destination width in bits (switch purposes only).
        AXI_TDEST_WIDTH       : natural        := 4;
        -- Enable read from match-action tables.
        MAT_READ_ENABLE       : boolean        := true;
        -- Target device.
        DEVICE                : string         := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- =========================================================================
        -- RX AXI INTERFACE
        -- =========================================================================
        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TDEST     : out std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic;

        -- =========================================================================
        -- PROTOCOL HEADERS
        -- =========================================================================
        HDR_MAC          : in  std_logic_vector(MAC_HDR_W-1 downto 0);
        HDR_MAC_VLD      : in  std_logic;
        HDR_VLAN1        : in  std_logic_vector(VLAN_HDR_W-1 downto 0);
        HDR_VLAN1_VLD    : in  std_logic;
        HDR_VLAN2        : in  std_logic_vector(VLAN_HDR_W-1 downto 0);
        HDR_VLAN2_VLD    : in  std_logic;
        HEADERS_SRC_RDY  : in  std_logic;

        -- =========================================================================
        -- MATCH-ACTION TABLES READ/WRITE INTERFACE
        -- =========================================================================
        MAT_READ_ADDR    : in  std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
        MAT_READ_EN      : in  std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_READ_RDY     : out std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_READ_VLD     : out std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_READ_DATA    : out std_logic_vector(CONFIG_SIZE*CONFIG_MAX_DATA_WIDTH-1 downto 0) := (others => '0');
        MAT_READ_MASK    : out std_logic_vector(CONFIG_SIZE*CONFIG_MAX_DATA_WIDTH-1 downto 0) := (others => '0');
        MAT_READ_ACTION  : out std_logic_vector(CONFIG_SIZE*AXI_TDEST_WIDTH-1 downto 0);

        MAT_WRITE_ADDR   : in  std_logic_vector(CONFIG_MAX_ADDR_WIDTH-1 downto 0);
        MAT_WRITE_EN     : in  std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_WRITE_RDY    : out std_logic_vector(CONFIG_SIZE-1 downto 0);
        MAT_WRITE_DATA   : in  std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_WRITE_MASK   : in  std_logic_vector(CONFIG_MAX_DATA_WIDTH-1 downto 0);
        MAT_WRITE_ACTION : in  std_logic_vector(AXI_TDEST_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of AXIS_DISPATCHER is

    constant LATENCY_MAT       : natural := 4;
    constant LATENCY_RESOLVER  : natural := 0;
    constant LATENCY_TOTAL     : natural := LATENCY_MAT + LATENCY_RESOLVER;

    signal s_rx_axi_tvalid     : std_logic;
    signal s_rx_axi_tready     : std_logic;
    signal s_tx_axi_tvalid     : std_logic;
    signal s_tx_axi_tready     : std_logic;

    signal s_mat_match_rdy     : std_logic_vector(CONFIG_SIZE-1 downto 0);
    signal s_mat_action_vld    : std_logic_vector(CONFIG_SIZE-1 downto 0);
    signal s_mat_action        : slv_array_t(CONFIG_SIZE-1 downto 0)(AXI_TDEST_WIDTH-1 downto 0);

    signal s_buffer_fill       : std_logic;
    signal s_buffer_flush      : std_logic;
    signal s_buffer_full       : std_logic;
    signal s_buffer_empty      : std_logic;

    signal s_action_res        : std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);
    signal s_action_res_buffer : std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);
    signal s_action_res_mux    : std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);
    signal s_action_res_reg    : std_logic_vector(AXI_TDEST_WIDTH-1 downto 0);

    signal s_tx_start_of_frame : std_logic;
    signal s_tx_end_of_frame   : std_logic;
    signal s_tx_in_frame_reg   : std_logic;

    type   mode is (NORMAL, STOP, RECOVER);
    signal p_state : mode := NORMAL;
    signal n_state : mode;

    signal s_hdr_vlan1_arr      : slv_array_t(VLAN_HDR_W/8-1 downto 0)(8-1 downto 0);
    signal s_hdr_vlan1_swap_arr : slv_array_t(VLAN_HDR_W/8-1 downto 0)(8-1 downto 0);
    signal s_hdr_vlan1_swap     : std_logic_vector(VLAN_HDR_W-1 downto 0);
    signal s_hdr_vlan2_arr      : slv_array_t(VLAN_HDR_W/8-1 downto 0)(8-1 downto 0);
    signal s_hdr_vlan2_swap_arr : slv_array_t(VLAN_HDR_W/8-1 downto 0)(8-1 downto 0);
    signal s_hdr_vlan2_swap     : std_logic_vector(VLAN_HDR_W-1 downto 0);

    function reverse (slv: std_logic_vector) return std_logic_vector is
        variable slv_rev : std_logic_vector(slv'length-1 downto 0);
    begin
        for i in 0 to slv'length-1 loop
            slv_rev(i) := slv(slv'high-i);
        end loop;
        return slv_rev;
    end function;

begin

    state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                p_state <= NORMAL;
            else
                p_state <= n_state;
            end if;
        end if;
    end process;

    state_logic_p : process (p_state, TX_AXI_TREADY, s_buffer_full, s_buffer_empty)
    begin
        n_state <= p_state;
        case p_state is
            when NORMAL =>
                if (TX_AXI_TREADY = '0') then
                    n_state <= STOP;
                end if;
            when STOP =>
                if (s_buffer_full = '1') then
                    n_state <= RECOVER;
                end if;
            when RECOVER =>
                if (s_buffer_empty = '1') then
                    n_state <= NORMAL;
                end if;
            when others =>
                null;
        end case;
    end process;

    state_signals_p : process (p_state, RX_AXI_TVALID, TX_AXI_TREADY, s_rx_axi_tready, s_tx_axi_tvalid, s_mat_match_rdy)
    begin
        s_buffer_fill   <= not TX_AXI_TREADY;
        s_buffer_flush  <= '0';
        RX_AXI_TREADY   <= s_rx_axi_tready and (and s_mat_match_rdy);
        s_rx_axi_tvalid <= RX_AXI_TVALID;
        TX_AXI_TVALID   <= s_tx_axi_tvalid;
        s_tx_axi_tready <= TX_AXI_TREADY;
        case p_state is
            when STOP =>
                s_buffer_fill   <= '1';
                RX_AXI_TREADY   <= '0';
                s_rx_axi_tvalid <= '0';
                TX_AXI_TVALID   <= '0';
                s_tx_axi_tready <= '0';
            when RECOVER =>
                s_buffer_fill   <= '0';
                s_buffer_flush  <= '1';
                RX_AXI_TREADY   <= '0';
                s_rx_axi_tvalid <= '0';
            when others =>
                null;
        end case;
    end process;

    axis_sync_regs_i : entity work.AXIS_FIFO
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        AXI_TUSER_WIDTH => 0,
        ITEMS           => LATENCY_TOTAL,
        FIFO_TYPE       => 0
    )
    port map (
        CLK             => CLK,
        RESET           => RESET,
        RX_AXI_TDATA    => RX_AXI_TDATA,
        RX_AXI_TKEEP    => RX_AXI_TKEEP,
        RX_AXI_TUSER    => (others => '0'),
        RX_AXI_TLAST    => RX_AXI_TLAST,
        RX_AXI_TVALID   => s_rx_axi_tvalid,
        RX_AXI_TREADY   => s_rx_axi_tready,
        TX_AXI_TDATA    => TX_AXI_TDATA,
        TX_AXI_TKEEP    => TX_AXI_TKEEP,
        TX_AXI_TUSER    => open,
        TX_AXI_TLAST    => TX_AXI_TLAST,
        TX_AXI_TVALID   => s_tx_axi_tvalid,
        TX_AXI_TREADY   => s_tx_axi_tready
    );

    s_hdr_vlan1_arr  <= slv_array_deser(HDR_VLAN1, VLAN_HDR_W/8);
    s_hdr_vlan1_swap <= slv_array_ser(s_hdr_vlan1_swap_arr);
    s_hdr_vlan2_arr  <= slv_array_deser(HDR_VLAN2, VLAN_HDR_W/8);
    s_hdr_vlan2_swap <= slv_array_ser(s_hdr_vlan2_swap_arr);
    hdr_vlan_bytes_g : for i in 0 to VLAN_HDR_W/8-1 generate
        hdr_vlan_bitswap_g : for j in 0 to 8-1 generate
            s_hdr_vlan1_swap_arr(i)(j) <= s_hdr_vlan1_arr(i)(8-1-j);
            s_hdr_vlan2_swap_arr(i)(j) <= s_hdr_vlan2_arr(i)(8-1-j);
        end generate;
    end generate;

    match_action_tables_g : for i in 0 to CONFIG_SIZE-1 generate
        constant MAT_ITEMS       : natural         := CONFIG(i).match_items;
        constant MAT_ADDR_WIDTH  : natural         := log2(MAT_ITEMS);
        constant MAT_DATA_WIDTH  : natural         := mat_match_width(CONFIG(i));
        constant MAT_DATA_BASES  : natural_array_t := mat_match_data_bases(CONFIG(i));

        signal s_mat_match_data  : std_logic_vector(MAT_DATA_WIDTH-1 downto 0);
        signal s_mat_match_en    : std_logic_vector(CONFIG(i).match_num_fields-1 downto 0);
    begin

        mat_match_data_g : for j in 0 to CONFIG(i).match_num_fields-1 generate
            subtype MATCH_DATA_RANGE is natural range MAT_DATA_BASES(j+1)-1 downto MAT_DATA_BASES(j);
            subtype PROTO_HDR_RANGE  is natural range CONFIG(i).match_range_highs(j) downto CONFIG(i).match_range_lows(j);
        begin
            mat_match_protocols_g : case CONFIG(i).match_protocols(j) generate
                when MATCH_PROTOCOL_MAC     =>
                    s_mat_match_data(MATCH_DATA_RANGE) <= HDR_MAC(PROTO_HDR_RANGE);
                    s_mat_match_en(j)                  <= HDR_MAC_VLD;
                when MATCH_PROTOCOL_VLAN_Q  =>
                    s_mat_match_data(MATCH_DATA_RANGE) <= reverse(s_hdr_vlan1_swap(PROTO_HDR_RANGE));
                    s_mat_match_en(j)                  <= HDR_VLAN1_VLD;
                when MATCH_PROTOCOL_VLAN_AD =>
                    s_mat_match_data(MATCH_DATA_RANGE) <= reverse(s_hdr_vlan2_swap(PROTO_HDR_RANGE));
                    s_mat_match_en(j)                  <= HDR_VLAN2_VLD;
                when others                 =>
                    s_mat_match_data(MATCH_DATA_RANGE) <= (others => '0');
                    s_mat_match_en(j)                  <= '0';
            end generate;
        end generate;

        match_action_table_i : entity work.MATCH_ACTION_TABLE
        generic map (
            ITEMS             => MAT_ITEMS,
            MATCH_DATA_WIDTH  => MAT_DATA_WIDTH,
            ACTION_DATA_WIDTH => AXI_TDEST_WIDTH,
            READ_ENABLE       => MAT_READ_ENABLE,
            DEVICE            => DEVICE
        )
        port map (
            CLK          => CLK,
            RESET        => RESET,
            READ_ADDR    => MAT_READ_ADDR(MAT_ADDR_WIDTH-1 downto 0),
            READ_EN      => MAT_READ_EN(i),
            READ_RDY     => MAT_READ_RDY(i),
            READ_VLD     => MAT_READ_VLD(i),
            READ_DATA    => MAT_READ_DATA(i*CONFIG_MAX_DATA_WIDTH+MAT_DATA_WIDTH-1 downto i*CONFIG_MAX_DATA_WIDTH),
            READ_MASK    => MAT_READ_MASK(i*CONFIG_MAX_DATA_WIDTH+MAT_DATA_WIDTH-1 downto i*CONFIG_MAX_DATA_WIDTH),
            READ_ACTION  => MAT_READ_ACTION((i+1)*AXI_TDEST_WIDTH-1 downto i*AXI_TDEST_WIDTH),
            WRITE_ADDR   => MAT_WRITE_ADDR(MAT_ADDR_WIDTH-1 downto 0),
            WRITE_EN     => MAT_WRITE_EN(i),
            WRITE_RDY    => MAT_WRITE_RDY(i),
            WRITE_DATA   => MAT_WRITE_DATA(MAT_DATA_WIDTH-1 downto 0),
            WRITE_MASK   => MAT_WRITE_MASK(MAT_DATA_WIDTH-1 downto 0),
            WRITE_ACTION => MAT_WRITE_ACTION,
            MATCH_DATA   => s_mat_match_data,
            MATCH_EN     => RX_AXI_TREADY and HEADERS_SRC_RDY and (and s_mat_match_en),
            MATCH_RDY    => s_mat_match_rdy(i),
            ACTION_VLD   => s_mat_action_vld(i),
            ACTION       => s_mat_action(i)
        );

    end generate;

    action_resolver_i : entity work.RESOLVER
    generic map (
        DATA_WIDTH     => AXI_TDEST_WIDTH,
        SEL_WIDTH      => CONFIG_SIZE,
        ACTION_DEFAULT => 0,
        DEVICE         => DEVICE
    )
    port map (
        ACTION_IN_VLD  => s_mat_action_vld,
        ACTION_IN      => slv_array_ser(s_mat_action),
        ACTION_OUT     => s_action_res
    );

    s_action_buffer_i : entity work.FIFOX
    generic map (
        DATA_WIDTH => AXI_TDEST_WIDTH,
        ITEMS      => LATENCY_TOTAL,
        DEVICE     => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,
        DI         => s_action_res,
        WR         => s_buffer_fill,
        FULL       => s_buffer_full,
        DO         => s_action_res_buffer,
        RD         => s_buffer_flush and TX_AXI_TREADY,
        EMPTY      => s_buffer_empty
    );

    s_action_res_mux <= s_action_res_buffer when s_buffer_flush = '1' else s_action_res;

    s_tx_start_of_frame <= TX_AXI_TVALID and TX_AXI_TREADY and not s_tx_in_frame_reg;
    s_tx_end_of_frame   <= TX_AXI_TVALID and TX_AXI_TREADY and TX_AXI_TLAST;
    s_tx_in_frame_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or s_tx_end_of_frame = '1') then
                s_tx_in_frame_reg <= '0';
            elsif (s_tx_start_of_frame = '1') then
                s_tx_in_frame_reg <= '1';
                s_action_res_reg  <= s_action_res_mux;
            end if;
        end if;
    end process;

    TX_AXI_TDEST <= s_action_res_reg when s_tx_in_frame_reg = '1' else s_action_res_mux;

end architecture;
