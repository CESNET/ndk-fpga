-- op_manager.vhd: AXIS_OP_MANAGER component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity AXIS_OP_MANAGER is
    generic (
        -- Number of input ports.
        NUM_PORTS          : natural        := 2;
        -- Depth of individual virtual input queues.
        NUM_ITEMS_PER_PORT : integer_vector := (0 => 16, 1 => 16);
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH    : natural        := 512;
        -- AXI-Stream user data width in bits.
        AXI_TUSER_WIDTH    : natural        := 0;
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
        RX_AXI_TUSER    : in  std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST    : in  std_logic;
        RX_AXI_TVALID   : in  std_logic;
        RX_AXI_TREADY   : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER    : out std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        TX_AXI_TLAST    : out std_logic;
        TX_AXI_TVALID   : out std_logic;
        TX_AXI_TREADY   : in  std_logic;

        -- =========================================================================
        -- iSLIP CONTROL INTERFACE
        -- =========================================================================
        OP_CONN_VLD     : in  std_logic;
        OP_CONN_SEL     : in  std_logic_vector(log2(NUM_PORTS)-1 downto 0)
    );
end entity;

architecture FULL of AXIS_OP_MANAGER is

    signal s_rx_axi_tvalid         : std_logic;
    signal s_rx_axi_transfer_tlast : std_logic;
    signal s_tx_axi_transfer_tlast : std_logic;
    signal s_op_conn_sel_hot_en    : std_logic_vector(NUM_PORTS-1 downto 0);

    constant FRAME_CNT_WIDTH       : integer := log2(max(NUM_ITEMS_PER_PORT))+1;
    signal s_viq_frame_cnt_arr     : slv_array_t(NUM_PORTS-1 downto 0)(FRAME_CNT_WIDTH-1 downto 0);
    signal s_viq_not_empty_arr     : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_viq_next_hot          : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_viq_next_hot_reg      : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_viq_next              : std_logic_vector(log2(NUM_PORTS)-1 downto 0);
    signal s_viq_next_vld          : std_logic;

begin

    s_rx_axi_tvalid         <= RX_AXI_TVALID and OP_CONN_VLD;
    s_rx_axi_transfer_tlast <= s_rx_axi_tvalid and RX_AXI_TREADY and RX_AXI_TLAST;
    s_tx_axi_transfer_tlast <= TX_AXI_TVALID and TX_AXI_TREADY and TX_AXI_TLAST;

    -- TODO: optimize using some kind of DP memory
    viq_manager_i : entity work.AXIS_VOQ_MANAGER
    generic map (
        NUM_PORTS          => NUM_PORTS,
        NUM_ITEMS_PER_PORT => NUM_ITEMS_PER_PORT,
        AXI_TDATA_WIDTH    => AXI_TDATA_WIDTH,
        AXI_TDEST_WIDTH    => log2(NUM_PORTS),
        DEVICE             => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,
        RX_AXI_TDATA   => RX_AXI_TDATA,
        RX_AXI_TKEEP   => RX_AXI_TKEEP,
        RX_AXI_TDEST   => OP_CONN_SEL,
        RX_AXI_TLAST   => RX_AXI_TLAST,
        RX_AXI_TVALID  => s_rx_axi_tvalid,
        RX_AXI_TREADY  => RX_AXI_TREADY,
        TX_AXI_TDATA   => TX_AXI_TDATA,
        TX_AXI_TKEEP   => TX_AXI_TKEEP,
        TX_AXI_TLAST   => TX_AXI_TLAST,
        TX_AXI_TVALID  => TX_AXI_TVALID,
        TX_AXI_TREADY  => TX_AXI_TREADY,
        DEST_REQ_VEC   => open,
        DEST_REQ_SIZES => open,
        VOQ_CONN_VLD   => s_viq_next_vld,
        VOQ_CONN_SEL   => s_viq_next
    );

    op_conn_sel_dec_i : entity work.DEC1FN_ENABLE
    generic map (
        ITEMS => NUM_PORTS
    )
    port map (
        ADDR   => OP_CONN_SEL,
        ENABLE => OP_CONN_VLD,
        DO     => s_op_conn_sel_hot_en
    );

    viq_frame_cnt_regs_g : for i in 0 to NUM_PORTS-1 generate
        signal s_viq_frame_cnt_inc : std_logic;
        signal s_viq_frame_cnt_dec : std_logic;
    begin
        s_viq_frame_cnt_inc <= s_op_conn_sel_hot_en(i) and s_rx_axi_transfer_tlast;
        s_viq_frame_cnt_dec <= s_viq_next_hot(i) and s_tx_axi_transfer_tlast;
        frame_cnt_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_viq_frame_cnt_arr(i) <= (others => '0');
                elsif (s_viq_frame_cnt_inc = '1' and s_viq_frame_cnt_dec = '0') then
                    s_viq_frame_cnt_arr(i) <= std_logic_vector(unsigned(s_viq_frame_cnt_arr(i)) + 1);
                elsif (s_viq_frame_cnt_inc = '0' and s_viq_frame_cnt_dec = '1') then
                    s_viq_frame_cnt_arr(i) <= std_logic_vector(unsigned(s_viq_frame_cnt_arr(i)) - 1);
                end if;
            end if;
        end process;
        s_viq_not_empty_arr(i) <= or s_viq_frame_cnt_arr(i);
    end generate;

    viq_arbiter_i : entity work.ARBITER
    generic map (
        NUM_PORTS => NUM_PORTS
    )
    port map (
        CLK          => CLK,
        RESET        => RESET,
        REQ_VECTOR   => s_viq_not_empty_arr and s_viq_next_hot_reg,
        PRIORITY_INC => s_tx_axi_transfer_tlast,
        REQ_ACCEPT   => s_viq_next_hot
    );

    viq_next_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or s_tx_axi_transfer_tlast = '1') then
                s_viq_next_hot_reg <= (others => '1');
            elsif (s_viq_next_vld = '1') then
                s_viq_next_hot_reg <= s_viq_next_hot;
            end if;
        end if;
    end process;

    viq_next_enc_i : entity work.GEN_ENC
    generic map (
        ITEMS  => NUM_PORTS,
        DEVICE => DEVICE
    )
    port map (
        DI   => s_viq_next_hot,
        ADDR => s_viq_next
    );
    s_viq_next_vld <= or s_viq_next_hot;

end architecture;
