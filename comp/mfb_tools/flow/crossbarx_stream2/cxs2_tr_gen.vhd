-- cxs2_tr_gen.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_CROSSBARX_STREAM2_TR_GEN is
generic (
    MFB_REGIONS : natural := 4;
    PKT_MTU     : natural := 2**14;
    USERMETA_W  : natural := 32;
    MOD_W       : natural := 7;
    RXBUF_BYTES : natural := 32768;
    STREAMS     : natural := 4;
    STREAM_ID   : natural := 0;
    PKT_ID_W    : natural := 9;
    PLAN_META_W : natural := MOD_W + 1 + USERMETA_W + log2(RXBUF_BYTES) + STREAMS + PKT_ID_W;
    DEVICE      : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK                    : in  std_logic;
    RESET                  : in  std_logic;

    -- =========================================================================
    -- INPUT MVB INTERFACE WITH RX INSTRUCTION AND METADATA
    -- =========================================================================
    RX_MVB_USERMETA        : in  slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    RX_MVB_DISCARD         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_MOD_SOF_SIZE    : in  slv_array_t(MFB_REGIONS-1 downto 0)(MOD_W-1 downto 0);
    RX_MVB_MOD_SOF_TYPE    : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_MOD_SOF_EN      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_MOD_EOF_SIZE    : in  slv_array_t(MFB_REGIONS-1 downto 0)(MOD_W-1 downto 0);
    RX_MVB_MOD_EOF_TYPE    : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_MOD_EOF_EN      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_VLD             : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_SRC_RDY         : in  std_logic;
    RX_MVB_DST_RDY         : out std_logic;

    -- =========================================================================
    -- INPUT MVB INTERFACE WITH RX BUFFER TRANSACTIONS
    -- =========================================================================
    RXBUF_MVB_PKT_ID       : in  slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    RXBUF_MVB_EOF_ADDR     : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);
    RXBUF_MVB_LEN          : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    RXBUF_MVB_VLD          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RXBUF_MVB_SRC_RDY      : in  std_logic;
    RXBUF_MVB_DST_RDY      : out std_logic;

    -- =========================================================================
    -- OUTPUT MVB INTERFACE WITH DISCARD ID
    -- =========================================================================
    DIS_MVB_PKT_ID         : out slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    DIS_MVB_VLD            : out std_logic_vector(MFB_REGIONS-1 downto 0);
    DIS_MVB_SRC_RDY        : out std_logic;

    -- =========================================================================
    -- OUTPUT INTERFACE WITH TRANSACTIONS FOR PLANNER
    -- =========================================================================
    GEN_TR_MVB_USERMETA    : out slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    GEN_TR_MVB_RXBUF_ADDR  : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);
    GEN_TR_MVB_LEN         : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    GEN_TR_MVB_PLANMETA    : out slv_array_t(MFB_REGIONS-1 downto 0)(PLAN_META_W-1 downto 0);
    GEN_TR_MVB_VLD         : out std_logic_vector(MFB_REGIONS-1 downto 0);
    GEN_TR_MVB_SRC_RDY     : out std_logic;
    GEN_TR_MVB_AFULL       : in  std_logic
);
end entity;

architecture FULL of MFB_CROSSBARX_STREAM2_TR_GEN is

    constant RX_DATA_W    : natural := USERMETA_W + MOD_W + MOD_W + 3;
    constant RXBUF_DATA_W : natural := PKT_ID_W + log2(RXBUF_BYTES) + log2(PKT_MTU+1);

    signal rx_mvb_sof_size        : slv_array_t(MFB_REGIONS-1 downto 0)(MOD_W-1 downto 0);
    signal rx_mvb_eof_size        : slv_array_t(MFB_REGIONS-1 downto 0)(MOD_W-1 downto 0);
    signal rx_mvb_data_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(RX_DATA_W-1 downto 0);
    signal rxbuf_mvb_data_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(RXBUF_DATA_W-1 downto 0);

    signal me_mvb_data_rx         : std_logic_vector(MFB_REGIONS*RX_DATA_W-1 downto 0);
    signal me_mvb_data_buf        : std_logic_vector(MFB_REGIONS*RXBUF_DATA_W-1 downto 0);
    signal me_mvb_data_rx_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(RX_DATA_W-1 downto 0);
    signal me_mvb_data_buf_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(RXBUF_DATA_W-1 downto 0);
    signal me_mvb_vld             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal me_mvb_src_rdy         : std_logic;
    signal me_mvb_dst_rdy         : std_logic;

    signal me_mvb_discard         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal me_mvb_ext_sof_type    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal me_mvb_ext_sof_size    : slv_array_t(MFB_REGIONS-1 downto 0)(MOD_W-1 downto 0);
    signal me_mvb_ext_eof_type    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal me_mvb_ext_eof_size    : slv_array_t(MFB_REGIONS-1 downto 0)(MOD_W-1 downto 0);
    signal me_mvb_pkt_id          : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    signal me_mvb_streams         : slv_array_t(MFB_REGIONS-1 downto 0)(STREAMS-1 downto 0);
    signal me_mvb_usermeta        : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    signal me_mvb_len             : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal me_mvb_eof_addr        : slv_array_t(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);
    signal me_mvb_rxbuf_addr      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);

    signal mod_mvb_pkt_id         : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    signal mod_mvb_streams        : slv_array_t(MFB_REGIONS-1 downto 0)(STREAMS-1 downto 0);
    signal mod_mvb_usermeta       : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    signal mod_mvb_len            : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal mod_mvb_len2           : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal mod_mvb_rxbuf_addr     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);
    signal mod_mvb_planmeta       : slv_array_t(MFB_REGIONS-1 downto 0)(PLAN_META_W-1 downto 0);
    signal mod_mvb_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mod_mvb_dis_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mod_mvb_src_rdy        : std_logic;
    signal mod_mvb_dst_rdy        : std_logic;

    signal dbg_cnt_rx_mvb         : unsigned(64-1 downto 0);
    signal dbg_cnt_rxbuf_mvb      : unsigned(64-1 downto 0);
    signal dbg_cnt_gen_tr_mvb     : unsigned(64-1 downto 0);

begin

    -- =========================================================================
    -- INPUT MVB ITEM MERGER
    -- =========================================================================

    rx_mvb_data_arr_g : for i in 0 to MFB_REGIONS-1 generate
        rx_mvb_sof_size(i) <= RX_MVB_MOD_SOF_SIZE(i) when (RX_MVB_MOD_SOF_EN(i) = '1') else (others => '0');
        rx_mvb_eof_size(i) <= RX_MVB_MOD_EOF_SIZE(i) when (RX_MVB_MOD_EOF_EN(i) = '1') else (others => '0');

        rx_mvb_data_arr(i)    <= RX_MVB_USERMETA(i) & rx_mvb_eof_size(i) & RX_MVB_MOD_EOF_TYPE(i) & rx_mvb_sof_size(i) & RX_MVB_MOD_SOF_TYPE(i) & RX_MVB_DISCARD(i);
        rxbuf_mvb_data_arr(i) <= RXBUF_MVB_PKT_ID(i) & RXBUF_MVB_EOF_ADDR(i) & RXBUF_MVB_LEN(i);
    end generate;

    mvb_merge_i : entity work.MVB_MERGE_ITEMS
    generic map(
        RX0_ITEMS      => MFB_REGIONS,
        RX0_ITEM_WIDTH => RXBUF_DATA_W,
        RX1_ITEMS      => MFB_REGIONS,
        RX1_ITEM_WIDTH => RX_DATA_W,
        RX0_FIFO_EN    => True,
        FIFO_DEPTH     => 32,
        OUTPUT_REG     => True,
        DEVICE         => DEVICE
    )
    port map(
        CLK         => CLK,
        RESET       => RESET,

        RX0_DATA    => slv_array_ser(rxbuf_mvb_data_arr),
        RX0_VLD     => RXBUF_MVB_VLD,
        RX0_SRC_RDY => RXBUF_MVB_SRC_RDY,
        RX0_DST_RDY => RXBUF_MVB_DST_RDY,

        RX1_DATA    => slv_array_ser(rx_mvb_data_arr),
        RX1_VLD     => RX_MVB_VLD,
        RX1_SRC_RDY => RX_MVB_SRC_RDY,
        RX1_DST_RDY => RX_MVB_DST_RDY,

        TX_DATA     => open,
        TX_DATA0    => me_mvb_data_buf,
        TX_DATA1    => me_mvb_data_rx,
        TX_VLD      => me_mvb_vld,
        TX_SRC_RDY  => me_mvb_src_rdy,
        TX_DST_RDY  => mod_mvb_dst_rdy
    );

    me_mvb_data_rx_arr  <= slv_array_deser(me_mvb_data_rx, MFB_REGIONS);
    me_mvb_data_buf_arr <= slv_array_deser(me_mvb_data_buf, MFB_REGIONS);

    me_arr_g : for i in 0 to MFB_REGIONS-1 generate
        process (all)
        begin
            me_mvb_streams(i) <= (others => '0');
            me_mvb_streams(i)(STREAM_ID) <= '1';
        end process;

        me_mvb_discard(i)        <= me_mvb_data_rx_arr(i)(0);
        me_mvb_ext_sof_type(i)   <= me_mvb_data_rx_arr(i)(1);
        me_mvb_ext_sof_size(i)   <= me_mvb_data_rx_arr(i)(MOD_W+2-1 downto 2);
        me_mvb_ext_eof_type(i)   <= me_mvb_data_rx_arr(i)(MOD_W+2);
        me_mvb_ext_eof_size(i)   <= me_mvb_data_rx_arr(i)(MOD_W+MOD_W+3-1 downto MOD_W+3);
        me_mvb_usermeta(i)       <= me_mvb_data_rx_arr(i)(USERMETA_W+MOD_W+MOD_W+3-1 downto MOD_W+MOD_W+3);

        me_mvb_len(i)            <= me_mvb_data_buf_arr(i)(log2(PKT_MTU+1)-1 downto 0);
        me_mvb_eof_addr(i)       <= me_mvb_data_buf_arr(i)(log2(RXBUF_BYTES)+log2(PKT_MTU+1)-1 downto log2(PKT_MTU+1));
        me_mvb_pkt_id(i)         <= me_mvb_data_buf_arr(i)(PKT_ID_W+log2(RXBUF_BYTES)+log2(PKT_MTU+1)-1 downto log2(RXBUF_BYTES)+log2(PKT_MTU+1));

        me_mvb_rxbuf_addr(i)     <= std_logic_vector(unsigned(me_mvb_eof_addr(i)) - unsigned(me_mvb_len(i)));
    end generate;

    -- =========================================================================
    -- PRE PLANNER MODIFY LOGIC
    -- =========================================================================

    mod_arr_g : for i in 0 to MFB_REGIONS-1 generate
        mod_mvb_streams(i)    <= me_mvb_streams(i);
        mod_mvb_usermeta(i)   <= me_mvb_usermeta(i);

        process (all)
        begin
            if (me_mvb_ext_sof_type(i) = '1') then -- trim sof
                mod_mvb_rxbuf_addr(i) <= std_logic_vector(unsigned(me_mvb_rxbuf_addr(i)) + unsigned(me_mvb_ext_sof_size(i)));
                mod_mvb_len(i)        <= std_logic_vector(unsigned(me_mvb_len(i)) - unsigned(me_mvb_ext_sof_size(i)));
            else -- extend sof
                mod_mvb_rxbuf_addr(i) <= me_mvb_rxbuf_addr(i); --std_logic_vector(unsigned(me_mvb_rxbuf_addr(i)) - unsigned(me_mvb_ext_sof_size(i)));
                mod_mvb_len(i)        <= std_logic_vector(unsigned(me_mvb_len(i)) + unsigned(me_mvb_ext_sof_size(i)));
            end if;
        end process;

        process (all)
        begin
            if (me_mvb_ext_eof_type(i) = '1') then -- trim eof
                mod_mvb_len2(i) <= std_logic_vector(unsigned(mod_mvb_len(i)) - unsigned(me_mvb_ext_eof_size(i)));
            else -- extend eof
                mod_mvb_len2(i) <= std_logic_vector(unsigned(mod_mvb_len(i)) + unsigned(me_mvb_ext_eof_size(i)));
            end if;
        end process;

        mod_mvb_pkt_id(i)     <= me_mvb_pkt_id(i);
        mod_mvb_vld(i)        <= me_mvb_src_rdy and (me_mvb_vld(i) and not me_mvb_discard(i));
        mod_mvb_dis_vld(i)    <= me_mvb_src_rdy and (me_mvb_vld(i) and me_mvb_discard(i));

        -- pack into meta signal for packet planner
        mod_mvb_planmeta(i) <= me_mvb_ext_sof_size(i) & me_mvb_ext_sof_type(i) & mod_mvb_pkt_id(i) & mod_mvb_streams(i) & mod_mvb_rxbuf_addr(i) & mod_mvb_usermeta(i);
    end generate;

    mod_mvb_src_rdy <= (or mod_mvb_vld);

    -- =========================================================================
    -- OUTPUT ASSIGMENT
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            DIS_MVB_PKT_ID   <= mod_mvb_pkt_id;
            DIS_MVB_VLD      <= mod_mvb_dis_vld;
            DIS_MVB_SRC_RDY  <= (or mod_mvb_dis_vld);
            if (RESET = '1') then
                DIS_MVB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    mod_mvb_dst_rdy <= not GEN_TR_MVB_AFULL;

    GEN_TR_MVB_USERMETA   <= mod_mvb_usermeta;
    GEN_TR_MVB_RXBUF_ADDR <= mod_mvb_rxbuf_addr;
    GEN_TR_MVB_LEN        <= mod_mvb_len2;
    GEN_TR_MVB_PLANMETA   <= mod_mvb_planmeta;
    GEN_TR_MVB_VLD        <= mod_mvb_vld;
    GEN_TR_MVB_SRC_RDY    <= mod_mvb_src_rdy and not GEN_TR_MVB_AFULL;

    -- =========================================================================
    -- DEBUG LOGIC
    -- =========================================================================

    --pragma synthesis_off
    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_cnt_rx_mvb <= (others => '0');
            elsif (RX_MVB_SRC_RDY = '1' and RX_MVB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RX_MVB_VLD(i);
                end loop;
                dbg_cnt_rx_mvb <= dbg_cnt_rx_mvb + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_cnt_rxbuf_mvb <= (others => '0');
            elsif (RXBUF_MVB_SRC_RDY = '1' and RXBUF_MVB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RXBUF_MVB_VLD(i);
                end loop;
                dbg_cnt_rxbuf_mvb <= dbg_cnt_rxbuf_mvb + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_cnt_gen_tr_mvb <= (others => '0');
            elsif (GEN_TR_MVB_SRC_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + GEN_TR_MVB_VLD(i);
                end loop;
                dbg_cnt_gen_tr_mvb <= dbg_cnt_gen_tr_mvb + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;
    --pragma synthesis_on

end architecture;
