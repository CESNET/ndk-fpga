-- crossbarx_stream2.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The MFB_CROSSBARX_STREAM2 module uses data copying between two buffers to
-- rearrange packets on the MFB bus. It modifies
-- (extends/trims at the beginning or end) and discards selected packets.
-- The user must ensure that the final packet length is not less than 60B.
-- Future features include the support for multiple input streams (merging)
-- and packet duplication.
entity MFB_CROSSBARX_STREAM2 is
generic (
    -- IN_STREAMS must be 1 for now!!!
    IN_STREAMS      : natural := 1;
    -- The number of MFB regions
    MFB_REGIONS     : natural := 4;
    -- MFB region size in blocks, must be power of two
    MFB_REGION_SIZE : natural := 8;
    -- MFB block size in items, must be 8
    MFB_BLOCK_SIZE  : natural := 8;
    -- MFB item size in bits, must be 8
    MFB_ITEM_WIDTH  : natural := 8;
    -- Maximum size of a MFB frame (in bytes)
    PKT_MTU         : natural := 2**14;
    -- The width determines the total number of packet IDs
    -- that the component can handle simultaneously
    PKT_ID_WIDTH    : natural := 10;
    -- The width determines the maximum size of packet modifications
    MOD_WIDTH       : natural := 7;
    -- Width of User Metadata information
    USERMETA_WIDTH  : natural := 32;
    -- Target device: AGILEX, STRATIX10, ULTRASCALE,...
    DEVICE          : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK                    : in  std_logic;
    CLK_X2                 : in  std_logic;
    RESET                  : in  std_logic;

    -- =========================================================================
    -- RX MFB+MVB interface
    -- =========================================================================
    RX_MVB_USERMETA        : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    -- Flag specifying packets to drop
    RX_MVB_DISCARD         : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    -- Size of packet SOF expansion/truncation in MFB items, valid with ``RX_MVB_MOD_SOF_EN``
    RX_MVB_MOD_SOF_SIZE    : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*MOD_WIDTH-1 downto 0);
    -- SOF packet modification type: 0 = expansion, 1 = truncation, valid with ``RX_MVB_MOD_SOF_EN``
    RX_MVB_MOD_SOF_TYPE    : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    -- Enable modification of Start of Packet (SOF)
    RX_MVB_MOD_SOF_EN      : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    -- Size of packet EOF expansion/truncation in MFB items, valid with ``RX_MVB_MOD_EOF_EN``
    RX_MVB_MOD_EOF_SIZE    : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*MOD_WIDTH-1 downto 0);
    -- EOF packet modification type: 0 = expansion, 1 = truncation, valid with ``RX_MVB_MOD_EOF_EN``
    RX_MVB_MOD_EOF_TYPE    : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    -- Enable modification of End of Packet (EOF)
    RX_MVB_MOD_EOF_EN      : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    RX_MVB_VLD             : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    RX_MVB_SRC_RDY         : in  std_logic_vector(IN_STREAMS-1 downto 0);
    RX_MVB_DST_RDY         : out std_logic_vector(IN_STREAMS-1 downto 0);

    RX_MFB_DATA            : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_SOF             : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF             : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    RX_MFB_SOF_POS         : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS         : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SRC_RDY         : in  std_logic_vector(IN_STREAMS-1 downto 0);
    RX_MFB_DST_RDY         : out std_logic_vector(IN_STREAMS-1 downto 0);

    -- =========================================================================
    --  TX MFB+MVB interface
    -- =========================================================================
    TX_MVB_USERMETA        : out std_logic_vector(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    TX_MVB_VLD             : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MVB_SRC_RDY         : out std_logic;
    TX_MVB_DST_RDY         : in  std_logic;

    TX_MFB_DATA            : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_MFB_SOF             : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF             : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SOF_POS         : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS         : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SRC_RDY         : out std_logic;
    TX_MFB_DST_RDY         : in  std_logic
);
end entity;

architecture FULL of MFB_CROSSBARX_STREAM2 is

    constant CROSSBARX_DIR : boolean := False; -- for debug only

    constant RXBUF_WORDS   : natural := 1024;
    constant RXBUF_BLOCKS  : natural := MFB_REGIONS*MFB_REGION_SIZE;
    constant RXBUF_BLOCK_W : natural := MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant RXBUF_BYTES   : natural := (RXBUF_WORDS*RXBUF_BLOCKS*RXBUF_BLOCK_W)/8;

    constant TXBUF_WORDS   : natural := 512;
    constant TXBUF_BLOCKS  : natural := MFB_REGIONS*MFB_REGION_SIZE;
    constant TXBUF_BYTES   : natural := (TXBUF_WORDS*TXBUF_BLOCKS*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8;

    constant TX_COL_W   : natural := log2(TXBUF_BYTES/(TXBUF_BLOCKS*MFB_BLOCK_SIZE));
    constant RX_COL_W   : natural := log2(RXBUF_BYTES/(RXBUF_BLOCKS*MFB_BLOCK_SIZE));
    constant TX_ROW_W   : natural := log2(TXBUF_BLOCKS*MFB_BLOCK_SIZE);
    constant RX_ROW_W   : natural := log2(RXBUF_BLOCKS*MFB_BLOCK_SIZE);

    constant CX_A_COL_W : natural := tsel(CROSSBARX_DIR, RX_COL_W, TX_COL_W);
    constant CX_A_ROW_W : natural := tsel(CROSSBARX_DIR, RX_ROW_W, TX_ROW_W);
    constant CX_B_COL_W : natural := tsel(CROSSBARX_DIR, TX_COL_W, RX_COL_W);
    constant CX_B_ROW_W : natural := tsel(CROSSBARX_DIR, TX_ROW_W, RX_ROW_W);

    constant PLAN_META_W   : natural := MOD_WIDTH + 1 + PKT_ID_WIDTH + IN_STREAMS + log2(RXBUF_BYTES) + USERMETA_WIDTH;

    signal rxbuf_mvb_pkt_id           : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal rxbuf_mvb_eof_addr         : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);
    signal rxbuf_mvb_len              : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal rxbuf_mvb_vld              : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rxbuf_mvb_src_rdy          : std_logic_vector(IN_STREAMS-1 downto 0);
    signal rxbuf_mvb_dst_rdy          : std_logic_vector(IN_STREAMS-1 downto 0);

    signal rxbuf_done_id              : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal rxbuf_done_vld             : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal rxbuf_rd_addr              : slv_array_2d_t(IN_STREAMS-1 downto 0)(RXBUF_BLOCKS-1 downto 0)(log2(RXBUF_WORDS)-1 downto 0);
    signal rxbuf_rd_data              : slv_array_2d_t(IN_STREAMS-1 downto 0)(RXBUF_BLOCKS-1 downto 0)(RXBUF_BLOCK_W-1 downto 0);

    signal rx_mvb_usermeta_arr        : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(USERMETA_WIDTH-1 downto 0);
    signal rx_mvb_mod_sof_size_arr    : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(MOD_WIDTH-1 downto 0);
    signal rx_mvb_mod_eof_size_arr    : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(MOD_WIDTH-1 downto 0);

    signal dis_mvb_pkt_id             : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal dis_mvb_vld                : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dis_mvb_src_rdy            : std_logic_vector(IN_STREAMS-1 downto 0);
    signal dis_mvb_dst_rdy            : std_logic_vector(IN_STREAMS-1 downto 0);

    signal dis_fifo_mvb_data          : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*PKT_ID_WIDTH-1 downto 0);
    signal dis_fifo_mvb_pkt_id        : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal dis_fifo_mvb_vld           : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dis_fifo_mvb_src_rdy       : std_logic_vector(IN_STREAMS-1 downto 0);
    signal dis_fifo_mvb_dst_rdy       : std_logic_vector(IN_STREAMS-1 downto 0);
    signal dis_fifo_wr_err_reg        : std_logic_vector(IN_STREAMS-1 downto 0);

    signal gen_tr_mvb_len             : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal gen_tr_mvb_planmeta        : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PLAN_META_W-1 downto 0);
    signal gen_tr_mvb_vld             : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal gen_tr_mvb_src_rdy         : std_logic_vector(IN_STREAMS-1 downto 0);
    signal gen_tr_mvb_afull           : std_logic_vector(IN_STREAMS-1 downto 0);

    signal txbuf_rd_pointer           : std_logic_vector(log2(TXBUF_BYTES)-1 downto 0);
    signal txbuf_rd_pointer_blk       : std_logic_vector(log2(TXBUF_BYTES/MFB_BLOCK_SIZE)-1 downto 0);

    signal plan_str_mvb_meta          : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PLAN_META_W-1 downto 0);
    signal plan_str_mvb_len           : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal plan_str_mvb_len2          : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal plan_str_mvb_txbuf_addr    : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    signal plan_str_mvb_txbuf_addr2   : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    signal plan_str_mvb_vld           : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal plan_str_mvb_dst_rdy       : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal plan_str_mvb_rxbuf_addr    : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(RXBUF_BYTES)-1 downto 0);
    signal plan_str_mvb_pkt_id        : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal plan_str_mvb_a_col         : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(CX_A_COL_W-1 downto 0);
    signal plan_str_mvb_mod_sof_size  : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(MOD_WIDTH-1 downto 0);
    signal plan_str_mvb_mod_sof_type  : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal plan_glb_mvb_meta          : slv_array_t(MFB_REGIONS-1 downto 0)(PLAN_META_W-1 downto 0);
    signal plan_glb_mvb_len           : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal plan_glb_mvb_txbuf_addr    : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    signal plan_glb_mvb_vld           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal plan_glb_mvb_dst_rdy       : std_logic;
    signal plan_glb_mvb_usermeta      : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_WIDTH-1 downto 0);
    signal plan_glb_mvb_streams       : slv_array_t(MFB_REGIONS-1 downto 0)(IN_STREAMS-1 downto 0);

    signal crox_instr_a_col           : slv_array_t(IN_STREAMS-1 downto 0)(CX_A_COL_W-1 downto 0);
    signal crox_instr_a_item          : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(CX_A_ROW_W-1 downto 0);
    signal crox_instr_b_col           : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(CX_B_COL_W-1 downto 0);
    signal crox_instr_b_item          : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(CX_B_ROW_W-1 downto 0);
    signal crox_instr_len             : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal crox_instr_meta            : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal crox_instr_vld             : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal crox_instr_src_rdy         : std_logic_vector(IN_STREAMS-1 downto 0);
    signal crox_instr_dst_rdy         : std_logic_vector(IN_STREAMS-1 downto 0);

    signal crox_rxbuf_rd_addr         : slv_array_t(IN_STREAMS*RXBUF_BLOCKS-1 downto 0)(log2(RXBUF_WORDS)-1 downto 0);
    signal crox_rxbuf_rd_data         : slv_array_t(IN_STREAMS*RXBUF_BLOCKS-1 downto 0)(RXBUF_BLOCK_W-1 downto 0);

    signal crox_done_meta             : slv_array_2d_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0)(PKT_ID_WIDTH-1 downto 0);
    signal crox_done_vld              : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal crox_done_src_rdy          : std_logic_vector(IN_STREAMS-1 downto 0);

    signal txbuf_done_vld             : slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal txbuf_instr_usermeta       : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_WIDTH-1 downto 0);
    signal txbuf_instr_txbuf_addr     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    signal txbuf_instr_len            : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal txbuf_instr_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal txbuf_instr_src_rdy        : std_logic;
    signal txbuf_instr_dst_rdy        : std_logic;

    signal txbuf_wr_addr              : slv_array_t(TXBUF_BLOCKS-1 downto 0)(log2(TXBUF_WORDS)-1 downto 0);
    signal txbuf_wr_data              : slv_array_t(TXBUF_BLOCKS-1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal txbuf_wr_ie                : slv_array_t(TXBUF_BLOCKS-1 downto 0)(MFB_BLOCK_SIZE-1 downto 0);
    signal txbuf_wr_en                : std_logic_vector(TXBUF_BLOCKS-1 downto 0);

    signal dbg_rx_mvb_pkt_cnt         : unsigned(64-1 downto 0);
    signal dbg_rx_mfb_pkt_cnt         : unsigned(64-1 downto 0);
    signal dbg_tx_mvb_pkt_cnt         : unsigned(64-1 downto 0);
    signal dbg_tx_mfb_pkt_cnt         : unsigned(64-1 downto 0);
    signal dbg_plan_glb_cnt           : unsigned(64-1 downto 0);
    signal dbg_crox_instr_cnt         : unsigned(64-1 downto 0);
    signal dbg_crox_done_cnt          : unsigned(64-1 downto 0);
    signal dbg_txbuf_instr_cnt        : unsigned(64-1 downto 0);

begin

    assert (IN_STREAMS = 1)
        report "CXS2: Only the input stream is currently supported!"
        severity failure;

    -- =========================================================================
    -- RX STREAM BUFFER AND LOGIC
    -- =========================================================================

    rx_stream_g: for s in 0 to IN_STREAMS-1 generate

        rx_buf_i : entity work.MFB_CROSSBARX_STREAM2_RX_BUF
        generic map(
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
            BUF_BLOCK_WIDTH => MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,
            BUF_BLOCKS      => RXBUF_BLOCKS,
            BUF_WORDS       => RXBUF_WORDS,
            BUF_BYTES       => RXBUF_BYTES,
            PKT_MTU         => PKT_MTU,
            PKT_ID_W        => PKT_ID_WIDTH,
            DEVICE          => DEVICE
        )
        port map(
            CLK              => CLK,
            CLK_X2           => CLK_X2,
            RESET            => RESET,

            RX_MFB_DATA      => RX_MFB_DATA(s),
            RX_MFB_SOF       => RX_MFB_SOF(s),
            RX_MFB_EOF       => RX_MFB_EOF(s),
            RX_MFB_SOF_POS   => RX_MFB_SOF_POS(s),
            RX_MFB_EOF_POS   => RX_MFB_EOF_POS(s),
            RX_MFB_SRC_RDY   => RX_MFB_SRC_RDY(s),
            RX_MFB_DST_RDY   => RX_MFB_DST_RDY(s),

            BUF_MVB_PKT_ID   => rxbuf_mvb_pkt_id(s),
            BUF_MVB_EOF_ADDR => rxbuf_mvb_eof_addr(s),
            BUF_MVB_LEN      => rxbuf_mvb_len(s),
            BUF_MVB_VLD      => rxbuf_mvb_vld(s),
            BUF_MVB_SRC_RDY  => rxbuf_mvb_src_rdy(s),
            BUF_MVB_DST_RDY  => rxbuf_mvb_dst_rdy(s),

            BUF_RD_DONE_ID   => rxbuf_done_id(s),
            BUF_RD_DONE_VLD  => rxbuf_done_vld(s),

            BUF_RD_ADDR      => rxbuf_rd_addr(s),
            BUF_RD_DATA      => rxbuf_rd_data(s)
        );

        rx_mvb_usermeta_arr(s)     <= slv_array_deser(RX_MVB_USERMETA(s), MFB_REGIONS);
        rx_mvb_mod_sof_size_arr(s) <= slv_array_deser(RX_MVB_MOD_SOF_SIZE(s), MFB_REGIONS);
        rx_mvb_mod_eof_size_arr(s) <= slv_array_deser(RX_MVB_MOD_EOF_SIZE(s), MFB_REGIONS);

        tr_gen_i : entity work.MFB_CROSSBARX_STREAM2_TR_GEN
        generic map(
            MFB_REGIONS => MFB_REGIONS,
            PKT_MTU     => PKT_MTU,
            USERMETA_W  => USERMETA_WIDTH,
            MOD_W       => MOD_WIDTH,
            RXBUF_BYTES => RXBUF_BYTES,
            STREAMS     => IN_STREAMS,
            STREAM_ID   => s,
            PKT_ID_W    => PKT_ID_WIDTH,
            PLAN_META_W => PLAN_META_W,
            DEVICE      => DEVICE
        )
        port map(
            CLK                    => CLK,
            RESET                  => RESET,

            RX_MVB_USERMETA        => rx_mvb_usermeta_arr(s),
            RX_MVB_DISCARD         => RX_MVB_DISCARD(s),
            RX_MVB_MOD_SOF_SIZE    => rx_mvb_mod_sof_size_arr(s),
            RX_MVB_MOD_SOF_TYPE    => RX_MVB_MOD_SOF_TYPE(s),
            RX_MVB_MOD_SOF_EN      => RX_MVB_MOD_SOF_EN(s),
            RX_MVB_MOD_EOF_SIZE    => rx_mvb_mod_eof_size_arr(s),
            RX_MVB_MOD_EOF_TYPE    => RX_MVB_MOD_EOF_TYPE(s),
            RX_MVB_MOD_EOF_EN      => RX_MVB_MOD_EOF_EN(s),
            RX_MVB_VLD             => RX_MVB_VLD(s),
            RX_MVB_SRC_RDY         => RX_MVB_SRC_RDY(s),
            RX_MVB_DST_RDY         => RX_MVB_DST_RDY(s),

            RXBUF_MVB_PKT_ID       => rxbuf_mvb_pkt_id(s),
            RXBUF_MVB_EOF_ADDR     => rxbuf_mvb_eof_addr(s),
            RXBUF_MVB_LEN          => rxbuf_mvb_len(s),
            RXBUF_MVB_VLD          => rxbuf_mvb_vld(s),
            RXBUF_MVB_SRC_RDY      => rxbuf_mvb_src_rdy(s),
            RXBUF_MVB_DST_RDY      => rxbuf_mvb_dst_rdy(s),

            DIS_MVB_PKT_ID         => dis_mvb_pkt_id(s),
            DIS_MVB_VLD            => dis_mvb_vld(s),
            DIS_MVB_SRC_RDY        => dis_mvb_src_rdy(s),

            GEN_TR_MVB_USERMETA    => open,
            GEN_TR_MVB_RXBUF_ADDR  => open,
            GEN_TR_MVB_LEN         => gen_tr_mvb_len(s),
            GEN_TR_MVB_PLANMETA    => gen_tr_mvb_planmeta(s),
            GEN_TR_MVB_VLD         => gen_tr_mvb_vld(s),
            GEN_TR_MVB_SRC_RDY     => gen_tr_mvb_src_rdy(s),
            GEN_TR_MVB_AFULL       => gen_tr_mvb_afull(s)
        );
    end generate;

    -- =========================================================================
    -- COMMON PACKET PLANNER
    -- =========================================================================

    txbuf_rd_pointer_blk <= std_logic_vector(resize_right(unsigned(txbuf_rd_pointer), txbuf_rd_pointer_blk'length));

    pkt_planner_i : entity work.PACKET_PLANNER
    generic map(
        DEVICE            => DEVICE,
        STREAMS           => IN_STREAMS,
        PKTS              => MFB_REGIONS,
        PLANNED_PKTS      => MFB_REGIONS,
        METADATA_WIDTH    => PLAN_META_W,
        SPACE_SIZE        => TXBUF_BYTES,
        PKT_SIZE          => PKT_MTU,
        GAP_SIZE          => 0,
        GAP_SIZE_MIN      => 0,
        ALIGN             => MFB_BLOCK_SIZE,
        FIFO_ITEMS        => 32,
        FIFO_AFULL_OFFSET => 4,
        STREAM_OUT_EN     => true,
        GLOBAL_OUT_EN     => true
    )
    port map(
        CLK                   => CLK,
        RESET                 => RESET,

        RX_STR_PKT_META       => gen_tr_mvb_planmeta,
        RX_STR_PKT_LEN        => gen_tr_mvb_len,
        RX_STR_PKT_VLD        => gen_tr_mvb_vld,
        RX_STR_PKT_SRC_RDY    => gen_tr_mvb_src_rdy,
        RX_STR_PKT_AFULL      => gen_tr_mvb_afull,

        SPACE_GLB_RD_PTR      => txbuf_rd_pointer_blk,

        TX_STR_PKT_META       => plan_str_mvb_meta,
        TX_STR_PKT_LEN        => plan_str_mvb_len,
        TX_STR_PKT_ADDR       => plan_str_mvb_txbuf_addr,
        TX_STR_PKT_VLD        => plan_str_mvb_vld,
        TX_STR_PKT_DST_RDY    => plan_str_mvb_dst_rdy,

        TX_GLB_PKT_META       => plan_glb_mvb_meta,
        TX_GLB_PKT_LEN        => plan_glb_mvb_len,
        TX_GLB_PKT_ADDR       => plan_glb_mvb_txbuf_addr,
        TX_GLB_PKT_VLD        => plan_glb_mvb_vld,
        TX_GLB_PKT_DST_RDY    => (others => plan_glb_mvb_dst_rdy)
    );

    plan_glb_meta_unpack_g: for i in 0 to MFB_REGIONS-1 generate
        plan_glb_mvb_usermeta(i) <= plan_glb_mvb_meta(i)(USERMETA_WIDTH-1 downto 0);
        plan_glb_mvb_streams(i)  <= plan_glb_mvb_meta(i)(IN_STREAMS+log2(RXBUF_BYTES)+USERMETA_WIDTH-1 downto log2(RXBUF_BYTES)+USERMETA_WIDTH);
    end generate;

    crox_instr_g: for s in 0 to IN_STREAMS-1 generate
        crox_instr_g2: for i in 0 to MFB_REGIONS-1 generate
            plan_str_mvb_rxbuf_addr(s)(i) <= plan_str_mvb_meta(s)(i)(log2(RXBUF_BYTES)+USERMETA_WIDTH-1 downto USERMETA_WIDTH);
            plan_str_mvb_pkt_id(s)(i)     <= plan_str_mvb_meta(s)(i)(PKT_ID_WIDTH+IN_STREAMS+log2(RXBUF_BYTES)+USERMETA_WIDTH-1 downto IN_STREAMS+log2(RXBUF_BYTES)+USERMETA_WIDTH);
            plan_str_mvb_mod_sof_type(s)(i) <= plan_str_mvb_meta(s)(i)(PKT_ID_WIDTH+IN_STREAMS+log2(RXBUF_BYTES)+USERMETA_WIDTH);
            plan_str_mvb_mod_sof_size(s)(i) <= plan_str_mvb_meta(s)(i)(MOD_WIDTH+1+PKT_ID_WIDTH+IN_STREAMS+log2(RXBUF_BYTES)+USERMETA_WIDTH-1 downto 1+PKT_ID_WIDTH+IN_STREAMS+log2(RXBUF_BYTES)+USERMETA_WIDTH);

            process (all)
            begin
                if (plan_str_mvb_mod_sof_type(s)(i) = '1') then -- trim sof part 2
                    plan_str_mvb_txbuf_addr2(s)(i) <= plan_str_mvb_txbuf_addr(s)(i);
                    plan_str_mvb_len2(s)(i)        <= plan_str_mvb_len(s)(i);
                else -- extend sof part 2
                    plan_str_mvb_txbuf_addr2(s)(i) <= std_logic_vector(unsigned(plan_str_mvb_txbuf_addr(s)(i)) + unsigned(plan_str_mvb_mod_sof_size(s)(i)));
                    plan_str_mvb_len2(s)(i)        <= std_logic_vector(unsigned(plan_str_mvb_len(s)(i)) - unsigned(plan_str_mvb_mod_sof_size(s)(i)));
                end if;
            end process;

            cx_dir_g: if CROSSBARX_DIR generate
                crox_instr_b_col(s)(i)   <= plan_str_mvb_txbuf_addr2(s)(i)(log2(TXBUF_BYTES)-1 downto TX_ROW_W);
                crox_instr_b_item(s)(i)  <= plan_str_mvb_txbuf_addr2(s)(i)(TX_ROW_W-1 downto 0);
                plan_str_mvb_a_col(s)(i) <= plan_str_mvb_rxbuf_addr(s)(i)(log2(RXBUF_BYTES)-1 downto RX_ROW_W);
                crox_instr_a_item(s)(i)  <= plan_str_mvb_rxbuf_addr(s)(i)(RX_ROW_W-1 downto 0);
            else generate
                plan_str_mvb_a_col(s)(i) <= plan_str_mvb_txbuf_addr2(s)(i)(log2(TXBUF_BYTES)-1 downto TX_ROW_W);
                crox_instr_a_item(s)(i)  <= plan_str_mvb_txbuf_addr2(s)(i)(TX_ROW_W-1 downto 0);
                crox_instr_b_col(s)(i)   <= plan_str_mvb_rxbuf_addr(s)(i)(log2(RXBUF_BYTES)-1 downto RX_ROW_W);
                crox_instr_b_item(s)(i)  <= plan_str_mvb_rxbuf_addr(s)(i)(RX_ROW_W-1 downto 0);
            end generate;

            crox_instr_len(s)(i)  <= plan_str_mvb_len2(s)(i);
            crox_instr_meta(s)(i) <= plan_str_mvb_pkt_id(s)(i);
        end generate;

        crox_instr_a_col(s) <= plan_str_mvb_a_col(s)(0);

        process (all)
        begin
            plan_str_mvb_dst_rdy(s) <= (others => '0');
            crox_instr_vld(s) <= (others => '0');
            for i in 0 to MFB_REGIONS-1 loop
                if (plan_str_mvb_a_col(s)(i) = crox_instr_a_col(s)) then
                    plan_str_mvb_dst_rdy(s)(i) <= crox_instr_dst_rdy(s);
                    crox_instr_vld(s)(i)       <= plan_str_mvb_vld(s)(i);
                else
                    exit;
                end if;
            end loop;
        end process;

        crox_instr_src_rdy(s) <= (or crox_instr_vld(s));
    end generate;

    -- =========================================================================
    -- COMMON CROSSBARX
    -- =========================================================================

    crox_rxbuf_g : for s in 0 to IN_STREAMS-1 generate
        crox_rxbuf_g2 : for b in 0 to RXBUF_BLOCKS-1 generate
            rxbuf_rd_addr(s)(b)                  <= crox_rxbuf_rd_addr(s*RXBUF_BLOCKS+b);
            crox_rxbuf_rd_data(s*RXBUF_BLOCKS+b) <= rxbuf_rd_data(s)(b);
        end generate;
    end generate;

    crossbarx_i : entity work.CROSSBARX
    generic map(
        DATA_DIR            => CROSSBARX_DIR,
        USE_CLK2            => true,
        USE_CLK_ARB         => False,
        BUF_A_COLS          => tsel(CROSSBARX_DIR, RXBUF_WORDS, TXBUF_WORDS),
        BUF_A_STREAM_ROWS   => tsel(CROSSBARX_DIR, RXBUF_BLOCKS, TXBUF_BLOCKS),
        BUF_B_COLS          => tsel(CROSSBARX_DIR, TXBUF_WORDS, RXBUF_WORDS),
        BUF_B_ROWS          => tsel(CROSSBARX_DIR, TXBUF_BLOCKS, TXBUF_BLOCKS),

        ROW_ITEMS           => MFB_BLOCK_SIZE,
        ITEM_WIDTH          => MFB_ITEM_WIDTH,
        TRANS_MTU           => PKT_MTU,

        METADATA_WIDTH      => PKT_ID_WIDTH,
        TRANSS              => MFB_REGIONS,
        TRANS_FIFO_ITEMS    => 256,
        --COLOR_TIMEOUT_WIDTH => 3,
        --COLOR_CONF_DELAY    => 5,
        RD_LATENCY          => 1,
        TRANS_STREAMS       => IN_STREAMS,
        DATA_MUX_LAT        => 0,
        DATA_MUX_OUTREG_EN  => true,
        DATA_ROT_LAT        => 0,
        DATA_ROT_OUTREG_EN  => true,
        DEVICE              => DEVICE
    )
    port map(
        CLK                => CLK,
        CLK2               => CLK_X2,
        RESET              => RESET,
        CLK_ARB            => CLK,
        RESET_ARB          => RESET,

        TRANS_A_COL        => crox_instr_a_col,
        TRANS_A_ITEM       => crox_instr_a_item,
        TRANS_B_COL        => crox_instr_b_col,
        TRANS_B_ITEM       => crox_instr_b_item,
        TRANS_LEN          => crox_instr_len,
        TRANS_META         => crox_instr_meta,
        TRANS_VLD          => crox_instr_vld,
        TRANS_SRC_RDY      => crox_instr_src_rdy,
        TRANS_DST_RDY      => crox_instr_dst_rdy,

        SRC_BUF_RD_ADDR    => crox_rxbuf_rd_addr,
        SRC_BUF_RD_DATA    => crox_rxbuf_rd_data,

        DST_BUF_WR_ADDR    => txbuf_wr_addr,
        DST_BUF_WR_DATA    => txbuf_wr_data,
        DST_BUF_WR_IE      => txbuf_wr_ie,
        DST_BUF_WR_EN      => txbuf_wr_en,

        TRANS_COMP_META    => crox_done_meta,
        TRANS_COMP_SRC_RDY => crox_done_vld,
        TRANS_COMP_DST_RDY => (others => (others => '1'))
    );

    done_vld_g: for s in 0 to IN_STREAMS-1 generate
        crox_done_src_rdy(s) <= (or crox_done_vld(s));

        dis_fifo_i : entity work.MVB_FIFOX
        generic map(
            ITEMS      => MFB_REGIONS,
            ITEM_WIDTH => PKT_ID_WIDTH,
            FIFO_DEPTH => 2**PKT_ID_WIDTH,
            RAM_TYPE   => "AUTO",
            DEVICE     => DEVICE
        ) port map(
            CLK        => CLK,
            RESET      => RESET,

            RX_DATA    => slv_array_ser(dis_mvb_pkt_id(s)),
            RX_VLD     => dis_mvb_vld(s),
            RX_SRC_RDY => dis_mvb_src_rdy(s),
            RX_DST_RDY => dis_mvb_dst_rdy(s),

            TX_DATA    => dis_fifo_mvb_data(s),
            TX_VLD     => dis_fifo_mvb_vld(s),
            TX_SRC_RDY => dis_fifo_mvb_src_rdy(s),
            TX_DST_RDY => dis_fifo_mvb_dst_rdy(s)
        );

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (dis_mvb_src_rdy(s) = '1' and dis_mvb_dst_rdy(s) = '0') then
                    dis_fifo_wr_err_reg(s) <= '1';
                end if;
                if (RESET = '1') then
                    dis_fifo_wr_err_reg(s) <= '0';
                end if;
            end if;
        end process;

        assert (dis_fifo_wr_err_reg(s) /= '1')
           report "CXS2: dst_rdy error! Writing in full dis_fifo_i!"
           severity failure;

        dis_fifo_mvb_pkt_id(s)  <= slv_array_deser(dis_fifo_mvb_data(s), MFB_REGIONS);
        dis_fifo_mvb_dst_rdy(s) <= not crox_done_src_rdy(s);

        rxbuf_done_id(s)  <= crox_done_meta(s) when (crox_done_src_rdy(s) = '1') else dis_fifo_mvb_pkt_id(s);
        rxbuf_done_vld(s) <= crox_done_vld(s) or (dis_fifo_mvb_src_rdy(s) and dis_fifo_mvb_vld(s));
        txbuf_done_vld(s) <= crox_done_vld(s);
    end generate;

    -- =========================================================================
    -- COMMON TX TRANSACTION FIFO
    -- =========================================================================

    tr_fifo_i : entity work.MFB_CROSSBARX_STREAM2_TR_FIFO
    generic map(
        MFB_REGIONS => MFB_REGIONS,
        STREAMS     => IN_STREAMS,
        PKT_MTU     => PKT_MTU,
        PKT_ID_W    => PKT_ID_WIDTH,
        USERMETA_W  => USERMETA_WIDTH,
        TXBUF_BYTES => TXBUF_BYTES,
        DEVICE      => DEVICE
    )
    port map(
        CLK                  => CLK,
        RESET                => RESET,

        RX_TR_MVB_STREAMS    => plan_glb_mvb_streams,
        RX_TR_MVB_USERMETA   => plan_glb_mvb_usermeta,
        RX_TR_MVB_TXBUF_ADDR => plan_glb_mvb_txbuf_addr,
        RX_TR_MVB_LEN        => plan_glb_mvb_len,
        RX_TR_MVB_VLD        => plan_glb_mvb_vld,
        RX_TR_MVB_SRC_RDY    => (or plan_glb_mvb_vld),
        RX_TR_MVB_DST_RDY    => plan_glb_mvb_dst_rdy,

        TXBUF_DONE_VLD       => txbuf_done_vld,

        TX_TR_MVB_USERMETA   => txbuf_instr_usermeta,
        TX_TR_MVB_TXBUF_ADDR => txbuf_instr_txbuf_addr,
        TX_TR_MVB_LEN        => txbuf_instr_len,
        TX_TR_MVB_VLD        => txbuf_instr_vld,
        TX_TR_MVB_SRC_RDY    => txbuf_instr_src_rdy,
        TX_TR_MVB_DST_RDY    => txbuf_instr_dst_rdy
    );

    -- =========================================================================
    -- COMMON TX BUFFER
    -- =========================================================================

    tx_buf_i : entity work.MFB_CROSSBARX_OUTPUT_BUFFER
    generic map(
        DEVICE            => DEVICE,
        HDR_META_WIDTH    => USERMETA_WIDTH,
        MVB_ITEMS         => MFB_REGIONS,
        MFB_REGIONS       => MFB_REGIONS,
        MFB_REGION_SIZE   => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE    => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH    => MFB_ITEM_WIDTH,
        MFB_META_WIDTH    => 2,
        MFB_META_WITH_SOF => false,
        BUF_BLOCKS        => TXBUF_BLOCKS,
        DATA_BLOCK_SIZE   => MFB_BLOCK_SIZE,
        DATA_ITEM_WIDTH   => MFB_ITEM_WIDTH,
        BUF_WORDS         => TXBUF_WORDS,
        CHANNELS          => 2,
        PKT_SIZE_MAX      => PKT_MTU,
        META_EQ_OUTPUT    => True,
        INPUT_EQ_OUTPUT   => False
    )
    port map(
        CLK_META         => CLK,
        RESET_META       => RESET,
        CLK_IN           => CLK_X2,
        RESET_IN         => RESET,
        CLK_OUT          => CLK,
        RESET_OUT        => RESET,

        WR_ADDR          => txbuf_wr_addr,
        WR_DATA          => txbuf_wr_data,
        WR_IE            => txbuf_wr_ie,
        WR_EN            => txbuf_wr_en,

        RX_HDR_META      => txbuf_instr_usermeta,
        RX_HDR_MFB_META  => (others => (others => '0')),
        RX_HDR_CHAN      => (others => (others => '0')),
        RX_HDR_ADDR      => txbuf_instr_txbuf_addr,
        RX_HDR_LEN       => txbuf_instr_len,
        RX_HDR_VLD       => txbuf_instr_vld,
        RX_HDR_SRC_RDY   => txbuf_instr_src_rdy,
        RX_HDR_DST_RDY   => txbuf_instr_dst_rdy,

        RD_PTR           => txbuf_rd_pointer,

        PKT_SENT_CHAN    => open,
        PKT_SENT_LEN     => open,
        PKT_SENT_SRC_RDY => open,
        PKT_SENT_DST_RDY => '1',

        TX_MVB_LEN       => open,
        TX_MVB_HDR_META  => TX_MVB_USERMETA,
        TX_MVB_CHANNEL   => open,
        TX_MVB_VLD       => TX_MVB_VLD,
        TX_MVB_SRC_RDY   => TX_MVB_SRC_RDY,
        TX_MVB_DST_RDY   => TX_MVB_DST_RDY,

        TX_MFB_DATA      => TX_MFB_DATA,
        TX_MFB_META      => open,
        TX_MFB_SOF       => TX_MFB_SOF,
        TX_MFB_EOF       => TX_MFB_EOF,
        TX_MFB_SOF_POS   => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS   => TX_MFB_EOF_POS,
        TX_MFB_SRC_RDY   => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY   => TX_MFB_DST_RDY
    );

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
                dbg_rx_mvb_pkt_cnt <= (others => '0');
            elsif (RX_MVB_SRC_RDY(0) = '1' and RX_MVB_DST_RDY(0) = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RX_MVB_VLD(0)(i);
                end loop;
                dbg_rx_mvb_pkt_cnt <= dbg_rx_mvb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_tx_mvb_pkt_cnt <= (others => '0');
            elsif (TX_MVB_SRC_RDY = '1' and TX_MVB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + TX_MVB_VLD(i);
                end loop;
                    dbg_tx_mvb_pkt_cnt <= dbg_tx_mvb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rx_mfb_pkt_cnt <= (others => '0');
            elsif (RX_MFB_SRC_RDY(0) = '1' and RX_MFB_DST_RDY(0) = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RX_MFB_EOF(0)(i);
                end loop;
                dbg_rx_mfb_pkt_cnt <= dbg_rx_mfb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_tx_mfb_pkt_cnt <= (others => '0');
            elsif (TX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + TX_MFB_EOF(i);
                end loop;
                    dbg_tx_mfb_pkt_cnt <= dbg_tx_mfb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_txbuf_instr_cnt <= (others => '0');
            elsif (txbuf_instr_src_rdy = '1' and txbuf_instr_dst_rdy = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + txbuf_instr_vld(i);
                end loop;
                    dbg_txbuf_instr_cnt <= dbg_txbuf_instr_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_plan_glb_cnt <= (others => '0');
            elsif (plan_glb_mvb_dst_rdy = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + plan_glb_mvb_vld(i);
                end loop;
                dbg_plan_glb_cnt <= dbg_plan_glb_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_crox_instr_cnt <= (others => '0');
            elsif (crox_instr_src_rdy(0) = '1' and crox_instr_dst_rdy(0) = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + crox_instr_vld(0)(i);
                end loop;
                dbg_crox_instr_cnt <= dbg_crox_instr_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_crox_done_cnt <= (others => '0');
            else
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + crox_done_vld(0)(i);
                end loop;
                dbg_crox_done_cnt <= dbg_crox_done_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    --pragma synthesis_on

end architecture;
