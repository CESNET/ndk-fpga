-- cxs2_rx_buf.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_CROSSBARX_STREAM2_RX_BUF is
generic (
    MFB_REGIONS     : natural := 4;
    MFB_REGION_SIZE : natural := 8;
    MFB_BLOCK_SIZE  : natural := 8;
    MFB_ITEM_WIDTH  : natural := 8;
    BUF_BLOCK_WIDTH : natural := MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    BUF_BLOCKS      : natural := (MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/BUF_BLOCK_WIDTH;
    BUF_WORDS       : natural := 512;
    BUF_BYTES       : natural := (BUF_WORDS*BUF_BLOCKS*BUF_BLOCK_WIDTH)/8;
    PKT_MTU         : natural := 2**14;
    PKT_ID_W        : natural := 9;
    DEVICE          : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- CLOCK AND RESETS INPUTS
    -- =========================================================================
    CLK              : in  std_logic;
    CLK_X2           : in  std_logic;
    RESET            : in  std_logic;

    -- =========================================================================
    -- INPUT MFB INTERFACE (CLK)
    -- =========================================================================
    RX_MFB_DATA      : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_SOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SRC_RDY   : in  std_logic;
    RX_MFB_DST_RDY   : out std_logic;

    -- =========================================================================
    -- OUTPUT MVB INTERFACE WITH TRANSACTIONS STORED IN RX BUFFER (CLK)
    -- =========================================================================
    BUF_MVB_PKT_ID   : out slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    BUF_MVB_EOF_ADDR : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    BUF_MVB_LEN      : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    BUF_MVB_VLD      : out std_logic_vector(MFB_REGIONS-1 downto 0);
    BUF_MVB_SRC_RDY  : out std_logic;
    BUF_MVB_DST_RDY  : in  std_logic;

    -- =========================================================================
    -- INPUT INTERFACE WITH DONE PKT ID (CLK)
    -- =========================================================================
    BUF_RD_DONE_ID   : in  slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    BUF_RD_DONE_VLD  : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    -- =========================================================================
    -- READ INTERFACE OF RX BUFFER (CLK_X2)
    -- =========================================================================
    BUF_RD_ADDR      : in  slv_array_t(BUF_BLOCKS-1 downto 0)(log2(BUF_WORDS)-1 downto 0);
    BUF_RD_DATA      : out slv_array_t(BUF_BLOCKS-1 downto 0)(BUF_BLOCK_WIDTH-1 downto 0)
);
end entity;

architecture FULL of MFB_CROSSBARX_STREAM2_RX_BUF is

    signal len_mfb_data         : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal len_mfb_len          : std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal len_mfb_sof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal len_mfb_eof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal len_mfb_sof_pos      : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal len_mfb_eof_pos      : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal len_mfb_src_rdy      : std_logic;
    signal len_mfb_dst_rdy      : std_logic;
    signal len_mfb_eof_pos_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal len_mfb_len_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);

    signal buf_wr_data          : slv_array_t(BUF_BLOCKS-1 downto 0)(BUF_BLOCK_WIDTH-1 downto 0);
    signal buf_wr_addr          : unsigned(log2(BUF_WORDS)-1 downto 0);
    signal buf_wr_en            : std_logic;
    signal buf_wr_data_reg      : slv_array_t(BUF_BLOCKS-1 downto 0)(BUF_BLOCK_WIDTH-1 downto 0);
    signal buf_wr_addr_reg      : unsigned(log2(BUF_WORDS)-1 downto 0);
    signal buf_wr_en_reg        : std_logic;
    signal buf_full             : std_logic;

    signal buf_pkt_eof_addr     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal buf_rd_pointer_reg   : std_logic_vector(log2(BUF_BYTES)-1 downto 0);
    signal buf_rd_pointer_word  : unsigned(log2(BUF_WORDS)-1 downto 0);

    signal acc_mvb_eof_addr     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal acc_mvb_len          : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal acc_mvb_vld          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal acc_mvb_src_rdy      : std_logic;
    signal acc_mvb_dst_rdy      : std_logic;
    signal acc_pkt_id_cnt       : unsigned(PKT_ID_W-1 downto 0);
    signal acc_mvb_wr_ptr       : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal acc_mvb_pkt_id       : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);

    signal acc2_mvb_wr_ptr      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal acc2_mvb_pkt_id      : slv_array_t(MFB_REGIONS-1 downto 0)(PKT_ID_W-1 downto 0);
    signal acc2_mvb_len         : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal acc2_mvb_vld         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal acc2_mvb_src_rdy     : std_logic;
    signal acc2_mvb_dst_rdy     : std_logic;

    signal trsr_mvb_vld         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trsr_mvb_afull       : std_logic;
    signal trsr_mvb_afull_reg   : std_logic;
    signal trsr_tx_ptr          : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal trsr_tx_vld          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trsr_tx_src_rdy      : std_logic;

    signal dbg_cnt_acc          : unsigned(64-1 downto 0);
    signal dbg_cnt_trsr_rx      : unsigned(64-1 downto 0);
    signal dbg_cnt_trsr_tx      : unsigned(64-1 downto 0);

begin

    mfb_len_i : entity work.MFB_FRAME_LNG
    generic map(
        REGIONS        => MFB_REGIONS,
        REGION_SIZE    => MFB_REGION_SIZE,
        BLOCK_SIZE     => MFB_BLOCK_SIZE,
        ITEM_WIDTH     => MFB_ITEM_WIDTH,
        LNG_WIDTH      => log2(PKT_MTU+1),
        REG_BITMAP     => "100",
        IMPLEMENTATION => "parallel"
    )
        port map(
        CLK          => CLK,
        RESET        => RESET,

        RX_DATA      => RX_MFB_DATA,
        RX_SOF       => RX_MFB_SOF,
        RX_EOF       => RX_MFB_EOF,
        RX_SOF_POS   => RX_MFB_SOF_POS,
        RX_EOF_POS   => RX_MFB_EOF_POS,
        RX_SRC_RDY   => RX_MFB_SRC_RDY,
        RX_DST_RDY   => RX_MFB_DST_RDY,

        TX_DATA      => len_mfb_data,
        TX_META      => open,
        TX_FRAME_LNG => len_mfb_len,
        TX_SOF       => len_mfb_sof,
        TX_EOF       => len_mfb_eof,
        TX_SOF_POS   => len_mfb_sof_pos,
        TX_EOF_POS   => len_mfb_eof_pos,
        TX_SRC_RDY   => len_mfb_src_rdy,
        TX_DST_RDY   => len_mfb_dst_rdy,
        TX_COF       => open,
        TX_TEMP_LNG  => open
    );

    -- =========================================================================
    -- RX MFB buffer
    -- =========================================================================

    buf_wr_data <= slv_array_deser(len_mfb_data, BUF_BLOCKS);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            buf_wr_data_reg <= buf_wr_data;
            buf_wr_addr_reg <= buf_wr_addr;
            buf_wr_en_reg   <= buf_wr_en;
            if (RESET = '1') then
                buf_wr_en_reg <= '0';
            end if;
        end if;
    end process;

    bram_g : for i in 0 to BUF_BLOCKS-1 generate
        bram_i : entity work.SDP_BRAM
        generic map(
            DATA_WIDTH   => BUF_BLOCK_WIDTH,
            ITEMS        => BUF_WORDS,
            BLOCK_ENABLE => False,
            BLOCK_WIDTH  => 8,
            COMMON_CLOCK => False,
            OUTPUT_REG   => False,
            DEVICE       => DEVICE
        )
        port map(
            WR_CLK      => CLK,
            WR_RST      => RESET,
            WR_EN       => buf_wr_en_reg,
            WR_BE       => (others => '1'),
            WR_ADDR     => std_logic_vector(buf_wr_addr_reg),
            WR_DATA     => buf_wr_data_reg(i),

            RD_CLK      => CLK_X2,
            RD_RST      => RESET,
            RD_EN       => '1',
            RD_PIPE_EN  => '1',
            RD_ADDR     => BUF_RD_ADDR(i),
            RD_DATA     => BUF_RD_DATA(i),
            RD_DATA_VLD => open
        );
    end generate;

    -- =========================================================================
    -- BUFFER WRITE LOGIC
    -- =========================================================================

    buf_rd_pointer_word <= unsigned(buf_rd_pointer_reg(log2(BUF_BYTES)-1 downto log2(BUF_BYTES)-log2(BUF_WORDS)));
    buf_wr_en   <= len_mfb_src_rdy and not buf_full and acc_mvb_dst_rdy;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (buf_wr_en = '1') then
                buf_wr_addr <= buf_wr_addr + 1;
            end if;
            if (RESET = '1') then
                buf_wr_addr <= (others => '0');
            end if;
        end if;
    end process;

    buf_full <= '1' when ((buf_wr_addr+1) = buf_rd_pointer_word) else '0';

    len_mfb_dst_rdy <= not buf_full and acc_mvb_dst_rdy;

    -- =========================================================================
    -- BUFFER ACCEPT LOGIC
    -- =========================================================================

    len_mfb_eof_pos_arr <= slv_array_deser(len_mfb_eof_pos, MFB_REGIONS);
    len_mfb_len_arr     <= slv_array_deser(len_mfb_len, MFB_REGIONS);

    buf_pkt_eof_addr_g : for i in 0 to MFB_REGIONS-1 generate
        buf_pkt_eof_addr(i) <= std_logic_vector(buf_wr_addr) &
                               std_logic_vector(to_unsigned(i,log2(MFB_REGIONS))) &
                               len_mfb_eof_pos_arr(i);
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (acc_mvb_dst_rdy = '1') then
                acc_mvb_eof_addr <= buf_pkt_eof_addr;
                acc_mvb_len      <= len_mfb_len_arr;
                acc_mvb_vld      <= len_mfb_eof;
                acc_mvb_src_rdy  <= len_mfb_src_rdy and (or len_mfb_eof) and not buf_full;
            end if;
            if (RESET = '1') then
                acc_mvb_src_rdy <= '0';
            end if;
        end if;
    end process;

    process (CLK)
        variable v_pkt_id_cnt_inc : integer range 0 to MFB_REGIONS;
    begin
        if (rising_edge(CLK)) then
            v_pkt_id_cnt_inc := 0;
            for i in 0 to MFB_REGIONS-1 loop
                if (acc_mvb_vld(i) = '1') then
                    v_pkt_id_cnt_inc := v_pkt_id_cnt_inc + 1;
                end if;
            end loop;
            if (acc_mvb_dst_rdy = '1' and acc_mvb_src_rdy = '1') then
                acc_pkt_id_cnt <= acc_pkt_id_cnt + v_pkt_id_cnt_inc;
            end if;
            if (RESET = '1') then
                acc_pkt_id_cnt <= (others => '0');
            end if;
        end if;
    end process;

    acc_g : for i in 0 to MFB_REGIONS-1 generate
        process (all)
            variable v_pkt_id_cnt_inc : integer range 0 to MFB_REGIONS;
        begin
            v_pkt_id_cnt_inc := 0;
            for j in 0 to i-1 loop
                if (acc_mvb_vld(j) = '1') then
                    v_pkt_id_cnt_inc := v_pkt_id_cnt_inc + 1;
                end if;
            end loop;
            acc_mvb_wr_ptr(i) <= std_logic_vector(unsigned(acc_mvb_eof_addr(i)) + 1);
            acc_mvb_pkt_id(i) <= std_logic_vector(acc_pkt_id_cnt + v_pkt_id_cnt_inc);
        end process;
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (acc_mvb_dst_rdy = '1') then
                acc2_mvb_wr_ptr   <= acc_mvb_wr_ptr;
                acc2_mvb_pkt_id   <= acc_mvb_pkt_id;
                acc2_mvb_len      <= acc_mvb_len;
                acc2_mvb_vld      <= acc_mvb_vld;
                acc2_mvb_src_rdy  <= acc_mvb_src_rdy;
            end if;
            if (RESET = '1') then
                acc2_mvb_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- =========================================================================
    -- BUFFER READ POINTER LOGIC
    -- =========================================================================

    BUF_MVB_PKT_ID   <= acc2_mvb_pkt_id;
    BUF_MVB_EOF_ADDR <= acc2_mvb_wr_ptr;
    BUF_MVB_LEN      <= acc2_mvb_len;
    BUF_MVB_VLD      <= acc2_mvb_vld;
    BUF_MVB_SRC_RDY  <= acc2_mvb_src_rdy and not trsr_mvb_afull_reg;

    acc_mvb_dst_rdy <= not trsr_mvb_afull_reg and BUF_MVB_DST_RDY;
    trsr_mvb_vld <= acc2_mvb_vld and acc2_mvb_src_rdy and acc_mvb_dst_rdy;

    trsr_i : entity work.TRANS_SORTER
    generic map(
        RX_TRANSS           => MFB_REGIONS,
        TX_TRANSS           => MFB_REGIONS,
        ID_CONFS            => MFB_REGIONS,
        ID_WIDTH            => PKT_ID_W,
        TRANS_FIFO_ITEMS    => 2**PKT_ID_W,
        METADATA_WIDTH      => log2(BUF_BYTES),
        MSIDT_BEHAV         => 0,
        MAX_SAME_ID_TRANS   => 1,
        USE_SHAKEDOWN_FIFOX => True,
        ALMOST_FULL_OFFSET  => 2*MFB_REGIONS,
        DEVICE              => DEVICE
    )
    port map(
        CLK              => CLK,
        RESET            => RESET,

        RX_TRANS_ID      => acc2_mvb_pkt_id,
        RX_TRANS_META    => acc2_mvb_wr_ptr,
        RX_TRANS_SRC_RDY => trsr_mvb_vld,
        RX_TRANS_DST_RDY => open,

        TRANS_FIFO_AFULL => trsr_mvb_afull,

        RX_CONF_ID       => BUF_RD_DONE_ID,
        RX_CONF_VLD      => BUF_RD_DONE_VLD,

        TX_TRANS_ID      => open,
        TX_TRANS_META    => trsr_tx_ptr,
        TX_TRANS_SRC_RDY => trsr_tx_vld,
        TX_TRANS_DST_RDY => '1'
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            trsr_mvb_afull_reg <= trsr_mvb_afull;
            if (RESET = '1') then
                trsr_mvb_afull_reg <= '1';
            end if;
        end if;
    end process;

    trsr_tx_src_rdy <= (or trsr_tx_vld);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (trsr_tx_src_rdy = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    if (trsr_tx_vld(i) = '1') then
                        buf_rd_pointer_reg <= trsr_tx_ptr(i);
                    end if;
                end loop;
            end if;
            if (RESET = '1') then
                buf_rd_pointer_reg <= (others => '0');
            end if;
        end if;
    end process;

    --pragma synthesis_off
    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_cnt_acc <= (others => '0');
            elsif (acc_mvb_src_rdy = '1' and acc_mvb_dst_rdy = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + acc_mvb_vld(i);
                end loop;
                dbg_cnt_acc <= dbg_cnt_acc + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_cnt_trsr_rx <= (others => '0');
            elsif (acc2_mvb_src_rdy = '1' ) then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + trsr_mvb_vld(i);
                end loop;
                    dbg_cnt_trsr_rx <= dbg_cnt_trsr_rx + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_cnt_trsr_tx <= (others => '0');
            else
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + trsr_tx_vld(i);
                end loop;
                    dbg_cnt_trsr_tx <= dbg_cnt_trsr_tx + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;
    --pragma synthesis_on

end architecture;
