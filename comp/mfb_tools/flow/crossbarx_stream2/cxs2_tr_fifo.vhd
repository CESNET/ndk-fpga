-- cxs2_tr_fifo.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_CROSSBARX_STREAM2_TR_FIFO is
generic (
    MFB_REGIONS : natural := 4;
    STREAMS     : natural := 4;
    PKT_MTU     : natural := 2**14;
    PKT_ID_W    : natural := 9;
    USERMETA_W  : natural := 32;
    TXBUF_BYTES : natural := 512;
    DEVICE      : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK                  : in  std_logic;
    RESET                : in  std_logic;

    -- =========================================================================
    -- Input transaction MVB interface
    -- =========================================================================
    RX_TR_MVB_STREAMS    : in  slv_array_t(MFB_REGIONS-1 downto 0)(STREAMS-1 downto 0);
    RX_TR_MVB_USERMETA   : in  slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    RX_TR_MVB_TXBUF_ADDR : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    RX_TR_MVB_LEN        : in  slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    RX_TR_MVB_VLD        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_TR_MVB_SRC_RDY    : in  std_logic;
    RX_TR_MVB_DST_RDY    : out std_logic;

    -- =========================================================================
    -- Input TXBUF done valids
    -- =========================================================================
    TXBUF_DONE_VLD       : in  slv_array_t(STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- =========================================================================
    -- Output transaction MVB interface
    -- =========================================================================
    TX_TR_MVB_USERMETA   : out slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    TX_TR_MVB_TXBUF_ADDR : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    TX_TR_MVB_LEN        : out slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    TX_TR_MVB_VLD        : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_TR_MVB_SRC_RDY    : out std_logic;
    TX_TR_MVB_DST_RDY    : in  std_logic
);
end entity;

architecture FULL of MFB_CROSSBARX_STREAM2_TR_FIFO is

    constant FIFO_ITEM_W : natural := log2(PKT_MTU+1) + log2(TXBUF_BYTES) + USERMETA_W + STREAMS;
    constant FIFO_DEPTH  : natural := 512; --TODO
    constant DONE_CNT_W  : natural := log2((MFB_REGIONS*FIFO_DEPTH) + (2**PKT_ID_W)) + 1;

    signal rx_tr_mvb_data_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(FIFO_ITEM_W-1 downto 0);
    signal fifo_mvb_data       : std_logic_vector(MFB_REGIONS*FIFO_ITEM_W-1 downto 0);
    signal fifo_mvb_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(FIFO_ITEM_W-1 downto 0);
    signal fifo_mvb_streams    : slv_array_t(MFB_REGIONS-1 downto 0)(STREAMS-1 downto 0);
    signal fifo_mvb_usermeta   : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_W-1 downto 0);
    signal fifo_mvb_txbuf_addr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TXBUF_BYTES)-1 downto 0);
    signal fifo_mvb_len        : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal fifo_mvb_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifo_mvb_src_rdy    : std_logic;
    signal fifo_mvb_dst_rdy    : std_logic;

    signal fifo_req_done_sum   : u_array_t(STREAMS-1 downto 0)(log2(MFB_REGIONS+1)-1 downto 0);
    signal stream_ready        : std_logic_vector(STREAMS-1 downto 0);
    signal stream_ready_and    : std_logic;
    signal txbuf_done_cnt      : u_array_t(STREAMS-1 downto 0)(DONE_CNT_W-1 downto 0);
    signal txbuf_done_dec      : u_array_t(STREAMS-1 downto 0)(log2(MFB_REGIONS+1)-1 downto 0);

    signal txbuf_done_cnt_ovf     : std_logic_vector(STREAMS-1 downto 0);
    signal txbuf_done_cnt_ovf_reg : std_logic_vector(STREAMS-1 downto 0);

begin

    rx_tr_mvb_pack_g: for i in 0 to MFB_REGIONS-1 generate
        rx_tr_mvb_data_arr(i) <= RX_TR_MVB_LEN(i) & RX_TR_MVB_TXBUF_ADDR(i) & RX_TR_MVB_USERMETA(i) & RX_TR_MVB_STREAMS(i);
    end generate;

    fifo_i : entity work.MVB_FIFOX
    generic map(
        ITEMS      => MFB_REGIONS,
        ITEM_WIDTH => FIFO_ITEM_W,
        FIFO_DEPTH => FIFO_DEPTH,
        RAM_TYPE   => "AUTO",
        DEVICE     => DEVICE
    ) port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => slv_array_ser(rx_tr_mvb_data_arr),
        RX_VLD     => RX_TR_MVB_VLD,
        RX_SRC_RDY => RX_TR_MVB_SRC_RDY,
        RX_DST_RDY => RX_TR_MVB_DST_RDY,

        TX_DATA    => fifo_mvb_data,
        TX_VLD     => fifo_mvb_vld,
        TX_SRC_RDY => fifo_mvb_src_rdy,
        TX_DST_RDY => fifo_mvb_dst_rdy
    );

    fifo_mvb_data_arr <= slv_array_deser(fifo_mvb_data, MFB_REGIONS);

    rx_tr_mvb_unpack_g: for i in 0 to MFB_REGIONS-1 generate
        fifo_mvb_streams(i)    <= fifo_mvb_data_arr(i)(STREAMS-1 downto 0);
        fifo_mvb_usermeta(i)   <= fifo_mvb_data_arr(i)(USERMETA_W+STREAMS-1 downto STREAMS);
        fifo_mvb_txbuf_addr(i) <= fifo_mvb_data_arr(i)(log2(TXBUF_BYTES)+USERMETA_W+STREAMS-1 downto USERMETA_W+STREAMS);
        fifo_mvb_len(i)        <= fifo_mvb_data_arr(i)(log2(PKT_MTU+1)+log2(TXBUF_BYTES)+USERMETA_W+STREAMS-1 downto log2(TXBUF_BYTES)+USERMETA_W+STREAMS);
    end generate;

    fifo_req_done_g: for s in 0 to STREAMS-1 generate
        process (all)
            variable v_sum : unsigned(log2(MFB_REGIONS+1)-1 downto 0);
        begin
            v_sum := (others => '0');
            for i in 0 to MFB_REGIONS-1 loop
                if (fifo_mvb_vld(i) = '1') then
                    v_sum := v_sum + fifo_mvb_streams(i)(s);
                end if;
            end loop;
            fifo_req_done_sum(s) <= v_sum;
        end process;

        stream_ready(s) <= '1' when (txbuf_done_cnt(s) >= fifo_req_done_sum(s)) else '0';
        txbuf_done_dec(s) <= fifo_req_done_sum(s) and (fifo_mvb_src_rdy and fifo_mvb_dst_rdy);
    end generate;

    stream_ready_and <= (and stream_ready);
    fifo_mvb_dst_rdy <= TX_TR_MVB_DST_RDY and stream_ready_and;

    TX_TR_MVB_USERMETA   <= fifo_mvb_usermeta;
    TX_TR_MVB_TXBUF_ADDR <= fifo_mvb_txbuf_addr;
    TX_TR_MVB_LEN        <= fifo_mvb_len;
    TX_TR_MVB_VLD        <= fifo_mvb_vld;
    TX_TR_MVB_SRC_RDY    <= fifo_mvb_src_rdy and stream_ready_and;

    txbuf_done_cnt_g: for s in 0 to STREAMS-1 generate
        process (CLK)
            variable v_txbuf_done_inc : unsigned(log2(MFB_REGIONS+1)-1 downto 0);
        begin
            if (rising_edge(CLK)) then
                v_txbuf_done_inc := (others => '0');
                for i in 0 to MFB_REGIONS-1 loop
                    if (TXBUF_DONE_VLD(s)(i) = '1') then
                        v_txbuf_done_inc := v_txbuf_done_inc + 1;
                    end if;
                end loop;

                txbuf_done_cnt(s) <= txbuf_done_cnt(s) - txbuf_done_dec(s) + v_txbuf_done_inc;

                if (RESET = '1') then
                    txbuf_done_cnt(s) <= (others => '0');
                end if;
            end if;
        end process;

        txbuf_done_cnt_ovf(s) <= (and txbuf_done_cnt(s));

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (txbuf_done_cnt_ovf(s) = '1') then
                    txbuf_done_cnt_ovf_reg(s) <= '1';
                end if;
                if (RESET = '1') then
                    txbuf_done_cnt_ovf_reg(s) <= '0';
                end if;
            end if;
        end process;

        assert (txbuf_done_cnt_ovf_reg(s) /= '1')
            report "CXS2-TRFIFO: Counter txbuf_done_cnt overflowed!"
            severity failure;
    end generate;

end architecture;
