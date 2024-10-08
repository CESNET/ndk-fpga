-- avst_100g.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity TX_MAC_LITE_ADAPTER_AVST_100G is
    generic(
        DATA_WIDTH : natural := 512;
        FIFO_DEPTH : natural := 512;
        DEVICE     : string  := "STRATIX10"
    );
    port(
        -- CLOCK AND RESET
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- INPUT MFB INTERFACE
        -- (RX MAC LITE, allowed MFB configurations: 1,N,8,8, N=DATA_WIDTH/64)
        RX_MFB_DATA    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(1-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(max(1,log2(DATA_WIDTH/64))-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(1-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- OUTPUT AVST INTERFACE (Intel Ethernet IP cores)
        TX_AVST_DATA   : out std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_AVST_SOP    : out std_logic;
        TX_AVST_EOP    : out std_logic;
        TX_AVST_EMPTY  : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
        TX_AVST_ERROR  : out std_logic;
        TX_AVST_VALID  : out std_logic;
        TX_AVST_READY  : in  std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_ADAPTER_AVST_100G is

    constant DATA_BYTES            : natural := DATA_WIDTH/8;
    constant SOP_POS_WIDTH         : natural := max(1,log2(DATA_WIDTH/64));
    constant PKT_CNT_WIDTH         : natural := 6;
    constant PKT_CNT_INC_DLY_WIDTH : natural := 10;

    signal fl_sof_n      : std_logic;
    signal fl_eof_n      : std_logic;
    signal fl_src_rdy_n  : std_logic;
    signal fl_dst_rdy_n  : std_logic;
    signal fl_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal fl_drem       : std_logic_vector(log2(DATA_BYTES)-1 downto 0);

    signal mfb_aligned_data    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mfb_aligned_sof     : std_logic_vector(1-1 downto 0);
    signal mfb_aligned_eof     : std_logic_vector(1-1 downto 0);
    signal mfb_aligned_eof_pos : std_logic_vector(log2(DATA_BYTES)-1 downto 0);
    signal mfb_aligned_src_rdy : std_logic;
    signal mfb_aligned_dst_rdy : std_logic;

    signal mfb_pipe_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mfb_pipe_sof         : std_logic_vector(1-1 downto 0);
    signal mfb_pipe_eof         : std_logic_vector(1-1 downto 0);
    signal mfb_pipe_eof_pos     : std_logic_vector(log2(DATA_BYTES)-1 downto 0);
    signal mfb_pipe_src_rdy     : std_logic;
    signal mfb_pipe_dst_rdy     : std_logic;
    signal mfb_pipe_src_rdy_fix : std_logic;
    signal mfb_pipe_dst_rdy_fix : std_logic;

    signal mfb_fifo_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mfb_fifo_data_rotated : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mfb_fifo_sof          : std_logic_vector(1-1 downto 0);
    signal mfb_fifo_eof          : std_logic_vector(1-1 downto 0);
    signal mfb_fifo_eof_pos      : std_logic_vector(log2(DATA_BYTES)-1 downto 0);
    signal mfb_fifo_src_rdy      : std_logic;
    signal mfb_fifo_dst_rdy      : std_logic;

    signal pkt_cnt_inc_flag   : std_logic;
    signal pkt_cnt_inc_dly    : std_logic_vector(PKT_CNT_INC_DLY_WIDTH-1 downto 0);
    signal pkt_cnt_inc        : std_logic;
    signal pkt_cnt_stop_flag  : std_logic;
    signal pkt_cnt_next       : unsigned(PKT_CNT_WIDTH-1 downto 0);
    signal pkt_cnt_reg        : unsigned(PKT_CNT_WIDTH-1 downto 0);
    signal pkt_cnt_dec        : std_logic;
    signal pkt_cnt_ready_flag : std_logic;

begin

    flu2fl : entity work.flu2fl
    generic map (
        DATA_WIDTH      => DATA_WIDTH,
        SOP_POS_WIDTH   => SOP_POS_WIDTH,
        IN_PIPE_EN      => True,
        IN_PIPE_TYPE    => "REG",
        IN_PIPE_OUTREG  => True
    )
    port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_DATA         => RX_MFB_DATA,
        RX_SOP_POS      => RX_MFB_SOF_POS,
        RX_EOP_POS      => RX_MFB_EOF_POS,
        RX_SOP          => RX_MFB_SOF(0),
        RX_EOP          => RX_MFB_EOF(0),
        RX_SRC_RDY      => RX_MFB_SRC_RDY,
        RX_DST_RDY      => RX_MFB_DST_RDY,

        TX_SOF_N        => fl_sof_n,
        TX_EOP_N        => open,
        TX_SOP_N        => open,
        TX_EOF_N        => fl_eof_n,
        TX_SRC_RDY_N    => fl_src_rdy_n,
        TX_DST_RDY_N    => fl_dst_rdy_n,
        TX_DATA         => fl_data,
        TX_DREM         => fl_drem
    );

    mfb_aligned_data    <= fl_data;
    mfb_aligned_eof_pos <= fl_drem;
    mfb_aligned_sof(0)  <= not fl_sof_n;
    mfb_aligned_eof(0)  <= not fl_eof_n;
    mfb_aligned_src_rdy <= not fl_src_rdy_n;
    fl_dst_rdy_n <= not mfb_aligned_dst_rdy;

    mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => 1,
        REGION_SIZE => 1,
        BLOCK_SIZE  => DATA_WIDTH/8,
        ITEM_WIDTH  => 8,
        META_WIDTH  => 2,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        PIPE_TYPE   => "REG",
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_META    => (others => '0'),
        RX_DATA    => mfb_aligned_data,
        RX_SOF     => mfb_aligned_sof,
        RX_EOF     => mfb_aligned_eof,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => mfb_aligned_eof_pos,
        RX_SRC_RDY => mfb_aligned_src_rdy,
        RX_DST_RDY => mfb_aligned_dst_rdy,

        TX_META    => open,
        TX_DATA    => mfb_pipe_data,
        TX_SOF     => mfb_pipe_sof,
        TX_EOF     => mfb_pipe_eof,
        TX_SOF_POS => open,
        TX_EOF_POS => mfb_pipe_eof_pos,
        TX_SRC_RDY => mfb_pipe_src_rdy,
        TX_DST_RDY => mfb_pipe_dst_rdy_fix
    );

    mfb_pipe_src_rdy_fix <= mfb_pipe_src_rdy and not pkt_cnt_stop_flag;
    mfb_pipe_dst_rdy_fix <= mfb_pipe_dst_rdy and not pkt_cnt_stop_flag;

    fifo_i : entity work.MFB_FIFOX
    generic map(
        REGIONS     => 1,
        REGION_SIZE => 1,
        BLOCK_SIZE  => DATA_WIDTH/8,
        ITEM_WIDTH  => 8,
        FIFO_DEPTH  => FIFO_DEPTH,
        RAM_TYPE    => "AUTO",
        DEVICE      => DEVICE
    )
    port map(
        CLK => CLK,
        RST => RESET,

        RX_DATA    => mfb_pipe_data,
        RX_SOF     => mfb_pipe_sof,
        RX_EOF     => mfb_pipe_eof,
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => mfb_pipe_eof_pos,
        RX_SRC_RDY => mfb_pipe_src_rdy_fix,
        RX_DST_RDY => mfb_pipe_dst_rdy,

        TX_DATA    => mfb_fifo_data,
        TX_SOF     => mfb_fifo_sof,
        TX_EOF     => mfb_fifo_eof,
        TX_SOF_POS => open,
        TX_EOF_POS => mfb_fifo_eof_pos,
        TX_SRC_RDY => mfb_fifo_src_rdy,
        TX_DST_RDY => mfb_fifo_dst_rdy,

        FIFO_STATUS => open,
        FIFO_AFULL  => open,
        FIFO_AEMPTY => open
    );

    pkt_cnt_inc_flag <= mfb_aligned_src_rdy and mfb_aligned_dst_rdy and mfb_aligned_eof(0);

    pkt_cnt_inc_dly_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                pkt_cnt_inc_dly <= (others => '0');
            else
                pkt_cnt_inc_dly <= pkt_cnt_inc_dly(PKT_CNT_INC_DLY_WIDTH-2 downto 0) & pkt_cnt_inc_flag;
            end if;
        end if;
    end process;

    pkt_cnt_inc <= pkt_cnt_inc_dly(PKT_CNT_INC_DLY_WIDTH-1);
    pkt_cnt_stop_flag <= pkt_cnt_reg(PKT_CNT_WIDTH-1);

    pkt_cnt_next_p : process (all)
    begin
        pkt_cnt_next <= pkt_cnt_reg;
        if (pkt_cnt_inc = '1' and pkt_cnt_dec = '0') then
            pkt_cnt_next <= pkt_cnt_reg + 1;
        elsif (pkt_cnt_inc = '0' and pkt_cnt_dec = '1') then
            pkt_cnt_next <= pkt_cnt_reg - 1;
        end if;
    end process;

    pkt_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                pkt_cnt_reg <= (others => '0');
            else
                pkt_cnt_reg <= pkt_cnt_next;
            end if;
        end if;
    end process;

    pkt_cnt_dec <= mfb_fifo_src_rdy and mfb_fifo_dst_rdy and mfb_fifo_eof(0);
    pkt_cnt_ready_flag <= '1' when (pkt_cnt_reg > 0) else '0';

    -- rotate bytes
    data_rotation : for i in 0 to DATA_BYTES-1 generate
        mfb_fifo_data_rotated((i+1)*8-1 downto i*8) <= mfb_fifo_data((DATA_BYTES-i)*8-1 downto (DATA_BYTES-1-i)*8);
    end generate;

    TX_AVST_DATA  <= mfb_fifo_data_rotated;
    TX_AVST_SOP   <= mfb_fifo_sof(0);
    TX_AVST_EOP   <= mfb_fifo_eof(0);
    TX_AVST_EMPTY <= std_logic_vector((DATA_BYTES-1) - unsigned(mfb_fifo_eof_pos));
    TX_AVST_ERROR <= '0';
    TX_AVST_VALID <= mfb_fifo_src_rdy and pkt_cnt_ready_flag;
    mfb_fifo_dst_rdy <= TX_AVST_READY and pkt_cnt_ready_flag;

end architecture;
