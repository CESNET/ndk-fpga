-- spacer.vhd: TX MAC Lite Spacer
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--  Description
-- =========================================================================
-- This unit adds space after each passed packet. The unit makes sure, that
-- there is at least ETH_GAP MFB items after every TX packet.

entity TX_MAC_LITE_SPACER is
generic(
    -- Number of regions within a data word, must be power of 2.
    MFB_REGIONS        : natural := 4;
    -- Region size (in blocks).
    MFB_REGION_SIZE    : natural := 8;
    -- Block size (in items).
    MFB_BLOCK_SIZE     : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH     : natural := 8;

    -- Maximum packet size in MFB ITEMS.
    PKT_MTU            : natural := 1024;
    -- Required average gap after every packet in MFB ITEMS.
    -- 4B CRC + 12B Idle + 8B Preamble
    ETH_GAP            : natural := 24;
    -- Required minimum gap after every packet in MFB ITEMS.
    -- for 10Gb Ethernet   -> ETH_GAP-3
    -- for other standarts -> ETH_GAP-7
    ETH_GAP_MIN        : natural := max(0,ETH_GAP-7);

    -- Maximum number of Transaction waiting for data transfer.
    -- Setting this value too low will lead to lower throughput,
    -- which should trigger a simulation assert warning in component CrossbarX.
    TRANS_FIFO_SIZE    : natural := 64;

    -- Spacing mode
    -- 0 -> insert spaces between frames (defined by ETH_GAP and ETH_GAP_MIN)
    -- 1 -> insert spaces at the end of frames (defined by ETH_GAP)
    -- 2 -> insert spaces at the start of frames (defined by ETH_GAP)
    MODE               : natural := 0;

    -- FPGA device name.
    DEVICE             : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    RX_CLK         : in  std_logic;
    RX_CLK2        : in  std_logic; -- double frequency and same source as RX_CLK
    RX_RESET       : in  std_logic;
    TX_CLK         : in  std_logic;
    TX_RESET       : in  std_logic;

    -- =====================================================================
    --  RX MFB STREAM (without gaps inside frame)
    -- =====================================================================

    RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_LENGTH  : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0); -- valid on EOF
    RX_MFB_DISCARD : in  std_logic_vector(MFB_REGIONS-1 downto 0);                 -- valid on EOF
    RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY : in  std_logic;
    RX_MFB_DST_RDY : out std_logic;

    -- =====================================================================
    --  TX MFB STREAM
    -- =====================================================================

    TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SRC_RDY : out std_logic;
    TX_MFB_DST_RDY : in  std_logic
);
end entity;

architecture FULL of TX_MAC_LITE_SPACER is

    constant MFB_REGION_WIDTH : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_DATA_WIDTH   : natural := MFB_REGIONS*MFB_REGION_WIDTH;
    constant RX_BUF_WORDS     : natural := PKT_MTU*MFB_ITEM_WIDTH/MFB_DATA_WIDTH*4; -- enough space for 4 maximum sized packets
    constant TX_BUF_WORDS     : natural := PKT_MTU*MFB_ITEM_WIDTH/MFB_DATA_WIDTH*4; -- enough space for 4 maximum sized packets
    constant ROW_WIDTH        : natural := MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant BUF_ROWS         : natural := MFB_REGIONS*MFB_REGION_SIZE;

    -- =====================================================================
    --  RX MFB parsing
    -- =====================================================================

    signal RX_MFB_DATA_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal RX_MFB_LENGTH_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal RX_MFB_SOF_POS_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal RX_MFB_EOF_POS_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  RX Buffer data writing logic
    -- =====================================================================

    signal rx_buf_wr_ptr_reg     : unsigned(log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_wr_ptr_inc_reg : unsigned(log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_full           : std_logic;

    -- =====================================================================
    --  Transaction Generator
    -- =====================================================================

    signal trgen_mfb_src_rdy    : std_logic;
    signal trgen_mfb_dst_rdy    : std_logic;
    signal trgen_trans_a_col    : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal trgen_trans_a_item   : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal trgen_trans_len      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal trgen_trans_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal trgen_trans_src_rdy  : std_logic;
    signal trgen_trans_dst_rdy  : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Gap Counter
    -- =====================================================================

    constant PACP_META_WIDTH : natural := log2(RX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE);

    signal pacp_rx_pkt_meta     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(PACP_META_WIDTH-1 downto 0);
    signal pacp_rx_pkt_len      : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_rx_pkt_vld      : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pacp_rx_pkt_src_rdy  : std_logic_vector(1-1 downto 0);
    signal pacp_rx_pkt_afull    : std_logic_vector(1-1 downto 0);
    signal pacp_space_rd_ptr    : std_logic_vector(log2(TX_BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE)-1 downto 0);
    signal pacp_tx_pkt_meta     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(PACP_META_WIDTH-1 downto 0);
    signal pacp_tx_pkt_a_col    : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal pacp_tx_pkt_len      : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_tx_pkt_addr     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal pacp_tx_pkt_vld      : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pacp_tx_pkt_dst_rdy  : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal pacp_tx_pkt_len_mod  : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal pacp_tx_pkt_addr_mod : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);

    signal gapc_trans_a_col       : std_logic_vector(log2(RX_BUF_WORDS)-1 downto 0);
    signal gapc_trans_a_item      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal gapc_trans_b_col       : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal gapc_trans_b_item      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    signal gapc_trans_len         : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal gapc_trans_a_len_sum   : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+PKT_MTU                    +1)-1 downto 0);
    signal gapc_trans_b_len_sum   : std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE+PKT_MTU+MFB_REGIONS*ETH_GAP+1)-1 downto 0);
    signal gapc_trans_vld         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal gapc_trans_src_rdy     : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  RX Buffer
    -- =====================================================================

    signal rx_buf_wr_addr : slv_array_t     (BUF_ROWS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_wr_data : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);
    signal rx_buf_wr_en   : std_logic_vector(BUF_ROWS-1 downto 0);

    signal rx_buf_rd_addr : slv_array_t     (BUF_ROWS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal rx_buf_rd_data : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  CrossbarX
    -- =====================================================================

    constant CROX_META_WIDTH : integer := log2(PKT_MTU+1)+log2(RX_BUF_WORDS*BUF_ROWS)+log2(TX_BUF_WORDS*BUF_ROWS*MFB_BLOCK_SIZE);

    signal crox_instr_a_col     : slv_array_t     (1-1 downto 0)                        (log2(RX_BUF_WORDS)-1 downto 0);
    signal crox_instr_b_col     : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    -----------------
    -- THESE SIGNALS ARE ALL ONE BIT WIDER THAN THEY HAVE TO BE AND THE LOWEST BIT IS ALLWAYS 0.
    -- THIS IS TO AVOID A FAILURE CAUSED BY A BUG IN VIVADO 2019.
    signal crox_instr_a_item    : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS)+1-1 downto 0);
    signal crox_instr_b_item    : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(BUF_ROWS)+1-1 downto 0);
    signal crox_instr_len       : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MTU/MFB_BLOCK_SIZE*2+1)-1 downto 0);
    -----------------
    signal crox_instr_meta      : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(CROX_META_WIDTH-1 downto 0);
    signal crox_instr_vld       : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal crox_instr_src_rdy   : std_logic_vector(1-1 downto 0);
    signal crox_instr_dst_rdy   : std_logic_vector(1-1 downto 0);

    signal crox_src_buf_rd_addr : slv_array_t     (BUF_ROWS-1 downto 0)(log2(RX_BUF_WORDS)-1 downto 0);
    signal crox_src_buf_rd_data : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);

    signal crox_dst_buf_wr_addr : slv_array_t     (BUF_ROWS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal crox_dst_buf_wr_data : slv_array_t     (BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);
    signal crox_dst_buf_wr_ie   : slv_array_t     (BUF_ROWS-1 downto 0)(2-1 downto 0); -- item enable
    signal crox_dst_buf_wr_en   : std_logic_vector(BUF_ROWS-1 downto 0);

    signal crox_comp_meta       : slv_array_2d_t  (1-1 downto 0)(MFB_REGIONS-1 downto 0)(CROX_META_WIDTH-1 downto 0);
    signal crox_comp_src_rdy    : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal crox_comp_dst_rdy    : slv_array_t     (1-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal crox_comp_a_ptr      : slv_array_t(MFB_REGIONS-1 downto 0)(log2(RX_BUF_WORDS*BUF_ROWS)-1 downto 0);
    signal crox_buf_a_ptr       : unsigned(log2(RX_BUF_WORDS*BUF_ROWS)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  TX Buffer
    -- =====================================================================

    signal tx_buf_rx_instr_len     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal tx_buf_rx_instr_dst_row : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_DATA_WIDTH/MFB_ITEM_WIDTH)-1 downto 0);
    signal tx_buf_rx_instr_dst_col : slv_array_t(MFB_REGIONS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal tx_buf_rx_instr_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_buf_rx_instr_src_rdy : std_logic;
    signal tx_buf_rx_instr_dst_rdy : std_logic;

    signal tx_buf_wr_ptr_addr      : std_logic_vector(log2(TX_BUF_WORDS)-1 downto 0);
    signal tx_buf_wr_ptr_offset    : std_logic_vector(log2(BUF_ROWS)-1 downto 0);
    signal tx_buf_rd_ptr_addr      : std_logic_vector(log2(TX_BUF_WORDS)-1 downto 0);

    signal tx_buf_wr_data          : slv_array_t(BUF_ROWS-1 downto 0)(ROW_WIDTH-1 downto 0);
    signal tx_buf_wr_addr          : slv_array_t(BUF_ROWS-1 downto 0)(log2(TX_BUF_WORDS)-1 downto 0);
    signal tx_buf_wr_ie            : slv_array_t(BUF_ROWS-1 downto 0)(MFB_BLOCK_SIZE-1 downto 0);
    signal tx_buf_wr_en            : std_logic_vector(BUF_ROWS-1 downto 0);

    signal tx_buf_mfb_data         : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal tx_buf_mfb_sof_pos      : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_buf_mfb_eof_pos      : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    -- TX Buffer WR PTR logic
    -- =====================================================================

    constant TX_BUF_WR_PTR_DELAY : integer := 32;
    signal tx_buf_wr_ptr_delay_cnt_reg : unsigned(log2(TX_BUF_WR_PTR_DELAY)-1 downto 0);
    signal tx_buf_wr_ptr_reg           : std_logic_vector(log2(TX_BUF_WORDS*BUF_ROWS)-1 downto 0);
    signal last_vld_tx_buf_wr_ptr_reg  : std_logic_vector(log2(TX_BUF_WORDS*BUF_ROWS)-1 downto 0);
    signal tx_buf_wr_ptr_reg_vld       : std_logic;

    -- =====================================================================

begin

    -- =====================================================================
    --  RX MFB parsing
    -- =====================================================================

    rx_mfb_arr_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_RX_MFB_SOF_POS : std_logic_vector(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        signal tmp_RX_MFB_EOF_POS : std_logic_vector(max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    begin
        RX_MFB_DATA_arr   (i) <= RX_MFB_DATA   ((i+1)*MFB_REGION_WIDTH-1 downto i*MFB_REGION_WIDTH);
        RX_MFB_LENGTH_arr (i) <= RX_MFB_LENGTH ((i+1)*log2(PKT_MTU+1)-1 downto i*log2(PKT_MTU+1));
        tmp_RX_MFB_SOF_POS    <= RX_MFB_SOF_POS((i+1)*max(1,log2(MFB_REGION_SIZE))-1 downto i*max(1,log2(MFB_REGION_SIZE)));
        tmp_RX_MFB_EOF_POS    <= RX_MFB_EOF_POS((i+1)*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto i*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)));
        RX_MFB_SOF_POS_arr(i) <= std_logic_vector(resize_left(unsigned(tmp_RX_MFB_SOF_POS),log2(MFB_REGION_SIZE)));
        RX_MFB_EOF_POS_arr(i) <= std_logic_vector(resize_left(unsigned(tmp_RX_MFB_EOF_POS),log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)));
    end generate;

    RX_MFB_DST_RDY <= trgen_mfb_dst_rdy and (not rx_buf_full);

    -- =====================================================================

    -- =====================================================================
    --  RX Buffer data writing logic
    -- =====================================================================

    rx_buf_wr_ptr_pr : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then

            if (RX_MFB_SRC_RDY='1' and trgen_mfb_dst_rdy='1' and rx_buf_full='0') then
                rx_buf_wr_ptr_reg     <= rx_buf_wr_ptr_reg    +1;
                rx_buf_wr_ptr_inc_reg <= rx_buf_wr_ptr_inc_reg+1;
            end if;

            if (RX_RESET='1') then
                rx_buf_wr_ptr_reg     <= to_unsigned(0,log2(RX_BUF_WORDS));
                rx_buf_wr_ptr_inc_reg <= to_unsigned(1,log2(RX_BUF_WORDS));
            end if;
        end if;
    end process;

    crox_buf_a_ptr_pr : process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then

            for i in 0 to MFB_REGIONS-1 loop
                if (crox_comp_src_rdy(0)(i)='1') then
                    crox_buf_a_ptr <= unsigned(crox_comp_a_ptr(i));
                end if;
            end loop;

            if (RX_RESET='1') then
                crox_buf_a_ptr <= (others => '0');
            end if;
        end if;
    end process;

    -- RX Buffer is full whe write pointer reaches read pointer
    rx_buf_full <= '1' when rx_buf_wr_ptr_inc_reg=resize_right(crox_buf_a_ptr,log2(RX_BUF_WORDS)) else '0';

    -- propagate write pointer
    rx_buf_wr_addr <= (others => std_logic_vector(rx_buf_wr_ptr_reg));

    -- =====================================================================

    -- =====================================================================
    --  Transaction Generator
    -- =====================================================================

    trans_gen_i : entity work.TX_MAC_LITE_SPACER_TRANS_GEN
    generic map(
        MFB_REGIONS     => MFB_REGIONS    ,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        RX_BUF_WORDS    => RX_BUF_WORDS   ,
        PKT_MTU         => PKT_MTU        ,
        DEVICE          => DEVICE
    )
    port map(
        CLK   => RX_CLK  ,
        RESET => RX_RESET,

        RX_MFB_SOF_ADDR    => rx_buf_wr_addr(0)  ,
        RX_MFB_SOF_POS     => RX_MFB_SOF_POS_arr ,
        RX_MFB_SOF_VLD     => RX_MFB_SOF         ,

        RX_MFB_EOF_LEN     => RX_MFB_LENGTH_arr  ,
        RX_MFB_EOF_DISCARD => RX_MFB_DISCARD     ,
        RX_MFB_EOF_VLD     => RX_MFB_EOF         ,

        RX_MFB_SRC_RDY     => trgen_mfb_src_rdy  ,
        RX_MFB_DST_RDY     => trgen_mfb_dst_rdy  ,

        TX_TRANS_A_COL     => trgen_trans_a_col  ,
        TX_TRANS_A_ITEM    => trgen_trans_a_item ,
        TX_TRANS_LEN       => trgen_trans_len    ,
        TX_TRANS_VLD       => trgen_trans_vld    ,
        TX_TRANS_SRC_RDY   => trgen_trans_src_rdy,
        TX_TRANS_DST_RDY   => trgen_trans_dst_rdy
    );

    trgen_mfb_src_rdy <= RX_MFB_SRC_RDY and (not rx_buf_full);

    -- =====================================================================

    -- =====================================================================
    --  Gap Counter
    -- =====================================================================

    pkt_planner_i : entity work.PACKET_PLANNER
    generic map(
        DEVICE            => DEVICE                                          ,
        STREAMS           => 1                                               ,
        PKTS              => MFB_REGIONS                                     ,
        PLANNED_PKTS      => MFB_REGIONS                                     ,
        METADATA_WIDTH    => log2(RX_BUF_WORDS)+log2(BUF_ROWS*MFB_BLOCK_SIZE),
        SPACE_SIZE        => TX_BUF_WORDS*MFB_DATA_WIDTH/MFB_ITEM_WIDTH      ,
        PKT_SIZE          => PKT_MTU                                         ,
        GAP_SIZE          => tsel(MODE=0,ETH_GAP    ,MFB_BLOCK_SIZE)         ,
        GAP_SIZE_MIN      => tsel(MODE=0,ETH_GAP_MIN,MFB_BLOCK_SIZE)         ,
        ALIGN             => MFB_BLOCK_SIZE                                  ,
        FIFO_ITEMS        => 32                                              ,
        FIFO_AFULL_OFFSET => 1                                               ,
        STREAM_OUT_EN     => true                                            ,
        GLOBAL_OUT_EN     => false
    )
    port map(
        CLK   => RX_CLK  ,
        RESET => RX_RESET,

        RX_STR_PKT_META    => pacp_rx_pkt_meta   ,
        RX_STR_PKT_LEN     => pacp_rx_pkt_len    ,
        RX_STR_PKT_VLD     => pacp_rx_pkt_vld    ,
        RX_STR_PKT_SRC_RDY => pacp_rx_pkt_src_rdy,
        RX_STR_PKT_AFULL   => pacp_rx_pkt_afull  ,

        SPACE_GLB_RD_PTR   => pacp_space_rd_ptr  ,

        TX_STR_PKT_META    => pacp_tx_pkt_meta   ,
        TX_STR_PKT_LEN     => pacp_tx_pkt_len    ,
        TX_STR_PKT_ADDR    => pacp_tx_pkt_addr   ,
        TX_STR_PKT_VLD     => pacp_tx_pkt_vld    ,
        TX_STR_PKT_DST_RDY => pacp_tx_pkt_dst_rdy
    );

    trgen_trans_dst_rdy <= (not pacp_rx_pkt_afull(0));

    pacp_space_rd_ptr   <= std_logic_vector(resize_right(unsigned(tx_buf_rd_ptr_addr),pacp_space_rd_ptr'length));

    pacp_rx_gen : for i in 0 to MFB_REGIONS-1 generate
        pacp_rx_pkt_meta(0)(i) <= trgen_trans_a_col & trgen_trans_a_item(i);
        pacp_rx_pkt_vld (0)(i) <= trgen_trans_vld(i);
        pacp_rx_pkt_len_gen : if (MODE=0) generate
            pacp_rx_pkt_len(0)(i) <= trgen_trans_len(i);
        else generate
            pacp_rx_pkt_len(0)(i) <= std_logic_vector(unsigned(trgen_trans_len(i))+ETH_GAP);
        end generate;
    end generate;
    pacp_rx_pkt_src_rdy(0) <= trgen_trans_src_rdy and (not pacp_rx_pkt_afull(0));

    pacp_tx_gen : for i in 0 to MFB_REGIONS-1 generate
        pacp_tx_pkt_len_mod_gen : if (MODE=2 or MODE=1) generate
            pacp_tx_pkt_len_mod(0)(i) <= std_logic_vector(unsigned(pacp_tx_pkt_len(0)(i))-ETH_GAP);
        else generate
            pacp_tx_pkt_len_mod(0)(i) <= pacp_tx_pkt_len(0)(i);
        end generate;

        pacp_tx_pkt_addr_mod_gen : if (MODE=2) generate
            pacp_tx_pkt_addr_mod(0)(i) <= std_logic_vector(unsigned(pacp_tx_pkt_addr(0)(i))+ETH_GAP);
        else generate
            pacp_tx_pkt_addr_mod(0)(i) <= pacp_tx_pkt_addr(0)(i);
        end generate;

        pacp_tx_pkt_a_col(0)(i) <= pacp_tx_pkt_meta (0)(i)(pacp_tx_pkt_meta(0)(0)'high downto log2(BUF_ROWS*MFB_BLOCK_SIZE));
        gapc_trans_a_item(i) <= pacp_tx_pkt_meta    (0)(i)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
        gapc_trans_b_col (i) <= pacp_tx_pkt_addr_mod(0)(i)(pacp_tx_pkt_addr_mod(0)(i)'high downto log2(BUF_ROWS*MFB_BLOCK_SIZE));
        gapc_trans_b_item(i) <= pacp_tx_pkt_addr_mod(0)(i)(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
        gapc_trans_len   (i) <= pacp_tx_pkt_len_mod (0)(i);
    end generate;
    gapc_trans_a_col   <= pacp_tx_pkt_a_col(0)(0);
    gapc_trans_src_rdy <= (or pacp_tx_pkt_vld(0));

    pacp_rx_pkt_dst_rdy_pr : process (all)
    begin
        for i in 0 to MFB_REGIONS-1 loop
            if (pacp_tx_pkt_a_col(0)(i)=pacp_tx_pkt_a_col(0)(0)) then
                pacp_tx_pkt_dst_rdy(0)(i) <= crox_instr_dst_rdy(0);
                gapc_trans_vld        (i) <= pacp_tx_pkt_vld (0)(i);
            else
                pacp_tx_pkt_dst_rdy(0)(i) <= '0';
                gapc_trans_vld        (i) <= '0';
            end if;
        end loop;
    end process;

    -- =====================================================================

    crox_instr_a_col  (0) <= gapc_trans_a_col;
    crox_instr_b_col  (0) <= gapc_trans_b_col;
    crox_instr_vld    (0) <= gapc_trans_vld;
    crox_instr_src_rdy(0) <= gapc_trans_src_rdy;

    crox_instr_item_round_gen : for i in 0 to MFB_REGIONS-1 generate
        crox_instr_a_item(0)(i) <= std_logic_vector(enlarge_right(enlarge_right(unsigned(gapc_trans_a_item(i)),-log2(MFB_BLOCK_SIZE)),1));
        crox_instr_b_item(0)(i) <= std_logic_vector(enlarge_right(enlarge_right(unsigned(gapc_trans_b_item(i)),-log2(MFB_BLOCK_SIZE)),1));
        crox_instr_len   (0)(i) <= std_logic_vector(enlarge_right(enlarge_right(round_up(unsigned(gapc_trans_len(i)),log2(MFB_BLOCK_SIZE)),-log2(MFB_BLOCK_SIZE)),1));
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  RX Buffer
    -- =====================================================================

    rx_buffer_i : entity work.SCHEDULER_TX_PCIE_BUF_400G
    generic map(
        ETH_MFB_REGIONS     => MFB_REGIONS    ,
        ETH_MFB_REGION_SIZE => MFB_REGION_SIZE,
        ETH_MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        ETH_MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        PCIE_ENDPOINTS      => 1              ,
        PCIE_BUF_DATA_WIDTH => MFB_DATA_WIDTH ,
        PCIE_BUF_WORDS      => RX_BUF_WORDS   ,
        DEVICE              => DEVICE
    )
    port map(
        CLK   => RX_CLK  ,
        CLK2  => RX_CLK2 ,
        RESET => RX_RESET,

        RX_PAC_ADDR    => rx_buf_wr_addr,
        RX_PAC_DATA    => rx_buf_wr_data,
        RX_PAC_SRC_RDY => rx_buf_wr_en  ,

        RD_ADDR        => rx_buf_rd_addr,
        RD_DATA        => rx_buf_rd_data
    );

    rx_buf_wr_data <= slv_array_deser(RX_MFB_DATA,BUF_ROWS);
    rx_buf_wr_en   <= (others => (RX_MFB_SRC_RDY and trgen_mfb_dst_rdy and (not rx_buf_full)));

    -- =====================================================================

    rx_buf_rd_addr       <= crox_src_buf_rd_addr;
    crox_src_buf_rd_data <= rx_buf_rd_data;

    crox_meta_gen : for i in 0 to MFB_REGIONS-1 generate
        crox_instr_meta(0)(i) <= pacp_tx_pkt_len(0)(i)
                                &gapc_trans_a_col
                                &crox_instr_a_item(0)(i)(crox_instr_a_item(0)(i)'high downto 1)
                                &pacp_tx_pkt_addr(0)(i);
    end generate;

    -- =====================================================================
    --  CrossbarX
    -- =====================================================================

    crossbarx_i : entity work.CROSSBARX
    generic map(
        DATA_DIR            => true           ,
        USE_CLK2            => true           ,
        BUF_A_COLS          => RX_BUF_WORDS   ,
        BUF_A_STREAM_ROWS   => BUF_ROWS       ,
        BUF_B_COLS          => TX_BUF_WORDS   ,
        BUF_B_ROWS          => BUF_ROWS       ,
        -----------------
        -- THESE PARAMTETERS ARE ALL MODIFIED TO AVOID
        -- A FAILURE CAUSED BY A BUG IN VIVADO 2019.
        ROW_ITEMS           => 2              , -- This should be 1;
        ITEM_WIDTH          => MFB_BLOCK_SIZE*MFB_ITEM_WIDTH/2, -- This should be .../1;
        TRANS_MTU           => PKT_MTU/MFB_BLOCK_SIZE*2, -- This should be ...*1;
        -----------------
        METADATA_WIDTH      => CROX_META_WIDTH,
        TRANSS              => MFB_REGIONS    ,
        TRANS_FIFO_ITEMS    => TRANS_FIFO_SIZE,
        COLOR_TIMEOUT_WIDTH => 6              ,
        COLOR_CONF_DELAY    => 20             ,
        RD_LATENCY          => 1              ,
        TRANS_STREAMS       => 1              ,
        DATA_MUX_LAT        => 0              ,
        DATA_MUX_OUTREG_EN  => true           ,
        DATA_ROT_LAT        => 0              ,
        DATA_ROT_OUTREG_EN  => true           ,
        DEVICE              => DEVICE
    )
    port map(
        CLK   => RX_CLK  ,
        CLK2  => RX_CLK2 ,
        RESET => RX_RESET,

        TRANS_A_COL        => crox_instr_a_col    ,
        TRANS_A_ITEM       => crox_instr_a_item   ,
        TRANS_B_COL        => crox_instr_b_col    ,
        TRANS_B_ITEM       => crox_instr_b_item   ,
        TRANS_LEN          => crox_instr_len      ,
        TRANS_META         => crox_instr_meta     ,
        TRANS_VLD          => crox_instr_vld      ,
        TRANS_SRC_RDY      => crox_instr_src_rdy  ,
        TRANS_DST_RDY      => crox_instr_dst_rdy  ,

        SRC_BUF_RD_ADDR    => crox_src_buf_rd_addr,
        SRC_BUF_RD_DATA    => crox_src_buf_rd_data,

        DST_BUF_WR_ADDR    => crox_dst_buf_wr_addr,
        DST_BUF_WR_DATA    => crox_dst_buf_wr_data,
        DST_BUF_WR_IE      => crox_dst_buf_wr_ie  ,
        DST_BUF_WR_EN      => crox_dst_buf_wr_en  ,

        TRANS_COMP_META    => crox_comp_meta      ,
        TRANS_COMP_SRC_RDY => crox_comp_src_rdy   ,
        TRANS_COMP_DST_RDY => crox_comp_dst_rdy
    );

    -- =====================================================================

    crox_comp_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_len    : std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        signal tmp_a_ptr  : std_logic_vector(log2(RX_BUF_WORDS*BUF_ROWS)-1 downto 0);
        signal tmp_b_col  : std_logic_vector(log2(TX_BUF_WORDS)-1 downto 0);
        signal tmp_b_item : std_logic_vector(log2(BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    begin
        (tmp_len, tmp_a_ptr, tmp_b_col, tmp_b_item) <= crox_comp_meta(0)(i);

        crox_comp_a_ptr(i) <= tmp_a_ptr;

        tx_buf_rx_instr_len    (i) <= tmp_len;
        tx_buf_rx_instr_dst_row(i) <= tmp_b_item;
        tx_buf_rx_instr_dst_col(i) <= tmp_b_col;
    end generate;
    tx_buf_rx_instr_vld     <= crox_comp_src_rdy(0);
    tx_buf_rx_instr_src_rdy <= (or crox_comp_src_rdy(0));
    crox_comp_dst_rdy <= (others => (others => tx_buf_rx_instr_dst_rdy));

    tx_buf_wr_data <= crox_dst_buf_wr_data;
    tx_buf_wr_addr <= crox_dst_buf_wr_addr;
    tx_buf_wr_en   <= crox_dst_buf_wr_en;

    tx_buf_wr_ie_gen : for i in 0 to BUF_ROWS-1 generate
        tx_buf_wr_ie(i) <= (others => crox_dst_buf_wr_ie(i)(0));
    end generate;

    -- =====================================================================
    --  TX Buffer
    -- =====================================================================

    tx_buffer_i : entity work.SCHEDULER_TX_GMII_BUF_400G
    generic map(
        ETH_MFB_REGIONS     => MFB_REGIONS    ,
        ETH_MFB_REGION_SIZE => MFB_REGION_SIZE,
        ETH_MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        ETH_MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        PCIE_ENDPOINTS      => 1              ,
        PCIE_MTU            => 0              ,
        GMII_BUF_DATA_WIDTH => MFB_DATA_WIDTH ,
        GMII_BUF_WORDS      => TX_BUF_WORDS   ,
        INSTR_ASFIFO_SIZE   => 512            ,
        INSTR_FIFOXM_SIZE   => 32             ,
        SZEUH_MTU           => 1              ,
        PKT_MTU             => PKT_MTU        ,
        DMA_CHANNELS        => 2              ,
        DMA_CHANNELS_RED    => 2              ,
        DEVICE              => DEVICE
    )
    port map(
        CLK        => RX_CLK  ,
        CLK2       => RX_CLK2 ,
        RESET      => RX_RESET,
        GMII_CLK   => TX_CLK  ,
        GMII_RESET => TX_RESET,

        RX_INSTRS_LEN          => tx_buf_rx_instr_len        ,
        RX_INSTRS_DST_ROW      => tx_buf_rx_instr_dst_row    ,
        RX_INSTRS_DST_COL      => tx_buf_rx_instr_dst_col    ,
        RX_INSTRS_DMA_CHAN_RED => (others => (others => '0')),
        RX_INSTRS_DMA_CHAN     => (others => (others => '0')),
        RX_INSTRS_HDR          => (others => (others => '0')),
        RX_INSTRS_VLD          => tx_buf_rx_instr_vld        ,
        RX_INSTRS_SRC_RDY      => tx_buf_rx_instr_src_rdy    ,
        RX_INSTRS_DST_RDY      => tx_buf_rx_instr_dst_rdy    ,

        GMII_WR_ADDR           => tx_buf_wr_ptr_addr         ,
        GMII_WR_OFFSET         => tx_buf_wr_ptr_offset       ,
        GMII_RD_ADDR           => tx_buf_rd_ptr_addr         ,

        WR_GMII_BUF_DATA       => tx_buf_wr_data             ,
        WR_GMII_BUF_BE         => tx_buf_wr_ie               ,
        WR_GMII_BUF_ADDR       => tx_buf_wr_addr             ,
        WR_GMII_BUF_SRC_RDY    => tx_buf_wr_en               ,

        TX_ETH_MFB_DATA        => tx_buf_mfb_data            ,
        TX_ETH_MFB_SOF_POS     => tx_buf_mfb_sof_pos         ,
        TX_ETH_MFB_EOF_POS     => tx_buf_mfb_eof_pos         ,
        TX_ETH_MFB_SOF         => TX_MFB_SOF                 ,
        TX_ETH_MFB_EOF         => TX_MFB_EOF                 ,
        TX_ETH_MFB_SRC_RDY     => TX_MFB_SRC_RDY             ,
        TX_ETH_MFB_DST_RDY     => TX_MFB_DST_RDY
    );

    -- =====================================================================

    -- =====================================================================
    -- TX Buffer WR PTR logic
    -- =====================================================================
    -- The TX Buffer WR PTR (i.e. the Trans FIFO output Buffer B pointer)
    -- must be delayed before being sent to TX Buffer. This is for cases when
    -- Transactions propagated from Trans FIFO in different CLK ticks start
    -- all in the same word in the TX Buffer. It takes some time for these
    -- transactions to be buffered in the TX Buffer Transaction FIFOX Multi.
    -- (The TX Buffer expects for each word to already have buffered all
    -- Transactions for the word and not just some of them.)

    tx_buf_wr_ptr_delay_cnt_pr : process (RX_CLK)
        variable tmp_ptr : unsigned(log2(TX_BUF_WORDS*BUF_ROWS*MFB_BLOCK_SIZE)-1 downto 0);
    begin
        if (rising_edge(RX_CLK)) then

            -- decrement delay counter
            tx_buf_wr_ptr_delay_cnt_reg <= tx_buf_wr_ptr_delay_cnt_reg-1;

            -- propagate Buffer B pointer after delay timeout
            if (tx_buf_wr_ptr_reg_vld='1' and to_integer(tx_buf_wr_ptr_delay_cnt_reg)=0) then
                (tx_buf_wr_ptr_addr,tx_buf_wr_ptr_offset) <= tx_buf_wr_ptr_reg;
                tx_buf_wr_ptr_reg_vld <= '0';
            end if;

            -- sample Buffer B pointer for valid Transactions
            if (tx_buf_rx_instr_src_rdy='1' and tx_buf_rx_instr_dst_rdy='1') then
                for i in 0 to MFB_REGIONS-1 loop
                    if (tx_buf_rx_instr_vld(i)='1') then
                        tmp_ptr := unsigned(tx_buf_rx_instr_dst_col(i)) & unsigned(tx_buf_rx_instr_dst_row(i));
                        tmp_ptr := tmp_ptr + unsigned(tx_buf_rx_instr_len(i));
                        last_vld_tx_buf_wr_ptr_reg <= std_logic_vector(enlarge_right(round_up(tmp_ptr,log2(MFB_BLOCK_SIZE)),-log2(MFB_BLOCK_SIZE)));
                    end if;
                end loop;
            end if;

            -- get ready to propagate new sampled pointer
            if (tx_buf_wr_ptr_reg_vld='0') then
                tx_buf_wr_ptr_delay_cnt_reg <= to_unsigned(TX_BUF_WR_PTR_DELAY-1,log2(TX_BUF_WR_PTR_DELAY));
                tx_buf_wr_ptr_reg           <= last_vld_tx_buf_wr_ptr_reg;
                tx_buf_wr_ptr_reg_vld       <= '1';
            end if;

            if (RX_RESET='1') then
                tx_buf_wr_ptr_delay_cnt_reg <= (others => '0');
                tx_buf_wr_ptr_reg           <= (others => '0');
                last_vld_tx_buf_wr_ptr_reg  <= (others => '0');
                tx_buf_wr_ptr_reg_vld       <= '0';
                tx_buf_wr_ptr_addr          <= (others => '0');
                tx_buf_wr_ptr_offset        <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  TX MFB generation
    -- =====================================================================

    TX_MFB_DATA    <= slv_array_ser(tx_buf_mfb_data);
    TX_MFB_SOF_POS <= slv_array_ser(tx_buf_mfb_sof_pos);
    TX_MFB_EOF_POS <= slv_array_ser(tx_buf_mfb_eof_pos);

    -- =====================================================================

end architecture;
