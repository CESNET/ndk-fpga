-- output_buffer.vhd: Output Buffer for TX side of CrossbarX architecture
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- -------------------------------------------------------------------------
--                             Description
-- -------------------------------------------------------------------------

-- This component receives data through a buffer write interface.
-- It also receives informations about Packets contained in that data and
-- based on these informations automaticly sends the written data to output
-- MFB interface (the Packet info is sent on separated MVB interface).
--
entity MFB_CROSSBARX_OUTPUT_BUFFER is
generic(
    -- =====================
    -- Others
    -- =====================

    -- Target Device
    -- STRATIX10, ULTRASCALE, ..
    DEVICE            : string  := "STRATIX10";
    -- Width of Header Metadata signal
    HDR_META_WIDTH    : natural := 12;

    -- =====================
    -- Output MVB info
    -- =====================

    MVB_ITEMS         : natural := 8;
    -- =====================
    -- Output MFB info
    -- =====================

    MFB_REGIONS       : natural := 4;
    MFB_REGION_SIZE   : natural := 2;
    MFB_BLOCK_SIZE    : natural := 8;
    MFB_ITEM_WIDTH    : natural := 16;
    -- =====================
    -- MFB metadata info
    -- =====================

    -- metadata is valid with SOF when True, or with EOF when False
    MFB_META_WITH_SOF : boolean := true;
    MFB_META_WIDTH    : natural := 1;

    -- ========================
    -- Buffer data information
    -- ========================

    BUF_BLOCKS        : natural := 16;
    DATA_BLOCK_SIZE   : natural := 8;
    DATA_ITEM_WIDTH   : natural := 8;

    -- Number of words in buffer
    BUF_WORDS         : natural := 512;

    -- Number of Channels
    CHANNELS          : natural := 64;

    -- Maximum size of Packet (in number of Data Items)
    PKT_SIZE_MAX      : natural := 2**12;

    -- =====================
    -- Clock signal relations
    -- =====================

    -- CLK_META is the same as CLK_OUT
    META_EQ_OUTPUT    : boolean := false;
    -- CLK_IN is the same as CLK_OUT
    INPUT_EQ_OUTPUT   : boolean := false;

    -- =====================
    -- Derived aliases
    -- =====================

    DATA_BLOCK_WIDTH  : natural := DATA_BLOCK_SIZE*DATA_ITEM_WIDTH;
    BUF_BYTES         : natural := BUF_WORDS*BUF_BLOCKS*DATA_BLOCK_SIZE
);
port (
    -- =====================================================================
    -- Clock and Reset
    -- =====================================================================

    -- Clock and Reset for Metadata interfaces
    CLK_META         : in  std_logic;
    RESET_META       : in  std_logic;
    -- Clock and Reset for Data input
    CLK_IN           : in  std_logic;
    RESET_IN         : in  std_logic;
    -- Clock and Reset for Data output
    CLK_OUT          : in  std_logic;
    RESET_OUT        : in  std_logic;

    -- =====================================================================
    -- Buffer data interface
    --
    -- Runs on CLK_IN
    -- =====================================================================

    WR_ADDR          : in  slv_array_t     (BUF_BLOCKS-1 downto 0)(log2(BUF_WORDS)-1 downto 0);
    WR_DATA          : in  slv_array_t     (BUF_BLOCKS-1 downto 0)(DATA_BLOCK_WIDTH-1 downto 0);
    WR_IE            : in  slv_array_t     (BUF_BLOCKS-1 downto 0)(DATA_BLOCK_SIZE-1 downto 0);
    WR_EN            : in  std_logic_vector(BUF_BLOCKS-1 downto 0);

    -- =====================================================================
    -- Other components input interfaces
    --
    -- Runs on CLK_OUT
    -- =====================================================================

    RX_HDR_META      : in  slv_array_t     (MFB_REGIONS-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    RX_HDR_MFB_META  : in  slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
    RX_HDR_CHAN      : in  slv_array_t     (MFB_REGIONS-1 downto 0)(log2(CHANNELS)-1 downto 0);
    RX_HDR_ADDR      : in  slv_array_t     (MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    RX_HDR_LEN       : in  slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_SIZE_MAX+1)-1 downto 0);
    RX_HDR_VLD       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_HDR_SRC_RDY   : in  std_logic;
    RX_HDR_DST_RDY   : out std_logic;

    -- =====================================================================
    -- Other components output interfaces
    --
    -- Runs on CLK_META
    -- =====================================================================

    -- Current read pointer to Buffer
    RD_PTR           : out std_logic_vector(log2(BUF_BYTES)-1 downto 0);

    -- Information about sending each packet
    PKT_SENT_CHAN    : out slv_array_t     (MFB_REGIONS-1 downto 0)(log2(CHANNELS)-1 downto 0);
    PKT_SENT_LEN     : out slv_array_t     (MFB_REGIONS-1 downto 0)(log2(PKT_SIZE_MAX+1)-1 downto 0);
    PKT_SENT_SRC_RDY : out std_logic_vector(MFB_REGIONS-1 downto 0);
    PKT_SENT_DST_RDY : in  std_logic;

    -- =====================================================================
    -- Output MVB interface
    --
    -- Runs on CLK_OUT
    --
    -- MVB DATA contains three parts:
    --   - length (TX_MVB_LEN),
    --   - header metadata (TX_MVB_HDR_META),
    --   - channel (TX_MVB_CHANNEL)
    -- =====================================================================

    TX_MVB_LEN          : out std_logic_vector(MVB_ITEMS*log2(PKT_SIZE_MAX+1)-1 downto 0);
    TX_MVB_HDR_META     : out std_logic_vector(MVB_ITEMS*HDR_META_WIDTH      -1 downto 0);
    TX_MVB_CHANNEL      : out std_logic_vector(MVB_ITEMS*log2(CHANNELS)      -1 downto 0);
    TX_MVB_VLD          : out std_logic_vector(MVB_ITEMS                     -1 downto 0);
    TX_MVB_SRC_RDY      : out std_logic;
    TX_MVB_DST_RDY      : in  std_logic;

    -- =====================================================================
    -- Output MFB interface
    --
    -- Runs on CLK_OUT
    -- =====================================================================

    TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_MFB_META         : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH                               -1 downto 0);
    TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS                                              -1 downto 0);
    TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS                                              -1 downto 0);
    TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))                 -1 downto 0);
    TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))  -1 downto 0);
    TX_MFB_SRC_RDY      : out std_logic;
    TX_MFB_DST_RDY      : in  std_logic

    -- =====================================================================
    --  Debug signals
    -- =====================================================================
);
end entity;

architecture FULL of MFB_CROSSBARX_OUTPUT_BUFFER is

    -- =====================================================================
    --  Constants, aliases, functions
    -- =====================================================================

    -- Change DEVICE to "NONE" if this is a simulation
    -- altera_syncram does not work correctly in simulation in some configurations
    -- Using "NONE" device switches the memory to behavioral architecture
    function SDP_BRAM_DEVICE return string is
        variable dev0 : string(DEVICE'range) := DEVICE;
        variable dev1 : string(1 to 3) := "SIM";
    begin
--pragma synthesis_off
        if (DEVICE = "STRATIX10" or DEVICE = "ARRIA10") then
            return dev1;
        end if;
--pragma synthesis_on
        return dev0;
    end function;

    -- =====================================================================

    -- =====================================================================
    --  Main Buffer
    -- =====================================================================

    signal buf_rd_en      : std_logic_vector(BUF_BLOCKS-1 downto 0);
    signal buf_rd_pipe_en : std_logic_vector(BUF_BLOCKS-1 downto 0);
    signal buf_rd_addr    : slv_array_t     (BUF_BLOCKS-1 downto 0)(log2(BUF_WORDS)-1 downto 0);
    signal buf_rd_data    : slv_array_t     (BUF_BLOCKS-1 downto 0)(DATA_BLOCK_WIDTH-1 downto 0);
    signal buf_rd_vld     : std_logic_vector(BUF_BLOCKS-1 downto 0);

    signal buf_rd_en_l      : std_logic;
    signal buf_rd_pipe_en_l : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Header FIFOX Multi
    -- =====================================================================

    constant HDR_WIDTH : natural := HDR_META_WIDTH
                                   +MFB_META_WIDTH
                                   +log2(CHANNELS)
                                   +log2(BUF_BYTES)
                                   +log2(BUF_BYTES)
                                   +log2(PKT_SIZE_MAX+1);

    signal hdrf_di    : std_logic_vector(MFB_REGIONS*HDR_WIDTH-1 downto 0);
    signal hdrf_wr    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal hdrf_full  : std_logic;
    signal hdrf_do    : std_logic_vector((MFB_REGIONS+1)*HDR_WIDTH-1 downto 0);
    signal hdrf_rd    : std_logic_vector((MFB_REGIONS+1)-1 downto 0);
    signal hdrf_empty : std_logic_vector((MFB_REGIONS+1)-1 downto 0);

    signal hdrf_di_arr             : slv_array_t(MFB_REGIONS-1 downto 0)(HDR_WIDTH-1 downto 0);

    signal rx_hdr_sof_addr         : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal rx_hdr_eof_addr         : slv_array_t(MFB_REGIONS-1 downto 0)(log2(BUF_BYTES)-1 downto 0);

    signal hdrf_do_arr             : slv_array_t(MFB_REGIONS+1-1 downto 0)(HDR_WIDTH-1 downto 0);

    signal hdrf_do_meta            : slv_array_t(MFB_REGIONS+1-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    signal hdrf_do_mfb_meta        : slv_array_t(MFB_REGIONS+1-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal hdrf_do_chan            : slv_array_t(MFB_REGIONS+1-1 downto 0)(log2(CHANNELS)-1 downto 0);
    signal hdrf_do_sof_addr        : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal hdrf_do_eof_addr        : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(BUF_BYTES)-1 downto 0);
    signal hdrf_do_len             : slv_array_t(MFB_REGIONS+1-1 downto 0)(log2(PKT_SIZE_MAX+1)-1 downto 0);

    signal hdrf_do_sof_addr_word   : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(BUF_WORDS)-1 downto 0);
    signal hdrf_do_sof_addr_region : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(MFB_REGIONS)-1 downto 0);
    signal hdrf_do_sof_addr_block  : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal hdrf_do_sof_addr_item   : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(MFB_BLOCK_SIZE)-1 downto 0);

    signal hdrf_do_eof_addr_word   : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(BUF_WORDS)-1 downto 0);
    signal hdrf_do_eof_addr_region : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(MFB_REGIONS)-1 downto 0);
    signal hdrf_do_eof_addr_block  : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal hdrf_do_eof_addr_item   : u_array_t  (MFB_REGIONS+1-1 downto 0)(log2(MFB_BLOCK_SIZE)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Buffer read pointer register
    -- =====================================================================

    signal rd_ptr_reg : unsigned(log2(BUF_BYTES)-1 downto 0);

    signal rd_ptr_mfb : unsigned(log2(BUF_BYTES*DATA_ITEM_WIDTH/MFB_ITEM_WIDTH)-1 downto 0);

    signal rd_ptr_word     : unsigned(log2(BUF_WORDS)-1 downto 0);
    signal rd_ptr_region   : unsigned(log2(MFB_REGIONS)-1 downto 0);
    signal rd_ptr_block    : unsigned(log2(MFB_REGION_SIZE)-1 downto 0);
    signal rd_ptr_item     : unsigned(log2(MFB_BLOCK_SIZE)-1 downto 0);

    signal a_rd_ptr_data   : std_logic_vector(log2(BUF_BYTES)-1 downto 0);
    signal a_rd_ptr_vld    : std_logic;
    signal a_rd_ptr_n_vld  : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  TX MVB
    -- =====================================================================

    constant OUT_HDR_WIDTH : natural := log2(PKT_SIZE_MAX+1)
                                       +HDR_META_WIDTH
                                       +log2(CHANNELS);

    signal txhf_di    : std_logic_vector(MFB_REGIONS*OUT_HDR_WIDTH-1 downto 0);
    signal txhf_wr    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal txhf_full  : std_logic;
    signal txhf_do    : std_logic_vector(MVB_ITEMS*OUT_HDR_WIDTH-1 downto 0);
    signal txhf_rd    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal txhf_empty : std_logic_vector(MVB_ITEMS-1 downto 0);

    signal txhf_di_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(OUT_HDR_WIDTH-1 downto 0);
    signal txhf_do_arr      : slv_array_t(MVB_ITEMS-1 downto 0)(OUT_HDR_WIDTH-1 downto 0);
    signal txhf_do_len      : slv_array_t(MVB_ITEMS-1 downto 0)(log2(PKT_SIZE_MAX+1)-1 downto 0);
    signal txhf_do_meta     : slv_array_t(MVB_ITEMS-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    signal txhf_do_chan     : slv_array_t(MVB_ITEMS-1 downto 0)(log2(CHANNELS)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  SOF and EOF
    -- =====================================================================

    constant SHREG_DATA_WIDTH : natural := 1
                                          +log2(MFB_REGION_SIZE)
                                          +1
                                          +log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)
                                          +MFB_META_WIDTH;
    constant MEM_LATENCY : natural := 2;

    signal shreg_di_row : slv_array_t(BUF_BLOCKS-1 downto 0)(MFB_REGIONS*SHREG_DATA_WIDTH-1 downto 0);
    signal shreg_do_row : slv_array_t(BUF_BLOCKS-1 downto 0)(MFB_REGIONS*SHREG_DATA_WIDTH-1 downto 0);

    signal shreg_di : std_logic_vector(MFB_REGIONS*SHREG_DATA_WIDTH-1 downto 0);
    signal shreg_do : std_logic_vector(MFB_REGIONS*SHREG_DATA_WIDTH-1 downto 0);

    signal shreg_di_arr      : slv_array_t     (MFB_REGIONS-1 downto 0)(SHREG_DATA_WIDTH-1 downto 0);
    signal shreg_di_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shreg_di_sof_pos  : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal shreg_di_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shreg_di_eof_pos  : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal shreg_di_mfb_meta : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);

    signal shreg_do_arr      : slv_array_t     (MFB_REGIONS-1 downto 0)(SHREG_DATA_WIDTH-1 downto 0);
    signal shreg_do_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shreg_do_sof_pos  : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal shreg_do_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shreg_do_eof_pos  : slv_array_t     (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal shreg_do_mfb_meta : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  TX MFB
    -- =====================================================================

    signal rd_TX_MFB_SOF_POS_arr : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(MFB_REGION_SIZE))                 -1 downto 0);
    signal rd_TX_MFB_EOF_POS_arr : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))  -1 downto 0);

    signal rd_TX_MFB_DATA        : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal rd_TX_MFB_META        : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rd_TX_MFB_SOF         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rd_TX_MFB_EOF         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rd_TX_MFB_SOF_POS     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal rd_TX_MFB_EOF_POS     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal rd_TX_MFB_SRC_RDY     : std_logic;
    signal rd_TX_MFB_DST_RDY     : std_logic;

    signal tx_mfb_aux_src_rdy    : std_logic;
    signal tx_mfb_aux_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Packet sent info propagation
    -- =====================================================================

    constant PACS_DATA_WIDTH : natural := log2(CHANNELS)
                                         +log2(PKT_SIZE_MAX+1)
                                         +1;

    signal pacs_di    : std_logic_vector(MFB_REGIONS*PACS_DATA_WIDTH-1 downto 0);
    signal pacs_wr    : std_logic;
    signal pacs_full  : std_logic;
    signal pacs_do    : std_logic_vector(MFB_REGIONS*PACS_DATA_WIDTH-1 downto 0);
    signal pacs_rd    : std_logic;
    signal pacs_empty : std_logic;

    signal pacs_di_arr : slv_array_t(MFB_REGIONS-1 downto 0)(PACS_DATA_WIDTH-1 downto 0);
    signal pacs_do_arr : slv_array_t(MFB_REGIONS-1 downto 0)(PACS_DATA_WIDTH-1 downto 0);

    -- =====================================================================

begin

    assert (MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH=BUF_BLOCKS*DATA_BLOCK_WIDTH)
        report "ERROR: MFB_CROSSBARX_OUTPUT_BUFFER: The width of the internal buffer ("&to_string(BUF_BLOCKS*DATA_BLOCK_WIDTH)&") is different from the width of the output MFB ("&to_string(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)&")!"
        severity failure;

    -- =====================================================================
    --  Main Buffer
    -- =====================================================================

    main_buffer_gen : for i in 0 to BUF_BLOCKS-1 generate

        main_buffer_i : entity work.SDP_BRAM_BE
        generic map(
            DATA_WIDTH     => DATA_BLOCK_WIDTH            ,
            ITEMS          => BUF_WORDS                   ,
            BLOCK_ENABLE   => true                        ,
            BLOCK_WIDTH    => DATA_ITEM_WIDTH             ,
            COMMON_CLOCK   => INPUT_EQ_OUTPUT             ,
            OUTPUT_REG     => true                        ,
            METADATA_WIDTH => MFB_REGIONS*SHREG_DATA_WIDTH,
            DEVICE         => SDP_BRAM_DEVICE
        )
        port map(
            WR_CLK      => CLK_IN           ,
            WR_RST      => RESET_IN         ,
            WR_EN       => WR_EN         (i),
            WR_BE       => WR_IE         (i),
            WR_ADDR     => WR_ADDR       (i),
            WR_DATA     => WR_DATA       (i),

            RD_CLK      => CLK_OUT          ,
            RD_RST      => RESET_OUT        ,
            RD_EN       => buf_rd_en     (i),
            RD_PIPE_EN  => buf_rd_pipe_en(i),
            RD_META_IN  => shreg_di_row  (i),
            RD_ADDR     => buf_rd_addr   (i),
            RD_DATA     => buf_rd_data   (i),
            RD_META_OUT => shreg_do_row  (i),
            RD_DATA_VLD => buf_rd_vld    (i)
        );

    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Header FIFOX Multi
    -- =====================================================================

    hdr_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => HDR_WIDTH    ,
        ITEMS               => (MFB_REGIONS+1)*32,
        WRITE_PORTS         => MFB_REGIONS  ,
        READ_PORTS          => MFB_REGIONS+1,
        RAM_TYPE            => "AUTO"       ,
        DEVICE              => DEVICE       ,
        ALMOST_FULL_OFFSET  => 0            ,
        ALMOST_EMPTY_OFFSET => 0            ,
        SAFE_READ_MODE      => true
    )
    port map(
        CLK    => CLK_OUT  ,
        RESET  => RESET_OUT,

        DI     => hdrf_di   ,
        WR     => hdrf_wr   ,
        FULL   => hdrf_full ,
        AFULL  => open      ,

        DO     => hdrf_do   ,
        RD     => hdrf_rd   ,
        EMPTY  => hdrf_empty,
        AEMPTY => open
    );

    -- Input
    hdrf_di_gen : for i in 0 to MFB_REGIONS-1 generate
        rx_hdr_sof_addr(i) <= RX_HDR_ADDR(i);
        rx_hdr_eof_addr(i) <= std_logic_vector(unsigned(RX_HDR_ADDR(i))+resize_left(unsigned(RX_HDR_LEN(i)),log2(BUF_BYTES))-1);

        hdrf_di_arr    (i) <= RX_HDR_META(i) & RX_HDR_MFB_META(i) & RX_HDR_CHAN(i) & rx_hdr_sof_addr(i) & rx_hdr_eof_addr(i) & RX_HDR_LEN(i);
    end generate;
    hdrf_di <= slv_array_ser(hdrf_di_arr);

    hdrf_wr <= RX_HDR_VLD and RX_HDR_SRC_RDY;
    RX_HDR_DST_RDY <= not hdrf_full;

    -- Output
    hdrf_do_arr <= slv_array_deser(hdrf_do,MFB_REGIONS+1);
    hdrf_do_gen : for i in 0 to MFB_REGIONS+1-1 generate
        signal tmp_meta         : std_logic_vector(HDR_META_WIDTH-1 downto 0);
        signal tmp_mfb_meta     : std_logic_vector(MFB_META_WIDTH-1 downto 0);
        signal tmp_chan         : std_logic_vector(log2(CHANNELS)-1 downto 0);
        signal tmp_sof_addr     : std_logic_vector(log2(BUF_BYTES)-1 downto 0);
        signal tmp_eof_addr     : std_logic_vector(log2(BUF_BYTES)-1 downto 0);
        signal tmp_len          : std_logic_vector(log2(PKT_SIZE_MAX+1)-1 downto 0);

        signal tmp_sof_addr_mfb : unsigned(log2(BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        signal tmp_eof_addr_mfb : unsigned(log2(BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    begin
        (tmp_meta    ,
         tmp_mfb_meta,
         tmp_chan    ,
         tmp_sof_addr,
         tmp_eof_addr,
         tmp_len      ) <= hdrf_do_arr(i);

        hdrf_do_meta    (i) <= tmp_meta;
        hdrf_do_mfb_meta(i) <= tmp_mfb_meta;
        hdrf_do_chan    (i) <= tmp_chan;
        hdrf_do_sof_addr(i) <= unsigned(tmp_sof_addr);
        hdrf_do_eof_addr(i) <= unsigned(tmp_eof_addr);
        hdrf_do_len     (i) <= tmp_len;

        --sof_debug_p : process (CLK_OUT)
        --begin
        --    if (rising_edge(CLK_OUT)) then
        --        if (hdrf_empty(i) = '0') and (hdrf_rd(i) = '1') then
        --            report "Output buffer, paket " & to_string(i) &
        --                   " ma SOF " & to_string(to_integer(hdrf_do_sof_addr(i)))
        --            severity note;
        --        end if;
        --    end if;
        --end process;

        -- Parse SOF and EOF addr to parts (convert from data item width to output MFB item width)
        tmp_sof_addr_mfb <= enlarge_right(enlarge_right(unsigned(tmp_sof_addr),log2(DATA_ITEM_WIDTH)),-log2(MFB_ITEM_WIDTH));
        hdrf_do_sof_addr_word  (i) <= tmp_sof_addr_mfb(log2(BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE));
        hdrf_do_sof_addr_region(i) <= tmp_sof_addr_mfb(log2(          MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(            MFB_REGION_SIZE*MFB_BLOCK_SIZE));
        hdrf_do_sof_addr_block (i) <= tmp_sof_addr_mfb(log2(                      MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(                            MFB_BLOCK_SIZE));
        hdrf_do_sof_addr_item  (i) <= tmp_sof_addr_mfb(log2(                                      MFB_BLOCK_SIZE)-1 downto log2(                                         0));

        tmp_eof_addr_mfb <= enlarge_right(enlarge_right(unsigned(tmp_eof_addr),log2(DATA_ITEM_WIDTH)),-log2(MFB_ITEM_WIDTH));
        hdrf_do_eof_addr_word  (i) <= tmp_eof_addr_mfb(log2(BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE));
        hdrf_do_eof_addr_region(i) <= tmp_eof_addr_mfb(log2(          MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(            MFB_REGION_SIZE*MFB_BLOCK_SIZE));
        hdrf_do_eof_addr_block (i) <= tmp_eof_addr_mfb(log2(                      MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(                            MFB_BLOCK_SIZE));
        hdrf_do_eof_addr_item  (i) <= tmp_eof_addr_mfb(log2(                                      MFB_BLOCK_SIZE)-1 downto log2(                                         0));

        hdrf_rd(i) <= '1' when     hdrf_do_eof_addr_word(i)=rd_ptr_word -- Currently reading the last word of this Packet
                               and TX_MFB_DST_RDY='1'                   -- Can send new MFB data
                               and txhf_full='0'                        -- Can send new MVB data
                               and pacs_full='0'                        -- Can send 'Packet sent' info
                      else '0';
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Buffer read pointer register
    -- =====================================================================

    rd_ptr_reg_pr : process (CLK_OUT)
    begin
        if (rising_edge(CLK_OUT)) then

            if (TX_MFB_DST_RDY='1' and txhf_full='0' and pacs_full='0') then
                for i in 0 to MFB_REGIONS-1 loop
                    if (hdrf_empty(i)='0') then
                        if (hdrf_do_eof_addr_word(i)=rd_ptr_word) then
                            -- Move read pointer after the last read Packet
                            rd_ptr_reg <= hdrf_do_eof_addr(i)+1;
                            if (hdrf_empty(i+1)='0') then
                                -- Move read to start of the next word (create an empty word if the next packet starts later on)
                                rd_ptr_reg <= resize_right(resize_right(rd_ptr_reg,log2(BUF_WORDS))+1,log2(BUF_BYTES));
                            end if;
                        else
                            -- Move read to start of the next word
                            rd_ptr_reg <= resize_right(resize_right(rd_ptr_reg,log2(BUF_WORDS))+1,log2(BUF_BYTES));
                        end if;
                    end if;
                end loop;
            end if;

            if (RESET_OUT='1') then
                rd_ptr_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- Parse read pointer to parts (convert from data item width to output MFB item width)
    rd_ptr_mfb    <= enlarge_right(enlarge_right(rd_ptr_reg,log2(DATA_ITEM_WIDTH)),-log2(MFB_ITEM_WIDTH));
    rd_ptr_word   <= rd_ptr_mfb(log2(BUF_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    rd_ptr_region <= rd_ptr_mfb(log2(          MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(            MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    rd_ptr_block  <= rd_ptr_mfb(log2(                      MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto log2(                            MFB_BLOCK_SIZE));
    rd_ptr_item   <= rd_ptr_mfb(log2(                                      MFB_BLOCK_SIZE)-1 downto                                                0);

    rd_ptr_asynch_g : if (META_EQ_OUTPUT) generate
        a_rd_ptr_data <= std_logic_vector(rd_ptr_reg);
        a_rd_ptr_vld  <= hdrf_rd(0) and (not hdrf_empty(0));
    else generate
        -- Propagate pointer to output through asynch FIFO
        rd_ptr_asfifo_i : entity work.ASFIFOX
        generic map(
            DATA_WIDTH => log2(BUF_BYTES),
            ITEMS      => 16             ,
            RAM_TYPE   => "LUT"          ,
            FWFT_MODE  => true           ,
            OUTPUT_REG => true           ,
            DEVICE     => DEVICE
        )
        port map(
            WR_CLK    => CLK_OUT                     ,
            WR_RST    => RESET_OUT                   ,
            WR_DATA   => std_logic_vector(rd_ptr_reg),
            WR_EN     => '1'                         ,
            WR_FULL   => open                        ,

            RD_CLK    => CLK_META      ,
            RD_RST    => RESET_META    ,
            RD_DATA   => a_rd_ptr_data ,
            RD_EN     => '1'           ,
            RD_EMPTY  => a_rd_ptr_n_vld
        );

        a_rd_ptr_vld <= not a_rd_ptr_n_vld;
    end generate;

    -- Propagate stable value
    out_rd_ptr_reg_pr : process (CLK_META)
    begin
        if (rising_edge(CLK_META)) then

            if (a_rd_ptr_vld='1') then
                RD_PTR <= a_rd_ptr_data;
            end if;

            if (RESET_META='1') then
                RD_PTR <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================

    -- =====================================================================
    --  TX MVB
    -- =====================================================================

    -- Output FIFOX Multi to separate MVB and MFB TX DST RDY
    tx_mvb_fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => OUT_HDR_WIDTH,
        ITEMS               => 32           ,
        WRITE_PORTS         => MFB_REGIONS  ,
        READ_PORTS          => MVB_ITEMS    ,
        RAM_TYPE            => "AUTO"       ,
        DEVICE              => DEVICE       ,
        ALMOST_FULL_OFFSET  => 0            ,
        ALMOST_EMPTY_OFFSET => 0            ,
        SAFE_READ_MODE      => true
    )
    port map(
        CLK    => CLK_OUT  ,
        RESET  => RESET_OUT,

        DI     => txhf_di   ,
        WR     => txhf_wr   ,
        FULL   => txhf_full ,
        AFULL  => open      ,

        DO     => txhf_do   ,
        RD     => txhf_rd   ,
        EMPTY  => txhf_empty,
        AEMPTY => open
    );

    -- Input
    txhf_di_gen : for i in 0 to MFB_REGIONS-1 generate
        txhf_di_arr(i) <= hdrf_do_len(i) & hdrf_do_meta(i) & hdrf_do_chan(i);

        txhf_wr(i) <= '1' when     hdrf_do_eof_addr_word(i)=rd_ptr_word -- Currently reading the last word of this Packet
                               and TX_MFB_DST_RDY='1'                   -- Can send new MFB data
                               and hdrf_empty(i)='0'                    -- Sending at least this many Packet
                               and pacs_full='0'                        -- Can send 'Packet sent' info
                      else '0';
    end generate;
    txhf_di <= slv_array_ser(txhf_di_arr);

    -- Output
    txhf_do_arr <= slv_array_deser(txhf_do,MVB_ITEMS);
    txhf_do_gen : for i in 0 to MVB_ITEMS-1 generate
        signal tmp_len  : std_logic_vector(log2(PKT_SIZE_MAX+1)-1 downto 0);
        signal tmp_meta : std_logic_vector(HDR_META_WIDTH-1 downto 0);
        signal tmp_chan : std_logic_vector(log2(CHANNELS)-1 downto 0);
    begin
        (tmp_len ,
         tmp_meta,
         tmp_chan ) <= txhf_do_arr(i);

        txhf_do_len (i) <= tmp_len;
        txhf_do_meta(i) <= tmp_meta;
        txhf_do_chan(i) <= tmp_chan;
    end generate;

    TX_MVB_LEN      <= slv_array_ser(txhf_do_len);
    TX_MVB_HDR_META <= slv_array_ser(txhf_do_meta);
    TX_MVB_CHANNEL  <= slv_array_ser(txhf_do_chan);
    TX_MVB_VLD      <= not txhf_empty;
    TX_MVB_SRC_RDY  <= (or TX_MVB_VLD);
    txhf_rd <= (others => TX_MVB_DST_RDY);

    -- =====================================================================

    -- =====================================================================
    --  SOF and EOF
    -- =====================================================================

    -- SHREG DEPRECATED; SDP BRAM METADATA is used instead

    ---- Propagate MFB SOF/EOF info while reading from memory
    --of_shreg_i : entity work.SH_REG_BASE_STATIC
    --generic map(
    --    DATA_WIDTH      => MFB_REGIONS*SHREG_DATA_WIDTH,
    --    NUM_BITS        => MEM_LATENCY                 ,
    --    INIT_TYPE       => 0                           ,
    --    IS_CLK_INVERTED => '0'
    --)
    --port map(
    --    CLK  => CLK_OUT       ,
    --
    --    DIN  => shreg_di      ,
    --    CE   => TX_MFB_DST_RDY,
    --    DOUT => shreg_do
    --);

    -- Input
    shreg_di_pr : process (all)
        -- Debug only
        variable tmp_sof : std_logic_vector(MFB_REGIONS+1-1 downto 0);
        variable tmp_eof : std_logic_vector(MFB_REGIONS+1-1 downto 0);
    begin
        shreg_di_sof     <= (others => '0');
        shreg_di_sof_pos <= (others => (others => 'X'));
        shreg_di_eof     <= (others => '0');
        shreg_di_eof_pos <= (others => (others => 'X'));

        -- For each output MFB Region
        for i in 0 to MFB_REGIONS-1 loop
            tmp_sof := (others => '0');
            tmp_eof := (others => '0');
            -- For each input Packet
            for e in 0 to MFB_REGIONS+1-1 loop
                -- Only consider valid Packet headers
                if (hdrf_empty(e)='0') then
                    -- SOF, SOF_POS ----

                    -- If is in this word and in this region
                    if (hdrf_do_sof_addr_word(e)=rd_ptr_word and (hdrf_do_sof_addr_region(e)=i or MFB_REGIONS<2)) then
                        -- Only done on rising edge to avoid false alerts caused by simulation signal evaluation order (empty falls before data is set)
                        if (rising_edge(CLK_OUT)) then
                            -- Check that no previous Packet was in this region
                            for g in 0 to e-1 loop
                                assert (tmp_sof(g)='0' or hdrf_empty(g)='1' or hdrf_empty(e)='1')
                                    report "ERROR: MFB_CROSSBARX_OUTPUT_BUFFER: Packets on Header FIFOX Multi output "&to_string(g)&" and "&to_string(e)&
                                           "both have SOF in Region "&to_string(i)&" of data Word "&to_string(rd_ptr_word)&"!"
                                    severity failure;
                            end loop;
                        end if;

                        tmp_sof         (e) := '1';
                        shreg_di_sof    (i) <= '1';
                        shreg_di_sof_pos(i) <= std_logic_vector(hdrf_do_sof_addr_block(e));
                    end if;

                    --------------------

                    -- EOF, EOF_POS ----

                    -- If is in this word and in this region
                    if (hdrf_do_eof_addr_word(e)=rd_ptr_word and (hdrf_do_eof_addr_region(e)=i or MFB_REGIONS<2)) then
                        -- Only done on rising edge to avoid false alerts caused by simulation signal evaluation order (empty falls before data is set)
                        if (rising_edge(CLK_OUT)) then
                            -- Check that no previous Packet was in this region
                            for g in 0 to e-1 loop
                                assert (tmp_eof(g)='0' or hdrf_empty(g)='1' or hdrf_empty(e)='1')
                                    report "ERROR: MFB_CROSSBARX_OUTPUT_BUFFER: Packets on Header FIFOX Multi output "&to_string(g)&" and "&to_string(e)&
                                           "both have EOF in Region "&to_string(i)&" of data Word "&to_string(rd_ptr_word)&"!"
                                    severity failure;
                            end loop;
                        end if;

                        tmp_eof          (e) := '1';
                        shreg_di_eof     (i) <= '1';
                        shreg_di_eof_pos (i) <= std_logic_vector(hdrf_do_eof_addr_block(e)) & std_logic_vector(hdrf_do_eof_addr_item(e));
                    end if;

                    --------------------
                end if;
            end loop;

            shreg_di_arr(i) <= shreg_di_sof(i) & shreg_di_sof_pos(i) & shreg_di_eof(i) & shreg_di_eof_pos(i) & shreg_di_mfb_meta(i);
        end loop;
    end process;

    mfb_meta_valid_with_what_g : if (MFB_META_WITH_SOF) generate
        mfb_meta_with_sof_p : process (all)
        begin
            shreg_di_mfb_meta <= (others => (others => '0'));
            for i in 0 to MFB_REGIONS-1 loop
                -- For each input Packet
                for e in 0 to MFB_REGIONS+1-1 loop
                    -- Only consider valid Packet headers
                    if (hdrf_empty(e)='0') then
                        if (hdrf_do_sof_addr_word(e)=rd_ptr_word and (hdrf_do_sof_addr_region(e)=i or MFB_REGIONS<2)) then
                            shreg_di_mfb_meta(i) <= hdrf_do_mfb_meta(i); -- valid with SOF
                        end if;
                    end if;
                end loop;
            end loop;
        end process;
    else generate
        mfb_meta_with_eof_p : process (all)
        begin
            shreg_di_mfb_meta <= (others => (others => '0'));
            for i in 0 to MFB_REGIONS-1 loop
                -- For each input Packet
                for e in 0 to MFB_REGIONS+1-1 loop
                    -- Only consider valid Packet headers
                    if (hdrf_empty(e)='0') then
                        if (hdrf_do_eof_addr_word(e)=rd_ptr_word and (hdrf_do_eof_addr_region(e)=i or MFB_REGIONS<2)) then
                            shreg_di_mfb_meta(i) <= hdrf_do_mfb_meta(i); -- valid with EOF
                        end if;
                    end if;
                end loop;
            end loop;
        end process;
    end generate;

    shreg_di     <= slv_array_ser(shreg_di_arr);
    shreg_di_row(BUF_BLOCKS-1 downto 1) <= (others => (others => '0'));
    shreg_di_row(0)                     <= shreg_di;

    -- Output
    shreg_do     <= shreg_do_row(0);
    shreg_do_arr <= slv_array_deser(shreg_do,MFB_REGIONS);
    shreg_do_gen : for i in 0 to MFB_REGIONS-1 generate
    begin
        shreg_do_sof     (i) <= shreg_do_arr(i)(log2(MFB_REGION_SIZE)+1+log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)+MFB_META_WIDTH);
        shreg_do_sof_pos (i) <= shreg_do_arr(i)(log2(MFB_REGION_SIZE)+1+log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)+MFB_META_WIDTH-1 downto 1+log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)+MFB_META_WIDTH);
        shreg_do_eof     (i) <= shreg_do_arr(i)(                        log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)+MFB_META_WIDTH);
        shreg_do_eof_pos (i) <= shreg_do_arr(i)(                        log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)+MFB_META_WIDTH-1 downto                                       +MFB_META_WIDTH);
        shreg_do_mfb_meta(i) <= shreg_do_arr(i)(                                                             MFB_META_WIDTH-1 downto                                                     0);
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  TX MFB
    -- =====================================================================

    -- Read when at least one Packet is present in the data
    buf_rd_en_l <= '1' when     rd_TX_MFB_DST_RDY='1' -- Can send new MFB data
                            and txhf_full='0'      -- Can send new MVB data
                            and hdrf_empty(0)='0'  -- Sending at least one Packet
                            and pacs_full='0'      -- Can send 'Packet sent' info
                   else '0';
    buf_rd_en   <= (others => buf_rd_en_l);

    -- Propagate data
    buf_rd_pipe_en_l <= rd_TX_MFB_DST_RDY;
    buf_rd_pipe_en   <= (others => buf_rd_pipe_en_l);

    -- Read from current word reading address
    buf_rd_addr <= (others => std_logic_vector(rd_ptr_word));

    -- Propagate data read from buffer
    rd_TX_MFB_DATA    <= slv_array_ser(buf_rd_data);
    rd_TX_MFB_SRC_RDY <= buf_rd_vld(0);

    -- Propagate SOF/EOF info from shreg
    rd_TX_MFB_SOF     <= shreg_do_sof;
    rd_TX_MFB_EOF     <= shreg_do_eof;
    -- Resize to fit max(1,...)
    tx_mfb_pos_gen : for i in 0 to MFB_REGIONS-1 generate
        rd_TX_MFB_SOF_POS_arr(i) <= std_logic_vector(resize_left(unsigned(shreg_do_sof_pos(i)),max(1,log2(MFB_REGION_SIZE))));
        rd_TX_MFB_EOF_POS_arr(i) <= std_logic_vector(resize_left(unsigned(shreg_do_eof_pos(i)),max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))));
    end generate;
    rd_TX_MFB_SOF_POS <= slv_array_ser(rd_TX_MFB_SOF_POS_arr);
    rd_TX_MFB_EOF_POS <= slv_array_ser(rd_TX_MFB_EOF_POS_arr);

    rd_TX_MFB_META <= slv_array_ser(shreg_do_mfb_meta);

    -- Auxiliary signals unit for invalidation of empty Words
    tx_mfb_aux_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map(
        REGIONS       => MFB_REGIONS    ,
        REGION_SIZE   => MFB_REGION_SIZE,
        BLOCK_SIZE    => MFB_BLOCK_SIZE ,
        ITEM_WIDTH    => MFB_ITEM_WIDTH ,
        META_WIDTH    => MFB_META_WIDTH ,
        REGION_AUX_EN => true           ,
        BLOCK_AUX_EN  => false          ,
        ITEM_AUX_EN   => false
    )
    port map(
        CLK              => CLK_OUT  ,
        RESET            => RESET_OUT,

        RX_DATA          => rd_TX_MFB_DATA    ,
        RX_META          => rd_TX_MFB_META    ,
        RX_SOF           => rd_TX_MFB_SOF     ,
        RX_EOF           => rd_TX_MFB_EOF     ,
        RX_SOF_POS       => rd_TX_MFB_SOF_POS ,
        RX_EOF_POS       => rd_TX_MFB_EOF_POS ,
        RX_SRC_RDY       => rd_TX_MFB_SRC_RDY ,
        RX_DST_RDY       => rd_TX_MFB_DST_RDY ,

        TX_DATA          => TX_MFB_DATA       ,
        TX_META          => TX_MFB_META       ,
        TX_SOF           => TX_MFB_SOF        ,
        TX_EOF           => TX_MFB_EOF        ,
        TX_SOF_POS       => TX_MFB_SOF_POS    ,
        TX_EOF_POS       => TX_MFB_EOF_POS    ,
        TX_SRC_RDY       => tx_mfb_aux_src_rdy,
        TX_DST_RDY       => TX_MFB_DST_RDY    ,

        TX_REGION_SHARED => open              ,
        TX_REGION_VLD    => tx_mfb_aux_vld    ,
        TX_BLOCK_VLD     => open              ,
        TX_ITEM_VLD      => open
    );

    -- Words with no valid Regions do not have SRC_RDY
    TX_MFB_SRC_RDY <= tx_mfb_aux_src_rdy and (or tx_mfb_aux_vld);

    -- =====================================================================

    -- =====================================================================
    --  Packet sent info propagation
    -- =====================================================================

    pac_sent_asynch_g : if (META_EQ_OUTPUT) generate

        pacs_do    <= pacs_di;
        pacs_empty <= not pacs_wr;
        pacs_full  <= not pacs_rd;

    else generate

        -- Propagate info to output through asynch FIFO
        pac_sent_asfifox_i : entity work.ASFIFOX
        generic map(
            DATA_WIDTH          => MFB_REGIONS*PACS_DATA_WIDTH,
            ITEMS               => 32    ,
            RAM_TYPE            => "LUT" ,
            FWFT_MODE           => true  ,
            OUTPUT_REG          => true  ,
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0     ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            WR_CLK    => CLK_OUT   ,
            WR_RST    => RESET_OUT ,
            WR_DATA   => pacs_di   ,
            WR_EN     => pacs_wr   ,
            WR_FULL   => pacs_full ,
            WR_AFULL  => open      ,
            WR_STATUS => open      ,

            RD_CLK    => CLK_META  ,
            RD_RST    => RESET_META,
            RD_DATA   => pacs_do   ,
            RD_EN     => pacs_rd   ,
            RD_EMPTY  => pacs_empty,
            RD_AEMPTY => open      ,
            RD_STATUS => open
        );

    end generate;

    -- Input
    pacs_di_gen : for i in 0 to MFB_REGIONS-1 generate
        pacs_di_arr(i) <= hdrf_do_chan(i) & hdrf_do_len(i) & (hdrf_rd(i) and (not hdrf_empty(i)));
    end generate;
    pacs_di <= slv_array_ser(pacs_di_arr);

    pacs_wr <= '1' when     hdrf_do_eof_addr_word(0)=rd_ptr_word -- Currently reading the last word of at least one packet
                        and TX_MFB_DST_RDY='1'                   -- Can send new MFB data
                        and hdrf_empty(0)='0'                    -- Sending at least one Packet
                        and txhf_full='0'                        -- Can send new MVB data
               else '0';

    -- Output
    pacs_do_arr <= slv_array_deser(pacs_do,MFB_REGIONS);
    pacs_do_gen : for i in 0 to MFB_REGIONS-1 generate
        signal tmp_chan    : std_logic_vector(log2(CHANNELS)-1 downto 0);
        signal tmp_len     : std_logic_vector(log2(PKT_SIZE_MAX+1)-1 downto 0);
        signal tmp_src_rdy : std_logic;
    begin
        (tmp_chan   ,
         tmp_len    ,
         tmp_src_rdy ) <= pacs_do_arr(i);

        PKT_SENT_CHAN   (i) <= tmp_chan;
        PKT_SENT_LEN    (i) <= tmp_len;
        PKT_SENT_SRC_RDY(i) <= tmp_src_rdy and (not pacs_empty);
    end generate;

    pacs_rd <= PKT_SENT_DST_RDY;

    -- =====================================================================

end architecture;
