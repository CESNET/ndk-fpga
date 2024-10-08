-- ptc_full.vhd: PCIE_TRANSACTION_CTRL implementation
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

architecture full of PCIE_TRANSACTION_CTRL is

    function getDmaUphdrWidthDW return integer is
        variable width : integer := 0;
    begin
        width := DMA_UPHDR_WIDTH/(8*4);
        if ((DMA_UPHDR_WIDTH mod (8*4))/=0) then
            width := width + 1;
        end if;
        return width;
    end function;

    function getPcieLowAddrWidth return integer is
        variable width : integer := 12;
    begin
        width := 12;
        if (DEVICE="STRATIX10" or DEVICE="AGILEX") then
            width := 7;
        end if;
        return width;
    end function;

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    constant DOWN_ASFIFO_AFULL_OFFSET : integer := 32;--4+4+1; -- Based on number of pipe levels from Down storage FIFO to Down ASFIFO. +4 because PRECISE_FULL is false. +1 for afull register

    constant DMA_REQUEST_LEN_WIDTH    : integer := DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1;
    constant DMA_UPHDR_WIDTH_DW       : integer := getDmaUphdrWidthDW;

    constant MFB_UP_WIDTH             : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH;
    constant MFB_DOWN_WIDTH           : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH;

    -- Width of 'lower address' field in PCIE completion header
    constant PCIE_LOW_ADDR_WIDTH      : integer := getPcieLowAddrWidth;

    -- HDM (Header Data Merge) MFB FIFO is ready for 16 MPS transaction
    constant HDM_MFB_FIFO_DEPTH       : integer := (16*MPS*8)/MFB_UP_WIDTH;
    -- CODAPA counter must hold all transaction (1 transaction per region) in HDM MFB FIFO
    constant CODAPA_CNT_WIDTH         : integer := log2(MFB_UP_REGIONS*HDM_MFB_FIFO_DEPTH)+1;

    -- This constant can be used to disable Down Storage FIFO unit
    -- on some devices.
    -- (DEVICE="ULTRASCALE")
    constant DISABLE_STFIFO           : boolean := false;
    constant CUT_HDR_BYPASS_DEV       : boolean := (DEVICE="STRATIX10" and ENDPOINT_TYPE/="H_TILE") or (DEVICE="AGILEX");
    constant INTEL_DEV                : boolean := (DEVICE="STRATIX10" or DEVICE="AGILEX");

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    -- UP MVB ASFIFO output / UP MVB Transformer input
    signal up_mvb_asfifo_out_data     : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal up_mvb_asfifo_out_vld      : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_UP_ITEMS                -1 downto 0);
    signal up_mvb_asfifo_out_src_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);
    signal up_mvb_asfifo_out_dst_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);

    -- UP MVB Transformer output / AXI2PCIE hdr transform input
    signal up_mvb_trans_out_data     : slv_array_t(DMA_PORTS-1 downto 0)(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal up_mvb_trans_out_vld      : slv_array_t(DMA_PORTS-1 downto 0)(MVB_UP_ITEMS                -1 downto 0);
    signal up_mvb_trans_out_payload  : slv_array_t(DMA_PORTS-1 downto 0)(MVB_UP_ITEMS                -1 downto 0);
    signal up_mvb_trans_out_src_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);
    signal up_mvb_trans_out_dst_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);

    -- UP MFB ASFIFO output / MFB hdr Tranformer input
    signal up_mfb_asfifo_out_data    : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0);
    signal up_mfb_asfifo_out_sof_pos : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0);
    signal up_mfb_asfifo_out_eof_pos : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0);
    signal up_mfb_asfifo_out_sof     : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0);
    signal up_mfb_asfifo_out_eof     : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0);
    signal up_mfb_asfifo_out_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0);
    signal up_mfb_asfifo_out_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0);

    -- UP MFB Tranformer output / MFB hdr data merge input
    signal up_mfb_trans_out_data     : slv_array_t(DMA_PORTS-1 downto 0)(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0);
    signal up_mfb_trans_out_sof_pos  : slv_array_t(DMA_PORTS-1 downto 0)(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0);
    signal up_mfb_trans_out_eof_pos  : slv_array_t(DMA_PORTS-1 downto 0)(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0);
    signal up_mfb_trans_out_sof      : slv_array_t(DMA_PORTS-1 downto 0)(MFB_UP_REGIONS-1 downto 0);
    signal up_mfb_trans_out_eof      : slv_array_t(DMA_PORTS-1 downto 0)(MFB_UP_REGIONS-1 downto 0);
    signal up_mfb_trans_out_src_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);
    signal up_mfb_trans_out_dst_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);

    -- UP MVB ports Merger output /  UP MVB Merger FIFO input
    signal up_mvb_merge_out_data     : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal up_mvb_merge_out_vld      : std_logic_vector(MVB_UP_ITEMS                -1 downto 0);
    signal up_mvb_merge_out_src_rdy  : std_logic;
    signal up_mvb_merge_out_dst_rdy  : std_logic;

    -- UP MVB Merger FIFO output /  UP Credit flow control input
    signal up_mvb_mrgfi_out_data     : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal up_mvb_mrgfi_out_vld      : std_logic_vector(MVB_UP_ITEMS                -1 downto 0);
    signal up_mvb_mrgfi_out_src_rdy  : std_logic;
    signal up_mvb_mrgfi_out_dst_rdy  : std_logic;

    -- UP MFB ports merger output / MFB hdr data merge input
    signal up_mfb_merge_out_data    : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0);
    signal up_mfb_merge_out_sof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0);
    signal up_mfb_merge_out_eof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0);
    signal up_mfb_merge_out_sof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
    signal up_mfb_merge_out_eof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
    signal up_mfb_merge_out_src_rdy : std_logic;
    signal up_mfb_merge_out_dst_rdy : std_logic;

    -- codapa inc / MFB hdr data merge input
    signal s_codapa_inc_sync       : std_logic_vector(log2(MFB_UP_REGIONS+1)-1 downto 0);
    signal s_codapa_inc_sync_vld   : std_logic;
    signal s_codapa_inc_sync_reg   : std_logic_vector(log2(MFB_UP_REGIONS+1)-1 downto 0);

    -- credit reservation checking interface (between DMA2PCIe and Tag manager)
    signal tagm_mvb_in          : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal tagm_mvb_in_vld      : std_logic_vector(MVB_UP_ITEMS                -1 downto 0);
    signal tagm_mvb_in_src_rdy  : std_logic;
    signal tagm_mvb_in_dst_rdy  : std_logic;
    signal tagm_mvb_out         : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal tagm_mvb_out_tag     : std_logic_vector(MVB_UP_ITEMS*PCIE_TAG_WIDTH -1 downto 0);
    signal tagm_mvb_out_vld     : std_logic_vector(MVB_UP_ITEMS                -1 downto 0);
    signal tagm_mvb_out_src_rdy : std_logic := '0';
    signal tagm_mvb_out_dst_rdy : std_logic := '0';

    -- DMA2PCIe hdr transform output / CODAPA Checker input
    signal up_mvb_dma2pcie_out_data         : std_logic_vector(MVB_UP_ITEMS*PCIE_UPHDR_WIDTH     -1 downto 0);
    signal up_mvb_dma2pcie_out_be           : std_logic_vector(MVB_UP_ITEMS*8                    -1 downto 0);
    signal up_mvb_dma2pcie_out_payload      : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0);
    signal up_mvb_dma2pcie_out_payload_size : std_logic_vector(MVB_UP_ITEMS*DMA_REQUEST_LEN_WIDTH-1 downto 0);
    signal up_mvb_dma2pcie_out_type         : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0);
    signal up_mvb_dma2pcie_out_vld          : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0);
    signal up_mvb_dma2pcie_out_src_rdy      : std_logic := '0';
    signal up_mvb_dma2pcie_out_dst_rdy      : std_logic := '0';

    -- CODAPA Checker output / MFB hdr data merge input
    signal up_mvb_c_checker_out_data         : std_logic_vector(MVB_UP_ITEMS*PCIE_UPHDR_WIDTH     -1 downto 0);
    signal up_mvb_c_checker_out_be           : std_logic_vector(MVB_UP_ITEMS*8                    -1 downto 0);
    signal up_mvb_c_checker_out_payload      : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0);
    signal up_mvb_c_checker_out_payload_size : std_logic_vector(MVB_UP_ITEMS*DMA_REQUEST_LEN_WIDTH-1 downto 0);
    signal up_mvb_c_checker_out_type         : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0);
    signal up_mvb_c_checker_out_vld          : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0);
    signal up_mvb_c_checker_out_src_rdy      : std_logic := '0';
    signal up_mvb_c_checker_out_dst_rdy      : std_logic := '0';

    -- MFB get items output / MFB cutter input
    signal down_mfb_cutter_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    signal down_mfb_cutter_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    signal down_mfb_cutter_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_cutter_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_cutter_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_cutter_in_src_rdy : std_logic := '0';
    signal down_mfb_cutter_in_dst_rdy : std_logic := '0';

    -- MVB get items output / MVB storage FIFO input
    signal down_mvb_stfifo_in_data    : std_logic_vector(MVB_DOWN_ITEMS*PCIE_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_stfifo_in_vld     : std_logic_vector(MVB_DOWN_ITEMS                   -1 downto 0);
    signal down_mvb_stfifo_in_src_rdy : std_logic := '0';
    signal down_mvb_stfifo_in_dst_rdy : std_logic := '0';

    -- MFB cutter output / MFB storage FIFO input
    signal down_mfb_stfifo_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    signal down_mfb_stfifo_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    signal down_mfb_stfifo_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_stfifo_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_stfifo_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_stfifo_in_src_rdy : std_logic := '0';
    signal down_mfb_stfifo_in_dst_rdy : std_logic := '0';

    -- MVB storage FIFO output / PCIe2DMA hdr transform input
    signal down_mvb_pcie2dma_in_data          : std_logic_vector(MVB_DOWN_ITEMS*PCIE_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_pcie2dma_in_vld           : std_logic_vector(MVB_DOWN_ITEMS                   -1 downto 0);
    signal down_mvb_pcie2dma_in_src_rdy       : std_logic;
    signal down_mvb_pcie2dma_in_dst_rdy       : std_logic;
    signal down_mvb_pcie2dma_in_src_rdy_force : std_logic;

    -- tag manager tag releasing interface (between PCIe2DMA and Tag manager)
    signal tagm_tag                : std_logic_vector(MVB_DOWN_ITEMS*PCIE_TAG_WIDTH-1 downto 0);
    signal tagm_tag_compl_low_addr : std_logic_vector(MVB_DOWN_ITEMS*PCIE_LOW_ADDR_WIDTH-1 downto 0);
    signal tagm_tag_compl_len      : std_logic_vector(MVB_DOWN_ITEMS*(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1)-1 downto 0);
    signal tagm_tag_release        : std_logic_vector(MVB_DOWN_ITEMS               -1 downto 0);
    signal tagm_tag_vld            : std_logic_vector(MVB_DOWN_ITEMS               -1 downto 0);
    signal tagm_dma_down_tag       : std_logic_vector(MVB_DOWN_ITEMS*DMA_TAG_WIDTH -1 downto 0);
    signal tagm_dma_down_id        : std_logic_vector(MVB_DOWN_ITEMS*DMA_ID_WIDTH  -1 downto 0);

    signal down_mvb_tfifo_in_data    : std_logic_vector(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_tfifo_in_vld     : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    signal down_mvb_tfifo_in_src_rdy : std_logic;
    signal down_mvb_tfifo_in_dst_rdy : std_logic;
    signal down_mvb_tfifo_afull      : std_logic;
    signal down_mvb_tfifo_afull_reg  : std_logic;
    signal down_mvb_tfifo_in_err_reg : std_logic;

    -- PCIe2DMA hdr transform output / DOWN Splitter MVB input
    signal down_mvb_split_in_data       : std_logic_vector(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_split_in_data_arr   : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(DMA_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_split_in_tag_arr    : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(DMA_COMPLETION_TAG_W-1 downto 0);
    signal down_mvb_split_in_switch_arr : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(log2(DMA_PORTS)-1 downto 0);
    signal down_mvb_split_in_switch     : std_logic_vector(MVB_DOWN_ITEMS*log2(DMA_PORTS)-1 downto 0);
    signal down_mvb_split_in_vld        : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    signal down_mvb_split_in_src_rdy    : std_logic;
    signal down_mvb_split_in_dst_rdy    : std_logic;

    -- MFB storage FIFO output / DOWN Splitter MFB FIFO input
    signal down_mfb_splfi_in_data         : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    signal down_mfb_splfi_in_sof_pos      : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    signal down_mfb_splfi_in_eof_pos      : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_splfi_in_sof          : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_splfi_in_eof          : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_splfi_in_src_rdy      : std_logic;
    signal down_mfb_splfi_in_dst_rdy      : std_logic;

    -- DOWN Splitter MFB FIFO output / DOWN Splitter MFB input
    signal down_mfb_split_in_data         : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    signal down_mfb_split_in_sof_pos      : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    signal down_mfb_split_in_eof_pos      : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_split_in_sof          : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_split_in_eof          : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_split_in_src_rdy      : std_logic;
    signal down_mfb_split_in_dst_rdy      : std_logic;

    -- DOWN Splitter MVB output / DOWN MVB Transformer input
    signal down_mvb_trans_in_data     : slv_array_t(DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_trans_in_vld      : slv_array_t(DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS                  -1 downto 0);
    signal down_mvb_trans_in_src_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mvb_trans_in_dst_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);

    -- DOWN MVB Transformer output / DOWN MVB ASFIFO input
    signal down_mvb_asfifo_in_data    : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
    signal down_mvb_asfifo_in_vld     : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_DOWN_ITEMS                  -1 downto 0) := (others => (others => '0'));
    signal down_mvb_asfifo_in_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mvb_asfifo_in_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mvb_asfifo_afull      : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mvb_asfifo_afull_reg  : std_logic_vector(DMA_PORTS-1 downto 0);

    -- DOWN Splitter MFB output / DOWN MFB Transformer input
    signal down_mfb_trans_in_data     : slv_array_t(DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    signal down_mfb_trans_in_sof_pos  : slv_array_t(DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    signal down_mfb_trans_in_eof_pos  : slv_array_t(DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_trans_in_sof      : slv_array_t(DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_trans_in_eof      : slv_array_t(DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_trans_in_src_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mfb_trans_in_dst_rdy  : std_logic_vector(DMA_PORTS-1 downto 0);

    -- DOWN MFB Transformer output / DOWN MFB ASFIFO input
    signal down_mfb_asfifo_in_data    : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    signal down_mfb_asfifo_in_sof_pos : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    signal down_mfb_asfifo_in_eof_pos : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    signal down_mfb_asfifo_in_sof     : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_asfifo_in_eof     : slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0);
    signal down_mfb_asfifo_in_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mfb_asfifo_in_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mfb_asfifo_afull      : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mfb_asfifo_afull_reg  : std_logic_vector(DMA_PORTS-1 downto 0);

    signal down_afull_flag : std_logic;

    ---------------------------------------------------------------------------
    -- debug signals
    signal down_storage_fifo_err_reg    : std_logic;
    signal down_mvb_asynch_fifo_err_reg : std_logic_vector(DMA_PORTS-1 downto 0);
    signal down_mfb_asynch_fifo_err_reg : std_logic_vector(DMA_PORTS-1 downto 0);

    signal dbg_rc_cnt               : unsigned(63 downto 0);
    signal dbg_rq_cnt               : unsigned(63 downto 0);
    signal dbg_di_mvb_cnt           : unsigned(63 downto 0);
    signal dbg_di_mfb_cnt           : unsigned(63 downto 0);

begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "PCIE_TRANSACTION_CTRL: unsupported device!" severity failure;

    assert (ENDPOINT_TYPE = "H_TILE" OR ENDPOINT_TYPE = "P_TILE" OR ENDPOINT_TYPE = "R_TILE" OR INTEL_DEV = False)
        report "PCIE_TRANSACTION_CTRL: unsupported ENDPOINT_TYPE (Intel FPGA only)!" severity failure;

    -- ========================================================================
    -- UPSTREAM
    -- ========================================================================

    dma_up_ports_g: for i in 0 to DMA_PORTS-1 generate
        ---------------------------------------------------------------------------
        -- UP MVB Asynch FIFO
        ---------------------------------------------------------------------------

        up_mvb_asynch_fifo_i : entity work.MVB_ASFIFOX
        generic map(
            DEVICE         => DEVICE         ,
            MVB_ITEM_WIDTH => DMA_UPHDR_WIDTH,
            MVB_ITEMS      => DMA_MVB_UP_ITEMS,
            FIFO_ITEMS     => UP_ASFIFO_ITEMS,
            OUTPUT_REG     => true           ,
            RAM_TYPE       => "BRAM"         ,
            FWFT_MODE      => true
        )
        port map(
            RX_CLK       => CLK_DMA  ,
            RX_RESET     => RESET_DMA,

            RX_DATA      => UP_MVB_DATA(i)   ,
            RX_VLD       => UP_MVB_VLD(i)    ,
            RX_SRC_RDY   => UP_MVB_SRC_RDY(i),
            RX_DST_RDY   => UP_MVB_DST_RDY(i),

            TX_CLK       => CLK  ,
            TX_RESET     => RESET,

            TX_DATA      => up_mvb_asfifo_out_data(i)   ,
            TX_VLD       => up_mvb_asfifo_out_vld(i)    ,
            TX_SRC_RDY   => up_mvb_asfifo_out_src_rdy(i),
            TX_DST_RDY   => up_mvb_asfifo_out_dst_rdy(i)
        );

        ---------------------------------------------------------------------------

        ---------------------------------------------------------------------------
        -- UP MVB Shakedown
        ---------------------------------------------------------------------------

        up_mvb_shake_on_g: if (MVB_UP_ITEMS /= DMA_MVB_UP_ITEMS) generate
            up_mvb_shake_i : entity work.MVB_SHAKEDOWN
            generic map(
                RX_ITEMS    => DMA_MVB_UP_ITEMS,
                TX_ITEMS    => MVB_UP_ITEMS,
                ITEM_WIDTH  => DMA_UPHDR_WIDTH,
                SHAKE_PORTS => 1
            )
            port map(
                CLK        => CLK,
                RESET      => RESET,

                RX_DATA    => up_mvb_asfifo_out_data(i)   ,
                RX_VLD     => up_mvb_asfifo_out_vld(i)    ,
                RX_SRC_RDY => up_mvb_asfifo_out_src_rdy(i),
                RX_DST_RDY => up_mvb_asfifo_out_dst_rdy(i),

                TX_DATA    => up_mvb_trans_out_data(i),
                TX_VLD     => up_mvb_trans_out_vld(i) ,
                TX_NEXT    => (others => up_mvb_trans_out_dst_rdy(i))
            );

            up_mvb_trans_out_src_rdy(i) <= or up_mvb_trans_out_vld(i);
        end generate;

        up_mvb_shake_off_g: if (MVB_UP_ITEMS = DMA_MVB_UP_ITEMS) generate
            up_mvb_trans_out_data(i)     <= up_mvb_asfifo_out_data(i);
            up_mvb_trans_out_vld(i)      <= up_mvb_asfifo_out_vld(i);
            up_mvb_trans_out_src_rdy(i)  <= up_mvb_asfifo_out_src_rdy(i);
            up_mvb_asfifo_out_dst_rdy(i) <= up_mvb_trans_out_dst_rdy(i);
        end generate;

        ---------------------------------------------------------------------------

        ---------------------------------------------------------------------------
        -- UP MFB Asynch FIFO
        ---------------------------------------------------------------------------

        up_mfb_asynch_fifo_i : entity work.MFB_ASFIFOX
        generic map(
            DEVICE           => DEVICE            ,
            MFB_REGIONS      => DMA_MFB_UP_REGIONS,
            MFB_REG_SIZE     => MFB_UP_REG_SIZE   ,
            MFB_BLOCK_SIZE   => MFB_UP_BLOCK_SIZE ,
            MFB_ITEM_WIDTH   => MFB_UP_ITEM_WIDTH ,
            FIFO_ITEMS       => UP_ASFIFO_ITEMS   ,
            OUTPUT_REG       => true              ,
            RAM_TYPE         => "BRAM"            ,
            FWFT_MODE        => true
        )
        port map(
            RX_CLK       => CLK_DMA  ,
            RX_RESET     => RESET_DMA,

            RX_DATA      => UP_MFB_DATA(i)   ,
            RX_SOF_POS   => UP_MFB_SOF_POS(i),
            RX_EOF_POS   => UP_MFB_EOF_POS(i),
            RX_SOF       => UP_MFB_SOF(i)    ,
            RX_EOF       => UP_MFB_EOF(i)    ,
            RX_SRC_RDY   => UP_MFB_SRC_RDY(i),
            RX_DST_RDY   => UP_MFB_DST_RDY(i),

            TX_CLK       => CLK  ,
            TX_RESET     => RESET,

            TX_DATA      => up_mfb_asfifo_out_data(i)   ,
            TX_SOF_POS   => up_mfb_asfifo_out_sof_pos(i),
            TX_EOF_POS   => up_mfb_asfifo_out_eof_pos(i),
            TX_SOF       => up_mfb_asfifo_out_sof(i)    ,
            TX_EOF       => up_mfb_asfifo_out_eof(i)    ,
            TX_SRC_RDY   => up_mfb_asfifo_out_src_rdy(i),
            TX_DST_RDY   => up_mfb_asfifo_out_dst_rdy(i)
        );

        ---------------------------------------------------------------------------

        ---------------------------------------------------------------------------
        -- UP MFB Transformer
        ---------------------------------------------------------------------------

        up_mfb_transformer_i : entity work.MFB_TRANSFORMER
        generic map(
            RX_REGIONS  => DMA_MFB_UP_REGIONS,
            TX_REGIONS  => MFB_UP_REGIONS,
            REGION_SIZE => MFB_UP_REG_SIZE,
            BLOCK_SIZE  => MFB_UP_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_UP_ITEM_WIDTH
        )
        port map(
            CLK         => CLK,
            RESET       => RESET,

            RX_DATA     => up_mfb_asfifo_out_data(i),
            RX_SOP      => up_mfb_asfifo_out_sof(i),
            RX_EOP      => up_mfb_asfifo_out_eof(i),
            RX_SOP_POS  => up_mfb_asfifo_out_sof_pos(i),
            RX_EOP_POS  => up_mfb_asfifo_out_eof_pos(i),
            RX_SRC_RDY  => up_mfb_asfifo_out_src_rdy(i),
            RX_DST_RDY  => up_mfb_asfifo_out_dst_rdy(i),

            TX_DATA     => up_mfb_trans_out_data(i),
            TX_SOP      => up_mfb_trans_out_sof(i),
            TX_EOP      => up_mfb_trans_out_eof(i),
            TX_SOP_POS  => up_mfb_trans_out_sof_pos(i),
            TX_EOP_POS  => up_mfb_trans_out_eof_pos(i),
            TX_SRC_RDY  => up_mfb_trans_out_src_rdy(i),
            TX_DST_RDY  => up_mfb_trans_out_dst_rdy(i)
        );

        ---------------------------------------------------------------------------
    end generate; -- end of DMA UP ports generate

    ---------------------------------------------------------------------------
    -- Merger of DMA UP ports
    ---------------------------------------------------------------------------

    up_mvb_trans_out_payload_g : for i in 0 to DMA_PORTS-1 generate
        up_mvb_trans_out_payload_g2 : for e in 0 to MVB_UP_ITEMS-1 generate
            up_mvb_trans_out_payload(i)(e) <= '1' when up_mvb_trans_out_data(i)(e*DMA_UPHDR_WIDTH+DMA_REQUEST_TYPE'high downto e*DMA_UPHDR_WIDTH+DMA_REQUEST_TYPE'low)=DMA_TYPE_WRITE else '0';
        end generate;
    end generate;

    dma_up_ports_nomerge_g : if DMA_PORTS = 1 generate
        up_mvb_mrgfi_out_data       <= up_mvb_trans_out_data   (0);
        up_mvb_mrgfi_out_vld        <= up_mvb_trans_out_vld    (0);
        up_mvb_mrgfi_out_src_rdy    <= up_mvb_trans_out_src_rdy(0);
        up_mvb_trans_out_dst_rdy(0) <= up_mvb_mrgfi_out_dst_rdy;

        up_mfb_merge_out_data       <= up_mfb_trans_out_data   (0);
        up_mfb_merge_out_sof_pos    <= up_mfb_trans_out_sof_pos(0);
        up_mfb_merge_out_eof_pos    <= up_mfb_trans_out_eof_pos(0);
        up_mfb_merge_out_sof        <= up_mfb_trans_out_sof    (0);
        up_mfb_merge_out_eof        <= up_mfb_trans_out_eof    (0);
        up_mfb_merge_out_src_rdy    <= up_mfb_trans_out_src_rdy(0);
        up_mfb_trans_out_dst_rdy(0) <= up_mfb_merge_out_dst_rdy;
    end generate;

    dma_up_ports_merge_g : if DMA_PORTS > 1 generate
        dma_up_merger_i : entity work.MFB_MERGER_GEN
        generic map(
            MERGER_INPUTS   => DMA_PORTS,
            MVB_ITEMS       => MVB_UP_ITEMS,
            MVB_ITEM_WIDTH  => DMA_UPHDR_WIDTH,
            MFB_REGIONS     => MFB_UP_REGIONS,
            MFB_REG_SIZE    => MFB_UP_REG_SIZE,
            MFB_BLOCK_SIZE  => MFB_UP_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_UP_ITEM_WIDTH,
            INPUT_FIFO_SIZE => 16,
            RX_PAYLOAD_EN   => (others => true),
            IN_PIPE_EN      => false,
            OUT_PIPE_EN     => true,
            DEVICE          => DEVICE
        )
        port map(
            CLK            => CLK,
            RESET          => RESET,

            RX_MVB_DATA    => up_mvb_trans_out_data,
            RX_MVB_PAYLOAD => up_mvb_trans_out_payload,
            RX_MVB_VLD     => up_mvb_trans_out_vld,
            RX_MVB_SRC_RDY => up_mvb_trans_out_src_rdy,
            RX_MVB_DST_RDY => up_mvb_trans_out_dst_rdy,

            RX_MFB_DATA    => up_mfb_trans_out_data,
            RX_MFB_SOF     => up_mfb_trans_out_sof,
            RX_MFB_EOF     => up_mfb_trans_out_eof,
            RX_MFB_SOF_POS => up_mfb_trans_out_sof_pos,
            RX_MFB_EOF_POS => up_mfb_trans_out_eof_pos,
            RX_MFB_SRC_RDY => up_mfb_trans_out_src_rdy,
            RX_MFB_DST_RDY => up_mfb_trans_out_dst_rdy,

            TX_MVB_DATA    => up_mvb_merge_out_data,
            TX_MVB_PAYLOAD => open,
            TX_MVB_VLD     => up_mvb_merge_out_vld,
            TX_MVB_SRC_RDY => up_mvb_merge_out_src_rdy,
            TX_MVB_DST_RDY => up_mvb_merge_out_dst_rdy,

            TX_MFB_DATA    => up_mfb_merge_out_data,
            TX_MFB_SOF     => up_mfb_merge_out_sof,
            TX_MFB_EOF     => up_mfb_merge_out_eof,
            TX_MFB_SOF_POS => up_mfb_merge_out_sof_pos,
            TX_MFB_EOF_POS => up_mfb_merge_out_eof_pos,
            TX_MFB_SRC_RDY => up_mfb_merge_out_src_rdy,
            TX_MFB_DST_RDY => up_mfb_merge_out_dst_rdy
        );

        dma_up_merger_fifo_i : entity work.MVB_FIFOX
        generic map(
            ITEMS               => MVB_UP_ITEMS   ,
            ITEM_WIDTH          => DMA_UPHDR_WIDTH,
            FIFO_DEPTH          => 32             ,
            RAM_TYPE            => "AUTO"         ,
            DEVICE              => DEVICE         ,
            ALMOST_FULL_OFFSET  => 0              ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            CLK   => CLK  ,
            RESET => RESET,

            RX_DATA    => up_mvb_merge_out_data   ,
            RX_VLD     => up_mvb_merge_out_vld    ,
            RX_SRC_RDY => up_mvb_merge_out_src_rdy,
            RX_DST_RDY => up_mvb_merge_out_dst_rdy,

            TX_DATA    => up_mvb_mrgfi_out_data   ,
            TX_VLD     => up_mvb_mrgfi_out_vld    ,
            TX_SRC_RDY => up_mvb_mrgfi_out_src_rdy,
            TX_DST_RDY => up_mvb_mrgfi_out_dst_rdy,

            STATUS     => open,
            AFULL      => open,
            AEMPTY     => open
        );
    end generate;

    ---------------------------------------------------------------------------
    -- Complet Data Packet Increment signal generation
    ---------------------------------------------------------------------------

    sum_stored_eof_i : entity work.SUM_ONE
    generic map(
        INPUT_WIDTH  => MFB_UP_REGIONS,
        OUTPUT_WIDTH => log2(MFB_UP_REGIONS+1),
        OUTPUT_REG   => True
    )
    port map(
        CLK      => CLK  ,
        RESET    => RESET,

        DIN      => up_mfb_merge_out_eof,
        DIN_MASK => (others => '1')     ,
        DIN_VLD  => up_mfb_merge_out_src_rdy and up_mfb_merge_out_dst_rdy,

        DOUT     => s_codapa_inc_sync    ,
        DOUT_VLD => s_codapa_inc_sync_vld
    );

    codapa_inc_sync_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (s_codapa_inc_sync_vld = '1') then
                s_codapa_inc_sync_reg <= s_codapa_inc_sync;
            else
                s_codapa_inc_sync_reg <= (others => '0');
            end if;

            if (RESET = '1') then
                s_codapa_inc_sync_reg <= (others => '0');
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- DMA to PCIe Header transform
    ---------------------------------------------------------------------------

    dma2pcie_hdr_trans_i : entity work.PTC_DMA2PCIE_HDR_TRANSFORM
    generic map(
        MVB_ITEMS        => MVB_UP_ITEMS    ,
        PCIE_UPHDR_WIDTH => PCIE_UPHDR_WIDTH,
        PCIE_TAG_WIDTH   => PCIE_TAG_WIDTH  ,
        TRANS_SIZE_WIDTH => DMA_REQUEST_LEN_WIDTH,
        DEVICE           => DEVICE
    )
    port map(
        CLK       => CLK  ,
        RESET     => RESET,

        RX_MVB_DATA          => up_mvb_mrgfi_out_data   ,
        RX_MVB_VLD           => up_mvb_mrgfi_out_vld    ,
        RX_MVB_SRC_RDY       => up_mvb_mrgfi_out_src_rdy,
        RX_MVB_DST_RDY       => up_mvb_mrgfi_out_dst_rdy,

        TAGM_MVB_IN          => tagm_mvb_in         ,
        TAGM_MVB_IN_VLD      => tagm_mvb_in_vld     ,
        TAGM_MVB_IN_SRC_RDY  => tagm_mvb_in_src_rdy ,
        TAGM_MVB_IN_DST_RDY  => tagm_mvb_in_dst_rdy ,

        TAGM_MVB_OUT         => tagm_mvb_out        ,
        TAGM_MVB_OUT_TAG     => tagm_mvb_out_tag    ,
        TAGM_MVB_OUT_VLD     => tagm_mvb_out_vld    ,
        TAGM_MVB_OUT_SRC_RDY => tagm_mvb_out_src_rdy,
        TAGM_MVB_OUT_DST_RDY => tagm_mvb_out_dst_rdy,

        TX_MVB_DATA          => up_mvb_dma2pcie_out_data        ,
        TX_MVB_BE            => up_mvb_dma2pcie_out_be          ,
        TX_MVB_PAYLOAD       => up_mvb_dma2pcie_out_payload     ,
        TX_MVB_PAYLOAD_SIZE  => up_mvb_dma2pcie_out_payload_size,
        TX_MVB_TYPE          => up_mvb_dma2pcie_out_type        ,
        TX_MVB_VLD           => up_mvb_dma2pcie_out_vld         ,
        TX_MVB_SRC_RDY       => up_mvb_dma2pcie_out_src_rdy     ,
        TX_MVB_DST_RDY       => up_mvb_dma2pcie_out_dst_rdy
    );

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- CODAPA Checker
    ---------------------------------------------------------------------------

    codapa_checker : entity work.PTC_CODAPA_CHECKER
    generic map(
        MVB_ITEMS           => MVB_UP_ITEMS          ,
        MVB_ITEM_WIDTH      => PCIE_UPHDR_WIDTH      ,
        TRANS_SIZE_WIDTH    => DMA_REQUEST_LEN_WIDTH ,
        CODAPA_INC_WIDTH    => log2(MFB_UP_REGIONS+1),
        CODAPA_CNT_WIDTH    => CODAPA_CNT_WIDTH      ,
        DEVICE              => DEVICE
    )
    port map(
        CLK     => CLK  ,
        RESET   => RESET,

        RX_MVB_DATA         => up_mvb_dma2pcie_out_data         ,
        RX_MVB_BE           => up_mvb_dma2pcie_out_be           ,
        RX_MVB_PAYLOAD      => up_mvb_dma2pcie_out_payload      ,
        RX_MVB_PAYLOAD_SIZE => up_mvb_dma2pcie_out_payload_size ,
        RX_MVB_TYPE         => up_mvb_dma2pcie_out_type         ,
        RX_MVB_VLD          => up_mvb_dma2pcie_out_vld          ,
        RX_MVB_SRC_RDY      => up_mvb_dma2pcie_out_src_rdy      ,
        RX_MVB_DST_RDY      => up_mvb_dma2pcie_out_dst_rdy      ,

        RX_CODAPA_INC       => s_codapa_inc_sync_reg            ,

        TX_MVB_DATA         => up_mvb_c_checker_out_data        ,
        TX_MVB_BE           => up_mvb_c_checker_out_be          ,
        TX_MVB_PAYLOAD      => up_mvb_c_checker_out_payload     ,
        TX_MVB_PAYLOAD_SIZE => up_mvb_c_checker_out_payload_size,
        TX_MVB_TYPE         => up_mvb_c_checker_out_type        ,
        TX_MVB_VLD          => up_mvb_c_checker_out_vld         ,
        TX_MVB_SRC_RDY      => up_mvb_c_checker_out_src_rdy     ,
        TX_MVB_DST_RDY      => up_mvb_c_checker_out_dst_rdy
    );

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- MFB Header data merge
    ---------------------------------------------------------------------------

    mfb_hdr_data_merge : entity work.PTC_HDR_DATA_MERGE
    generic map(
        MFB_REGIONS         => MFB_UP_REGIONS       ,
        MFB_REGION_SIZE     => MFB_UP_REG_SIZE      ,
        MFB_BLOCK_SIZE      => MFB_UP_BLOCK_SIZE    ,
        MFB_ITEM_WIDTH      => MFB_UP_ITEM_WIDTH    ,

        MVB_ITEMS           => MVB_UP_ITEMS         ,
        MVB_ITEM_WIDTH      => PCIE_UPHDR_WIDTH     ,

        MFB_FIFO_DEPTH      => HDM_MFB_FIFO_DEPTH   ,

        TRANS_SIZE_WIDTH    => DMA_REQUEST_LEN_WIDTH,
        DEVICE              => DEVICE               ,
        ENDPOINT_TYPE       => ENDPOINT_TYPE
    )
    port map(
        CLK     => CLK  ,
        RESET   => RESET,

        RX_MVB_DATA         => up_mvb_c_checker_out_data        ,
        RX_MVB_BE           => up_mvb_c_checker_out_be          ,
        RX_MVB_PAYLOAD      => up_mvb_c_checker_out_payload     ,
        RX_MVB_PAYLOAD_SIZE => up_mvb_c_checker_out_payload_size,
        RX_MVB_TYPE         => up_mvb_c_checker_out_type        ,
        RX_MVB_VLD          => up_mvb_c_checker_out_vld         ,
        RX_MVB_SRC_RDY      => up_mvb_c_checker_out_src_rdy     ,
        RX_MVB_DST_RDY      => up_mvb_c_checker_out_dst_rdy     ,

        RX_MFB_DATA         => up_mfb_merge_out_data      ,
        RX_MFB_SOF          => up_mfb_merge_out_sof       ,
        RX_MFB_EOF          => up_mfb_merge_out_eof       ,
        RX_MFB_SOF_POS      => up_mfb_merge_out_sof_pos   ,
        RX_MFB_EOF_POS      => up_mfb_merge_out_eof_pos   ,
        RX_MFB_SRC_RDY      => up_mfb_merge_out_src_rdy   ,
        RX_MFB_DST_RDY      => up_mfb_merge_out_dst_rdy   ,

        TX_MVB_DATA         => RQ_MVB_HDR_DATA,
        TX_MVB_VLD          => RQ_MVB_VLD     ,

        TX_MFB_DATA         => RQ_MFB_DATA   ,
        TX_MFB_SOF          => RQ_MFB_SOF    ,
        TX_MFB_EOF          => RQ_MFB_EOF    ,
        TX_MFB_SOF_POS      => RQ_MFB_SOF_POS,
        TX_MFB_EOF_POS      => RQ_MFB_EOF_POS,
        TX_MFB_SRC_RDY      => RQ_MFB_SRC_RDY,
        TX_MFB_DST_RDY      => RQ_MFB_DST_RDY,

        TX_MFB_BE           => RQ_MFB_BE
    );

    RQ_MVB_PREFIX_DATA <= (others => '0');

    ---------------------------------------------------------------------------

    -- ========================================================================
    -- Tag Manager
    -- ========================================================================

    ---------------------------------------------------------------------------
    -- Tag Manager unit
    ---------------------------------------------------------------------------

    tag_manager_i : entity work.PTC_TAG_MANAGER
    generic map(
        MVB_UP_ITEMS               => MVB_UP_ITEMS    ,

        MVB_DOWN_ITEMS             => MVB_DOWN_ITEMS  ,

        MFB_DOWN_REGIONS           => MFB_DOWN_REGIONS,
        MFB_DOWN_REG_SIZE          => MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH/32,

        DMA_TAG_WIDTH              => DMA_TAG_WIDTH      ,
        DMA_ID_WIDTH               => DMA_ID_WIDTH       ,

        PCIE_TAG_WIDTH             => PCIE_TAG_WIDTH     ,
        PCIE_LOW_ADDR_WIDTH        => PCIE_LOW_ADDR_WIDTH,

        CHECK_CPL_CREDITS          => not DISABLE_STFIFO ,
        EXTRA_WORDS                => DOWN_FIFO_ITEMS    ,

        AUTO_ASSIGN_TAGS           => AUTO_ASSIGN_TAGS   ,

        DMA_IN_FIFO_ITEMS          => 32,

        PCIE_IN_FIFO_ITEMS         => 32,
        PCIE_IN_FIFO_AFULL_OFFSET  => 16,

        DEVICE                     => DEVICE
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        MVB_UP_HDR_IN           => tagm_mvb_in            ,
        MVB_UP_HDR_IN_VLD       => tagm_mvb_in_vld        ,
        MVB_UP_HDR_IN_SRC_RDY   => tagm_mvb_in_src_rdy    ,
        MVB_UP_HDR_IN_DST_RDY   => tagm_mvb_in_dst_rdy    ,

        MVB_UP_HDR_OUT          => tagm_mvb_out           ,
        MVB_UP_TAG_OUT          => tagm_mvb_out_tag       ,
        MVB_UP_HDR_OUT_VLD      => tagm_mvb_out_vld       ,
        MVB_UP_HDR_OUT_SRC_RDY  => tagm_mvb_out_src_rdy   ,
        MVB_UP_HDR_OUT_DST_RDY  => tagm_mvb_out_dst_rdy   ,

        TAG_ASSIGN              => TAG_ASSIGN             ,
        TAG_ASSIGN_VLD          => TAG_ASSIGN_VLD         ,

        TAG                     => tagm_tag               ,
        TAG_COMPL_LOW_ADDR      => tagm_tag_compl_low_addr,
        TAG_COMPL_LEN           => tagm_tag_compl_len     ,
        TAG_RELEASE             => tagm_tag_release       ,
        TAG_VLD                 => tagm_tag_vld           ,

        DMA_DOWN_HDR_TAG        => tagm_dma_down_tag      ,
        DMA_DOWN_HDR_ID         => tagm_dma_down_id       ,

        RCB_SIZE                => RCB_SIZE
    );

    ---------------------------------------------------------------------------

    -- ========================================================================

    -- ========================================================================
    -- DOWNSTREAM
    -- ========================================================================

    non_p_tile_get_items_cutter_gen : if (not CUT_HDR_BYPASS_DEV) generate

        ---------------------------------------------------------------------------
        -- MFB to MFB+MVB interface convertor
        ---------------------------------------------------------------------------

        mfb_get_items_i : entity work.MFB_GET_ITEMS
        generic map(
            REGIONS          => MFB_DOWN_REGIONS   ,
            REGION_SIZE      => MFB_DOWN_REG_SIZE  ,
            BLOCK_SIZE       => MFB_DOWN_BLOCK_SIZE,
            ITEM_WIDTH       => MFB_DOWN_ITEM_WIDTH,

            MAX_FRAME_LENGHT => 2**14-1,

            EXTRACTED_ITEMS  => PCIE_DOWNHDR_WIDTH/MFB_DOWN_ITEM_WIDTH, -- must be devisible

            EXTRACTED_OFFSET => 0
        )
        port map(
            CLK        => CLK  ,
            RESET      => RESET,

            RX_DATA    => RC_MFB_DATA   ,
            RX_SOF     => RC_MFB_SOF    ,
            RX_EOF     => RC_MFB_EOF    ,
            RX_SOF_POS => RC_MFB_SOF_POS,
            RX_EOF_POS => RC_MFB_EOF_POS,
            RX_SRC_RDY => RC_MFB_SRC_RDY,
            RX_DST_RDY => RC_MFB_DST_RDY,

            TX_DATA    => down_mfb_cutter_in_data   ,
            TX_SOF     => down_mfb_cutter_in_sof    ,
            TX_EOF     => down_mfb_cutter_in_eof    ,
            TX_SOF_POS => down_mfb_cutter_in_sof_pos,
            TX_EOF_POS => down_mfb_cutter_in_eof_pos,
            TX_SRC_RDY => down_mfb_cutter_in_src_rdy,
            TX_DST_RDY => down_mfb_cutter_in_dst_rdy,

            EX_DATA    => down_mvb_stfifo_in_data   (MFB_DOWN_REGIONS*PCIE_DOWNHDR_WIDTH-1 downto 0),
            EX_VLD     => down_mvb_stfifo_in_vld    (MFB_DOWN_REGIONS-1 downto 0),
            EX_SRC_RDY => down_mvb_stfifo_in_src_rdy,
            EX_DST_RDY => down_mvb_stfifo_in_dst_rdy
        );

        down_mvb_stfifo_in_vld(MVB_DOWN_ITEMS-1 downto MFB_DOWN_REGIONS) <= (others => '0');

        ---------------------------------------------------------------------------

        ---------------------------------------------------------------------------
        -- MFB Cutter
        ---------------------------------------------------------------------------

        mfb_cutter_i : entity work.MFB_CUTTER_SIMPLE
        generic map(
            REGIONS      => MFB_DOWN_REGIONS   ,
            REGION_SIZE  => MFB_DOWN_REG_SIZE  ,
            BLOCK_SIZE   => MFB_DOWN_BLOCK_SIZE,
            ITEM_WIDTH   => MFB_DOWN_ITEM_WIDTH,

            CUTTED_ITEMS => 96/MFB_DOWN_ITEM_WIDTH
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            RX_DATA    => down_mfb_cutter_in_data   ,
            RX_SOF_POS => down_mfb_cutter_in_sof_pos,
            RX_EOF_POS => down_mfb_cutter_in_eof_pos,
            RX_SOF     => down_mfb_cutter_in_sof    ,
            RX_EOF     => down_mfb_cutter_in_eof    ,
            RX_SRC_RDY => down_mfb_cutter_in_src_rdy,
            RX_DST_RDY => down_mfb_cutter_in_dst_rdy,

            RX_CUT     => (others => '1'),

            TX_DATA    => down_mfb_stfifo_in_data   ,
            TX_SOF_POS => down_mfb_stfifo_in_sof_pos,
            TX_EOF_POS => down_mfb_stfifo_in_eof_pos,
            TX_SOF     => down_mfb_stfifo_in_sof    ,
            TX_EOF     => down_mfb_stfifo_in_eof    ,
            TX_SRC_RDY => down_mfb_stfifo_in_src_rdy,
            TX_DST_RDY => down_mfb_stfifo_in_dst_rdy
        );

        ---------------------------------------------------------------------------

    end generate;

    p_tile_get_items_cutter_bypass_gen : if (CUT_HDR_BYPASS_DEV) generate

        down_mvb_stfifo_in_data    <= RC_MVB_HDR_DATA;
        down_mvb_stfifo_in_vld     <= RC_MVB_VLD;

        down_mvb_stfifo_in_src_rdy <= RC_MFB_SRC_RDY;

        down_mfb_stfifo_in_data    <= RC_MFB_DATA;
        down_mfb_stfifo_in_sof     <= RC_MFB_SOF;
        down_mfb_stfifo_in_eof     <= RC_MFB_EOF;
        down_mfb_stfifo_in_sof_pos <= RC_MFB_SOF_POS;
        down_mfb_stfifo_in_eof_pos <= RC_MFB_EOF_POS;
        down_mfb_stfifo_in_src_rdy <= RC_MFB_SRC_RDY;
        RC_MFB_DST_RDY <= down_mfb_stfifo_in_dst_rdy;

    end generate;

    ---------------------------------------------------------------------------
    -- DOWN completion data storage FIFO
    ---------------------------------------------------------------------------

    down_storage_fifo_gen : if (not DISABLE_STFIFO) generate

        down_storage_fifo_i : entity work.PTC_STORAGE_FIFO
        generic map(
            DEVICE                 => DEVICE             ,
            MVB_ITEMS              => MVB_DOWN_ITEMS     ,
            MVB_ITEM_WIDTH         => PCIE_DOWNHDR_WIDTH ,
            MFB_REGIONS            => MFB_DOWN_REGIONS   ,
            MFB_REG_SIZE           => MFB_DOWN_REG_SIZE  ,
            MFB_BLOCK_SIZE         => MFB_DOWN_BLOCK_SIZE,
            MFB_ITEM_WIDTH         => MFB_DOWN_ITEM_WIDTH,
            MAIN_FIFO_ITEMS        => DOWN_FIFO_ITEMS    ,
            INPUT_MFB_FIFOXM_ITEMS => 8
        )
        port map(
            CLK     => CLK  ,
            RESET   => RESET,

            RX_MVB_DATA     => down_mvb_stfifo_in_data   ,
            RX_MVB_VLD      => down_mvb_stfifo_in_vld    ,
            RX_MVB_SRC_RDY  => down_mvb_stfifo_in_src_rdy,
            RX_MVB_DST_RDY  => down_mvb_stfifo_in_dst_rdy,

            RX_MFB_DATA     => down_mfb_stfifo_in_data   ,
            RX_MFB_SOF      => down_mfb_stfifo_in_sof    ,
            RX_MFB_EOF      => down_mfb_stfifo_in_eof    ,
            RX_MFB_SOF_POS  => down_mfb_stfifo_in_sof_pos,
            RX_MFB_EOF_POS  => down_mfb_stfifo_in_eof_pos,
            RX_MFB_SRC_RDY  => down_mfb_stfifo_in_src_rdy,
            RX_MFB_DST_RDY  => down_mfb_stfifo_in_dst_rdy,

            TX_MVB_DATA     => down_mvb_pcie2dma_in_data        ,
            TX_MVB_VLD      => down_mvb_pcie2dma_in_vld         ,
            TX_MVB_SRC_RDY  => down_mvb_pcie2dma_in_src_rdy,
            TX_MVB_DST_RDY  => down_mvb_pcie2dma_in_dst_rdy     ,

            TX_MFB_DATA     => down_mfb_splfi_in_data        ,
            TX_MFB_SOF      => down_mfb_splfi_in_sof         ,
            TX_MFB_EOF      => down_mfb_splfi_in_eof         ,
            TX_MFB_SOF_POS  => down_mfb_splfi_in_sof_pos     ,
            TX_MFB_EOF_POS  => down_mfb_splfi_in_eof_pos     ,
            TX_MFB_SRC_RDY  => down_mfb_splfi_in_src_rdy,
            TX_MFB_DST_RDY  => down_mfb_splfi_in_dst_rdy
        );

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (down_mfb_stfifo_in_dst_rdy = '0' and down_mfb_stfifo_in_src_rdy = '1') then
                    down_storage_fifo_err_reg <= '1';
                end if;
                if (RESET = '1') then
                    down_storage_fifo_err_reg <= '0';
                end if;
            end if;
        end process;

        assert (down_storage_fifo_err_reg /= '1')
           report "PTC: No dst_rdy part error! Writing in full DOWN MFB storage FIFO!"
           severity failure;

    else generate

        mvb_pipe_i : entity work.MVB_PIPE
        generic map(
            ITEMS       => MVB_DOWN_ITEMS    ,
            ITEM_WIDTH  => PCIE_DOWNHDR_WIDTH,
            OPT         => "SRL"             ,
            FAKE_PIPE   => false             ,
            USE_DST_RDY => true              ,
            DEVICE      => DEVICE
        )
        port map(
            CLK        => CLK  ,
            RESET      => RESET,

            RX_DATA    => down_mvb_stfifo_in_data   ,
            RX_VLD     => down_mvb_stfifo_in_vld    ,
            RX_SRC_RDY => down_mvb_stfifo_in_src_rdy,
            RX_DST_RDY => down_mvb_stfifo_in_dst_rdy,

            TX_DATA    => down_mvb_pcie2dma_in_data        ,
            TX_VLD     => down_mvb_pcie2dma_in_vld         ,
            TX_SRC_RDY => down_mvb_pcie2dma_in_src_rdy,
            TX_DST_RDY => down_mvb_pcie2dma_in_dst_rdy
        );

        mfb_pipe_i : entity work.MFB_PIPE
        generic map(
         REGIONS     => MFB_DOWN_REGIONS   ,
         REGION_SIZE => MFB_DOWN_REG_SIZE  ,
         BLOCK_SIZE  => MFB_DOWN_BLOCK_SIZE,
         ITEM_WIDTH  => MFB_DOWN_ITEM_WIDTH,
         META_WIDTH  => 0                  ,
         FAKE_PIPE   => false              ,
         USE_DST_RDY => true               ,
         PIPE_TYPE   => "SHREG"            ,
         DEVICE      => DEVICE
        )
        port map(
           CLK        => CLK  ,
           RESET      => RESET,

           RX_DATA    => down_mfb_stfifo_in_data   ,
           RX_SOF     => down_mfb_stfifo_in_sof    ,
           RX_EOF     => down_mfb_stfifo_in_eof    ,
           RX_SOF_POS => down_mfb_stfifo_in_sof_pos,
           RX_EOF_POS => down_mfb_stfifo_in_eof_pos,
           RX_SRC_RDY => down_mfb_stfifo_in_src_rdy,
           RX_DST_RDY => down_mfb_stfifo_in_dst_rdy,

           TX_DATA    => down_mfb_splfi_in_data        ,
           TX_SOF     => down_mfb_splfi_in_sof         ,
           TX_EOF     => down_mfb_splfi_in_eof         ,
           TX_SOF_POS => down_mfb_splfi_in_sof_pos     ,
           TX_EOF_POS => down_mfb_splfi_in_eof_pos     ,
           TX_SRC_RDY => down_mfb_splfi_in_src_rdy,
           TX_DST_RDY => down_mfb_splfi_in_dst_rdy
        );

    end generate;

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- PCIe to DMA Header transform
    ---------------------------------------------------------------------------

    down_mvb_pcie2dma_in_dst_rdy <= not down_mvb_tfifo_afull_reg;
    down_mvb_pcie2dma_in_src_rdy_force <= down_mvb_pcie2dma_in_src_rdy and not down_mvb_tfifo_afull_reg;

    pcie2dma_hdr_transform_i : entity work.PTC_PCIE2DMA_HDR_TRANSFORM
    generic map(
        MVB_ITEMS           => MVB_DOWN_ITEMS    ,

        PCIE_DOWNHDR_WIDTH  => PCIE_DOWNHDR_WIDTH,

        DMA_TAG_WIDTH       => DMA_TAG_WIDTH     ,
        DMA_ID_WIDTH        => DMA_ID_WIDTH      ,

        PCIE_TAG_WIDTH      => PCIE_TAG_WIDTH    ,
        PCIE_LOW_ADDR_WIDTH => PCIE_LOW_ADDR_WIDTH,

        DEVICE              => DEVICE
    )
    port map(
        CLK      => CLK  ,
        RESET    => RESET,

        RX_MVB_DATA        => down_mvb_pcie2dma_in_data   ,
        RX_MVB_VLD         => down_mvb_pcie2dma_in_vld    ,
        RX_MVB_SRC_RDY     => down_mvb_pcie2dma_in_src_rdy_force,

        TAG                => tagm_tag               ,
        TAG_COMPL_LOW_ADDR => tagm_tag_compl_low_addr,
        TAG_COMPL_LEN      => tagm_tag_compl_len     ,
        TAG_RELEASE        => tagm_tag_release       ,
        TAG_VLD            => tagm_tag_vld           ,

        DMA_DOWN_HDR_TAG   => tagm_dma_down_tag,
        DMA_DOWN_HDR_ID    => tagm_dma_down_id ,

        TX_MVB_DATA        => down_mvb_tfifo_in_data   ,
        TX_MVB_VLD         => down_mvb_tfifo_in_vld    ,
        TX_MVB_SRC_RDY     => down_mvb_tfifo_in_src_rdy
    );

    down_mvb_tfifo_i : entity work.MVB_FIFOX
    generic map(
        ITEMS               => MVB_DOWN_ITEMS,
        ITEM_WIDTH          => DMA_DOWNHDR_WIDTH,
        FIFO_DEPTH          => 16,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 8,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA    => down_mvb_tfifo_in_data,
        RX_VLD     => down_mvb_tfifo_in_vld,
        RX_SRC_RDY => down_mvb_tfifo_in_src_rdy,
        RX_DST_RDY => down_mvb_tfifo_in_dst_rdy,

        TX_DATA    => down_mvb_split_in_data,
        TX_VLD     => down_mvb_split_in_vld,
        TX_SRC_RDY => down_mvb_split_in_src_rdy,
        TX_DST_RDY => down_mvb_split_in_dst_rdy,

        STATUS     => open,
        AFULL      => down_mvb_tfifo_afull,
        AEMPTY     => open
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            down_mvb_tfifo_afull_reg <= down_mvb_tfifo_afull;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (down_mvb_tfifo_in_dst_rdy = '0' and down_mvb_tfifo_in_src_rdy = '1') then
                down_mvb_tfifo_in_err_reg <= '1';
            end if;
            if (RESET = '1') then
                down_mvb_tfifo_in_err_reg <= '0';
            end if;
        end if;
    end process;

    assert (down_mvb_tfifo_in_err_reg /= '1')
       report "PTC: No dst_rdy error! Writing in full DOWN MVB TFIFO!"
       severity failure;

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- DOWN Splitter to DMA DOWN ports
    ---------------------------------------------------------------------------

    down_mvb_split_in_data_arr <= slv_array_deser(down_mvb_split_in_data,MVB_DOWN_ITEMS);
    down_mvb_split_in_switch_g : for i in 0 to MVB_DOWN_ITEMS-1 generate
        down_mvb_split_in_tag_arr(i) <= down_mvb_split_in_data_arr(i)(DMA_COMPLETION_TAG);
        down_mvb_split_in_switch_arr(i) <= down_mvb_split_in_tag_arr(i)(DMA_COMPLETION_TAG_W-1 downto DMA_COMPLETION_TAG_W-log2(DMA_PORTS));
    end generate;
    down_mvb_split_in_switch <= slv_array_ser(down_mvb_split_in_switch_arr);

    dma_down_ports_nosplit_g : if DMA_PORTS = 1 generate
        down_mvb_trans_in_data   (0)   <= down_mvb_split_in_data;
        down_mvb_trans_in_vld    (0)   <= down_mvb_split_in_vld;
        down_mvb_trans_in_src_rdy(0)   <= down_mvb_split_in_src_rdy;
        down_mvb_split_in_dst_rdy      <= down_mvb_trans_in_dst_rdy(0);

        down_mfb_trans_in_data   (0)   <= down_mfb_splfi_in_data;
        down_mfb_trans_in_sof    (0)   <= down_mfb_splfi_in_sof;
        down_mfb_trans_in_eof    (0)   <= down_mfb_splfi_in_eof;
        down_mfb_trans_in_sof_pos(0)   <= down_mfb_splfi_in_sof_pos;
        down_mfb_trans_in_eof_pos(0)   <= down_mfb_splfi_in_eof_pos;
        down_mfb_trans_in_src_rdy(0)   <= down_mfb_splfi_in_src_rdy;
        down_mfb_splfi_in_dst_rdy      <= down_mfb_trans_in_dst_rdy(0);
    end generate;

    dma_down_ports_split_g : if DMA_PORTS > 1 generate
        -- FIFO for transactions freed from Storage FIFO, but not yet accepted by the Splitter
        dma_down_splitter_fifo_i : entity work.MFB_FIFOX
        generic map(
            REGIONS             => MFB_DOWN_REGIONS           ,
            REGION_SIZE         => MFB_DOWN_REG_SIZE          ,
            BLOCK_SIZE          => MFB_DOWN_BLOCK_SIZE        ,
            ITEM_WIDTH          => MFB_DOWN_ITEM_WIDTH        ,
            FIFO_DEPTH          => 4*(MRRS*4*8)/MFB_DOWN_WIDTH, -- Must fit at least 1 MRRS transaction + possible gap
            RAM_TYPE            => "AUTO"                     ,
            DEVICE              => DEVICE                     ,
            ALMOST_FULL_OFFSET  => 0                          ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            CLK => CLK  ,
            RST => RESET,

            RX_DATA     => down_mfb_splfi_in_data   ,
            RX_SOF      => down_mfb_splfi_in_sof    ,
            RX_EOF      => down_mfb_splfi_in_eof    ,
            RX_SOF_POS  => down_mfb_splfi_in_sof_pos,
            RX_EOF_POS  => down_mfb_splfi_in_eof_pos,
            RX_SRC_RDY  => down_mfb_splfi_in_src_rdy,
            RX_DST_RDY  => down_mfb_splfi_in_dst_rdy,

            TX_DATA     => down_mfb_split_in_data   ,
            TX_SOF      => down_mfb_split_in_sof    ,
            TX_EOF      => down_mfb_split_in_eof    ,
            TX_SOF_POS  => down_mfb_split_in_sof_pos,
            TX_EOF_POS  => down_mfb_split_in_eof_pos,
            TX_SRC_RDY  => down_mfb_split_in_src_rdy,
            TX_DST_RDY  => down_mfb_split_in_dst_rdy,

            FIFO_STATUS => open,
            FIFO_AFULL  => open,
            FIFO_AEMPTY => open
        );

        dma_down_splitter_i : entity work.MFB_SPLITTER_GEN
        generic map(
            SPLITTER_OUTPUTS => DMA_PORTS,
            MVB_ITEMS        => MVB_DOWN_ITEMS,
            MVB_ITEM_WIDTH   => DMA_DOWNHDR_WIDTH,
            MFB_REGIONS      => MFB_DOWN_REGIONS,
            MFB_REG_SIZE     => MFB_DOWN_REG_SIZE,
            MFB_BLOCK_SIZE   => MFB_DOWN_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_DOWN_ITEM_WIDTH,
            OUTPUT_FIFO_SIZE => 16,
            OUT_PIPE_EN      => true,
            DEVICE           => DEVICE
        )
        port map(
            CLK            => CLK,
            RESET          => RESET,

            RX_MVB_DATA    => down_mvb_split_in_data,
            RX_MVB_SWITCH  => down_mvb_split_in_switch,
            RX_MVB_PAYLOAD => (others => '1'), -- all DOWN transactions from Software have data
            RX_MVB_VLD     => down_mvb_split_in_vld,
            RX_MVB_SRC_RDY => down_mvb_split_in_src_rdy,
            RX_MVB_DST_RDY => down_mvb_split_in_dst_rdy,

            RX_MFB_DATA    => down_mfb_split_in_data,
            RX_MFB_SOF     => down_mfb_split_in_sof,
            RX_MFB_EOF     => down_mfb_split_in_eof,
            RX_MFB_SOF_POS => down_mfb_split_in_sof_pos,
            RX_MFB_EOF_POS => down_mfb_split_in_eof_pos,
            RX_MFB_SRC_RDY => down_mfb_split_in_src_rdy,
            RX_MFB_DST_RDY => down_mfb_split_in_dst_rdy,

            TX_MVB_DATA    => down_mvb_trans_in_data,
            TX_MVB_VLD     => down_mvb_trans_in_vld,
            TX_MVB_SRC_RDY => down_mvb_trans_in_src_rdy,
            TX_MVB_DST_RDY => down_mvb_trans_in_dst_rdy,

            TX_MFB_DATA    => down_mfb_trans_in_data,
            TX_MFB_SOF     => down_mfb_trans_in_sof,
            TX_MFB_EOF     => down_mfb_trans_in_eof,
            TX_MFB_SOF_POS => down_mfb_trans_in_sof_pos,
            TX_MFB_EOF_POS => down_mfb_trans_in_eof_pos,
            TX_MFB_SRC_RDY => down_mfb_trans_in_src_rdy,
            TX_MFB_DST_RDY => down_mfb_trans_in_dst_rdy
        );
    end generate;

    ---------------------------------------------------------------------------

    dma_down_ports_g: for i in 0 to DMA_PORTS-1 generate

        ---------------------------------------------------------------------------
        -- DOWN MVB Resize
        ---------------------------------------------------------------------------

        down_mvb_resize_down_g: if (MVB_DOWN_ITEMS > DMA_MVB_DOWN_ITEMS) generate
            down_mvb_shake_i : entity work.MVB_SHAKEDOWN
            generic map(
                RX_ITEMS    => MVB_DOWN_ITEMS,
                TX_ITEMS    => DMA_MVB_DOWN_ITEMS,
                ITEM_WIDTH  => DMA_DOWNHDR_WIDTH,
                SHAKE_PORTS => 1
            )
            port map(
                CLK        => CLK,
                RESET      => RESET,

                RX_DATA    => down_mvb_trans_in_data(i),
                RX_VLD     => down_mvb_trans_in_vld(i),
                RX_SRC_RDY => down_mvb_trans_in_src_rdy(i),
                RX_DST_RDY => down_mvb_trans_in_dst_rdy(i),

                TX_DATA    => down_mvb_asfifo_in_data(i),
                TX_VLD     => down_mvb_asfifo_in_vld(i) ,
                TX_NEXT    => (others => down_mvb_asfifo_in_dst_rdy(i))
            );

            down_mvb_asfifo_in_src_rdy(i) <= or down_mvb_asfifo_in_vld(i);
        end generate;

        down_mvb_resize_up_g: if (MVB_DOWN_ITEMS < DMA_MVB_DOWN_ITEMS) generate
            down_mvb_asfifo_in_data(i)(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0) <= down_mvb_trans_in_data(i);
            down_mvb_asfifo_in_vld(i)(MVB_DOWN_ITEMS-1 downto 0) <= down_mvb_trans_in_vld(i);
            down_mvb_asfifo_in_src_rdy(i) <= down_mvb_trans_in_src_rdy(i);
            down_mvb_trans_in_dst_rdy(i) <= down_mvb_asfifo_in_dst_rdy(i);
        end generate;

        down_mvb_noresize_g: if (MVB_DOWN_ITEMS = DMA_MVB_DOWN_ITEMS) generate
            down_mvb_asfifo_in_data(i)    <= down_mvb_trans_in_data(i);
            down_mvb_asfifo_in_vld(i)     <= down_mvb_trans_in_vld(i);
            down_mvb_asfifo_in_src_rdy(i) <= down_mvb_trans_in_src_rdy(i);
            down_mvb_trans_in_dst_rdy(i)  <= down_mvb_asfifo_in_dst_rdy(i);
        end generate;

        ---------------------------------------------------------------------------

        ---------------------------------------------------------------------------
        -- DOWN MVB Asynch FIFO
        ---------------------------------------------------------------------------

        down_mvb_asynch_fifo_i : entity work.MVB_ASFIFOX
        generic map(
            DEVICE             => DEVICE                  ,
            MVB_ITEM_WIDTH     => DMA_DOWNHDR_WIDTH       ,
            MVB_ITEMS          => DMA_MVB_DOWN_ITEMS      ,
            FIFO_ITEMS         => DOWN_ASFIFO_ITEMS       ,
            ALMOST_FULL_OFFSET => DOWN_ASFIFO_AFULL_OFFSET,
            OUTPUT_REG         => true                    ,
            RAM_TYPE           => "BRAM"                  ,
            FWFT_MODE          => true
        )
        port map(
            RX_CLK       => CLK  ,
            RX_RESET     => RESET,

            RX_DATA      => down_mvb_asfifo_in_data(i)   ,
            RX_VLD       => down_mvb_asfifo_in_vld(i)    ,
            RX_SRC_RDY   => down_mvb_asfifo_in_src_rdy(i),
            RX_DST_RDY   => down_mvb_asfifo_in_dst_rdy(i),
            RX_AFULL     => open,

            TX_CLK       => CLK_DMA  ,
            TX_RESET     => RESET_DMA,

            TX_DATA      => DOWN_MVB_DATA(i)   ,
            TX_VLD       => DOWN_MVB_VLD(i)    ,
            TX_SRC_RDY   => DOWN_MVB_SRC_RDY(i),
            TX_DST_RDY   => DOWN_MVB_DST_RDY(i)
        );

        ---------------------------------------------------------------------------

        ---------------------------------------------------------------------------
        -- DOWN MFB Transformer
        ---------------------------------------------------------------------------

        down_mfb_transformer_i : entity work.MFB_TRANSFORMER
        generic map(
            RX_REGIONS  => MFB_DOWN_REGIONS,
            TX_REGIONS  => DMA_MFB_DOWN_REGIONS,
            REGION_SIZE => MFB_DOWN_REG_SIZE,
            BLOCK_SIZE  => MFB_DOWN_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_DOWN_ITEM_WIDTH
        )
        port map(
            CLK         => CLK,
            RESET       => RESET,

            RX_DATA     => down_mfb_trans_in_data(i),
            RX_SOP      => down_mfb_trans_in_sof(i),
            RX_EOP      => down_mfb_trans_in_eof(i),
            RX_SOP_POS  => down_mfb_trans_in_sof_pos(i),
            RX_EOP_POS  => down_mfb_trans_in_eof_pos(i),
            RX_SRC_RDY  => down_mfb_trans_in_src_rdy(i),
            RX_DST_RDY  => down_mfb_trans_in_dst_rdy(i),

            TX_DATA     => down_mfb_asfifo_in_data(i),
            TX_SOP      => down_mfb_asfifo_in_sof(i),
            TX_EOP      => down_mfb_asfifo_in_eof(i),
            TX_SOP_POS  => down_mfb_asfifo_in_sof_pos(i),
            TX_EOP_POS  => down_mfb_asfifo_in_eof_pos(i),
            TX_SRC_RDY  => down_mfb_asfifo_in_src_rdy(i),
            TX_DST_RDY  => down_mfb_asfifo_in_dst_rdy(i)
        );

        ---------------------------------------------------------------------------
        -- DOWN MFB Asynch FIFO
        ---------------------------------------------------------------------------

        down_mfb_asynch_fifo_i : entity work.MFB_ASFIFOX
        generic map(
            DEVICE              => DEVICE                  ,
            MFB_REGIONS         => DMA_MFB_DOWN_REGIONS    ,
            MFB_REG_SIZE        => MFB_DOWN_REG_SIZE       ,
            MFB_BLOCK_SIZE      => MFB_DOWN_BLOCK_SIZE     ,
            MFB_ITEM_WIDTH      => MFB_DOWN_ITEM_WIDTH     ,
            FIFO_ITEMS          => DOWN_ASFIFO_ITEMS       ,
            ALMOST_FULL_OFFSET  => DOWN_ASFIFO_AFULL_OFFSET,
            OUTPUT_REG          => true                    ,
            RAM_TYPE            => "BRAM"                  ,
            FWFT_MODE           => true
        )
        port map(
            RX_CLK       => CLK  ,
            RX_RESET     => RESET,

            RX_DATA      => down_mfb_asfifo_in_data(i),
            RX_SOF_POS   => down_mfb_asfifo_in_sof_pos(i),
            RX_EOF_POS   => down_mfb_asfifo_in_eof_pos(i),
            RX_SOF       => down_mfb_asfifo_in_sof(i),
            RX_EOF       => down_mfb_asfifo_in_eof(i),
            RX_SRC_RDY   => down_mfb_asfifo_in_src_rdy(i),
            RX_DST_RDY   => down_mfb_asfifo_in_dst_rdy(i),
            RX_AFULL     => open,

            TX_CLK       => CLK_DMA  ,
            TX_RESET     => RESET_DMA,

            TX_DATA      => DOWN_MFB_DATA(i)   ,
            TX_SOF_POS   => DOWN_MFB_SOF_POS(i),
            TX_EOF_POS   => DOWN_MFB_EOF_POS(i),
            TX_SOF       => DOWN_MFB_SOF(i)    ,
            TX_EOF       => DOWN_MFB_EOF(i)    ,
            TX_SRC_RDY   => DOWN_MFB_SRC_RDY(i),
            TX_DST_RDY   => DOWN_MFB_DST_RDY(i)
        );

        ---------------------------------------------------------------------------

    end generate;

    -- ========================================================================

    --pragma synthesis_off
    process (CLK)
        variable dbg_rq_cnt_v : unsigned(63 downto 0);
    begin
        dbg_rq_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rq_cnt <= (others => '0');
            elsif (RQ_MFB_SRC_RDY = '1' and RQ_MFB_DST_RDY = '1') then
                for i in 0 to MFB_UP_REGIONS-1 loop
                    dbg_rq_cnt_v := dbg_rq_cnt_v + RQ_MVB_VLD(i);
                end loop;
                    dbg_rq_cnt <= dbg_rq_cnt + dbg_rq_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_rc_cnt_v : unsigned(63 downto 0);
    begin
        dbg_rc_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rc_cnt <= (others => '0');
            elsif (RC_MFB_SRC_RDY = '1' and RC_MFB_DST_RDY = '1') then
                for i in 0 to MFB_DOWN_REGIONS-1 loop
                    dbg_rc_cnt_v := dbg_rc_cnt_v + RC_MVB_VLD(i);
                end loop;
                    dbg_rc_cnt <= dbg_rc_cnt + dbg_rc_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_di_cnt_v : unsigned(63 downto 0);
    begin
        dbg_di_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_di_mvb_cnt <= (others => '0');
            elsif (down_mvb_split_in_src_rdy = '1' and down_mvb_split_in_dst_rdy = '1') then
                for i in 0 to MFB_DOWN_REGIONS-1 loop
                    dbg_di_cnt_v := dbg_di_cnt_v + down_mvb_split_in_vld(i);
                end loop;
                    dbg_di_mvb_cnt <= dbg_di_mvb_cnt + dbg_di_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_di_cnt_v : unsigned(63 downto 0);
    begin
        dbg_di_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_di_mfb_cnt <= (others => '0');
            elsif (down_mfb_split_in_src_rdy = '1' and down_mfb_split_in_dst_rdy = '1') then
                for i in 0 to MFB_DOWN_REGIONS-1 loop
                    dbg_di_cnt_v := dbg_di_cnt_v + down_mfb_split_in_eof(i);
                end loop;
                    dbg_di_mfb_cnt <= dbg_di_mfb_cnt + dbg_di_cnt_v;
            end if;
        end if;
    end process;
    --pragma synthesis_on

end architecture;
