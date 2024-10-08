-- frame_unpacker.vhd: The Frame Unpacker module.
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Basic description (more information in README)
-- =========================================================================

-- This unit accepts and processes SuperPackets.
-- SuperPackets consist of one or more MFB frames.
-- Each of these ``individual`` frames has a special header:
--
-- +---------------+-----------------------------------+---------------------------------------------+
-- | Length [16 b] | User-defined [HEADER_LENGTH-16 b] |  MFB frame [60 -- (PKT_MTU-HEADER_LENGTH)]  |
-- +---------------+-----------------------------------+---------------------------------------------+
--
-- Fields description:
--
-- - Length [B] - a 16-bit number in the little-endian format specifying the length of the frame (without this header) in bytes,
-- - User-defined - the rest of the header is defined by the user.
--
-- The length field is mandatory, from which the minimum size of the header is derived.
-- The header is cut off each frame and send to output as metadata/MVB header.
--
-- The frames inside a SuperPacket are aligned according to the MFB specification, which can create small alignment
-- "gaps" between them (max MBLOCK_SIZE-1 Items). This component can also deal with frames that have the small alignment gap
-- after the last frame of the SuperPacket (i.e., when the EOF POS of the SuperPacket is extended by the alignment gap and is
-- a few Items behind the EOF POS of the individual frame).
--
entity FRAME_UNPACKER is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS           : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE       : natural := 8;
    -- Block size (in Items), must be 8.
    MFB_BLOCK_SIZE        : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH        : natural := 8;

    -- Number of MVB headers.
    MVB_ITEMS             : natural := MFB_REGIONS;
    -- Width of each MVB header (in bits).
    MVB_ITEM_WIDTH        : natural := 16;

    -- Length of the prepended header (in Items).
    -- The minimum is 2 Items (16b), which are for the Length field that is necesary for the unpacking process.
    HEADER_LENGTH         : natural := 16;
    -- Number of stages in the Offset pipeline.
    -- It is also the maximum number of individual frames inside a single SuperPacket.
    -- Must be greater than 0!
    UNPACKING_STAGES      : natural := 20;
    -- The extracted Header is output as:
    --   - Insert header to output metadata with SOF (MODE 0),
    --   - Insert header to output metadata with EOF (MODE 1),
    --   - Insert header on MVB (MODE 2).
    META_OUT_MODE         : natural := 0;

    -- Maximum size of a packet (in Items).
    PKT_MTU               : natural := 2**14;

    -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE                : string := "STRATIX10"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- =====================================================================
    --  TX MVB Headers (per each SuperPacket)
    -- =====================================================================

    RX_MVB_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    RX_MVB_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_MVB_SRC_RDY : in  std_logic;
    RX_MVB_DST_RDY : out std_logic;

    -- =====================================================================
    --  RX MFB STREAM (SuperPackets)
    -- =====================================================================

    RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY : in  std_logic;
    RX_MFB_DST_RDY : out std_logic;

    -- =====================================================================
    --  TX MFB STREAM (unpacked frames)
    -- =====================================================================

    TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Valid with SOF, EOF, or not valid at all.
    -- Contains concatenated MVB header and extracted SuperPacket header (RX_MVB_DATA & getit_indv_hdr_data).
    TX_MFB_META    : out std_logic_vector(MFB_REGIONS*(MVB_ITEM_WIDTH+HEADER_LENGTH*MFB_ITEM_WIDTH)-1 downto 0) := (others => '0');
    TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SRC_RDY : out std_logic;
    TX_MFB_DST_RDY : in  std_logic;

    -- =====================================================================
    --  TX MVB Headers (MVB and SuperPacket headers)
    -- =====================================================================

    TX_MVB_DATA    : out std_logic_vector(MFB_REGIONS*(MVB_ITEM_WIDTH+HEADER_LENGTH*MFB_ITEM_WIDTH)-1 downto 0);
    TX_MVB_VLD     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MVB_SRC_RDY : out std_logic;
    TX_MVB_DST_RDY : in  std_logic := '1'
);
end entity;

architecture FULL of FRAME_UNPACKER is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    -- Header length (in bits).
    constant HDR_WIDTH        : natural := HEADER_LENGTH*MFB_ITEM_WIDTH;
    -- Length of the Length field (in bits).
    constant LENGTH_WIDTH     : natural := 16;

    -- Width of one MFB Region.
    constant MFB_REGION_WIDTH : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    -- MFB data word width.
    constant MFB_WORD_WIDTH   : natural := MFB_REGIONS*MFB_REGION_WIDTH;
    -- MFB SOF POS width.
    constant MFB_SOFPOS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE));
    -- MFB EOF POS width.
    constant MFB_EOFPOS_WIDTH : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    -- Maximum amount of Words a single packet can stretch over.
    constant PKT_MAX_WORDS           : natural := PKT_MTU/(MFB_WORD_WIDTH/MFB_ITEM_WIDTH);
    -- SOF offset width (in Items).
    constant OFFSET_WIDTH_ITEMS      : natural := log2(PKT_MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE);
    -- SOF offset width (in Blocks).
    constant OFFSET_WIDTH_BLOCKS     : natural := log2(PKT_MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE);

    -- Offset Processor metadata:          SuPkt SOF POS    + SOF + EOF
    constant OP_META_WIDTH    : natural := MFB_SOFPOS_WIDTH + 1   + 1;
    -- Width of merged MVB and SuPkt headers.
    constant MERGED_ITEMS_WIDTH : natural := MVB_ITEM_WIDTH + HDR_WIDTH;
    -- Last Valid implementation.
    -- Options: "serial", "parallel", "prefixsum"
    constant LAST_VLD_IMPL : string := "serial";

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    subtype my_integer is integer range MFB_REGIONS-1 downto 0;
    type my_integer_vector is array(natural range <>) of my_integer;

    -- Debug cnt
    signal rx_pkt_count     : u_array_t(MFB_REGIONS downto 0)(16-1 downto 0);
    -- attribute noprune: boolean;
    -- attribute noprune of rx_pkt_count : signal is true;
    attribute preserve_for_debug : boolean;
    attribute preserve_for_debug of rx_pkt_count : signal is true;

    -- MVB headers
    signal fifoxm_data         : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal fifoxm_wr           : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal fifoxm_full         : std_logic;
    signal fifoxm_do           : std_logic_vector(MVB_ITEMS*            MVB_ITEM_WIDTH-1 downto 0);
    signal fifoxm_do_arr       : slv_array_t     (MVB_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal fifoxm_rd           : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal fifoxm_empty        : std_logic_vector(MVB_ITEMS-1 downto 0);

    signal last_eof_remapped   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_eof_respaced   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_remapped        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifoxm_output_addr  : my_integer_vector(MFB_REGIONS-1 downto 1);

    signal fifoxm_hdr_data_arr : slv_array_t     (MVB_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal fifoxm_hdr_vld_arr  : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal fifoxm_hdr_data     : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal fifoxm_hdr_vld      : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal fifoxm_hdr_src_rdy  : std_logic;
    signal fifoxm_hdr_dst_rdy  : std_logic;

    -- Input logic
    signal supkt_sof_pos_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_SOFPOS_WIDTH-1 downto 0);
    signal supkt_eof_pos_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOFPOS_WIDTH-1 downto 0);
    signal rx_supkt_meta         : slv_array_t(MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);

    signal rx_data_blocks        : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal rx_per_region_sof_pos : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(            MFB_REGION_SIZE))-1 downto 0);
    signal rx_per_word_sof_pos   : u_array_t  (MFB_REGIONS-1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))-1 downto 0);
    signal rx_global_sof_pos     : u_array_t  (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal rx_ext_length         : slv_array_t(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH  -1 downto 0);
    signal rx_full_length        : u_array_t  (MFB_REGIONS-1 downto 0)(LENGTH_WIDTH+1-1 downto 0);
    signal rx_cut_length         : u_array_t  (MFB_REGIONS-1 downto 0)(LENGTH_WIDTH  -1 downto 0);

    signal word_cnt_reg          : unsigned                         (log2(PKT_MAX_WORDS)-1 downto 0) := (others => '0');
    signal word_cnt              : u_array_t(MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);

    signal eof_propg_reg         : std_logic;
    signal eof_propg             : std_logic_vector(MFB_REGIONS   downto 0);
    signal sof_mask              : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- Offset processing pipeline
    signal rx_op_data                : slv_array_2d_t  (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal rx_op_meta                : slv_array_2d_t  (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);
    signal rx_op_offset              : u_array_2d_t    (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal rx_op_length              : u_array_2d_t    (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal rx_op_word                : u_array_2d_t    (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal rx_op_old_sof             : slv_array_t     (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_op_new_sof             : slv_array_t     (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_op_sof_mask            : slv_array_t     (UNPACKING_STAGES downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_op_src_rdy             : std_logic_vector(UNPACKING_STAGES downto 0);
    signal rx_op_dst_rdy             : std_logic_vector(UNPACKING_STAGES downto 0);
    signal first_op_dst_rdy          : std_logic;

    signal tx_op_data                : slv_array_2d_t  (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal tx_op_meta                : slv_array_2d_t  (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);
    signal tx_op_offset              : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal tx_op_word                : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal tx_op_old_sof             : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_op_sof_mask            : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_op_src_rdy             : std_logic_vector(UNPACKING_STAGES-1 downto 0);
    signal tx_op_dst_rdy             : std_logic_vector(UNPACKING_STAGES-1 downto 0);

    signal rx_sc_data                : slv_array_2d_t  (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal rx_sc_meta                : slv_array_2d_t  (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);
    signal rx_sc_offset              : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal rx_sc_word                : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal rx_sc_old_sof             : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_sc_sof_mask            : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_sc_src_rdy             : std_logic_vector(UNPACKING_STAGES-1 downto 0);
    signal rx_sc_dst_rdy             : std_logic_vector(UNPACKING_STAGES-1 downto 0);

    signal tx_sc_data                : slv_array_2d_t  (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal tx_sc_meta                : slv_array_2d_t  (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);
    signal tx_sc_offset              : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal tx_sc_length              : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal tx_sc_word                : u_array_2d_t    (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal tx_sc_old_sof             : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_sc_new_sof             : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_sc_sof_mask            : slv_array_t     (UNPACKING_STAGES-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_sc_src_rdy             : std_logic_vector(UNPACKING_STAGES-1 downto 0);
    signal tx_sc_dst_rdy             : std_logic_vector(UNPACKING_STAGES-1 downto 0);

    signal last_op_data              : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal last_op_meta              : slv_array_t     (MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);
    signal last_op_offset            : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_op_length            : u_array_t       (MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal last_op_word              : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal last_op_old_sof           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_op_new_sof           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_op_sof_mask          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_op_src_rdy           : std_logic;
    signal last_op_dst_rdy           : std_logic;

    signal roundup_offset            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rounded_offset            : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_op_updated_offset    : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_op_updated_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_offset_propg         : std_logic_vector(MFB_REGIONS*OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_offset_propg_presc   : std_logic_vector(MFB_REGIONS*OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_offset_propg_src_rdy : std_logic;
    signal last_offset_propg_dst_rdy : std_logic;

    -- Second stage register
    signal last_data         : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal last_meta         : slv_array_t     (MFB_REGIONS-1 downto 0)(OP_META_WIDTH-1 downto 0);
    signal last_offset       : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_offset_presc : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal last_word         : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal last_sof          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_mask         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_src_rdy      : std_logic;
    signal last_dst_rdy      : std_logic;

    -- Final indv pkt logic
    signal roundup_sof_offset        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal sof_offset                : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_BLOCKS-1 downto 0);
    signal sof_pos_from_offset       : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_SOFPOS_WIDTH-1 downto 0);

    signal eof_offset                : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal target_word               : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal target_region             : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS)-1 downto 0);
    signal target_block              : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal target_item               : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_BLOCK_SIZE)-1 downto 0);
    signal eof_from_offset           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_pos_from_offset       : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_EOFPOS_WIDTH-1 downto 0);

    signal eof_offset_presc          : u_array_t       (MFB_REGIONS-1 downto 0)(OFFSET_WIDTH_ITEMS-1 downto 0);
    signal target_word_presc         : u_array_t       (MFB_REGIONS-1 downto 0)(log2(PKT_MAX_WORDS)-1 downto 0);
    signal target_region_presc       : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGIONS)-1 downto 0);
    signal target_block_presc        : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE)-1 downto 0);
    signal target_item_presc         : u_array_t       (MFB_REGIONS-1 downto 0)(log2(MFB_BLOCK_SIZE)-1 downto 0);
    signal eof_from_offset_presc     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_pos_from_offset_presc : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_EOFPOS_WIDTH-1 downto 0);

    signal eof_from_offset_final     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_pos_from_offset_final : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_EOFPOS_WIDTH-1 downto 0);

    signal last_supkt_sof_pos        : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_SOFPOS_WIDTH-1 downto 0);
    signal last_supkt_eof_pos        : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_EOFPOS_WIDTH-1 downto 0);
    signal last_supkt_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal last_supkt_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal data_new                  : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
    signal sof_pos_new               : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_SOFPOS_WIDTH-1 downto 0);
    signal eof_pos_new               : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_EOFPOS_WIDTH-1 downto 0);
    signal sof_new                   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_new                   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal src_rdy_new               : std_logic;
    signal dst_rdy_new               : std_logic;

    -- Third stage register
    signal indv_pkt_data     : std_logic_vector(MFB_WORD_WIDTH-1 downto 0);
    signal indv_pkt_sof_pos  : std_logic_vector(MFB_REGIONS*MFB_SOFPOS_WIDTH-1 downto 0);
    signal indv_pkt_eof_pos  : std_logic_vector(MFB_REGIONS*MFB_EOFPOS_WIDTH-1 downto 0);
    signal indv_pkt_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal indv_pkt_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal indv_pkt_last_eof : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal indv_pkt_src_rdy  : std_logic;
    signal indv_pkt_dst_rdy  : std_logic;

    -- MFB Get Items
    signal getit_indv_pkt_data     : std_logic_vector(MFB_WORD_WIDTH-1 downto 0);
    signal getit_indv_pkt_last_eof : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal getit_indv_pkt_sof_pos  : std_logic_vector(MFB_REGIONS*MFB_SOFPOS_WIDTH-1 downto 0);
    signal getit_indv_pkt_eof_pos  : std_logic_vector(MFB_REGIONS*MFB_EOFPOS_WIDTH-1 downto 0);
    signal getit_indv_pkt_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal getit_indv_pkt_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal getit_indv_pkt_src_rdy  : std_logic;
    signal getit_indv_pkt_src_rdy2 : std_logic;
    signal getit_indv_pkt_dst_rdy  : std_logic;
    signal getit_indv_pkt_dst_rdy2 : std_logic;

    signal not_a_single_valid_hdr  : std_logic;
    signal not_enough_hdrs_to_read : std_logic;
    signal too_many_eofs           : std_logic;
    signal more_indv_eofs_follow   : std_logic;
    signal wait_for_headers        : std_logic;

    signal getit_indv_hdr_data     : std_logic_vector(MFB_REGIONS*HDR_WIDTH-1 downto 0);
    signal getit_indv_hdr_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal getit_indv_hdr_src_rdy  : std_logic;
    signal getit_indv_hdr_dst_rdy  : std_logic;

    -- MVB Merge Items
    signal merg_hdr_data           : std_logic_vector(MFB_REGIONS*MERGED_ITEMS_WIDTH-1 downto 0);
    signal merg_hdr_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal merg_hdr_src_rdy        : std_logic;
    signal merg_hdr_dst_rdy        : std_logic;

    -- MFB FIFOX
    signal fifox_indv_pkt_data    : std_logic_vector(MFB_WORD_WIDTH-1 downto 0);
    signal fifox_indv_pkt_hdr     : std_logic_vector(MFB_REGIONS*HDR_WIDTH-1 downto 0);
    signal fifox_indv_pkt_sof_pos : std_logic_vector(MFB_REGIONS*MFB_SOFPOS_WIDTH-1 downto 0);
    signal fifox_indv_pkt_eof_pos : std_logic_vector(MFB_REGIONS*MFB_EOFPOS_WIDTH-1 downto 0);
    signal fifox_indv_pkt_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifox_indv_pkt_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifox_indv_pkt_src_rdy : std_logic;
    signal fifox_indv_pkt_dst_rdy : std_logic;

    signal fifox_indv_hdr_data    : std_logic_vector(MFB_REGIONS*MERGED_ITEMS_WIDTH-1 downto 0);
    signal fifox_indv_hdr_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifox_indv_hdr_src_rdy : std_logic;
    signal fifox_indv_hdr_dst_rdy : std_logic;

    -- Metadata Insertor
    signal metains_indv_pkt_data    : std_logic_vector(MFB_WORD_WIDTH-1 downto 0);
    signal metains_indv_pkt_hdr     : std_logic_vector(MFB_REGIONS*MERGED_ITEMS_WIDTH-1 downto 0);
    signal metains_indv_pkt_sof_pos : std_logic_vector(MFB_REGIONS*MFB_SOFPOS_WIDTH-1 downto 0);
    signal metains_indv_pkt_eof_pos : std_logic_vector(MFB_REGIONS*MFB_EOFPOS_WIDTH-1 downto 0);
    signal metains_indv_pkt_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal metains_indv_pkt_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal metains_indv_pkt_src_rdy : std_logic;
    signal metains_indv_pkt_dst_rdy : std_logic;

    signal metains_indv_hdr_data    : std_logic_vector(MFB_REGIONS*MERGED_ITEMS_WIDTH-1 downto 0);
    signal metains_indv_hdr_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal metains_indv_hdr_src_rdy : std_logic;
    signal metains_indv_hdr_dst_rdy : std_logic;

    -- Cutter
    signal cut_data        : std_logic_vector(MFB_WORD_WIDTH-1 downto 0);
    signal cut_meta        : std_logic_vector(MFB_REGIONS*MERGED_ITEMS_WIDTH-1 downto 0);
    signal cut_sof_pos     : std_logic_vector(MFB_REGIONS*MFB_SOFPOS_WIDTH-1 downto 0);
    signal cut_eof_pos     : std_logic_vector(MFB_REGIONS*MFB_EOFPOS_WIDTH-1 downto 0);
    signal cut_sof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cut_eof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cut_src_rdy     : std_logic;
    signal cut_dst_rdy     : std_logic;

    signal cut_hdr_data    : std_logic_vector(MFB_REGIONS*MERGED_ITEMS_WIDTH-1 downto 0);
    signal cut_hdr_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cut_hdr_src_rdy : std_logic;
    signal cut_hdr_dst_rdy : std_logic;

begin

    RX_MFB_DST_RDY <= first_op_dst_rdy;

    -- ========================================================================
    -- Asserts
    -- ========================================================================

    assert (MFB_ITEM_WIDTH = 8) and (MFB_BLOCK_SIZE = 8)
        report "FRAME UNPACKER: The values of the MFB_ITEM_WIDTH and MFB_BLOCK_SIZE generics must be 8!!"
        severity failure;

    assert (HDR_WIDTH >= 16)
        report "FRAME UNPACKER: The value of the HEADER_LENGTH generic is too small!!"
        severity failure;

    assert (UNPACKING_STAGES >= 1)
        report "FRAME UNPACKER: The value of the UNPACKING_STAGES generic is too small!!"
        severity failure;

    assert (META_OUT_MODE >= 0) and (META_OUT_MODE <= 2)
        report "FRAME UNPACKER: The value of the META_OUT_MODE generic is incorrect!!"
        severity failure;

    -- ========================================================================
    -- Debug counter
    -- ========================================================================

    --pragma synthesis_off
    process(CLK)
    begin
        if rising_edge(CLK) then
            if (RX_MFB_SRC_RDY = '1') and (first_op_dst_rdy = '1') then
                rx_pkt_count(0) <= rx_pkt_count(MFB_REGIONS);
                -- report "Packet count: " & to_string(to_integer(rx_pkt_count(0)));
            end if;

            if (RESET = '1') then
                rx_pkt_count(0) <= (others => '0');
            end if;
        end if;
    end process;

    dbg_cnt_g : for r in 0 to MFB_REGIONS-1 generate
        rx_pkt_count(r+1) <= rx_pkt_count(r)+1 when (RX_MFB_EOF(r) = '1') else rx_pkt_count(r);
    end generate;
    --pragma synthesis_on

    -- ========================================================================
    -- SupekPacket MVB headers
    -- ========================================================================

    fifoxm_data <= RX_MVB_DATA;
    fifoxm_wr   <= RX_MVB_VLD and RX_MVB_SRC_RDY;
    RX_MVB_DST_RDY <= not fifoxm_full;

    -- -------------
    --  FIFOX MULTI
    -- -------------
    fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH     => MVB_ITEM_WIDTH,
        ITEMS          => 512           ,
        WRITE_PORTS    => MVB_ITEMS     ,
        READ_PORTS     => MVB_ITEMS     ,
        RAM_TYPE       => "AUTO"        ,
        SAFE_READ_MODE => false         ,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        DI    => fifoxm_data ,
        WR    => fifoxm_wr   ,
        FULL  => fifoxm_full ,

        DO    => fifoxm_do   ,
        RD    => fifoxm_rd   ,
        EMPTY => fifoxm_empty
    );

    fifoxm_do_arr <= slv_array_deser(fifoxm_do, MFB_REGIONS);

    -- ------------------------
    --  MVB headers read logic
    -- ------------------------
    -- last EOF remapping (shakedown)
    process (all)
        variable last_eof_ptr : integer;
    begin
        last_eof_remapped <= (others => '0');
        last_eof_ptr      := 0;
        for r in 0 to MFB_REGIONS-1 loop
            if (getit_indv_pkt_last_eof(r) = '1') and (getit_indv_pkt_src_rdy = '1') then
                last_eof_remapped(last_eof_ptr) <= '1';
                last_eof_ptr := last_eof_ptr + 1;
            end if;
        end loop;
    end process;

    fifoxm_rd <= (last_eof_remapped and not fifoxm_empty) and getit_indv_pkt_dst_rdy2;

    -- ------------------------------------------
    --  MVB headers data redirect and validation
    -- ------------------------------------------
    -- EOF remapping (shakedown)
    process (all)
        variable eof_ptr : integer;
    begin
        last_eof_respaced <= (others => '0');
        eof_remapped      <= (others => '0');
        eof_ptr := 0;
        for r in 0 to MFB_REGIONS-1 loop
            if (getit_indv_pkt_eof(r) = '1') and (getit_indv_pkt_src_rdy = '1') then
                if (getit_indv_pkt_last_eof(r) = '1') then
                    last_eof_respaced(eof_ptr) <= '1';
                end if;
                eof_remapped(eof_ptr) <= '1';
                eof_ptr := eof_ptr + 1;
            end if;
        end loop;
    end process;

    -- generate address for FIFOXM output port selection
    count_ones_g : for r in 1 to MFB_REGIONS-1 generate
        -- fifoxm_output_addr(0) is always 0
        fifoxm_output_addr(r) <= count_ones(last_eof_respaced(r-1 downto 0));
    end generate;

    -- FIFOX MULTI output port selection
    fifoxm_hdr_data_arr(0) <=     fifoxm_do_arr(0);
    fifoxm_hdr_vld_arr (0) <= not fifoxm_empty (0) and eof_remapped(0);
    fifoxm_hdr_data_g : for r in 1 to MFB_REGIONS-1 generate
        fifoxm_hdr_data_arr(r) <=     fifoxm_do_arr(fifoxm_output_addr(r));
        fifoxm_hdr_vld_arr (r) <= not fifoxm_empty (fifoxm_output_addr(r)) and eof_remapped(r);
    end generate;

    fifoxm_hdr_data    <= slv_array_ser(fifoxm_hdr_data_arr);
    fifoxm_hdr_vld     <= fifoxm_hdr_vld_arr and getit_indv_pkt_dst_rdy2;
    fifoxm_hdr_src_rdy <= or (fifoxm_hdr_vld) and not wait_for_headers;

    -- ========================================================================
    -- Input logic
    -- ========================================================================

    -- ----------------------
    --  SuperPacket metadata
    -- ----------------------
    supkt_sof_pos_arr <= slv_array_deser(RX_MFB_SOF_POS, MFB_REGIONS);

    rx_supkt_meta_g : for r in 0 to MFB_REGIONS-1 generate
        rx_supkt_meta(r) <= supkt_sof_pos_arr(r) & RX_MFB_SOF(r) & RX_MFB_EOF(r);
    end generate;

    -- ----------------------------------------------
    --  Process the first header of each SuperPacket
    -- ----------------------------------------------
    rx_data_blocks        <= slv_array_deser(RX_MFB_DATA   , MFB_REGIONS*MFB_REGION_SIZE);
    rx_per_region_sof_pos <= slv_array_deser(RX_MFB_SOF_POS, MFB_REGIONS);

    supkt_hdr_extract_g : for r in 0 to MFB_REGIONS-1 generate
        -- Create a global SOF POS
        rx_per_word_sof_pos(r) <= to_unsigned(r,log2(MFB_REGIONS)) & unsigned(rx_per_region_sof_pos(r));
        rx_global_sof_pos  (r) <= resize_left(resize_right(rx_per_word_sof_pos(r), log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)), OFFSET_WIDTH_ITEMS);

        -- Select a Block, extract the Length field value, and ...
        rx_ext_length(r) <= rx_data_blocks(to_integer(rx_per_word_sof_pos(r)))(LENGTH_WIDTH-1 downto 0);
        -- ... add the Header length to it
        rx_full_length(r) <= resize(unsigned(rx_ext_length(r)), LENGTH_WIDTH+1) + to_unsigned(HEADER_LENGTH, LENGTH_WIDTH);
        rx_cut_length (r) <= rx_full_length(r)(LENGTH_WIDTH-1 downto 0);
    end generate;

    -- overflow_assert_p : process (CLK)
    -- begin
    --     if (rising_edge(CLK)) then
    --         if (RX_MFB_SRC_RDY = '1') and (first_op_dst_rdy = '1') then
    --             for r in 0 to MFB_REGIONS-1 loop
    --                 assert (rx_full_length(r)(LENGTH_WIDTH) = '1')
    --                     report "The frame with its header is too long! " &
    --                            "Extracted Length: " &
    --                            integer'image(to_integer(unsigned(rx_ext_length(r)))) &
    --                            "Full length: " &
    --                            integer'image(rx_ext_length(r))
    --                     severity failure;
    --             end loop;
    --         end if;
    --     end if;
    -- end process;

    -- --------------
    --  Word counter
    -- --------------
    word_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RX_MFB_SRC_RDY = '1') and (first_op_dst_rdy = '1') then
                word_cnt_reg <= word_cnt(MFB_REGIONS-1) + 1;
            end if;
            if (RESET = '1') then
                word_cnt_reg <= (others => '0');
            end if;
        end if;
    end process;

    word_cnt(0) <= word_cnt_reg when (RX_MFB_SOF(0) = '0') else (others => '0');
    word_cnt_g: for r in 1 to MFB_REGIONS-1 generate
        word_cnt(r) <= word_cnt(r-1) when (RX_MFB_SOF(r) = '0') else (others => '0');
    end generate;

    -- -----------------------------------------
    --  Precalculate the mask for the OM TX SOF
    -- -----------------------------------------
    process(CLK)
    begin
        if rising_edge(CLK) then
            if (RX_MFB_SRC_RDY = '1') and (first_op_dst_rdy = '1') then
                eof_propg_reg <= eof_propg(MFB_REGIONS);
            end if;
            if (RESET = '1') then
                eof_propg_reg <= '0';
            end if;
        end if;
    end process;

    eof_propg(0) <= '1' when (RX_MFB_EOF(0) = '1') else eof_propg_reg;
    eof_propg_g : for r in 1 to MFB_REGIONS-1 generate
        eof_propg(r) <= '1'            when (RX_MFB_EOF(r  ) = '1') else
                        '0'            when (RX_MFB_SOF(r-1) = '1') else
                        eof_propg(r-1);
    end generate;
    eof_propg(MFB_REGIONS) <= '0' when (RX_MFB_SOF(MFB_REGIONS-1) = '1') else eof_propg(MFB_REGIONS-1);

    sof_mask <= not eof_propg(MFB_REGIONS-1 downto 0);

    -- ========================================================================
    -- Input (first stage) register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (first_op_dst_rdy = '1') then
                rx_op_data    (0) <= slv_array_deser(RX_MFB_DATA, MFB_REGIONS);
                rx_op_meta    (0) <= rx_supkt_meta;
                rx_op_offset  (0) <= rx_global_sof_pos;
                rx_op_length  (0) <= rx_cut_length;
                rx_op_word    (0) <= word_cnt;
                rx_op_old_sof (0) <= (others => '0');
                rx_op_new_sof (0) <= RX_MFB_SOF and RX_MFB_SRC_RDY;
                rx_op_sof_mask(0) <= sof_mask;
                rx_op_src_rdy (0) <= RX_MFB_SRC_RDY;
            end if;

            if (RESET = '1') then
                rx_op_src_rdy(0) <= '0';
            end if;
        end if;
    end process;

    first_op_dst_rdy <= rx_op_dst_rdy(0);

    -- ========================================================================
    -- Offset processing pipeline
    -- Consists of multiple stages of the Offset Processor and the SOF Creator
    -- units, where both of them are separated by two register stages.
    -- ========================================================================

    offset_pipeline_g : for s in 0 to UNPACKING_STAGES-1 generate

        -- ------------------
        --  Offset Processor
        -- ------------------
        offset_processor_i : entity work.OFFSET_PROCESSOR
        generic map(
            MFB_REGIONS     => MFB_REGIONS       ,
            MFB_REGION_SIZE => MFB_REGION_SIZE   ,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE    ,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH    ,
            MFB_META_WIDTH  => OP_META_WIDTH     ,
            PKT_MTU         => PKT_MTU           ,
            MAX_WORDS       => PKT_MAX_WORDS     ,
            OFFSET_WIDTH    => OFFSET_WIDTH_ITEMS,
            LENGTH_WIDTH    => LENGTH_WIDTH      ,
            LAST_VLD_IMPL   => LAST_VLD_IMPL     ,
            DEVICE          => DEVICE
        )
        port map(
            CLK   => CLK,
            RESET => RESET,

            RX_DATA     => rx_op_data    (s),
            RX_META     => rx_op_meta    (s),
            RX_OFFSET   => rx_op_offset  (s),
            RX_LENGTH   => rx_op_length  (s),
            RX_WORD     => rx_op_word    (s),
            RX_OLD_SOF  => rx_op_old_sof (s),
            RX_NEW_SOF  => rx_op_new_sof (s),
            RX_SOF_MASK => rx_op_sof_mask(s),
            RX_SRC_RDY  => rx_op_src_rdy (s),
            RX_DST_RDY  => rx_op_dst_rdy (s),

            TX_DATA     => tx_op_data    (s),
            TX_META     => tx_op_meta    (s),
            TX_OFFSET   => tx_op_offset  (s),
            TX_WORD     => tx_op_word    (s),
            TX_OLD_SOF  => tx_op_old_sof (s),
            TX_SOF_MASK => tx_op_sof_mask(s),
            TX_SRC_RDY  => tx_op_src_rdy (s),
            TX_DST_RDY  => tx_op_dst_rdy (s)
        );

        -- ----------------------------------------------------
        --  First register stage (withing this pipeline stage)
        -- ----------------------------------------------------
        tx_op_dst_rdy(s) <= rx_sc_dst_rdy(s);

        process(CLK)
        begin
            if rising_edge(CLK) then
                if (rx_sc_dst_rdy(s) = '1') then
                    rx_sc_data    (s) <= tx_op_data    (s);
                    rx_sc_meta    (s) <= tx_op_meta    (s);
                    rx_sc_offset  (s) <= tx_op_offset  (s);
                    rx_sc_word    (s) <= tx_op_word    (s);
                    rx_sc_old_sof (s) <= tx_op_old_sof (s);
                    rx_sc_sof_mask(s) <= tx_op_sof_mask(s);
                    rx_sc_src_rdy (s) <= tx_op_src_rdy (s);
                end if;

                if (RESET = '1') then
                    rx_sc_src_rdy(s) <= '0';
                end if;
            end if;
        end process;

        -- ----------------------------------------------------
        --  SOF Creator(s) - one per Region
        -- ----------------------------------------------------
        rx_sc_dst_rdy(s) <= tx_sc_dst_rdy(s);

        sof_creator_g : for r in 0 to MFB_REGIONS-1 generate

            sof_creator_i : entity work.SOF_CREATOR
            generic map(
                MFB_REGIONS     => MFB_REGIONS       ,
                MFB_REGION_SIZE => MFB_REGION_SIZE   ,
                MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE    ,
                MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH    ,
                MFB_META_WIDTH  => OP_META_WIDTH     ,
                PKT_MTU         => PKT_MTU           ,
                MAX_WORDS       => PKT_MAX_WORDS     ,
                OFFSET_WIDTH    => OFFSET_WIDTH_ITEMS,
                LENGTH_WIDTH    => LENGTH_WIDTH      ,
                REGION_NUMBER   => r                 ,
                DEVICE          => DEVICE
            )
            port map(
                CLK   => CLK,
                RESET => RESET,

                RX_DATA     => rx_sc_data    (s)(r),
                RX_META     => rx_sc_meta    (s)(r),
                RX_OFFSET   => rx_sc_offset  (s)(r),
                RX_WORD     => rx_sc_word    (s)(r),
                RX_SOF_MASK => rx_sc_sof_mask(s)(r),

                TX_DATA     => tx_sc_data    (s)(r),
                TX_META     => tx_sc_meta    (s)(r),
                TX_OFFSET   => tx_sc_offset  (s)(r),
                TX_LENGTH   => tx_sc_length  (s)(r),
                TX_WORD     => tx_sc_word    (s)(r),
                TX_NEW_SOF  => tx_sc_new_sof (s)(r),
                TX_SOF_MASK => tx_sc_sof_mask(s)(r)
            );

        end generate;

        tx_sc_old_sof(s) <= rx_sc_old_sof(s);
        tx_sc_src_rdy(s) <= rx_sc_src_rdy(s);

        -- -----------------------------------------------------
        --  Second register stage (withing this pipeline stage)
        -- -----------------------------------------------------
        tx_sc_dst_rdy(s) <= rx_op_dst_rdy(s+1);

        process(CLK)
        begin
            if rising_edge(CLK) then
                if (rx_op_dst_rdy(s+1) = '1') then
                    rx_op_data    (s+1) <= tx_sc_data    (s);
                    rx_op_meta    (s+1) <= tx_sc_meta    (s);
                    rx_op_offset  (s+1) <= tx_sc_offset  (s);
                    rx_op_length  (s+1) <= tx_sc_length  (s);
                    rx_op_word    (s+1) <= tx_sc_word    (s);
                    rx_op_old_sof (s+1) <= tx_sc_old_sof (s);
                    rx_op_new_sof (s+1) <= tx_sc_new_sof (s);
                    rx_op_sof_mask(s+1) <= tx_sc_sof_mask(s);
                    rx_op_src_rdy (s+1) <= tx_sc_src_rdy (s);
                end if;

                if (RESET = '1') then
                    rx_op_src_rdy(s+1) <= '0';
                end if;
            end if;
        end process;

    end generate;

    -- ========================================================================
    -- One more offset processing
    -- ========================================================================

    rx_op_dst_rdy(UNPACKING_STAGES) <= last_op_dst_rdy;

    last_op_data     <= rx_op_data    (UNPACKING_STAGES);
    last_op_meta     <= rx_op_meta    (UNPACKING_STAGES);
    last_op_offset   <= rx_op_offset  (UNPACKING_STAGES);
    last_op_length   <= rx_op_length  (UNPACKING_STAGES);
    last_op_word     <= rx_op_word    (UNPACKING_STAGES);
    last_op_old_sof  <= rx_op_old_sof (UNPACKING_STAGES);
    last_op_new_sof  <= rx_op_new_sof (UNPACKING_STAGES);
    last_op_sof_mask <= rx_op_sof_mask(UNPACKING_STAGES);
    last_op_src_rdy  <= rx_op_src_rdy (UNPACKING_STAGES);

    -- Roundup and add the last offset to the last extracted length when the last packet's SOF is created in the last pipeline stage
    updated_offset_g : for r in 0 to MFB_REGIONS-1 generate
        roundup_offset(r) <= or (last_op_offset(r)(log2(MFB_BLOCK_SIZE)-1 downto 0));
        rounded_offset(r) <= resize_right(last_op_offset(r)(OFFSET_WIDTH_ITEMS-1 downto log2(MFB_BLOCK_SIZE)) + roundup_offset(r), OFFSET_WIDTH_ITEMS);

        last_op_updated_offset(r) <= last_op_offset(r) when (last_op_old_sof(r) = '1') else rounded_offset(r) + resize_left(last_op_length(r), OFFSET_WIDTH_ITEMS);
    end generate;

    last_op_updated_sof <= last_op_old_sof or last_op_new_sof;

    last_vld_i : entity work.MVB_AGGREGATE_LAST_VLD
    generic map(
        ITEMS          => MFB_REGIONS       ,
        ITEM_WIDTH     => OFFSET_WIDTH_ITEMS,
        IMPLEMENTATION => LAST_VLD_IMPL     ,
        INTERNAL_REG   => true
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA         => slv_array_ser(u_arr_to_slv_arr(last_op_updated_offset)),
        RX_VLD          => last_op_updated_sof                                    ,
        RX_SRC_RDY      => last_op_src_rdy                                        ,
        RX_DST_RDY      => last_op_dst_rdy                                        ,

        REG_IN_DATA     => (others => '0')                                        ,
        REG_IN_VLD      => '0'                                                    ,
        REG_OUT_DATA    => open                                                   ,
        REG_OUT_VLD     => open                                                   ,
        REG_OUT_WR      => open                                                   ,

        TX_DATA         => last_offset_propg                                      ,
        TX_VLD          => open                                                   ,
        TX_PRESCAN_DATA => last_offset_propg_presc                                ,
        TX_PRESCAN_VLD  => open                                                   ,
        TX_SRC_RDY      => last_offset_propg_src_rdy                              ,
        TX_DST_RDY      => last_offset_propg_dst_rdy
    );

    -- ========================================================================
    -- Second stage register
    -- ========================================================================

    last_offset_propg_dst_rdy <= last_dst_rdy;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (last_dst_rdy = '1') then
                last_data         <= last_op_data;
                last_meta         <= last_op_meta;
                last_offset       <= slv_arr_to_u_arr(slv_array_deser(last_offset_propg      , MFB_REGIONS));
                last_offset_presc <= slv_arr_to_u_arr(slv_array_deser(last_offset_propg_presc, MFB_REGIONS));
                last_word         <= last_op_word;
                last_sof          <= last_op_updated_sof;
                last_mask         <= last_op_sof_mask;
                last_src_rdy      <= last_offset_propg_src_rdy;
            end if;

            if (RESET = '1') then
                last_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Final logic for control signals of individual packets
    -- ========================================================================

    -- ---------
    --  SOF POS
    -- ---------
    sof_pos_from_offset_g : for r in 0 to MFB_REGIONS-1 generate
        -- Last roundup
        roundup_sof_offset(r) <= or (last_offset_presc(r)(log2(MFB_BLOCK_SIZE)-1 downto 0));
        sof_offset        (r) <= (unsigned(last_offset_presc(r)(OFFSET_WIDTH_ITEMS-1 downto log2(MFB_BLOCK_SIZE))) + roundup_sof_offset(r));

        sof_pos_from_offset(r) <= std_logic_vector(sof_offset(r)(log2(MFB_REGION_SIZE)-1 downto 0));
    end generate;

    -- -------------------------
    --  EOF and EOF POS current
    -- -------------------------
    eof_from_offset_g : for r in 0 to MFB_REGIONS-1 generate

        eof_offset(r) <= unsigned(last_offset(r))-1;

        -- EOF offset parsing
        target_word  (r) <= eof_offset(r)(OFFSET_WIDTH_ITEMS                                                -1 downto OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS                            ));
        target_region(r) <= eof_offset(r)(OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS                            )-1 downto OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS                ));
        target_block (r) <= eof_offset(r)(OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS                )-1 downto OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE));
        target_item  (r) <= eof_offset(r)(OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE)-1 downto 0                                                                 );

        -- EOF
        eof_from_offset_g : if MFB_REGIONS > 1 generate
            eof_from_offset(r) <= '1' when (last_word(r) = target_word(r)) and (r = target_region(r)) else '0';
        else generate
            eof_from_offset(r) <= '1' when (last_word(r) = target_word(r)) else '0';
        end generate;

        -- EOF POS
        eof_pos_from_offset(r) <= std_logic_vector(target_block(r)) & std_logic_vector(target_item(r));

    end generate;

    -- ----------------------------
    --  EOF and EOF POS prescanned
    -- ----------------------------
    eof_from_offset_presc_g : for r in 0 to MFB_REGIONS-1 generate

        eof_offset_presc(r) <= unsigned(last_offset_presc(r))-1;

        -- EOF offset parsing
        target_word_presc  (r) <= eof_offset_presc(r)(OFFSET_WIDTH_ITEMS                                                -1 downto OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS                            ));
        target_region_presc(r) <= eof_offset_presc(r)(OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS                            )-1 downto OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS                ));
        target_block_presc (r) <= eof_offset_presc(r)(OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS                )-1 downto OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE));
        target_item_presc  (r) <= eof_offset_presc(r)(OFFSET_WIDTH_ITEMS-log2(PKT_MAX_WORDS*MFB_REGIONS*MFB_REGION_SIZE)-1 downto 0                                                                 );

        -- EOF
        eof_from_offset2_g : if MFB_REGIONS > 1 generate
            eof_from_offset_presc(r) <= '1' when (last_word(r) = target_word_presc(r)) and (r = target_region_presc(r)) else '0';
        else generate
            eof_from_offset_presc(r) <= '1' when (last_word(r) = target_word_presc(r)) else '0';
        end generate;

        -- EOF POS
        eof_pos_from_offset_presc(r) <= std_logic_vector(target_block_presc(r)) & std_logic_vector(target_item_presc(r));

    end generate;

    -- ---------------------------------
    --  EOF and EOF POS final selection
    -- ---------------------------------
    eof_from_offset_final_g : for r in 0 to MFB_REGIONS-1 generate
        eof_from_offset_final    (r) <= '1'                    when (eof_from_offset(r) = '1') else eof_from_offset_presc    (r) and last_mask(r);
        eof_pos_from_offset_final(r) <= eof_pos_from_offset(r) when (eof_from_offset(r) = '1') else eof_pos_from_offset_presc(r);
    end generate;

    -- ---------------------------------------
    --  Select individual pkt control signals
    -- ---------------------------------------
    last_dst_rdy <= dst_rdy_new;

    data_new <= last_data;
    last_meta_g : for r in 0 to MFB_REGIONS-1 generate
        last_supkt_sof_pos(r) <= last_meta(r)(OP_META_WIDTH-1 downto OP_META_WIDTH-MFB_SOFPOS_WIDTH);
        last_supkt_sof    (r) <= last_meta(r)(1);
        last_supkt_eof    (r) <= last_meta(r)(0);
    end generate;

    -- MUX which chooses between control signals either from:
    --     the input or
    --     the Offset processing pipeline
    om_output_mux_g : for r in 0 to MFB_REGIONS-1 generate
        sof_new    (r) <= '1'                   when (last_supkt_sof(r) = '1') else last_sof           (r);
        sof_pos_new(r) <= last_supkt_sof_pos(r) when (last_supkt_sof(r) = '1') else sof_pos_from_offset(r);

        eof_new    (r) <= '1' when (last_supkt_eof(r) = '1') else eof_from_offset_final(r);
        eof_pos_new(r) <= eof_pos_from_offset_final(r);
    end generate;
    src_rdy_new <= last_src_rdy;

    -- ========================================================================
    -- Third stage register
    -- ========================================================================

    dst_rdy_new <= indv_pkt_dst_rdy;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (indv_pkt_dst_rdy = '1') then
                indv_pkt_data    <= slv_array_ser(data_new);
                indv_pkt_sof_pos <= slv_array_ser(sof_pos_new);
                indv_pkt_eof_pos <= slv_array_ser(eof_pos_new);
                indv_pkt_sof     <= sof_new;
                indv_pkt_eof     <= eof_new;
                indv_pkt_last_eof <= last_supkt_eof;
                indv_pkt_src_rdy <= src_rdy_new;
            end if;
            if (RESET = '1') then
                indv_pkt_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Extraction of the headers of the individual packets
    -- ========================================================================

    mfb_get_items_i : entity work.MFB_GET_ITEMS
    generic map(
        REGIONS          => MFB_REGIONS    ,
        REGION_SIZE      => MFB_REGION_SIZE,
        BLOCK_SIZE       => MFB_BLOCK_SIZE ,
        ITEM_WIDTH       => MFB_ITEM_WIDTH ,
        META_WIDTH       => 1              ,

        MAX_FRAME_LENGHT => PKT_MTU        ,
        EXTRACTED_ITEMS  => HEADER_LENGTH  ,
        EXTRACTED_OFFSET => 0
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA    => indv_pkt_data          ,
        RX_META    => indv_pkt_last_eof      ,
        RX_SOF_POS => indv_pkt_sof_pos       ,
        RX_EOF_POS => indv_pkt_eof_pos       ,
        RX_SOF     => indv_pkt_sof           ,
        RX_EOF     => indv_pkt_eof           ,
        RX_SRC_RDY => indv_pkt_src_rdy       ,
        RX_DST_RDY => indv_pkt_dst_rdy       ,

        TX_DATA    => getit_indv_pkt_data    ,
        TX_META    => getit_indv_pkt_last_eof,
        TX_SOF_POS => getit_indv_pkt_sof_pos ,
        TX_EOF_POS => getit_indv_pkt_eof_pos ,
        TX_SOF     => getit_indv_pkt_sof     ,
        TX_EOF     => getit_indv_pkt_eof     ,
        TX_SRC_RDY => getit_indv_pkt_src_rdy ,
        TX_DST_RDY => getit_indv_pkt_dst_rdy2,

        EX_DATA    => getit_indv_hdr_data    ,
        EX_VLD     => getit_indv_hdr_vld     ,
        EX_SRC_RDY => getit_indv_hdr_src_rdy ,
        EX_DST_RDY => getit_indv_hdr_dst_rdy
    );

    not_a_single_valid_hdr <= '1' when ((or getit_indv_pkt_eof and getit_indv_pkt_src_rdy) = '1') and (fifoxm_empty(0) = '1') else '0';
    too_many_eofs          <= '1' when (getit_indv_pkt_src_rdy = '1') and
                                       (( count_ones(getit_indv_pkt_last_eof) > count_ones(not fifoxm_empty)) or
                                        ((count_ones(getit_indv_pkt_last_eof) = count_ones(not fifoxm_empty)) and (more_indv_eofs_follow = '1'))) else '0';

    process(all)
    begin
        more_indv_eofs_follow <= '0';
        for r in MFB_REGIONS-2 downto 0 loop
            if (getit_indv_pkt_last_eof(r) = '1') then
                more_indv_eofs_follow <= or (getit_indv_pkt_eof(MFB_REGIONS-1 downto r+1));
                exit;
            end if;
        end loop;
        if (getit_indv_pkt_last_eof(MFB_REGIONS-1) = '1') then
            more_indv_eofs_follow <= '0';
        end if;
    end process;

    wait_for_headers <= '1' when (not_a_single_valid_hdr = '1') or (too_many_eofs = '1') else '0';

    -- new DST RDY deasserts when not enough MVB headers in FIFOXM are present
    getit_indv_pkt_dst_rdy2 <= getit_indv_pkt_dst_rdy and not wait_for_headers;

    -- ========================================================================
    -- Concatenate RX MVB headers and extracted headers of the indv packets
    -- ========================================================================

    assert (fifoxm_hdr_dst_rdy = '1')
        report "MVB_MERGE_ITEMS: FIFO at RX1 full!" & CR &
               "Increase FIFO DEPTH or use the fifoxm_hdr_dst_rdy signal."
        severity note;

    mvb_merge_items_i : entity work.MVB_MERGE_ITEMS
    generic map(
        RX0_ITEMS      => MFB_REGIONS,
        RX0_ITEM_WIDTH => HDR_WIDTH,
        RX1_ITEMS      => MVB_ITEMS,
        RX1_ITEM_WIDTH => MVB_ITEM_WIDTH,
        TX_ITEM_WIDTH  => MVB_ITEM_WIDTH+HDR_WIDTH,
        RX0_FIFO_EN    => True,
        FIFO_DEPTH     => 512,
        OUTPUT_REG     => False,
        DEVICE         => DEVICE
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX0_DATA    => getit_indv_hdr_data   ,
        RX0_VLD     => getit_indv_hdr_vld    ,
        RX0_SRC_RDY => getit_indv_hdr_src_rdy,
        RX0_DST_RDY => getit_indv_hdr_dst_rdy,

        RX1_DATA    => fifoxm_hdr_data       ,
        RX1_VLD     => fifoxm_hdr_vld        ,
        RX1_SRC_RDY => fifoxm_hdr_src_rdy    ,
        RX1_DST_RDY => fifoxm_hdr_dst_rdy    ,

        TX_DATA     => merg_hdr_data         ,
        TX_DATA0    => open                  ,
        TX_DATA1    => open                  ,
        TX_VLD      => merg_hdr_vld          ,
        TX_SRC_RDY  => merg_hdr_src_rdy      ,
        TX_DST_RDY  => merg_hdr_dst_rdy
    );

    meta_insert_g : if (META_OUT_MODE = 0) or (META_OUT_MODE = 1) generate

    -- ========================================================================
    -- Insert headers to metadata
    -- ========================================================================

    -- new SRC RDY deasserts when stopping
    getit_indv_pkt_src_rdy2 <= getit_indv_pkt_src_rdy and not wait_for_headers;

        -- ------------------
        --  Delay MFB stream
        -- ------------------
        mfb_fifox_i2 : entity work.MFB_FIFOX
        generic map(
            REGIONS     => MFB_REGIONS    ,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE ,
            ITEM_WIDTH  => MFB_ITEM_WIDTH ,
            META_WIDTH  => 0              ,

            FIFO_DEPTH          => 512    ,
            RAM_TYPE            => "AUTO" ,
            DEVICE              => DEVICE ,
            ALMOST_FULL_OFFSET  => 0      ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            CLK => CLK,
            RST => RESET,

            RX_DATA    => getit_indv_pkt_data    ,
            RX_META    => (others => '0')        ,
            RX_SOF_POS => getit_indv_pkt_sof_pos ,
            RX_EOF_POS => getit_indv_pkt_eof_pos ,
            RX_SOF     => getit_indv_pkt_sof     ,
            RX_EOF     => getit_indv_pkt_eof     ,
            RX_SRC_RDY => getit_indv_pkt_src_rdy2,
            RX_DST_RDY => getit_indv_pkt_dst_rdy ,

            TX_DATA     => fifox_indv_pkt_data   ,
            TX_META     => open                  ,
            TX_SOF_POS  => fifox_indv_pkt_sof_pos,
            TX_EOF_POS  => fifox_indv_pkt_eof_pos,
            TX_SOF      => fifox_indv_pkt_sof    ,
            TX_EOF      => fifox_indv_pkt_eof    ,
            TX_SRC_RDY  => fifox_indv_pkt_src_rdy,
            TX_DST_RDY  => fifox_indv_pkt_dst_rdy
        );

        -- -------------
        --  MVB headers
        -- -------------
        merg_hdr_dst_rdy <= fifox_indv_hdr_dst_rdy;

        fifox_indv_hdr_data    <= merg_hdr_data;
        fifox_indv_hdr_vld     <= merg_hdr_vld;
        fifox_indv_hdr_src_rdy <= merg_hdr_src_rdy;

        -- ---------------
        --  The insertion
        -- ---------------
        metadata_insertor_i : entity work.METADATA_INSERTOR
        generic map(
            MVB_ITEMS            => MFB_REGIONS    ,
            MVB_ITEM_WIDTH       => MERGED_ITEMS_WIDTH,

            MFB_REGIONS          => MFB_REGIONS    ,
            MFB_REGION_SIZE      => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE       => MFB_BLOCK_SIZE ,
            MFB_ITEM_WIDTH       => MFB_ITEM_WIDTH ,
            MFB_META_WIDTH       => 0              ,

            INSERT_MODE   => META_OUT_MODE         ,
            MVB_FIFO_SIZE => 32                    ,
            DEVICE        => DEVICE
        )
        port map(
            CLK   => CLK,
            RESET => RESET,

            RX_MVB_DATA    => fifox_indv_hdr_data      ,
            RX_MVB_VLD     => fifox_indv_hdr_vld       ,
            RX_MVB_SRC_RDY => fifox_indv_hdr_src_rdy   ,
            RX_MVB_DST_RDY => fifox_indv_hdr_dst_rdy   ,

            RX_MFB_DATA    => fifox_indv_pkt_data      ,
            RX_MFB_META    => (others => '0')          ,
            RX_MFB_SOF_POS => fifox_indv_pkt_sof_pos   ,
            RX_MFB_EOF_POS => fifox_indv_pkt_eof_pos   ,
            RX_MFB_SOF     => fifox_indv_pkt_sof       ,
            RX_MFB_EOF     => fifox_indv_pkt_eof       ,
            RX_MFB_SRC_RDY => fifox_indv_pkt_src_rdy   ,
            RX_MFB_DST_RDY => fifox_indv_pkt_dst_rdy   ,

            TX_MFB_DATA     => metains_indv_pkt_data   ,
            TX_MFB_META     => open                    ,
            TX_MFB_META_NEW => metains_indv_pkt_hdr    ,
            TX_MFB_SOF_POS  => metains_indv_pkt_sof_pos,
            TX_MFB_EOF_POS  => metains_indv_pkt_eof_pos,
            TX_MFB_SOF      => metains_indv_pkt_sof    ,
            TX_MFB_EOF      => metains_indv_pkt_eof    ,
            TX_MFB_SRC_RDY  => metains_indv_pkt_src_rdy,
            TX_MFB_DST_RDY  => metains_indv_pkt_dst_rdy
        );

        metains_indv_hdr_data    <= (others => '0');
        metains_indv_hdr_vld     <= (others => '0');
        metains_indv_hdr_src_rdy <= '0';

    else generate

        -- ========================================================================
        -- Keep headers on independent MVB stream
        -- ========================================================================

        -- ------------
        --  MFB stream
        -- ------------
        getit_indv_pkt_dst_rdy <= metains_indv_pkt_dst_rdy;

        metains_indv_pkt_data    <= getit_indv_pkt_data;
        metains_indv_pkt_hdr     <= (others => '0');
        metains_indv_pkt_sof_pos <= getit_indv_pkt_sof_pos;
        metains_indv_pkt_eof_pos <= getit_indv_pkt_eof_pos;
        metains_indv_pkt_sof     <= getit_indv_pkt_sof;
        metains_indv_pkt_eof     <= getit_indv_pkt_eof;
        metains_indv_pkt_src_rdy <= getit_indv_pkt_src_rdy and not wait_for_headers;

        -- -------------
        --  MVB headers
        -- -------------
        merg_hdr_dst_rdy <= metains_indv_hdr_dst_rdy;

        metains_indv_hdr_data    <= merg_hdr_data;
        metains_indv_hdr_vld     <= merg_hdr_vld;
        metains_indv_hdr_src_rdy <= merg_hdr_src_rdy;

    end generate;

    -- ========================================================================
    -- Get rid of the headers from the individual packets
    -- ========================================================================

    -- ------------
    --  MFB stream
    -- ------------
    mfb_cutter_i : entity work.MFB_CUTTER_SIMPLE
    generic map(
        REGIONS        => MFB_REGIONS    ,
        REGION_SIZE    => MFB_REGION_SIZE,
        BLOCK_SIZE     => MFB_BLOCK_SIZE ,
        ITEM_WIDTH     => MFB_ITEM_WIDTH ,
        META_WIDTH     => MERGED_ITEMS_WIDTH,
        META_ALIGNMENT => META_OUT_MODE  ,
        CUTTED_ITEMS   => HEADER_LENGTH
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA    => metains_indv_pkt_data   ,
        RX_META    => metains_indv_pkt_hdr    ,
        RX_SOF     => metains_indv_pkt_sof    ,
        RX_EOF     => metains_indv_pkt_eof    ,
        RX_SOF_POS => metains_indv_pkt_sof_pos,
        RX_EOF_POS => metains_indv_pkt_eof_pos,
        RX_SRC_RDY => metains_indv_pkt_src_rdy,
        RX_DST_RDY => metains_indv_pkt_dst_rdy,

        RX_CUT     => (others => '1')         ,

        TX_DATA    => cut_data                ,
        TX_META    => cut_meta                ,
        TX_SOF     => cut_sof                 ,
        TX_EOF     => cut_eof                 ,
        TX_SOF_POS => cut_sof_pos             ,
        TX_EOF_POS => cut_eof_pos             ,
        TX_SRC_RDY => cut_src_rdy             ,
        TX_DST_RDY => cut_dst_rdy
    );

    -- -------------
    --  MVB headers
    -- -------------
    metains_indv_hdr_dst_rdy <= cut_hdr_dst_rdy;

    cut_hdr_data    <= metains_indv_hdr_data;
    cut_hdr_vld     <= metains_indv_hdr_vld;
    cut_hdr_src_rdy <= metains_indv_hdr_src_rdy;

    -- ========================================================================
    -- Output assignment
    -- ========================================================================

    -- ------------
    --  MFB stream
    -- ------------
    cut_dst_rdy <= TX_MFB_DST_RDY;

    TX_MFB_DATA    <= cut_data;
    TX_MFB_META    <= cut_meta;
    TX_MFB_SOF_POS <= cut_sof_pos;
    TX_MFB_EOF_POS <= cut_eof_pos;
    TX_MFB_SOF     <= cut_sof;
    TX_MFB_EOF     <= cut_eof;
    TX_MFB_SRC_RDY <= cut_src_rdy;

    -- -------------
    --  MVB headers
    -- -------------
    cut_hdr_dst_rdy <= TX_MVB_DST_RDY;

    TX_MVB_DATA    <= cut_hdr_data;
    TX_MVB_VLD     <= cut_hdr_vld;
    TX_MVB_SRC_RDY <= cut_hdr_src_rdy;

end architecture;
