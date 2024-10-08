-- ptc_tag_manager.vhd: Tag manager for PTC component
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields
use work.basics_test_pkg.all; -- contains definitions hex std_logic_vector printing
use std.textio.all;

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity PTC_TAG_MANAGER is
generic(
    -- Number of MVB UP headers
    MVB_UP_ITEMS        : integer := 2;
    -- Number of MVB DOWN headers
    MVB_DOWN_ITEMS      : integer := 4;
    -- Number of MFB DOWN regions
    MFB_DOWN_REGIONS    : integer := 4;
    -- Size of one MFB DOWN region in DWORDS (1 DWORD is 4 Bytes)
    MFB_DOWN_REG_SIZE   : integer := 16;

    -- Width of DMA Tag field in MVB header (maximum defined by range in dma_bus_pack)
    DMA_TAG_WIDTH       : integer := DMA_REQUEST_TAG'high - DMA_REQUEST_TAG'low + 1;
    -- Width of DMA Unit ID field in MVB header (maximum defined by range in dma_bus_pack)
    DMA_ID_WIDTH        : integer := DMA_REQUEST_UNITID'high - DMA_REQUEST_UNITID'low + 1;

    -- Width of Tag field in PCIe header (maximum 8 defined in PCIe specification)
    PCIE_TAG_WIDTH      : integer := 8;

    -- Width of 'lower address' field in PCIE completion header
    PCIE_LOW_ADDR_WIDTH : integer := 12;

    -- CPL credits checking:
    -- Each credit represents one available 64B or 128B word in receiving buffer.
    -- The goal is to calculate, whether UP read request's response fits in available words in receiving buffer.

    -- Do check for enough credits
    CHECK_CPL_CREDITS   : boolean := true;
    -- Available space in receiving buffer (in data words) (added to base 64 words available in PCIe core)
    EXTRA_WORDS         : integer := 512;

    -- Auto-assign PCIe tags
    -- true  -> Tag Manager automaticaly generates remapped tags and sends transactions up with these tags.
    -- false -> Tag Manager receives tags from PCIe endpoint via the TAG_ASSIGN interface.
    --          (Can only be used on Xilinx FPGAs)
    -- This option must correspond with the PCIe settings.
    AUTO_ASSIGN_TAGS    : boolean := false;

    -- Size of FIFO for saving UP Tags and IDs while waiting for assigned Tag from PCIe endpoint [words]
    DMA_IN_FIFO_ITEMS   : integer := 16;

    -- Size of FIFO for saving PCIE assigned Tags while waiting for their freeing [words]
    -- Only used when AUTO_ASSIGN_TAGS is set to true.
    PCIE_IN_FIFO_ITEMS        : integer := 16;
    -- Offset for almost full of PCIE assigned tags FIFO [words]
    PCIE_IN_FIFO_AFULL_OFFSET : integer := 8;

    -- Target device
    -- "VIRTEX6", "7SERIES", "ULTRASCALE"
    DEVICE              : string  := "ULTRASCALE"
);
port(
    ---------------------------------------------------------------------------
    -- Common interface
    ---------------------------------------------------------------------------

    CLK                 : in  std_logic;
    RESET               : in  std_logic;

    ---------------------------------------------------------------------------
    -- Interface to MVB UP sending for each UP region
    ---------------------------------------------------------------------------

    -- IN - inserting headers to Tag manager
    -- Upstream headers
    MVB_UP_HDR_IN          : in  std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    -- Valid bit for each UP header
    MVB_UP_HDR_IN_VLD      : in  std_logic_vector(MVB_UP_ITEMS                -1 downto 0);
    -- Source ready for entire UP stream
    MVB_UP_HDR_IN_SRC_RDY  : in  std_logic;
    -- Destination ready for entire UP stream
    MVB_UP_HDR_IN_DST_RDY  : out std_logic;

    -- OUT - getting headers back from Tag manager after enough buffer space (credits) has been checked
    -- Upstream headers
    MVB_UP_HDR_OUT          : out std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    -- Tag is separated from rest of the header, since it can be different width from the input Tag
    MVB_UP_TAG_OUT          : out std_logic_vector(MVB_UP_ITEMS*PCIE_TAG_WIDTH -1 downto 0);
    -- Valid bit for each UP header
    MVB_UP_HDR_OUT_VLD      : out std_logic_vector(MVB_UP_ITEMS                -1 downto 0);
    -- Source ready for entire UP stream
    MVB_UP_HDR_OUT_SRC_RDY  : out std_logic;
    -- Destination ready for entire UP stream
    MVB_UP_HDR_OUT_DST_RDY  : in  std_logic;

    ---------------------------------------------------------------------------
    -- Interface to PCIe core tag assign (only used when AUTO_ASSIGN_TAGS is se to false)
    ---------------------------------------------------------------------------

    -- PCIe tag assigned to send transaction
    TAG_ASSIGN          : in  std_logic_vector(MVB_UP_ITEMS*PCIE_TAG_WIDTH-1 downto 0);
    -- Valid bit for assigned tags
    TAG_ASSIGN_VLD      : in  std_logic_vector(MVB_UP_ITEMS               -1 downto 0);

    ---------------------------------------------------------------------------
    -- Interface to MVB DOWN receiving
    ---------------------------------------------------------------------------

    -- PCIe tag of arriving completion transactions
    TAG                 : in  std_logic_vector(MVB_DOWN_ITEMS*PCIE_TAG_WIDTH-1 downto 0);
    -- Lower bits of address of requested tag's completition (address of a byte)
    TAG_COMPL_LOW_ADDR  : in  std_logic_vector(MVB_DOWN_ITEMS*PCIE_LOW_ADDR_WIDTH-1 downto 0);
    -- Length of requested tag's completition
    TAG_COMPL_LEN       : in  std_logic_vector(MVB_DOWN_ITEMS*(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1)-1 downto 0);
    -- Order for reserved tag release
    TAG_RELEASE         : in  std_logic_vector(MVB_DOWN_ITEMS               -1 downto 0);
    -- PCIe tag valid bit
    TAG_VLD             : in  std_logic_vector(MVB_DOWN_ITEMS               -1 downto 0);

    -- DMA DOWN HDR output has delay 2 CLK after TAG input is set

    -- DMA tag corresponding to given PCIe tag
    DMA_DOWN_HDR_TAG    : out std_logic_vector(MVB_DOWN_ITEMS*DMA_TAG_WIDTH-1 downto 0);
    -- DMA component ID corresponding to PCIe tag
    DMA_DOWN_HDR_ID     : out std_logic_vector(MVB_DOWN_ITEMS*DMA_ID_WIDTH -1 downto 0);

    ---------------------------------------------------------------------------
    -- Configuration status interface
    ---------------------------------------------------------------------------

    -- Read completition boundary status ('0' = RCB is 64B, '1' = RCB is 128B)
    -- Must not be changed while running.
    RCB_SIZE            : in  std_logic
);
end entity PTC_TAG_MANAGER;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PTC_TAG_MANAGER is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    -- When using 10-bit PCIe Tag, only 512 values from 256 to 3*256-1 can be used, so only 9 bits are actually needed.
    constant INTERNAL_PCIE_TAG_WIDTH : integer := tsel((PCIE_TAG_WIDTH=10),9,PCIE_TAG_WIDTH);
    -- PCIe Tag can be converted from PCIE_TAG_WIDTH to INTERNAL_PCIE_TAG_WIDTH and back using these functions
    function pcie_tag_int_to_ext(int_tag : std_logic_vector(INTERNAL_PCIE_TAG_WIDTH-1 downto 0)) return std_logic_vector is
        variable ext_tag : std_logic_vector(PCIE_TAG_WIDTH-1 downto 0);
    begin
        if (PCIE_TAG_WIDTH=10) then
            ext_tag := std_logic_vector(resize_left(unsigned(int_tag),PCIE_TAG_WIDTH)+256);
        else
            ext_tag := int_tag;
        end if;
        return ext_tag;
    end function;
    function pcie_tag_ext_to_int(ext_tag : std_logic_vector(PCIE_TAG_WIDTH-1 downto 0)) return std_logic_vector is
        variable int_tag : std_logic_vector(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    begin
        if (PCIE_TAG_WIDTH=10) then
            int_tag := std_logic_vector(resize_left(unsigned(ext_tag)-256,INTERNAL_PCIE_TAG_WIDTH));
        else
            int_tag := ext_tag;
        end if;
        return int_tag;
    end function;

    function div_ceil(a : integer; b : integer) return integer is
    begin
        if ((a mod b)=0) then
            return a/b;
        else
            return a/b+1;
        end if;
    end function;

    function get_pcie_fifoxm_items return integer is
    begin
        if (AUTO_ASSIGN_TAGS) then
            return 2**INTERNAL_PCIE_TAG_WIDTH; -- enough space for all possible tags
        else
            return PCIE_IN_FIFO_ITEMS*MVB_UP_ITEMS; -- user-defined size
        end if;
    end function;

    function get_pcie_fifoxm_write_ports return integer is
    begin
        if (AUTO_ASSIGN_TAGS) then
            return MVB_DOWN_ITEMS; -- one for each possible tag release
        else
            return MVB_UP_ITEMS; -- one for each possible tag assign from PCIe endpoint
        end if;
    end function;

    function get_pcie_fifoxm_read_ports return integer is
    begin
        if (AUTO_ASSIGN_TAGS) then
            return MVB_UP_ITEMS; -- one for each possible tag assign
        else
            return MVB_UP_ITEMS*2; -- one for each possible tag assign in this or the previous tick (on unsuccessful assign)
        end if;
    end function;

    -- CplH credits in PCIe receive buffer
    constant AVAILABLE_WORDS    : integer := EXTRA_WORDS;
    constant A_WORDS_WIDTH      : integer := log2(AVAILABLE_WORDS+1);

    constant MFB_DOWN_WORD_SIZE         : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE;
    constant MFB_DOWN_WORD_SIZE_WIDTH   : integer := log2(MFB_DOWN_WORD_SIZE);
    constant MFB_DOWN_WORD_SIZE_B_WIDTH : integer := MFB_DOWN_WORD_SIZE_WIDTH+2;

    -- Read completition boundary size in DWORDS for RCB_SIZE==0 and RCB_SIZE==1
    constant RCB_SIZE0          : integer := 64/4;
    constant RCB_SIZE0_WIDTH    : integer := log2(RCB_SIZE0);
    constant RCB_SIZE0_B_WIDTH  : integer := RCB_SIZE0_WIDTH;
    constant RCB_SIZE1          : integer := 128/4;
    constant RCB_SIZE1_WIDTH    : integer := log2(RCB_SIZE1);
    constant RCB_SIZE1_B_WIDTH  : integer := RCB_SIZE1_WIDTH;
    constant RCB_SIZE_MAX       : integer := max(RCB_SIZE0,RCB_SIZE1);
    constant RCB_SIZE_MAX_WIDTH : integer := log2(RCB_SIZE_MAX);
    constant RCB_SIZE_MIN       : integer := minimum(RCB_SIZE0,RCB_SIZE1);
    constant RCB_SIZE_MIN_WIDTH : integer := log2(RCB_SIZE_MIN);
    -- Number of words reserved for first / last part of completion for RCB_SIZE==0 and RCB_SIZE==1
    constant FIRST_LAST_PART_SIZE0 : integer := div_ceil(RCB_SIZE0,MFB_DOWN_WORD_SIZE);
    constant FIRST_LAST_PART_SIZE1 : integer := div_ceil(RCB_SIZE1,MFB_DOWN_WORD_SIZE);

    constant DMA_ADDR_WIDTH : integer := DMA_REQUEST_GLOBAL'high-DMA_REQUEST_GLOBAL'low+1-2;
    constant DMA_LEN_WIDTH  : integer := DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1;

    constant WORDS_COUNT_WIDTH      : integer := log2(2**DMA_LEN_WIDTH*2-MFB_DOWN_REG_SIZE-MFB_DOWN_REGIONS)+1;
    constant WORDS_COUNT_SUM_WIDTH  : integer := log2(2**WORDS_COUNT_WIDTH*MVB_UP_ITEMS);

    -- width of pointer for completion words counting
    constant COMPL_PTR_WIDTH : integer := log2(2**(DMA_LEN_WIDTH+2)+2**(RCB_SIZE_MAX_WIDTH+2)+1);
    -- Switches printing of debug info for process s1_reg_pr.
    -- Transcript file containing this info can be later checked by the max_words_num_transcript_check.py script for correctness.
    --
    -- The format of accepted info log lines is as follows:
    --
    -- <LINE>             -> # time: <time> :WORDS_COUNT_INFO:<INFO>
    -- <INFO>             -> <RCB_INFO>
    -- <INFO>             -> <REGIONS_INFO>
    -- <INFO>             -> <REG_SIZE_INFO>
    -- <INFO>             -> <TRANSACTION_INFO>
    -- <RCB_INFO>         -> RCB=<num>
    -- <REGIONS_INFO>     -> REGIONS=<num>
    -- <REG_SIZE_INFO>    -> REG_SIZE=<num>
    -- <TRANSACTION_INFO> -> <ADDR>,<LEN>,<MAX_WORDS>
    -- <ADDR>             -> trans_addr=0x<hex_num>
    -- <LEN>              -> trans_len=0x<hex_num>
    -- <MAX_WORDS>        -> trans_max_words_num=0x<hex_num>
    --
    -- where <num> and <hex_num> are values used by the script
    constant PRINT_WORDS_COUNT_INFO : boolean := false;

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    -- IN signals to arrays conversion
    signal TAG_ASSIGN_arr        : slv_array_t(MVB_UP_ITEMS  -1 downto 0)(INTERNAL_PCIE_TAG_WIDTH -1 downto 0);
    signal MVB_UP_HDR_IN_arr     : slv_array_t(MVB_UP_ITEMS  -1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);

    -----------------------
    -- Credits counting pipeline (from input to Tag/ID saving FIFO)
    -----------------------

     -- number of words to reserve for first / last part of transaction (as unsigned)
    signal FIRST_LAST_PART_SIZE_u : unsigned(WORDS_COUNT_WIDTH-1 downto 0);

    -- step 0 - input, sum of addr and len for each transaction

    -- MVB UP HDR fields
    signal s0_vld  : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s0_read : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s0_len  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_LEN_WIDTH-1 downto 0);
    signal s0_addr : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0);
    signal s0_tag  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_TAG_WIDTH-1 downto 0);
    signal s0_id   : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ID_WIDTH-1 downto 0);
    signal s0_hdr  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);

    -- step 1 - reg1, max number of words for each transaction

    -- enable register write
    signal s1_reg_en : std_logic;
    -- MVB UP HDR fields
    signal s1_reg_vld  : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s1_read_reg : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s1_tag_reg  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_TAG_WIDTH-1 downto 0);
    signal s1_id_reg   : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ID_WIDTH-1 downto 0);
    signal s1_hdr_reg  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);
    -- maximum number of words in responses for each read
    signal s1_max_words_num_reg : u_array_t(MVB_UP_ITEMS-1 downto 0)(WORDS_COUNT_WIDTH-1 downto 0);

    -- additional signals for max words counting
    signal s_len_u                : u_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_LEN_WIDTH-1 downto 0);
    signal s_addr_u               : u_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0);
    signal s_words_u              : u_array_t(MVB_UP_ITEMS-1 downto 0)(WORDS_COUNT_WIDTH-1 downto 0);

    -- step 2 - reg2, words sum

    -- enable register write
    signal s2_reg_en : std_logic;
    -- MVB UP HDR fields
    signal s2_reg_vld  : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s2_read_reg : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s2_read_vld : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s2_tag_reg  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_TAG_WIDTH-1 downto 0);
    signal s2_id_reg   : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ID_WIDTH-1 downto 0);
    signal s2_hdr_reg  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);
    -- maximum number of words in responses for each read
    signal s2_max_words_num_reg     : u_array_t(MVB_UP_ITEMS-1 downto 0)(WORDS_COUNT_WIDTH-1 downto 0);
    -- maximum number of words in responses sum
    signal s2_max_words_sum_num_reg     : unsigned(WORDS_COUNT_SUM_WIDTH-1 downto 0);
    signal s2_max_words_sum_num_res_reg : unsigned(WORDS_COUNT_SUM_WIDTH-1 downto 0);

    -- step 3 - reg3, Tag/ID saving FIFO input, free words counting, sending HDR OUT

    -- enable register write
    signal s3_reg_en : std_logic;
    -- MVB UP HDR fields
    signal s3_reg_vld  : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal s3_tag_reg  : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_TAG_WIDTH-1 downto 0);
    signal s3_id_reg   : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ID_WIDTH-1 downto 0);
    -- maximum number of words in responses for each read
    signal s3_max_words_num_reg : u_array_t(MVB_UP_ITEMS-1 downto 0)(WORDS_COUNT_WIDTH-1 downto 0);

    -- number of free words in receiving buffers
    signal free_cplh_reg    : unsigned(A_WORDS_WIDTH-1 downto 0);
    -- enough free words
    signal enough_free_cplh : std_logic;

    -- auto-assigned tags from PCIe tag FIFOX Multi distributed to instructions in the s2 register
    signal auto_assigned_tags : slv_array_t(MVB_UP_ITEMS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    -- enough tags available for auto-assign
    signal auto_assign_rdy    : std_logic;

    -----------------------

    -----------------------
    -- Tag assign input FIFOs
    -----------------------

    -- DMA Tag and ID saving FIFOX_MULTI interface
    -- Recomendation:
    -- -- Adjust generic DMA_IN_FIFO_ITEMS so that full is allways 0.
    -- Warning:
    -- -- Empty should never be 1 when attempting to read!
    -- -- For each assigned PCIe Tag there must allways be a corresponding DMA Tag and ID!
    constant DMA_IN_FIFO_DATA_WIDTH : integer := DMA_TAG_WIDTH+DMA_ID_WIDTH;
    signal dma_in_fifoxm_di      : std_logic_vector(MVB_UP_ITEMS*DMA_IN_FIFO_DATA_WIDTH-1 downto 0);
    signal dma_in_fifoxm_wr      : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
    signal dma_in_fifoxm_full    : std_logic;
    signal dma_in_fifoxm_do      : std_logic_vector(MVB_UP_ITEMS*DMA_IN_FIFO_DATA_WIDTH-1 downto 0);
    signal dma_in_fifoxm_rd      : std_logic_vector(MVB_UP_ITEMS-1 downto 0) := (others => '0');
    signal dma_in_fifoxm_empty   : std_logic_vector(MVB_UP_ITEMS-1 downto 0) := (others => '0');
    signal dma_in_fifoxm_n_empty : std_logic_vector(MVB_UP_ITEMS-1 downto 0) := (others => '0');

    -- Assigned PCIe Tag saving FIFOX_MULTI interface
    -- When AUTO_ASSIGN_TAGS is false:
    --     This FIFO only starts filling up when PCIe starts assigning Tags
    --     before the Tag Manager freed them here.
    --     Requirement: PCIE_IN_FIFO_ITEMS must be set, so that the FIFO never overflows
    --     (depends on PCIe endpoint behavior).
    constant PCIE_IN_FIFO_DATA_WIDTH : integer := INTERNAL_PCIE_TAG_WIDTH;
    signal pcie_in_fifoxm_di     : std_logic_vector(get_pcie_fifoxm_write_ports*PCIE_IN_FIFO_DATA_WIDTH-1 downto 0);
    signal pcie_in_fifoxm_wr     : std_logic_vector(get_pcie_fifoxm_write_ports-1 downto 0) := (others => '0');
    signal pcie_in_fifoxm_full   : std_logic := '0';
    signal pcie_in_fifoxm_afull  : std_logic;
    signal pcie_in_fifoxm_do     : std_logic_vector(get_pcie_fifoxm_read_ports*PCIE_IN_FIFO_DATA_WIDTH-1 downto 0);
    signal pcie_in_fifoxm_rd     : std_logic_vector(get_pcie_fifoxm_read_ports-1 downto 0);
    signal pcie_in_fifoxm_empty  : std_logic_vector(get_pcie_fifoxm_read_ports-1 downto 0);

    signal pcie_in_fifoxm_do_arr  : slv_array_t(get_pcie_fifoxm_read_ports-1 downto 0)(PCIE_IN_FIFO_DATA_WIDTH-1 downto 0);
    signal pcie_in_fifoxm_do_reg  : slv_array_t(get_pcie_fifoxm_read_ports-1 downto 0)(PCIE_IN_FIFO_DATA_WIDTH-1 downto 0);
    signal pcie_in_fifoxm_vld_reg : std_logic_vector(get_pcie_fifoxm_read_ports-1 downto 0);

    -- shift of pcie fifo read based on assign_unsuccess
    signal pcie_fifo_rd_shift : unsigned(log2(MVB_UP_ITEMS+1)-1 downto 0) := (others => '0');

    -- this pcie fifo output has ordered an assign
    signal assign_ordered_reg : std_logic_vector(MVB_UP_ITEMS-1 downto 0);

    -- tag requesting for mapping is also being released now
    signal being_released     : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    -- assign unsuccessful flag for each pcie fifo output reg
    signal assign_unsuccess   : std_logic_vector(MVB_UP_ITEMS-1 downto 0);

    -- tag auto-assign init counters (used to fill the PCIe Tag FIFOX Multi after reset)
    signal tag_assign_init_cnts : u_array_t(MVB_DOWN_ITEMS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH+1-1 downto 0);

    -----------------------

    -----------------------
    -- Tag mapping logic
    -----------------------
    -- =======================================================
    -- tag managing N_LOOP_OP unit (contains multiport memory)
    -- =======================================================

    -- DOWN mapping
    constant TAG_MAP_READ_PORTS  : integer := MVB_DOWN_ITEMS;
    -- UP for assigning
    constant TAG_MAP_OPERATORS   : integer := MVB_UP_ITEMS;
    -- assign
    constant TAG_MAP_OPERATIONS  : integer := 1;
    -- Tag+ID
    constant TAG_MAP_DATA_WIDTH  : integer := DMA_TAG_WIDTH+DMA_ID_WIDTH;
    signal tag_map_item_sel   : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    signal tag_map_ops        : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(TAG_MAP_OPERATIONS-1 downto 0);
    signal tag_map_in_sel     : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    signal tag_map_in_src     : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(TAG_MAP_OPERATORS-1 downto 0);
    signal tag_map_in_ops     : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(TAG_MAP_OPERATIONS-1 downto 0);
    signal tag_map_in_data    : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(TAG_MAP_DATA_WIDTH-1 downto 0);
    signal tag_map_out_data   : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(TAG_MAP_DATA_WIDTH-1 downto 0);
    signal tag_map_read_addr  : slv_array_t(TAG_MAP_READ_PORTS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0) := (others => (others => '0'));
    signal tag_map_read_data  : slv_array_t(TAG_MAP_READ_PORTS-1 downto 0)(TAG_MAP_DATA_WIDTH-1 downto 0) := (others => (others => '0'));

    -- TAG_MAP_DATA separated
    signal tag_map_in_data_tag    : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(DMA_TAG_WIDTH-1 downto 0);
    signal tag_map_in_data_id     : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(DMA_ID_WIDTH-1 downto 0);
    signal tag_map_out_data_tag   : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(DMA_TAG_WIDTH-1 downto 0);
    signal tag_map_out_data_id    : slv_array_t(TAG_MAP_OPERATORS-1 downto 0)(DMA_ID_WIDTH-1 downto 0);

    -- tag read info register
    signal tag_map_read_tag_reg      : slv_array_t     (MVB_DOWN_ITEMS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0) := (others => (others => '0'));
    signal tag_map_read_low_addr_reg : slv_array_t     (MVB_DOWN_ITEMS-1 downto 0)(PCIE_LOW_ADDR_WIDTH -1 downto 0) := (others => (others => '0'));
    signal tag_map_read_len_reg      : slv_array_t     (MVB_DOWN_ITEMS-1 downto 0)(DMA_LEN_WIDTH -1 downto 0) := (others => (others => '0'));
    signal tag_map_read_rel_reg      : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    signal tag_map_read_reg_vld      : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0) := (others => '0');

    -- valid bit for each tag mapping
    signal tag_map_vld_reg : std_logic_vector(2**INTERNAL_PCIE_TAG_WIDTH-1 downto 0);

    -- tag assign / release control
    signal tag_ass_tag   : slv_array_t     (MVB_UP_ITEMS  -1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    signal tag_ass_vld   : std_logic_vector(MVB_UP_ITEMS  -1 downto 0);
    signal tag_rel_tag   : slv_array_t     (MVB_DOWN_ITEMS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    signal tag_touch_vld : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    signal tag_rel_vld   : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);

    -- recently freed words sum counting unit
    signal pta_in_data_arr     : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(A_WORDS_WIDTH-1 downto 0);
    signal pta_in_data_reg     : std_logic_vector(MVB_DOWN_ITEMS*A_WORDS_WIDTH-1 downto 0);
    signal pta_in_vld          : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    signal pta_in_vld_reg      : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
    signal pta_out_data        : std_logic_vector(A_WORDS_WIDTH-1 downto 0);

    -- the sum of recently freed reserved words
    signal freed_words_reg : unsigned(A_WORDS_WIDTH-1 downto 0);

    -- register for RCB_SIZE (for better timing)
    signal RCB_SIZE_reg : std_logic;

    -----------------------

    ---------------------------------------------------------------------------

begin

    words_count_info_start_gen : if (PRINT_WORDS_COUNT_INFO) generate
        words_count_info_start_pr : process (RESET)
            variable rcb_s_vec : std_logic_vector(1-1 downto 0);
            variable l : line; -- debug print line
        begin
            if (RESET'event and RESET='0') then
                rcb_s_vec(0) := RCB_SIZE_reg;
                write(l,string'("time: "));
                write(l,now);
                write(l,string'(" :WORDS_COUNT_INFO:"));
                write(l,string'("RCB="));
                write_dec(l,rcb_s_vec);
                writeline(output,l);
                write(l,string'("time: "));
                write(l,now);
                write(l,string'(" :WORDS_COUNT_INFO:"));
                write(l,string'("REGIONS="));
                write_dec(l,MFB_DOWN_REGIONS);
                writeline(output,l);
                write(l,string'("time: "));
                write(l,now);
                write(l,string'(" :WORDS_COUNT_INFO:"));
                write(l,string'("REG_SIZE="));
                write_dec(l,MFB_DOWN_REG_SIZE);
                writeline(output,l);
                write(l,string'("time: "));
                write(l,now);
                write(l,string'(" :WORDS_COUNT_INFO:"));
                write(l,string'("ADDR_WIDTH="));
                write_dec(l,DMA_ADDR_WIDTH+2);
                writeline(output,l);
                write(l,string'("time: "));
                write(l,now);
                write(l,string'(" :WORDS_COUNT_INFO:"));
                write(l,string'("LEN_WIDTH="));
                write_dec(l,DMA_LEN_WIDTH);
                writeline(output,l);
            end if;
        end process;
    end generate;

    -- -------------------------------------------------------------------------
    -- IN signals to arrays conversion
    -- -------------------------------------------------------------------------

    in_arr_conv_gen : for i in 0 to MVB_UP_ITEMS-1 generate
        MVB_UP_HDR_IN_arr(i) <= MVB_UP_HDR_IN(DMA_UPHDR_WIDTH*(i+1)-1 downto DMA_UPHDR_WIDTH*i);
        TAG_ASSIGN_arr(i)    <= pcie_tag_ext_to_int(TAG_ASSIGN(PCIE_TAG_WIDTH*(i+1)-1 downto PCIE_TAG_WIDTH*i));
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Credits counting pipeline (from input to Tag/ID saving FIFO)
    -- -------------------------------------------------------------------------

    MVB_UP_HDR_IN_DST_RDY <= '1' when s1_reg_en='1' else '0';

    -- step 0 - input, sum of addr and len for each transaction

    s0_gen : for i in 0 to MVB_UP_ITEMS-1 generate
        s0_vld(i)  <= '1' when MVB_UP_HDR_IN_VLD(i)='1' and MVB_UP_HDR_IN_SRC_RDY='1' else '0';
        s0_read(i) <= '1' when MVB_UP_HDR_IN_arr(i)(DMA_REQUEST_TYPE)=DMA_TYPE_READ else '0';
        s0_len(i)  <= MVB_UP_HDR_IN_arr(i)(DMA_REQUEST_LENGTH'low+DMA_LEN_WIDTH   -1 downto DMA_REQUEST_LENGTH'low);
        s0_addr(i) <= MVB_UP_HDR_IN_arr(i)(DMA_REQUEST_GLOBAL'low+DMA_ADDR_WIDTH+2-1 downto DMA_REQUEST_GLOBAL'low+2); -- hide lowest 2 bits (always 0)
        s0_tag(i)  <= MVB_UP_HDR_IN_arr(i)(DMA_REQUEST_TAG   'low+DMA_TAG_WIDTH   -1 downto DMA_REQUEST_TAG   'low);
        s0_id(i)   <= MVB_UP_HDR_IN_arr(i)(DMA_REQUEST_UNITID'low+DMA_ID_WIDTH    -1 downto DMA_REQUEST_UNITID'low);
        s0_hdr(i)  <= MVB_UP_HDR_IN_arr(i);
    end generate;

    FIRST_LAST_PART_SIZE_u <= to_unsigned(FIRST_LAST_PART_SIZE0,WORDS_COUNT_WIDTH) when RCB_SIZE_reg='0' else to_unsigned(FIRST_LAST_PART_SIZE1,WORDS_COUNT_WIDTH);

    -- step 1 - reg1, max number of words for each transaction

    s1_reg_pr : process (CLK)
        variable len_u      : u_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_LEN_WIDTH-1 downto 0);        -- length of transaction as unsigned
        variable addr_u     : u_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0);       -- dword address of transaction as unsigned
        variable words_u         : u_array_t(MVB_UP_ITEMS-1 downto 0)(WORDS_COUNT_WIDTH-1 downto 0); -- complete number of words to reserve for the transaction
        variable l : line; -- debug print line
    begin
        if (CLK'event and CLK='1') then
            if (s1_reg_en='1') then
                s1_reg_vld  <= s0_vld;
                s1_read_reg <= s0_read;
                s1_tag_reg  <= s0_tag;
                s1_id_reg   <= s0_id;
                s1_hdr_reg  <= s0_hdr;

                for i in 0 to MVB_UP_ITEMS-1 loop
                    -- calculating the number of words to reserve for this transaction (see commentary of constant PRINT_WORDS_COUNT_INFO for explanation)
                    words_u(i) := (others => '0');

                    len_u(i)  := unsigned(s0_len(i));
                    addr_u(i) := unsigned(s0_addr(i));

                    words_u(i) := resize(enlarge_right(round_up(resize(len_u(i),addr_u(i)'length)+resize(resize(addr_u(i),MFB_DOWN_WORD_SIZE_WIDTH),addr_u(i)'length),MFB_DOWN_WORD_SIZE_WIDTH),-MFB_DOWN_WORD_SIZE_WIDTH),words_u(i)'length);

                    -- debug info
                    s_len_u(i)   <= len_u(i);
                    s_addr_u(i)  <= addr_u(i);
                    s_words_u(i) <= words_u(i);

                    if (PRINT_WORDS_COUNT_INFO and s0_vld(i)='1' and s0_read(i)='1') then
                        write(l,string'("time: "));
                        write(l,now);
                        write(l,string'(" :WORDS_COUNT_INFO:"));
                        write(l,string'("trans_addr=0x"));
                        write_hex(l,enlarge_right(addr_u(i),2));
                        write(l,string'(",trans_len=0x"));
                        write_hex(l,len_u(i));
                        write(l,string'(",trans_max_words_num=0x"));
                        write_hex(l,words_u(i));
                        writeline(output,l);
                    end if;

                    -- save result
                    s1_max_words_num_reg(i) <= words_u(i);
                end loop;
            elsif (s2_reg_en='1') then
                s1_reg_vld <= (others => '0');
            end if;

            if (RESET='1') then
                s1_reg_vld <= (others => '0');
            end if;
        end if;
    end process;

    auto_assign_s1_reg_en_gen : if (AUTO_ASSIGN_TAGS) generate
        s1_reg_en <= '1' when s2_reg_en='1' and tag_assign_init_cnts(0)(PCIE_IN_FIFO_DATA_WIDTH)='1' else '0';
    end generate;

    no_auto_assign_s1_reg_en_gen : if (not AUTO_ASSIGN_TAGS) generate
        s1_reg_en <= '1' when s2_reg_en='1' and pcie_in_fifoxm_afull='0' else '0';
    end generate;

    -- step 2 - reg2, words sum, free words counting

    s2_reg_pr : process (CLK)
        variable sum : unsigned(WORDS_COUNT_SUM_WIDTH-1 downto 0);
    begin
        if (CLK'event and CLK='1') then
            if (s2_reg_en='1') then
                s2_reg_vld  <= s1_reg_vld;
                s2_read_reg <= s1_read_reg;
                s2_tag_reg  <= s1_tag_reg;
                s2_id_reg   <= s1_id_reg;
                s2_hdr_reg  <= s1_hdr_reg;
                s2_max_words_num_reg <= s1_max_words_num_reg;

                sum := (others => '0');
                for i in 0 to MVB_UP_ITEMS-1 loop
                    if (s1_reg_vld(i)='1' and s1_read_reg(i)='1') then
                        sum := sum+s1_max_words_num_reg(i);
                    end if;
                end loop;
                s2_max_words_sum_num_reg     <= sum;
                -- Use a artificially increased sum to create a minimum reserve in Storage FIFOX
                -- There was a case when the precise counting of credits led to overflow
                -- I was not able to find out why, so this is just a simple dirty hack.
                s2_max_words_sum_num_res_reg <= sum+1;
            end if;

            if (RESET='1') then
                s2_reg_vld <= (others => '0');
            end if;
        end if;
    end process;

    s2_read_vld <= s2_reg_vld and s2_read_reg;

    s2_reg_en <= '1' when s3_reg_en='1' and MVB_UP_HDR_OUT_DST_RDY='1' and ((or s2_reg_vld)='0' or enough_free_cplh='1') else '0';

    -- step 3 - reg3, Tag/ID saving FIFO input, free words counting, sending HDR OUT

    -- free credits register
    free_cplh_reg_pr : process (CLK)
        variable l : line; -- debug print line
    begin
        if (CLK'event and CLK='1') then
            if (s2_reg_en='1' and (or s2_reg_vld)='1' and (or s2_read_reg)='1') then

                if (PRINT_WORDS_COUNT_INFO) then
                    write(l,string'("CPLH CHANGE ::"));write(l,now);write(l,string'("::"));write_dec(l,free_cplh_reg);write(l,string'(";"));
                    if (freed_words_reg>0) then
                        write(l,string'("+"));write_dec(l,freed_words_reg);write(l,string'(";"));
                    end if;
                    write(l,string'("-"));write_dec(l,s2_max_words_sum_num_reg);write(l,string'("::"));
                    writeline(output,l);
                end if;

                free_cplh_reg <= free_cplh_reg+freed_words_reg-resize(s2_max_words_sum_num_reg,A_WORDS_WIDTH);
            else

                if (PRINT_WORDS_COUNT_INFO) then
                    if (freed_words_reg>0) then
                        write(l,string'("CPLH CHANGE ::"));write(l,now);write(l,string'("::"));write_dec(l,free_cplh_reg);write(l,string'(";"));
                        write(l,string'("+"));write_dec(l,freed_words_reg);write(l,string'("::"));
                        writeline(output,l);
                    end if;
                end if;

                free_cplh_reg <= free_cplh_reg+freed_words_reg;
            end if;

            if (RESET='1') then
                free_cplh_reg <= to_unsigned(AVAILABLE_WORDS,A_WORDS_WIDTH);
            end if;
        end if;
    end process;

    -- is there enough space for reservation
    enough_free_cplh <= '1' when free_cplh_reg>=s2_max_words_sum_num_res_reg or CHECK_CPL_CREDITS=false else '0';

    -- in DMA FIFO input register
    s3_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (s3_reg_en='1') then
                s3_reg_vld <= s2_read_vld and enough_free_cplh and MVB_UP_HDR_OUT_DST_RDY;
                s3_tag_reg <= s2_tag_reg;
                s3_id_reg  <= s2_id_reg;
                s3_max_words_num_reg <= s2_max_words_num_reg;
            elsif (dma_in_fifoxm_full='0') then
                s3_reg_vld <= (others => '0');
            end if;

            if (RESET='1') then
                s3_reg_vld <= (others => '0');
            end if;
        end if;
    end process;

    s3_reg_en <= '1' when dma_in_fifoxm_full='0' and ((not AUTO_ASSIGN_TAGS) or auto_assign_rdy='1') else '0';

    auto_assign_hdr_out_gen : if (AUTO_ASSIGN_TAGS) generate

        -- tags distribution from PCIe tag FIFOX Multi
        pcie_tags_dist_pr : process (s2_read_vld,pcie_in_fifoxm_do_arr,pcie_in_fifoxm_empty)
            variable rd_ptr : integer := 0;
        begin
            auto_assigned_tags <= (others => (others => '0'));
            auto_assign_rdy    <= '1';
            rd_ptr := 0;
            for i in 0 to MVB_UP_ITEMS-1 loop
                if (s2_read_vld(i)='1') then
                    if (pcie_in_fifoxm_empty(i)='1') then -- There is not enough PCIe tags to assign -> stop the pipeline
                        auto_assign_rdy <= '0';
                    end if;
                    auto_assigned_tags(i) <= pcie_in_fifoxm_do_arr(rd_ptr);
                    rd_ptr := rd_ptr+1;
                end if;
            end loop;
        end process;

        -- HDR OUT sending
        hdr_out_gen_pr : process (s2_hdr_reg,auto_assigned_tags,s2_reg_vld)
        begin
            for i in 0 to MVB_UP_ITEMS-1 loop
                MVB_UP_HDR_OUT(DMA_UPHDR_WIDTH*(i+1)-1 downto DMA_UPHDR_WIDTH*i) <= s2_hdr_reg(i);
                MVB_UP_TAG_OUT((i+1)*PCIE_TAG_WIDTH-1 downto i*PCIE_TAG_WIDTH)   <= pcie_tag_int_to_ext(auto_assigned_tags(i));
                MVB_UP_HDR_OUT_VLD(i) <= s2_reg_vld(i);
            end loop;
        end process;

    end generate;

    no_auto_assign_hdr_out_gen : if (not AUTO_ASSIGN_TAGS) generate

        -- HDR OUT sending
        hdr_out_gen : for i in 0 to MVB_UP_ITEMS-1 generate
            MVB_UP_HDR_OUT(DMA_UPHDR_WIDTH*(i+1)-1 downto DMA_UPHDR_WIDTH*i) <= s2_hdr_reg(i);
            MVB_UP_HDR_OUT_VLD(i) <= '1' when s2_reg_vld(i)='1' else '0';
        end generate;

    end generate;

    MVB_UP_HDR_OUT_SRC_RDY <= '1' when (or s2_reg_vld)='1' and s3_reg_en='1' and enough_free_cplh='1' else '0';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- UP HDR DMA Tag and ID saving FIFO
    -- -------------------------------------------------------------------------

    dma_in_fifo_input_gen : for i in 0 to MVB_UP_ITEMS-1 generate
        dma_in_fifoxm_di(DMA_IN_FIFO_DATA_WIDTH*(i+1)-1 downto DMA_IN_FIFO_DATA_WIDTH*i) <= s3_tag_reg(i) & s3_id_reg(i);
        dma_in_fifoxm_wr(i) <= s3_reg_vld(i);
    end generate;

    auto_assign_fake_dma_fifoxm_gen : if (AUTO_ASSIGN_TAGS) generate

        dma_in_shakedown_i : entity work.SHAKEDOWN
        generic map(
            INPUTS     => MVB_UP_ITEMS,
            OUTPUTS    => MVB_UP_ITEMS,
            DATA_WIDTH => DMA_IN_FIFO_DATA_WIDTH,
            OUTPUT_REG => true
        )
        port map(
            CLK      => CLK  ,
            RESET    => RESET,

            DIN      => dma_in_fifoxm_di,
            DIN_VLD  => dma_in_fifoxm_wr,

            DOUT     => dma_in_fifoxm_do,
            DOUT_VLD => dma_in_fifoxm_n_empty
        );

        fake_dma_fifo_empty_full_gen : for i in 0 to MVB_UP_ITEMS-1 generate
            dma_in_fifoxm_empty(i) <= not dma_in_fifoxm_n_empty(i);
        end generate;
        dma_in_fifoxm_full <= '0';

    end generate;

    no_auto_assign_dma_fifoxm_gen : if (not AUTO_ASSIGN_TAGS) generate

        dma_in_fifoxm_i : entity work.FIFOX_MULTI
        generic map (
            DATA_WIDTH          => DMA_IN_FIFO_DATA_WIDTH        ,
            ITEMS               => DMA_IN_FIFO_ITEMS*MVB_UP_ITEMS,

            WRITE_PORTS         => MVB_UP_ITEMS,
            READ_PORTS          => MVB_UP_ITEMS,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            SAFE_READ_MODE      => false,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            ALLOW_SINGLE_FIFO   => false -- This FIFO must not have a lower latency than pcie_in_fifoxm
        )
        port map (
             CLK    => CLK  ,
             RESET  => RESET,

             DI     => dma_in_fifoxm_di   ,
             WR     => dma_in_fifoxm_wr   ,
             FULL   => dma_in_fifoxm_full ,
             AFULL  => open               ,

             DO     => dma_in_fifoxm_do   ,
             RD     => dma_in_fifoxm_rd   ,
             EMPTY  => dma_in_fifoxm_empty,
             AEMPTY => open
        );

        -- DMA in FIFO read by tag map unit
        dma_fifo_rd_gen : for i in 0 to MVB_UP_ITEMS-1 generate
            dma_in_fifoxm_rd(i) <= '1' when pcie_in_fifoxm_rd(i)='1' and pcie_in_fifoxm_empty(i)='0' else '0';
        end generate;

        -- check reading from empty fifo
        dma_fifo_read_check : for i in 0 to MVB_UP_ITEMS-1 generate
            assert ((dma_in_fifoxm_rd(i)='1' and dma_in_fifoxm_empty(i)='1')=false)
                report "Reading from empty FIFO! Invalid state in this case!" severity failure;
        end generate;

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- PCIe assign Tag saving FIFO
    -- -------------------------------------------------------------------------

    auto_assign_pcie_in_fifoxm_in_gen : if (AUTO_ASSIGN_TAGS) generate

        -- these counters fill the PCIe tag FIFOX Multi with all possible tags after reset
        tag_assign_init_cnts_pr : process (CLK)
        begin
            if (CLK'event and CLK='1') then
                for i in 0 to MVB_DOWN_ITEMS-1 loop
                    if (tag_assign_init_cnts(i)(INTERNAL_PCIE_TAG_WIDTH)='0' and (or tag_rel_vld)='0') then
                        tag_assign_init_cnts(i) <= tag_assign_init_cnts(i)+MVB_DOWN_ITEMS;
                    end if;
                end loop;

                if (RESET='1') then
                    for i in 0 to MVB_DOWN_ITEMS-1 loop
                        tag_assign_init_cnts(i) <= to_unsigned(i,INTERNAL_PCIE_TAG_WIDTH+1);
                    end loop;
                end if;
            end if;
        end process;

        -- after initial filling the FIFOX Multi is given every freed PCIe tag
        pcie_in_fifoxm_in_gen : for i in 0 to MVB_DOWN_ITEMS-1 generate
            pcie_in_fifoxm_di((i+1)*PCIE_IN_FIFO_DATA_WIDTH-1 downto i*PCIE_IN_FIFO_DATA_WIDTH)
                                   <= tag_rel_tag(i) -- tag release has priority
                                 when (or tag_rel_vld)='1'
                                 else std_logic_vector(tag_assign_init_cnts(i)(PCIE_IN_FIFO_DATA_WIDTH-1 downto 0));
            pcie_in_fifoxm_wr(i)   <= tag_rel_vld(i) -- tag release has priority
                                 when (or tag_rel_vld)='1'
                                 else (not tag_assign_init_cnts(i)(PCIE_IN_FIFO_DATA_WIDTH));
        end generate;
    end generate;

    no_auto_assign_pcie_in_fifoxm_in_gen : if (not AUTO_ASSIGN_TAGS) generate
        no_auto_assign_pcie_in_fifoxm_di_gen : for i in 0 to MVB_UP_ITEMS-1 generate
            pcie_in_fifoxm_di((i+1)*INTERNAL_PCIE_TAG_WIDTH-1 downto i*INTERNAL_PCIE_TAG_WIDTH) <= pcie_tag_ext_to_int(TAG_ASSIGN((i+1)*PCIE_TAG_WIDTH-1 downto i*PCIE_TAG_WIDTH));
        end generate;
        pcie_in_fifoxm_wr <= TAG_ASSIGN_VLD;
    end generate;

    pcie_in_fifoxm_i : entity work.FIFOX_MULTI(SHAKEDOWN)
    generic map (
        DATA_WIDTH          => PCIE_IN_FIFO_DATA_WIDTH,
        ITEMS               => get_pcie_fifoxm_items*get_pcie_fifoxm_write_ports,

        WRITE_PORTS         => get_pcie_fifoxm_write_ports,
        READ_PORTS          => get_pcie_fifoxm_read_ports ,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        SAFE_READ_MODE      => false ,
        ALMOST_FULL_OFFSET  => PCIE_IN_FIFO_AFULL_OFFSET,
        ALMOST_EMPTY_OFFSET => 0,
        ALLOW_SINGLE_FIFO   => false
   )
   port map (
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => pcie_in_fifoxm_di   ,
        WR     => pcie_in_fifoxm_wr   ,
        FULL   => pcie_in_fifoxm_full ,
        AFULL  => pcie_in_fifoxm_afull,

        DO     => pcie_in_fifoxm_do   ,
        RD     => pcie_in_fifoxm_rd   ,
        EMPTY  => pcie_in_fifoxm_empty,
        AEMPTY => open
   );

    -- check writing in full fifo
    pcie_fifo_write_check : for i in 0 to MVB_UP_ITEMS-1 generate
        assert ((pcie_in_fifoxm_wr(i)='1' and pcie_in_fifoxm_full='1' and RESET='0')=false)
            report "Writing in full FIFO! Invalid state in this case!" severity failure;
    end generate;

    pcie_in_fifoxm_out_reg_gen : if (AUTO_ASSIGN_TAGS) generate

        pcie_in_fifoxm_do_arr_gen : for i in 0 to MVB_UP_ITEMS-1 generate
            pcie_in_fifoxm_do_arr(i) <= pcie_in_fifoxm_do((i+1)*INTERNAL_PCIE_TAG_WIDTH-1 downto i*INTERNAL_PCIE_TAG_WIDTH);
        end generate;

        -- Tag FIFOX Multi output register
        pcie_in_fifoxm_out_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                pcie_in_fifoxm_do_reg  <= pcie_in_fifoxm_do_arr;
                pcie_in_fifoxm_vld_reg <= pcie_in_fifoxm_rd;

                if (RESET='1') then
                    pcie_in_fifoxm_vld_reg <= (others => '0');
                end if;
            end if;
        end process;
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- PCIe assign Tag saving FIFO reading
    -- -------------------------------------------------------------------------

    assign_ordered_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to MVB_UP_ITEMS-1 loop
                assign_ordered_reg(i) <= not pcie_in_fifoxm_empty(to_integer(pcie_fifo_rd_shift)+i);
            end loop;

            if (RESET='1') then
                assign_ordered_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- first unsuccessful assign detection
    pcie_in_fifo_rd_pr : process (all)
        variable rd_ptr : integer := 0;
    begin
        pcie_fifo_rd_shift <= (others => '0');
        pcie_in_fifoxm_rd  <= (others => '0');
        if ((not AUTO_ASSIGN_TAGS)) then -- this logic only applies when recieving tags from PCIe endpoint
            -- first 1 detection
            for i in 0 to MVB_UP_ITEMS-1 loop
                exit when (assign_unsuccess(i)='1' or assign_ordered_reg(i)='0');
                pcie_fifo_rd_shift   <= to_unsigned(i+1,log2(MVB_UP_ITEMS+1));
                pcie_in_fifoxm_rd(i) <= '1';
            end loop;
        else -- with auto-assigned tags the FIFOX Multi is read based on the content and enable of the s2 register
            -- shakedown
            rd_ptr := 0;
            for i in 0 to MVB_UP_ITEMS-1 loop
                if (s2_read_vld(i)='1' and s2_reg_en='1' and MVB_UP_HDR_OUT_DST_RDY='1') then
                    pcie_in_fifoxm_rd(rd_ptr) <= '1';
                    rd_ptr := rd_ptr+1;
                end if;
            end loop;
        end if;
    end process;

    being_released_det_pr : process(tag_rel_tag,tag_map_in_sel,tag_rel_vld)
    begin
        being_released <= (others => '0');
        -- detect if this tag is being released right now
        for i in 0 to MVB_UP_ITEMS-1 loop
            for e in 0 to MVB_DOWN_ITEMS-1 loop
                if (tag_rel_tag(e)=tag_map_in_sel(i) and tag_rel_vld(e)='1') then
                    being_released(i) <= '1';
                end if;
            end loop;
        end loop;
    end process;

    -- successful assign detection
    ass_succ_pr : process (tag_map_in_ops,tag_map_in_src,tag_map_vld_reg,tag_map_in_sel,being_released)
         variable tag_map_in_prev : boolean_vector(MVB_UP_ITEMS-1 downto 0);
    begin
        assign_unsuccess <= (others => '0');

        if (not AUTO_ASSIGN_TAGS) then -- This logic only applies when the unit is not auto-assigning tags
            for i in 0 to MVB_UP_ITEMS-1 loop
                for e in 0 to MVB_UP_ITEMS-1 loop

                    -- ((    assign ordered    ) and (ordered from this interface))
                    if (tag_map_in_ops(e)(0)='1' and    tag_map_in_src(e)(i)='1'  ) then

                        -- ((                           not free                       ))
                        if (tag_map_vld_reg(to_integer(unsigned(tag_map_in_sel(e))))='1') then

                            assign_unsuccess(i) <= '1';

                        --    ((not the first interface) and (        ordered from some previous interface        ))
                        elsif (           i>0            and tag_map_in_src(e)(i-1 downto 0)/=(i-1 downto 0 => '0')) then

                            assign_unsuccess(i) <= '1';

                        end if;

                    end if;

                end loop;
            end loop;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Tags mapping N_LOOP_OP unit
    -- -------------------------------------------------------------------------

    tags_map_n_loop_i : entity work.N_LOOP_OP
    generic map (
        DATA_WIDTH     => TAG_MAP_DATA_WIDTH,
        ITEMS          => 2**INTERNAL_PCIE_TAG_WIDTH  ,
        RESET_VAL      => 0,
        READ_PORTS     => TAG_MAP_READ_PORTS,

        OPERATORS      => TAG_MAP_OPERATORS ,
        OPERATIONS     => TAG_MAP_OPERATIONS,

        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK  ,
        RESET          => RESET,

        OP_ITEM_SEL    => tag_map_item_sel ,
        OP_OPERATIONS  => tag_map_ops      ,

        OP_IN_SEL      => tag_map_in_sel   ,
        OP_IN_SRC      => tag_map_in_src   ,
        OP_IN_OPS      => tag_map_in_ops   ,
        OP_IN_DATA     => tag_map_in_data  ,

        OP_OUT_DATA    => tag_map_out_data ,

        READ_ADDR      => tag_map_read_addr,
        READ_DATA      => tag_map_read_data
    );

    -- operation set
    tag_map_pr : process (all)
        variable ops_i_shift : integer := 0;
    begin
        for i in 0 to MVB_UP_ITEMS-1 loop
            if (not AUTO_ASSIGN_TAGS) then
                 tag_map_item_sel(i) <= pcie_in_fifoxm_do(INTERNAL_PCIE_TAG_WIDTH*(to_integer(pcie_fifo_rd_shift)+i+1)-1 downto INTERNAL_PCIE_TAG_WIDTH*(to_integer(pcie_fifo_rd_shift)+i));
                 tag_map_ops(i)      <= (others => '0');
                 tag_map_ops(i)(0)   <= (not pcie_in_fifoxm_empty(to_integer(pcie_fifo_rd_shift)+i));
             else
                 tag_map_item_sel(i) <= pcie_in_fifoxm_do_reg(i);
                 tag_map_ops(i)      <= (others => '0');
                 tag_map_ops(i)(0)   <= pcie_in_fifoxm_vld_reg(i);
             end if;
        end loop;
    end process;

    -- in data separation
    tag_map_in_data_sep_gen : for i in 0 to TAG_MAP_OPERATORS-1 generate
        tag_map_in_data_tag(i)   <= tag_map_in_data(i)(DMA_TAG_WIDTH+DMA_ID_WIDTH-1 downto DMA_ID_WIDTH);
        tag_map_in_data_id(i)    <= tag_map_in_data(i)(              DMA_ID_WIDTH-1 downto 0           );
    end generate;

    -- operators
    tag_map_operators_pr : process (all)
    begin
        for i in 0 to TAG_MAP_OPERATORS-1 loop
            tag_map_out_data_tag(i)   <= tag_map_in_data_tag(i);
            tag_map_out_data_id(i)    <= tag_map_in_data_id(i);
        end loop;

        for i in 0 to MVB_UP_ITEMS-1 loop
            tag_ass_tag(i) <= tag_map_in_sel(i);
            if (tag_map_in_ops(i)(0)='1') then
                if (AUTO_ASSIGN_TAGS) then
                    if (dma_in_fifoxm_empty(i)='0') then -- there is a valid instruction waiting
                        tag_map_out_data_tag(i) <= dma_in_fifoxm_do(DMA_IN_FIFO_DATA_WIDTH*i+DMA_TAG_WIDTH+DMA_ID_WIDTH-1 downto DMA_IN_FIFO_DATA_WIDTH*i+DMA_ID_WIDTH);
                        tag_map_out_data_id(i)  <= dma_in_fifoxm_do(DMA_IN_FIFO_DATA_WIDTH*i              +DMA_ID_WIDTH-1 downto DMA_IN_FIFO_DATA_WIDTH*i             );
                    end if;
                else
                    if (pcie_in_fifoxm_rd(i)='1') then -- all up to here can be assigned
                        tag_map_out_data_tag(i) <= dma_in_fifoxm_do(DMA_IN_FIFO_DATA_WIDTH*i+DMA_TAG_WIDTH+DMA_ID_WIDTH-1 downto DMA_IN_FIFO_DATA_WIDTH*i+DMA_ID_WIDTH);
                        tag_map_out_data_id(i)  <= dma_in_fifoxm_do(DMA_IN_FIFO_DATA_WIDTH*i              +DMA_ID_WIDTH-1 downto DMA_IN_FIFO_DATA_WIDTH*i             );
                    end if;
                end if;
            end if;
        end loop;
    end process;

    tag_ass_vld_p : process (all)
    begin
        for i in 0 to MVB_UP_ITEMS-1 loop
            tag_ass_vld(i) <= '0';
            if (tag_map_in_ops(i)(0)='1') then
                if (AUTO_ASSIGN_TAGS) then
                    if (dma_in_fifoxm_empty(i)='0') then -- there is a valid instruction waiting
                        tag_ass_vld(i) <= '1';
                    end if;
                else
                    if (pcie_in_fifoxm_rd(i)='1') then -- all up to here can be assigned
                        tag_ass_vld(i) <= '1';
                    end if;
                end if;
            end if;
        end loop;
    end process;

    -- out data merge
    tag_map_out_data_merge_gen : for i in 0 to TAG_MAP_OPERATORS-1 generate
        tag_map_out_data(i) <= tag_map_out_data_tag(i) & tag_map_out_data_id(i);
    end generate;

    -- tag map read
    tag_map_read_pr : process (tag_map_read_tag_reg,tag_map_read_data)
    begin
        for i in 0 to TAG_MAP_READ_PORTS-1 loop
            tag_map_read_addr(i) <= tag_map_read_tag_reg(i);

            DMA_DOWN_HDR_TAG(DMA_TAG_WIDTH*(i+1)-1 downto DMA_TAG_WIDTH*i) <= tag_map_read_data(i)(TAG_MAP_DATA_WIDTH-1 downto DMA_ID_WIDTH);
            DMA_DOWN_HDR_ID (DMA_ID_WIDTH *(i+1)-1 downto DMA_ID_WIDTH *i) <= tag_map_read_data(i)(DMA_ID_WIDTH-1 downto 0);
        end loop;
    end process;

    -- tag map read info register
    tag_map_read_info_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to MVB_DOWN_ITEMS-1 loop
                tag_map_read_tag_reg(i)      <= pcie_tag_ext_to_int(TAG(PCIE_TAG_WIDTH*(i+1)-1 downto PCIE_TAG_WIDTH*i));
                tag_map_read_low_addr_reg(i) <= TAG_COMPL_LOW_ADDR(PCIE_LOW_ADDR_WIDTH*(i+1)-1 downto PCIE_LOW_ADDR_WIDTH*i);
                tag_map_read_len_reg(i)      <= TAG_COMPL_LEN(DMA_LEN_WIDTH*(i+1)-1 downto DMA_LEN_WIDTH*i);
                tag_map_read_rel_reg(i)      <= TAG_RELEASE(i);
                tag_map_read_reg_vld(i)      <= TAG_VLD(i);
            end loop;
        end if;
    end process;

    tag_rel_tag   <= tag_map_read_tag_reg;
    tag_touch_vld <= tag_map_read_reg_vld;
    tag_rel_vld   <= tag_map_read_rel_reg;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Tag assign / release
    -- -------------------------------------------------------------------------

    tag_map_vld_gen : if (not AUTO_ASSIGN_TAGS) generate -- only when receiving tags for PCIe endpoint
        -- tag map valid register fields
        tag_map_vld_reg_pr : process (CLK)
        begin
            if (CLK'event and CLK='1') then
                -- release
                for i in 0 to MVB_DOWN_ITEMS-1 loop
                    if (tag_touch_vld(i)='1') then
                        if (tag_rel_vld(i)='1') then
                            tag_map_vld_reg(to_integer(unsigned(tag_rel_tag(i)))) <= '0';
                        end if;
                    end if;
                end loop;

                -- assign
                for i in 0 to MVB_UP_ITEMS-1 loop
                    if (tag_ass_vld(i)='1') then
                        tag_map_vld_reg      (to_integer(unsigned(tag_ass_tag(i)))) <= '1';
                    end if;
                end loop;

                -- reset
                if (RESET='1') then
                    tag_map_vld_reg <= (others => '0');
                end if;
            end if;
        end process;
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Freed words deduction
    -- -------------------------------------------------------------------------

    freed_words_adder_input_pr : process (all)
        variable rcb_ptr_s : unsigned(COMPL_PTR_WIDTH-1 downto 0); -- start pointer
        variable rcb_ptr_e : unsigned(COMPL_PTR_WIDTH-1 downto 0); -- end pointer (start + length)
        variable rcb_ptr_e_roundup : unsigned(COMPL_PTR_WIDTH-1 downto 0) := (others => '0'); -- end pointer rounded up to RCB_SIZE_reg
        variable rcb_ptr_e_roundup0 : unsigned(COMPL_PTR_WIDTH-1 downto 0) := (others => '0'); -- end pointer rounded up to RCB_SIZE_reg
        variable rcb_ptr_e_roundup1 : unsigned(COMPL_PTR_WIDTH-1 downto 0) := (others => '0'); -- end pointer rounded up to RCB_SIZE_reg
        variable words_wide        : unsigned(A_WORDS_WIDTH+MFB_DOWN_WORD_SIZE_WIDTH-1 downto 0);
        variable words             : unsigned(A_WORDS_WIDTH-1 downto 0); -- number of words to release by this completion transaction
        variable vld_vec : std_logic_vector(0 downto 0);
        variable l : line; -- debug print line
    begin
        for i in 0 to MVB_DOWN_ITEMS-1 loop

            words_wide := resize(unsigned(tag_map_read_len_reg(i)),words_wide'length)+resize(resize(enlarge_right(unsigned(tag_map_read_low_addr_reg(i)),-2),MFB_DOWN_WORD_SIZE_WIDTH),words_wide'length);
            if (tag_map_read_rel_reg(i)='1') then
                words := enlarge_right(round_up  (words_wide,MFB_DOWN_WORD_SIZE_WIDTH),-MFB_DOWN_WORD_SIZE_WIDTH);
            else -- When not completed, the possible unaligned part in last word will be accounted as part of the next completion piece (aonly applies when RCB is smaller than word)
                words := enlarge_right(round_down(words_wide,MFB_DOWN_WORD_SIZE_WIDTH),-MFB_DOWN_WORD_SIZE_WIDTH);
            end if;

            -- Negate all logic when not checking credits
            if (CHECK_CPL_CREDITS=false) then
                words := (others => '0');
            end if;

            -- propagate result
            pta_in_data_arr(i) <= std_logic_vector(words);
            pta_in_vld(i) <= tag_map_read_reg_vld(i);

        end loop;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Freed words sum counting
    -- -------------------------------------------------------------------------

    pta_input_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to MVB_DOWN_ITEMS-1 loop
                pta_in_data_reg(A_WORDS_WIDTH*(i+1)-1 downto A_WORDS_WIDTH*i) <= pta_in_data_arr(i);
                pta_in_vld_reg(i) <= pta_in_vld(i);
            end loop;
            if (RESET='1') then
                pta_in_vld_reg <= (others => '0');
            end if;
        end if;
    end process;

    freed_words_sum_adder_i : entity work.PIPE_TREE_ADDER
    generic map (
        ITEMS      => MVB_DOWN_ITEMS,
        DATA_WIDTH => A_WORDS_WIDTH ,
        LATENCY    => log2(MVB_DOWN_ITEMS)/log2(4) -- create 4-input adders
    )
    port map (
        CLK        => CLK  ,
        RESET      => RESET,

        IN_DATA    => pta_in_data_reg ,
        IN_VLD     => pta_in_vld_reg  ,

        OUT_DATA   => pta_out_data
    );

    freed_words_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            freed_words_reg <= unsigned(pta_out_data);
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RCB_SIZE register (for better timing)
    -- -------------------------------------------------------------------------

    rcb_size_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            RCB_SIZE_reg <= RCB_SIZE;
        end if;
    end process;

    -- -------------------------------------------------------------------------

end architecture;
