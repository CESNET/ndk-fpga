-- mtc.vhd: MI Transaction Controller
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

-- The MI Transaction Controller (MTC) component serves as the MI master
-- endpoint. It provides the conversion of PCIe read and write requests to MI
-- requests. It processes the responses to MI requests and sends them to
-- the host PC as PCIe completion transactions. If the MI slave does not respond
-- to an MI read request, the MTC module will be stuck, the PCIe communication
-- will be broken and the guest PC may get into an unexpected state.
--
-- **Simple block diagram including wiring:**
--
-- .. image:: doc/mtc.drawio.svg
--       :align: center
--       :width: 100 %
--
entity MTC is
    generic(
        -- MFB bus: number of regions in word
        MFB_REGIONS       : natural := 2;
        -- MFB bus: number of blocks in region, must be 1
        MFB_REGION_SIZE   : natural := 1;
        -- MFB bus: number of items in block, must be 8
        MFB_BLOCK_SIZE    : natural := 8;
        -- MFB bus: width of one item in bits, must be 32 (dword)
        MFB_ITEM_WIDTH    : natural := 32;
        -- MFB bus: width of single data region in bits, auxiliary parameter, do not change value!
        MFB_REGION_WIDTH  : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
        -- BAR0 base address for PCIE->MI32 transalation
        BAR0_BASE_ADDR    : std_logic_vector(31 downto 0) := X"01000000";
        -- BAR1 base address for PCIE->MI32 transalation
        BAR1_BASE_ADDR    : std_logic_vector(31 downto 0) := X"02000000";
        -- BAR2 base address for PCIE->MI32 transalation
        BAR2_BASE_ADDR    : std_logic_vector(31 downto 0) := X"03000000";
        -- BAR3 base address for PCIE->MI32 transalation
        BAR3_BASE_ADDR    : std_logic_vector(31 downto 0) := X"04000000";
        -- BAR4 base address for PCIE->MI32 transalation
        BAR4_BASE_ADDR    : std_logic_vector(31 downto 0) := X"05000000";
        -- BAR5 base address for PCIE->MI32 transalation
        BAR5_BASE_ADDR    : std_logic_vector(31 downto 0) := X"06000000";
        -- Expansion ROM base address for PCIE->MI32 transalation
        EXP_ROM_BASE_ADDR : std_logic_vector(31 downto 0) := X"0A000000";
        -- Enable Pipe component on CC interface
        CC_PIPE           : boolean := true;
        -- Enable Pipe component on CQ interface
        CQ_PIPE           : boolean := true;
        -- Enable Pipe component on MI32 interface
        MI_PIPE           : boolean := true;
        -- MI bus: width of data word in bits, must be 32.
        MI_DATA_WIDTH     : natural := 32;
        -- MI bus: width of address word in bits, must be 32.
        MI_ADDR_WIDTH     : natural := 32;
        -- Select correct FPGA device: "ULTRASCALE", "STRATIX10", "AGILEX"
        DEVICE            : string := "ULTRASCALE";
        -- Intel PCIe endpoint type:
        ENDPOINT_TYPE     : string := "USP"
    );
    port (
        -- Clock signal for the whole MTC module.
        -- Must be used clock from PCIe Hard IP!
        CLK                  : in  std_logic;
        -- Reset synchronized with CLK.
        RESET                : in  std_logic;

        -- =====================================================================
        -- Configuration Status Interface
        -- =====================================================================
        -- Maximum allowed size of completion payload: 000b = 128 bytes;
        -- 001b = 256 bytes; 010b = 512 bytes; 011b = 1024 bytes
        CTL_MAX_PAYLOAD_SIZE : in  std_logic_vector(2 downto 0);
        -- BAR aperture value (Intel FPGA only). Defines the size of the address
        -- space of BAR in the number of usable address bits.
        CTL_BAR_APERTURE     : in  std_logic_vector(5 downto 0);

        -- =====================================================================
        -- MFB Completer Request (CQ) Interface
        -- =====================================================================
        CQ_MFB_DATA          : in  std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
        CQ_MFB_META          : in  std_logic_vector(MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
        CQ_MFB_SOF           : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        CQ_MFB_EOF           : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        CQ_MFB_SOF_POS       : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        CQ_MFB_EOF_POS       : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        CQ_MFB_SRC_RDY       : in  std_logic;
        CQ_MFB_DST_RDY       : out std_logic;

        -- =====================================================================
        -- MFB Completer Completion (CC) Interface
        -- =====================================================================
        CC_MFB_DATA          : out std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
        CC_MFB_META          : out std_logic_vector(MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
        CC_MFB_SOF           : out std_logic_vector(MFB_REGIONS-1 downto 0);
        CC_MFB_EOF           : out std_logic_vector(MFB_REGIONS-1 downto 0);
        CC_MFB_SOF_POS       : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        CC_MFB_EOF_POS       : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        CC_MFB_SRC_RDY       : out std_logic;
        CC_MFB_DST_RDY       : in  std_logic;

        -- =====================================================================
        -- MI32 interface (master)
        -- =====================================================================
        -- MI bus: PCIe function number that generated the current MI request
        MI_FUNCTION          : out std_logic_vector(7 downto 0);
        -- MI bus: data from master to slave (write data)
        MI_DWR               : out std_logic_vector(31 downto 0);
        -- MI bus: slave address
        MI_ADDR              : out std_logic_vector(31 downto 0);
        -- MI bus: byte enable
        MI_BE                : out std_logic_vector(3 downto 0);
        -- MI bus: read request
        MI_RD                : out std_logic;
        -- MI bus: write request
        MI_WR                : out std_logic;
        -- MI bus: ready of slave module
        MI_ARDY              : in  std_logic;
        -- MI bus: data from slave to master (read data)
        MI_DRD               : in  std_logic_vector(31 downto 0);
        -- MI bus: valid of MI_DRD data signal
        MI_DRDY              : in  std_logic
    );
end entity;

architecture FULL of MTC is

    constant IS_XILINX_DEV   : boolean := DEVICE="ULTRASCALE" or DEVICE="7SERIES";
    constant IS_INTEL_DEV    : boolean := DEVICE="STRATIX10" or DEVICE="AGILEX";
    constant IS_MFB_META_DEV : boolean := (ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE") and IS_INTEL_DEV;
    constant RD_INDEX_BEGIN  : natural := tsel(IS_MFB_META_DEV,0,3);
    constant MFB_DATA_W      : natural := MFB_REGIONS*MFB_REGION_WIDTH;
    constant CQ_DATA_WIDTH   : natural := MFB_REGION_WIDTH;
    constant CC_DATA_WIDTH   : natural := MFB_DATA_W;
    constant MI_PER_CQ_WORD  : natural := CQ_DATA_WIDTH/MI_DATA_WIDTH;
    constant MI_PER_CC_WORD  : natural := CC_DATA_WIDTH/MI_DATA_WIDTH;
    constant DW_PER_CC_WORD  : natural := CC_DATA_WIDTH/32;
    constant CC_MAX_SIZE     : natural := 2**log2(4096+12); -- maximum MPS + HDR size
    constant CC_MAX_MI_WORDS : natural := CC_MAX_SIZE/(MI_DATA_WIDTH/8);
    constant CC_MEM_ITEMS    : natural := CC_MAX_SIZE/(CC_DATA_WIDTH/8);

    type mi_fsm_t is (st_idle, st_write, st_wait_for_data, st_read, st_wait_for_drdy, st_cc_done_mtu, st_error, st_ignore, st_cc_done_last);
    type cc_fsm_t is (st_idle, st_start_read, st_read, st_error, st_cc_done);

    signal reg_mps                   : unsigned(12 downto 0);
    signal reg_mps_mi                : unsigned(13-log2(MI_DATA_WIDTH/8)-1 downto 0);
    signal reg_mps_mask              : unsigned(12 downto 0);

    signal pi_cq_mfb_data            : std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
    signal pi_cq_mfb_meta            : std_logic_vector(MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
    signal pi_cq_mfb_sof             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pi_cq_mfb_eof             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pi_cq_mfb_sof_pos         : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal pi_cq_mfb_eof_pos         : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal pi_cq_mfb_src_rdy         : std_logic;
    signal pi_cq_mfb_dst_rdy         : std_logic;

    signal tr_cq_mfb_data            : std_logic_vector(CQ_DATA_WIDTH-1 downto 0);
    signal tr_cq_mfb_meta            : std_logic_vector(PCIE_CQ_META_WIDTH-1 downto 0);
    signal tr_cq_mfb_hdr             : std_logic_vector(128-1 downto 0);
    signal tr_cq_mfb_bar             : std_logic_vector(3-1 downto 0);
    signal tr_cq_mfb_fbe             : std_logic_vector(4-1 downto 0);
    signal tr_cq_mfb_lbe             : std_logic_vector(4-1 downto 0);
    signal tr_cq_mfb_tph_present     : std_logic;
    signal tr_cq_mfb_tph_type        : std_logic_vector(2-1 downto 0);
    signal tr_cq_mfb_tph_st_tag      : std_logic_vector(8-1 downto 0);
    signal tr_cq_mfb_sof             : std_logic;
    signal tr_cq_mfb_eof             : std_logic;
    signal tr_cq_mfb_src_rdy         : std_logic;
    signal tr_cq_mfb_dst_rdy         : std_logic;

    signal tr_cq_mfb_req_msg         : std_logic;
    signal tr_cq_mfb_wr              : std_logic;
    signal tr_cq_mfb_rd              : std_logic;
    signal tr_cq_index_begin         : unsigned(3-1 downto 0);

    signal cq_hdr_gen_dword_count    : std_logic_vector(11-1 downto 0);
    signal cq_hdr_gen_attr           : std_logic_vector(3-1 downto 0);
    signal cq_hdr_gen_tag            : std_logic_vector(10-1 downto 0);
    signal cq_hdr_gen_tc             : std_logic_vector(3-1 downto 0);
    signal cq_hdr_gen_req_type       : std_logic_vector(4-1 downto 0);
    signal cq_hdr_gen_fbe            : std_logic_vector(4-1 downto 0);
    signal cq_hdr_gen_lbe            : std_logic_vector(4-1 downto 0);
    signal cq_hdr_gen_req_id         : std_logic_vector(16-1 downto 0);
    signal cq_hdr_gen_addr           : std_logic_vector(64-1 downto 0);
    signal cq_hdr_gen_addr_type      : std_logic_vector(2-1 downto 0);
    signal cq_hdr_gen_hdr_type       : std_logic;
    signal cq_hdr_gen_target_func    : std_logic_vector(8-1 downto 0);
    signal cq_hdr_gen_bar_id         : std_logic_vector(3-1 downto 0);
    signal cq_hdr_gen_bar_aperture   : std_logic_vector(6-1 downto 0);

    signal cq_hdr_tag                : std_logic_vector(10-1 downto 0);
    signal cq_hdr_addr               : std_logic_vector(64-1 downto 0);
    signal cq_hdr_addr_type          : std_logic_vector(2-1 downto 0);
    signal cq_hdr_last_be            : std_logic_vector(4-1 downto 0);
    signal cq_hdr_first_be           : std_logic_vector(4-1 downto 0);
    signal cq_hdr_request_id         : std_logic_vector(16-1 downto 0);
    signal cq_hdr_tc                 : std_logic_vector(3-1 downto 0);
    signal cq_hdr_dword_count        : unsigned(11-1 downto 0);
    signal cq_hdr_attr               : std_logic_vector(3-1 downto 0);
    signal cq_meta_function_id       : std_logic_vector(8-1 downto 0);
    signal cq_meta_bar_id            : std_logic_vector(3-1 downto 0);
    signal cq_meta_bar_aperture      : std_logic_vector(6-1 downto 0);
    signal cq_meta_tph_present       : std_logic;
    signal cq_meta_tph_type          : std_logic_vector(1 downto 0);
    signal cq_meta_tph_st_tag        : std_logic_vector(7 downto 0);
    signal cq_wr_req                 : std_logic;
    signal cq_rd_req                 : std_logic;
    signal cq_ignore                 : std_logic;
    signal cq_data                   : std_logic_vector(CQ_DATA_WIDTH-1 downto 0);
    signal cq_data_index_begin       : unsigned(3-1 downto 0);
    signal cq_sot                    : std_logic;
    signal cq_eot                    : std_logic;
    signal cq_valid                  : std_logic;
    signal cq_ready                  : std_logic;

    signal cq_addr_translated        : std_logic_vector(64-1 downto 0);
    signal cq_first_ib               : std_logic_vector(2-1 downto 0);
    signal cq_laddr_init_low         : unsigned(2-1 downto 0);
    signal cq_laddr_init             : unsigned(7-1 downto 0);
    signal cq_byte_count             : std_logic_vector(13-1 downto 0);

    signal reg1_cq_hdr_tag           : std_logic_vector(10-1 downto 0);
    signal reg1_cq_hdr_addr_type     : std_logic_vector(2-1 downto 0);
    signal reg1_cq_hdr_last_be       : std_logic_vector(4-1 downto 0);
    signal reg1_cq_hdr_first_be      : std_logic_vector(4-1 downto 0);
    signal reg1_cq_first_ib          : unsigned(2-1 downto 0);
    signal reg1_cq_hdr_request_id    : std_logic_vector(16-1 downto 0);
    signal reg1_cq_hdr_tc            : std_logic_vector(3-1 downto 0);
    signal reg1_cq_hdr_dword_count   : unsigned(10-1 downto 0);
    signal reg1_cq_hdr_attr          : std_logic_vector(3-1 downto 0);
    signal reg1_cq_meta_function_id  : std_logic_vector(8-1 downto 0);
    signal reg1_cq_meta_tph_present  : std_logic;
    signal reg1_cq_meta_tph_type     : std_logic_vector(1 downto 0);
    signal reg1_cq_meta_tph_st_tag   : std_logic_vector(7 downto 0);
    signal reg1_cq_wr_req            : std_logic;
    signal reg1_cq_rd_req            : std_logic;
    signal reg1_cq_data              : std_logic_vector(CQ_DATA_WIDTH-1 downto 0);
    signal reg1_cq_data_index_begin  : unsigned(3-1 downto 0);
    signal reg1_cq_byte_count        : unsigned(13-1 downto 0);
    signal reg1_cq_addr_translated   : unsigned(64-1 downto 0);
    signal reg1_cq_laddr_init        : unsigned(7-1 downto 0);
    signal reg1_cq_sot               : std_logic;
    signal reg1_cq_eot               : std_logic;
    signal reg1_cq_valid             : std_logic;

    signal drdy_status               : unsigned(11-1 downto 0);
    signal wr_index_rst              : std_logic;
    signal wr_index_inc              : std_logic;
    signal wr_index                  : unsigned(log2(MI_PER_CQ_WORD)-1 downto 0);
    signal wr_index_max              : std_logic;
    signal mi_index_rst              : std_logic;
    signal mi_index_inc              : std_logic;
    signal mi_index                  : unsigned(11-1 downto 0);
    signal mi_index_bytes            : unsigned(11+log2(MI_DATA_WIDTH/8)-1 downto 0);
    signal mi_index_mtu_mask         : unsigned(11-1 downto 0);
    signal mi_index_mtu              : unsigned(11-1 downto 0);
    signal first_dword               : std_logic;
    signal last_dword                : std_logic;
    signal mi_index_is_mtu           : std_logic;

    signal mi_fsm_pst                : mi_fsm_t;
    signal mi_fsm_nst                : mi_fsm_t;
    signal last_mi_word_reg          : std_logic;
    signal last_mi_word              : std_logic;
    signal cc_request                : std_logic;

    -- interconnection of MI master logic and MI pipe
    signal mi_function_out           : std_logic_vector(8-1 downto 0);
    signal mi_dwr_out                : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal mi_addr_out               : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    signal mi_be_out                 : std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
    signal mi_rd_out                 : std_logic;
    signal mi_wr_out                 : std_logic;
    signal mi_drd_out                : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal mi_ardy_out               : std_logic;
    signal mi_drdy_out               : std_logic;
    signal mi_addrfn_out             : std_logic_vector(MI_ADDR_WIDTH+8-1 downto 0);
    signal mi_addrfn                 : std_logic_vector(MI_ADDR_WIDTH+8-1 downto 0);

    signal cc_dwords                 : unsigned(11-1 downto 0);
    signal cc_dwords_reg             : unsigned(11-1 downto 0);
    signal cc_byte_send              : unsigned(13-1 downto 0);
    signal cc_byte_send_reg          : unsigned(13-1 downto 0);
    signal cc_first_resp             : std_logic;
    signal cc_first_resp_reg         : std_logic;
    signal rd_index_rst              : std_logic;
    signal rd_index                  : unsigned(log2(CC_MAX_MI_WORDS)-1 downto 0);
    signal rd_index_round_up         : unsigned(log2(CC_MAX_MI_WORDS)-1 downto 0);
    signal rd_index_word             : unsigned(log2(CC_MAX_MI_WORDS)-log2(MI_PER_CC_WORD)-1 downto 0);
    signal rd_index_pos              : unsigned(log2(DW_PER_CC_WORD)-1 downto 0);
    signal cc_mem_wr_be_sel          : unsigned(log2(CC_DATA_WIDTH/8)-1 downto 0);
    signal cc_mem_wr_be_ini          : unsigned((CC_DATA_WIDTH/8)-1 downto 0);
    signal cc_mem_wr_be              : unsigned((CC_DATA_WIDTH/8)-1 downto 0);
    signal cc_mem_wr_addr            : unsigned(log2(CC_MEM_ITEMS)-1 downto 0);
    signal cc_mem_wr                 : std_logic;
    signal cc_mem_wr_data            : std_logic_vector(CC_DATA_WIDTH-1 downto 0);

    signal cc_mem_rd                 : std_logic;
    signal cc_mem_rd_addr            : unsigned(log2(CC_MEM_ITEMS)-1 downto 0);
    signal cc_mem_rd_addr_rst        : std_logic;
    signal cc_mem_rd_data            : std_logic_vector(CC_DATA_WIDTH-1 downto 0);
    signal cc_mem_rd_done            : std_logic;
    signal cc_mem_rd_first           : std_logic;

    signal cc_low_addr               : unsigned(7-1 downto 0);
    signal cc_low_addr_reg           : unsigned(7-1 downto 0);
    signal cc_byte_count             : unsigned(13-1 downto 0);
    signal cc_hdr                    : std_logic_vector(96-1 downto 0);
    signal cc_xilinx_error           : std_logic_vector(32-1 downto 0);
    signal cc_fsm_pst                : cc_fsm_t;
    signal cc_fsm_nst                : cc_fsm_t;
    signal cc_done                   : std_logic;
    signal cc_data                   : std_logic_vector(CC_DATA_WIDTH-1 downto 0);
    signal cc_valid                  : std_logic;
    signal cc_ready                  : std_logic;
    signal cc_sot                    : std_logic;
    signal cc_eot                    : std_logic;
    signal cc_eot_pos                : unsigned(log2(DW_PER_CC_WORD)-1 downto 0);
    signal cc_status                 : std_logic_vector(3-1 downto 0);

    signal mfb_sof                   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_eof                   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_eof_pos_arr           : slv_array_t(MFB_REGIONS-1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal mfb_meta_arr              : slv_array_t(MFB_REGIONS-1 downto 0)(PCIE_CC_META_WIDTH-1 downto 0) := (others => (others => '0'));

    -- attribute mark_debug               : string;
    -- attribute mark_debug of cc_fsm_pst : signal is "true";
begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "MTC: unsupported DEVICE!" severity failure;

    assert (ENDPOINT_TYPE = "H_TILE" OR ENDPOINT_TYPE = "P_TILE" OR ENDPOINT_TYPE = "R_TILE" OR IS_INTEL_DEV = False)
        report "MTC: unsupported ENDPOINT_TYPE (Intel FPGA only)!" severity failure;

    -- =========================================================================
    --  CONFIGURATION LOGIC AND REGISTERS
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            case CTL_MAX_PAYLOAD_SIZE is
                when "001"  =>
                    reg_mps      <= to_unsigned(256,reg_mps'length);
                    reg_mps_mask <= to_unsigned(255,reg_mps'length);
                when "010"  =>
                    reg_mps      <= to_unsigned(512,reg_mps'length);
                    reg_mps_mask <= to_unsigned(511,reg_mps'length);
                when "011"  =>
                    reg_mps      <= to_unsigned(1024,reg_mps'length);
                    reg_mps_mask <= to_unsigned(1023,reg_mps'length);
                when "100"  =>
                    reg_mps      <= to_unsigned(2048,reg_mps'length);
                    reg_mps_mask <= to_unsigned(2047,reg_mps'length);
                when "101"  =>
                    reg_mps      <= to_unsigned(4096,reg_mps'length);
                    reg_mps_mask <= to_unsigned(4095,reg_mps'length);
                when others =>
                    reg_mps      <= to_unsigned(128,reg_mps'length);
                    reg_mps_mask <= to_unsigned(127,reg_mps'length);
            end case;
        end if;
    end process;

    -- conversion to mi words
    reg_mps_mi <= enlarge_right(reg_mps,-log2(MI_DATA_WIDTH/8));

    --  CQ MFB parser logic
    cq_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => PCIE_CQ_META_WIDTH,
        FAKE_PIPE   => not CQ_PIPE,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => CQ_MFB_DATA,
        RX_META    => CQ_MFB_META,
        RX_SOF_POS => CQ_MFB_SOF_POS,
        RX_EOF_POS => CQ_MFB_EOF_POS,
        RX_SOF     => CQ_MFB_SOF,
        RX_EOF     => CQ_MFB_EOF,
        RX_SRC_RDY => CQ_MFB_SRC_RDY,
        RX_DST_RDY => CQ_MFB_DST_RDY,

        TX_DATA    => pi_cq_mfb_data,
        TX_META    => pi_cq_mfb_meta,
        TX_SOF_POS => pi_cq_mfb_sof_pos,
        TX_EOF_POS => pi_cq_mfb_eof_pos,
        TX_SOF     => pi_cq_mfb_sof,
        TX_EOF     => pi_cq_mfb_eof,
        TX_SRC_RDY => pi_cq_mfb_src_rdy,
        TX_DST_RDY => pi_cq_mfb_dst_rdy
    );

    mfb_transformer_i : entity work.MFB_TRANSFORMER
    generic map(
        RX_REGIONS  => MFB_REGIONS,
        TX_REGIONS  => 1,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => PCIE_CQ_META_WIDTH
    )
    port map(
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => pi_cq_mfb_data,
        RX_META     => pi_cq_mfb_meta,
        RX_SOP      => pi_cq_mfb_sof,
        RX_EOP      => pi_cq_mfb_eof,
        RX_SOP_POS  => pi_cq_mfb_sof_pos,
        RX_EOP_POS  => pi_cq_mfb_eof_pos,
        RX_SRC_RDY  => pi_cq_mfb_src_rdy,
        RX_DST_RDY  => pi_cq_mfb_dst_rdy,

        TX_DATA     => tr_cq_mfb_data,
        TX_META     => tr_cq_mfb_meta,
        TX_SOP(0)   => tr_cq_mfb_sof,
        TX_EOP(0)   => tr_cq_mfb_eof,
        TX_SOP_POS  => open,
        TX_EOP_POS  => open,
        TX_SRC_RDY  => tr_cq_mfb_src_rdy,
        TX_DST_RDY  => tr_cq_mfb_dst_rdy
    );

    tr_cq_mfb_dst_rdy <= cq_ready;

    tr_cq_mfb_bar         <= tr_cq_mfb_meta(PCIE_CQ_META_BAR);
    tr_cq_mfb_fbe         <= tr_cq_mfb_meta(PCIE_CQ_META_FBE);
    tr_cq_mfb_lbe         <= tr_cq_mfb_meta(PCIE_CQ_META_LBE);
    tr_cq_mfb_tph_present <= tr_cq_mfb_meta(PCIE_CQ_META_TPH_PRESENT_O);
    tr_cq_mfb_tph_type    <= tr_cq_mfb_meta(PCIE_CQ_META_TPH_TYPE);
    tr_cq_mfb_tph_st_tag  <= tr_cq_mfb_meta(PCIE_CQ_META_TPH_ST_TAG);

    tr_cq_mfb_hdr_g : if IS_MFB_META_DEV generate
        tr_cq_mfb_hdr <= tr_cq_mfb_meta(PCIE_CQ_META_HEADER);
    else generate
        tr_cq_mfb_hdr <= tr_cq_mfb_data(128-1 downto 0);
    end generate;

    pcie_cq_hdr_gen_i : entity work.PCIE_CQ_HDR_DEPARSER
    generic map(
        DEVICE => DEVICE
    )
    port map(
        OUT_DW_CNT        => cq_hdr_gen_dword_count,
        OUT_ATTRIBUTES    => cq_hdr_gen_attr,
        OUT_TAG           => cq_hdr_gen_tag,
        OUT_TC            => cq_hdr_gen_tc,
        OUT_REQ_TYPE      => cq_hdr_gen_req_type,
        OUT_FBE           => cq_hdr_gen_fbe,
        OUT_LBE           => cq_hdr_gen_lbe,
        OUT_REQ_ID        => cq_hdr_gen_req_id,
        OUT_ADDRESS       => cq_hdr_gen_addr,
        OUT_ADDRESS_TYPE  => cq_hdr_gen_addr_type,
        OUT_ADDR_LEN      => cq_hdr_gen_hdr_type,
        OUT_TARGET_FUNC   => cq_hdr_gen_target_func,
        OUT_BAR_ID        => cq_hdr_gen_bar_id,
        OUT_BAR_APERTURE  => cq_hdr_gen_bar_aperture,

        IN_HEADER        => tr_cq_mfb_hdr,
        IN_FBE           => tr_cq_mfb_fbe,
        IN_LBE           => tr_cq_mfb_lbe,
        IN_INTEL_META    => CTL_BAR_APERTURE & tr_cq_mfb_bar & "00000000"
    );

    tr_cq_mfb_rd      <= cq_hdr_gen_req_type(0);
    tr_cq_mfb_wr      <= cq_hdr_gen_req_type(1);
    tr_cq_mfb_req_msg <= cq_hdr_gen_req_type(2) or cq_hdr_gen_req_type(3);

    tr_cq_index_begin_p : process (all)
    begin
        if (IS_MFB_META_DEV) then -- header is not in DATA signal
            tr_cq_index_begin <= to_unsigned(0,3);
        else -- H-Tile - 3 or 4 dword header
            if (cq_hdr_gen_hdr_type = '1') then
                tr_cq_index_begin <= to_unsigned(4,3);
            else
                tr_cq_index_begin <= to_unsigned(3,3);
            end if;
        end if;
    end process;

    process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (cq_ready = '1' and tr_cq_mfb_src_rdy = '1') then
                if (tr_cq_mfb_sof = '1') then
                    cq_hdr_tag           <= cq_hdr_gen_tag;
                    cq_hdr_addr_type     <= cq_hdr_gen_addr_type;
                    cq_hdr_addr          <= cq_hdr_gen_addr;
                    cq_hdr_first_be      <= cq_hdr_gen_fbe;
                    cq_hdr_last_be       <= cq_hdr_gen_lbe;
                    cq_hdr_request_id    <= cq_hdr_gen_req_id;
                    cq_hdr_tc            <= cq_hdr_gen_tc;
                    cq_hdr_dword_count   <= unsigned(cq_hdr_gen_dword_count);
                    cq_hdr_attr          <= cq_hdr_gen_attr;
                    cq_meta_function_id  <= cq_hdr_gen_target_func;
                    cq_meta_bar_id       <= cq_hdr_gen_bar_id;
                    cq_meta_bar_aperture <= cq_hdr_gen_bar_aperture;
                    cq_data_index_begin  <= tr_cq_index_begin;
                    cq_meta_tph_present  <= tr_cq_mfb_tph_present;
                    cq_meta_tph_type     <= tr_cq_mfb_tph_type;
                    cq_meta_tph_st_tag   <= tr_cq_mfb_tph_st_tag;
                end if;
                cq_data   <= tr_cq_mfb_data;
                cq_wr_req <= tr_cq_mfb_wr;
                cq_rd_req <= tr_cq_mfb_rd;
                cq_ignore <= tr_cq_mfb_req_msg;
                cq_sot    <= tr_cq_mfb_sof;
                cq_eot    <= tr_cq_mfb_eof;
            end if;
        end if;
    end process;

    process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                cq_valid <= '0';
            elsif (cq_ready = '1') then
                cq_valid <= tr_cq_mfb_src_rdy;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  SECOND STAGE - PREPARE METADATA FROM CQ REQUEST
    -- =========================================================================

    -- CQ address translation
    addr_trans_i : entity work.PCIE_BAR_ADDR_TRANSLATOR
    generic map(
        BAR0_BASE_ADDR    => BAR0_BASE_ADDR,
        BAR1_BASE_ADDR    => BAR1_BASE_ADDR,
        BAR2_BASE_ADDR    => BAR2_BASE_ADDR,
        BAR3_BASE_ADDR    => BAR3_BASE_ADDR,
        BAR4_BASE_ADDR    => BAR4_BASE_ADDR,
        BAR5_BASE_ADDR    => BAR5_BASE_ADDR,
        EXP_ROM_BASE_ADDR => EXP_ROM_BASE_ADDR
    )
    port map(
        CLK             => CLK,
        RESET           => RESET,
        IN_BAR_APERTURE => cq_meta_bar_aperture,
        IN_BAR_ID       => cq_meta_bar_id,
        IN_ADDR         => cq_hdr_addr,
        OUT_ADDR        => cq_addr_translated
    );

    -- computation of invalid bytes and byte count
    byte_count_i : entity work.PCIE_BYTE_COUNT
    port map(
        CLK            => CLK,
        RESET          => RESET,
        IN_DW_COUNT    => std_logic_vector(cq_hdr_dword_count),
        IN_FIRST_BE    => cq_hdr_first_be,
        IN_LAST_BE     => cq_hdr_last_be,
        OUT_FIRST_IB   => cq_first_ib,
        OUT_LAST_IB    => open,
        OUT_BYTE_COUNT => cq_byte_count
    );

    -- computation of two LSB bits of lower address
    process (cq_hdr_first_be)
    begin
        cq_laddr_init_low <= (others => '0');
        for i in 0 to 4-1 loop
            if (cq_hdr_first_be(i) = '1') then
                cq_laddr_init_low <= to_unsigned(i,2);
                exit;
            end if;
        end loop;
    end process;

    -- initial address of the first completion data
    cq_laddr_init <= unsigned(cq_hdr_addr(6 downto 2)) & cq_laddr_init_low;

    -- second stage registers without reset
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (cq_ready = '1' and cq_valid = '1') then
                if (cq_sot = '1') then
                    reg1_cq_hdr_tag           <= cq_hdr_tag;
                    reg1_cq_hdr_addr_type     <= cq_hdr_addr_type;
                    reg1_cq_hdr_first_be      <= cq_hdr_first_be;
                    reg1_cq_first_ib          <= unsigned(cq_first_ib);
                    reg1_cq_hdr_last_be       <= cq_hdr_last_be;
                    reg1_cq_hdr_request_id    <= cq_hdr_request_id;
                    reg1_cq_hdr_tc            <= cq_hdr_tc;
                    reg1_cq_hdr_dword_count   <= cq_hdr_dword_count(10-1 downto 0);
                    reg1_cq_hdr_attr          <= cq_hdr_attr;
                    reg1_cq_meta_function_id  <= cq_meta_function_id;
                    reg1_cq_data_index_begin  <= cq_data_index_begin;
                    reg1_cq_addr_translated   <= unsigned(cq_addr_translated);
                    reg1_cq_laddr_init        <= cq_laddr_init;
                    reg1_cq_byte_count        <= unsigned(cq_byte_count);
                    reg1_cq_rd_req            <= cq_rd_req;
                    reg1_cq_wr_req            <= cq_wr_req;
                    reg1_cq_meta_tph_present  <= cq_meta_tph_present;
                    reg1_cq_meta_tph_type     <= cq_meta_tph_type;
                    reg1_cq_meta_tph_st_tag   <= cq_meta_tph_st_tag;
                end if;
                reg1_cq_data <= cq_data;
                reg1_cq_sot  <= cq_sot;
                reg1_cq_eot  <= cq_eot;
            end if;
        end if;
    end process;

    -- second stage registers with reset
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                reg1_cq_valid <= '0';
            elsif (cq_ready = '1') then
                reg1_cq_valid <= cq_valid;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  THIRD STAGE - MI MASTER LOGIC
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                drdy_status <= (others => '0');
            elsif (mi_rd_out = '1' and mi_ardy_out = '1' and mi_drdy_out = '0') then
                drdy_status <= drdy_status + 1;
            elsif ((mi_rd_out = '0' or mi_ardy_out = '0') and mi_drdy_out = '1') then
                drdy_status <= drdy_status - 1;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (wr_index_rst = '1') then
                wr_index <= resize(cq_data_index_begin,wr_index'length);
            elsif (wr_index_inc = '1') then
                wr_index <= wr_index + 1;
            end if;
        end if;
    end process;

    wr_index_max <= '1' when (wr_index = (MI_PER_CQ_WORD-1)) else '0';

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (mi_index_rst = '1') then
                mi_index <= (others => '0');
            elsif (mi_index_inc = '1') then
                mi_index <= mi_index + 1;
            end if;
        end if;
    end process;

    mi_index_bytes    <= enlarge_right(mi_index,log2(MI_DATA_WIDTH/8));
    mi_index_mtu_mask <= enlarge_right(reg_mps_mask,-log2(MI_DATA_WIDTH/8));
    mi_index_mtu      <= mi_index and mi_index_mtu_mask;

    first_dword     <= '1' when (mi_index = 0) else '0';
    last_dword      <= '1' when (mi_index = (reg1_cq_hdr_dword_count-1)) else '0';
    mi_index_is_mtu <= '1' when (mi_index_mtu = (reg_mps_mi-1)) else '0';

    mi_function_out <= reg1_cq_meta_function_id;
    mi_addr_out     <= std_logic_vector(reg1_cq_addr_translated(MI_ADDR_WIDTH-1 downto 0) + mi_index_bytes);
    mi_dwr_out      <= reg1_cq_data((to_integer(wr_index)+1)*MI_DATA_WIDTH-1 downto to_integer(wr_index)*MI_DATA_WIDTH);

    -- -------------------------------------------------------------------------
    --  MI MASTER FSM LOGIC
    -- -------------------------------------------------------------------------

    mi_fsm_pst_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            mi_fsm_pst       <= mi_fsm_nst;
            last_mi_word_reg <= last_mi_word;
            cc_dwords_reg    <= cc_dwords;
            cc_low_addr_reg  <= cc_low_addr;
            cc_byte_send_reg <= cc_byte_send;
            cc_first_resp_reg <= cc_first_resp;
            if (RESET = '1') then
                mi_fsm_pst <= st_idle;
            end if;
        end if;
    end process;

    mi_fsm_logic_p : process (all)
    begin
        mi_fsm_nst <= mi_fsm_pst;
        last_mi_word <= last_mi_word_reg;
        cq_ready   <= '0';
        cc_request <= '0';
        cc_dwords <= cc_dwords_reg;
        cc_low_addr  <= cc_low_addr_reg;
        cc_byte_send <= cc_byte_send_reg;
        cc_byte_count <= reg1_cq_byte_count - cc_byte_send_reg;
        cc_first_resp <= cc_first_resp_reg;

        wr_index_rst <= '0';
        wr_index_inc <= '0';
        rd_index_rst <= '0';
        mi_index_rst <= '0';
        mi_index_inc <= '0';

        mi_wr_out <= '0';
        mi_rd_out <= '0';
        mi_be_out <= (others => '1');

        case (mi_fsm_pst) is
            when st_idle =>
                cq_ready <= '1';
                wr_index_rst <= '1';
                rd_index_rst <= '1';
                mi_index_rst <= '1';
                cc_first_resp <= '1';
                cc_byte_send <= (others => '0');
                cc_dwords <= to_unsigned(1,cc_dwords'length);
                if (cq_valid = '1' and cq_sot = '1') then
                    if (cq_rd_req = '1') then
                        mi_fsm_nst <= st_read;
                    elsif (cq_wr_req = '1') then
                        mi_fsm_nst <= st_write;
                    else
                        if (cq_ignore = '1') then
                            mi_fsm_nst <= st_ignore;
                        else
                            mi_fsm_nst <= st_error;
                        end if;
                    end if;
                end if;

            when st_write =>
                mi_wr_out <= '1';
                if (first_dword = '1') then
                    mi_be_out <= reg1_cq_hdr_first_be;
                elsif (last_dword = '1') then
                    mi_be_out <= reg1_cq_hdr_last_be;
                end if;
                if (mi_ardy_out = '1') then
                    wr_index_inc <= '1';
                    mi_index_inc <= '1';
                    if (last_dword = '1') then
                        mi_fsm_nst <= st_idle;
                    elsif (wr_index_max = '1') then
                        cq_ready <= '1';
                        if (cq_valid = '0') then
                            mi_fsm_nst <= st_wait_for_data;
                        end if;
                    end if;
                end if;

            when st_wait_for_data =>
                cq_ready <= '1';
                if (cq_valid = '1') then
                    mi_fsm_nst <= st_write;
                end if;

            when st_read =>
                mi_rd_out <= '1';
                if (first_dword = '1') then
                    mi_be_out <= reg1_cq_hdr_first_be;
                elsif (last_dword = '1') then
                    mi_be_out <= reg1_cq_hdr_last_be;
                end if;
                if (mi_ardy_out = '1') then
                    mi_index_inc <= '1';
                    if (last_dword = '1' or mi_index_is_mtu = '1') then
                        last_mi_word <= last_dword;
                        cc_low_addr <= resize((reg1_cq_laddr_init + cc_byte_send_reg),7);
                        cc_dwords <= resize(enlarge_right(mi_index_mtu,log2(MI_DATA_WIDTH/32)),11)+1;
                        mi_fsm_nst <= st_wait_for_drdy;
                    end if;
                end if;

            when st_wait_for_drdy =>
                if (drdy_status = 0) then
                    cc_request <= '1';
                    if (last_mi_word_reg = '1') then
                        mi_fsm_nst <= st_cc_done_last;
                    else
                        mi_fsm_nst <= st_cc_done_mtu;
                    end if;
                end if;

            when st_cc_done_mtu =>
                last_mi_word <= '0';
                if (cc_done = '1') then
                    rd_index_rst <= '1';
                    cc_first_resp <= '0';
                    if (cc_first_resp_reg = '1') then
                        cc_byte_send <= cc_byte_send_reg + reg_mps - reg1_cq_first_ib;
                    else
                        cc_byte_send <= cc_byte_send_reg + reg_mps;
                    end if;
                    mi_fsm_nst <= st_read;
                end if;

            when st_error =>
                cc_low_addr <= (others => '0');
                cc_byte_count <= to_unsigned(1,cc_byte_count'length);
                if (IS_XILINX_DEV) then
                    cc_dwords <= to_unsigned(0,cc_dwords'length);
                end if;
                if (reg1_cq_valid = '1' and reg1_cq_eot = '1') then
                    cc_request <= '1';
                    mi_fsm_nst <= st_cc_done_last;
                else
                    cq_ready <= '1';
                end if;

            when st_ignore =>
                if (reg1_cq_valid = '1' and reg1_cq_eot = '1') then
                    mi_fsm_nst <= st_idle;
                else
                    cq_ready <= '1';
                end if;

            when st_cc_done_last =>
                if (cc_done = '1') then
                    mi_fsm_nst <= st_idle;
                end if;
        end case;
    end process;

    -- =========================================================================
    --  PIPE OF MI INTERFACE
    -- =========================================================================

    mi_addrfn_out <= mi_function_out & mi_addr_out;

    mi_pipe_i : entity work.MI_PIPE
    generic map(
        USE_OUTREG => True,
        FAKE_PIPE  => not MI_PIPE,
        DATA_WIDTH => MI_DATA_WIDTH,
        ADDR_WIDTH => MI_ADDR_WIDTH + 8,
        DEVICE     => DEVICE
    )
    port map(
        CLK      => CLK,
        RESET    => RESET,

        IN_DWR   => mi_dwr_out,
        IN_ADDR  => mi_addrfn_out,
        IN_BE    => mi_be_out,
        IN_RD    => mi_rd_out,
        IN_WR    => mi_wr_out,
        IN_DRD   => mi_drd_out,
        IN_ARDY  => mi_ardy_out,
        IN_DRDY  => mi_drdy_out,

        OUT_DWR  => MI_DWR,
        OUT_ADDR => mi_addrfn,
        OUT_BE   => MI_BE,
        OUT_RD   => MI_RD,
        OUT_WR   => MI_WR,
        OUT_DRD  => MI_DRD,
        OUT_ARDY => MI_ARDY,
        OUT_DRDY => MI_DRDY
    );

    MI_ADDR     <= mi_addrfn(MI_ADDR_WIDTH-1 downto 0);
    MI_FUNCTION <= mi_addrfn(mi_addrfn'length-1 downto MI_ADDR_WIDTH);

    -- =========================================================================
    --  FOURTH STAGE - CC RESPONSE LOGIC
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (rd_index_rst = '1') then
                rd_index <= to_unsigned(RD_INDEX_BEGIN,rd_index'length);
            elsif (MI_DRDY = '1') then
                rd_index <= rd_index + 1;
            end if;
        end if;
    end process;

    rd_index_round_up <= round_up(rd_index,log2(MI_PER_CC_WORD));
    rd_index_word     <= rd_index_round_up(rd_index'length-1 downto log2(MI_PER_CC_WORD));
    rd_index_pos      <= rd_index(log2(DW_PER_CC_WORD)-1 downto 0) - 1;

    -- -------------------------------------------------------------------------
    --  CC DATA MEMORY WITH BYTE ENABLES
    -- -------------------------------------------------------------------------

    cc_mem_wr_be_sel <= rd_index(log2(MI_PER_CC_WORD)-1 downto 0) & to_unsigned(0,log2(MI_DATA_WIDTH/8));
    cc_mem_wr_be_ini <= to_unsigned((2**(MI_DATA_WIDTH/8)-1),(CC_DATA_WIDTH/8));
    cc_mem_wr_be     <= shift_left(cc_mem_wr_be_ini, to_integer(cc_mem_wr_be_sel));

    cc_mem_wr_addr <= rd_index(rd_index'length-1 downto log2(MI_PER_CC_WORD));
    cc_mem_wr      <= MI_DRDY;

    cc_mem_wr_data_g : for i in 0 to MI_PER_CC_WORD-1 generate
        cc_mem_wr_data((i+1)*MI_DATA_WIDTH-1 downto i*MI_DATA_WIDTH) <= MI_DRD;
    end generate;

    cc_mem_i : entity work.SDP_BRAM
    generic map(
        DATA_WIDTH   => CC_DATA_WIDTH,
        ITEMS        => CC_MEM_ITEMS,
        BLOCK_ENABLE => True,
        BLOCK_WIDTH  => 8,
        COMMON_CLOCK => True,
        OUTPUT_REG   => False,
        DEVICE       => DEVICE
    )
    port map(
        WR_CLK      => CLK,
        WR_RST      => RESET,
        WR_EN       => cc_mem_wr,
        WR_BE       => std_logic_vector(cc_mem_wr_be),
        WR_ADDR     => std_logic_vector(cc_mem_wr_addr),
        WR_DATA     => cc_mem_wr_data,

        RD_CLK      => CLK,
        RD_RST      => RESET,
        RD_EN       => '1',
        RD_PIPE_EN  => cc_mem_rd,
        RD_ADDR     => std_logic_vector(cc_mem_rd_addr),
        RD_DATA     => cc_mem_rd_data,
        RD_DATA_VLD => open
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (cc_mem_rd_addr_rst = '1') then
                cc_mem_rd_addr <= (others => '0');
            elsif (cc_mem_rd = '1') then
                cc_mem_rd_addr <= cc_mem_rd_addr + 1;
            end if;
        end if;
    end process;

    cc_mem_rd_done  <= '1' when (cc_mem_rd_addr = rd_index_word) else '0';
    cc_mem_rd_first <= '1' when (cc_mem_rd_addr = 1) else '0';

    -- -------------------------------------------------------------------------
    --  CC HEADER TEMPLATE
    -- -------------------------------------------------------------------------

    pcie_cc_hdr_gen_i : entity work.PCIE_CC_HDR_GEN
    generic map(
        DEVICE => DEVICE
    )
    port map(

        IN_LOWER_ADDR   => std_logic_vector(cc_low_addr_reg),
        IN_ADDRESS_TYPE => reg1_cq_hdr_addr_type,
        IN_BYTE_CNT     => std_logic_vector(cc_byte_count),
        IN_DW_CNT       => std_logic_vector(cc_dwords_reg),
        IN_COMP_ST      => cc_status,
        IN_REQ_ID       => reg1_cq_hdr_request_id,
        IN_TAG          => reg1_cq_hdr_tag,
        IN_META_FUNC_ID => reg1_cq_meta_function_id,
        IN_BUS_NUM      => "00000000",
        IN_TC           => reg1_cq_hdr_tc,
        IN_ATTRIBUTES   => reg1_cq_hdr_attr,
        COMP_WITH_DATA  => '1',
        OUT_HEADER      => cc_hdr
    );

    cc_hdr_xilinx_g: if IS_XILINX_DEV generate
        cc_xilinx_error <=
            "00000000"               & -- RESERVED
            reg1_cq_meta_tph_st_tag  & -- tph_st_tag
            "00000"                  & -- RESERVED
            reg1_cq_meta_tph_type    & -- tph_type
            reg1_cq_meta_tph_present & -- tph_present
            reg1_cq_hdr_last_be      & -- last_be
            reg1_cq_hdr_first_be;      -- first_be
    end generate;

    -- -------------------------------------------------------------------------
    --  CC FSM LOGIC
    -- -------------------------------------------------------------------------

    cc_fsm_pst_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            cc_fsm_pst <= cc_fsm_nst;
            if (RESET = '1') then
                cc_fsm_pst <= st_idle;
            end if;
        end if;
    end process;

    cc_fsm_logic_p : process (all)
    begin
        cc_fsm_nst <= cc_fsm_pst;
        cc_done  <= '0';

        cc_data  <= cc_mem_rd_data;
        cc_valid <= '0';
        cc_sot   <= '0';
        cc_eot   <= '0';
        cc_eot_pos <= rd_index_pos;

        cc_status <= "000"; -- completion status (successful completion)

        cc_mem_rd <= '0';
        cc_mem_rd_addr_rst <= '0';

        case (cc_fsm_pst) is
            when st_idle =>
                cc_mem_rd_addr_rst <= '1';
                if (cc_request = '1') then
                    if (reg1_cq_rd_req = '1') then
                        cc_fsm_nst <= st_start_read;
                    elsif (reg1_cq_wr_req = '0') then
                        cc_fsm_nst <= st_error;
                    end if;
                end if;

            when st_start_read =>
                cc_mem_rd <= '1';
                cc_fsm_nst <= st_read;

            when st_read =>
                cc_mem_rd <= cc_ready;
                cc_valid <= '1';
                if (cc_mem_rd_first = '1') then
                    cc_sot <= '1';
                    if (IS_MFB_META_DEV = False) then
                        cc_data(96-1 downto 0) <= cc_hdr;
                    end if;
                end if;
                if (cc_mem_rd_done = '1') then
                    cc_eot <= '1';
                    if (cc_ready = '1') then
                        cc_fsm_nst <= st_cc_done;
                    end if;
                end if;

            when st_error =>
                cc_valid <= '1';
                cc_sot   <= '1';
                cc_eot   <= '1';
                if (IS_XILINX_DEV = True) then
                    cc_eot_pos <= to_unsigned(7,cc_eot_pos'length);
                    cc_data <= (others => '0');
                    cc_data(128-1 downto 96) <= cc_xilinx_error;
                else
                    cc_eot_pos <= to_unsigned(2,cc_eot_pos'length);
                end if;
                cc_status <= "001"; -- completion status (unsupported request)
                if (IS_MFB_META_DEV = False) then
                    cc_data(96-1 downto 0) <= cc_hdr;
                end if;
                if (cc_ready = '1') then
                    cc_fsm_nst <= st_cc_done;
                end if;

            when st_cc_done =>
                cc_done <= '1';
                cc_fsm_nst <= st_idle;
        end case;
    end process;

    -- =========================================================================
    --  OUTPUT STAGE - CONVERSION CC INTERFACE TO MFB
    -- =========================================================================

    cc_sot_fill_g: if (MFB_REGIONS = 1) generate
        mfb_sof(0) <= cc_sot;
    else generate
        mfb_sof <= (MFB_REGIONS-1 downto 1 => '0') & cc_sot;
    end generate;

    process (cc_eot, cc_eot_pos)
    begin
        mfb_eof <= (others => '0');
        if (MFB_REGIONS = 1) then
            mfb_eof(0) <= cc_eot;
        else
            for i in 0 to MFB_REGIONS-1 loop
                if (cc_eot_pos(log2(DW_PER_CC_WORD)-1 downto log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) = i) then
                    mfb_eof(i) <= cc_eot;
                end if;
            end loop;
        end if;
    end process;

    mfb_eof_pos_arr_g: for i in 0 to MFB_REGIONS-1 generate
        mfb_eof_pos_arr(i) <= std_logic_vector(cc_eot_pos(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0));
    end generate;

    mfb_meta_arr(0)(PCIE_CC_META_HEADER) <= cc_hdr;

    cc_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => PCIE_CC_META_WIDTH,
        FAKE_PIPE   => not CC_PIPE,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => cc_data,
        RX_META    => slv_array_ser(mfb_meta_arr),
        RX_SOF_POS => (others => '0'),
        RX_EOF_POS => slv_array_ser(mfb_eof_pos_arr),
        RX_SOF     => mfb_sof,
        RX_EOF     => mfb_eof,
        RX_SRC_RDY => cc_valid,
        RX_DST_RDY => cc_ready,

        TX_DATA    => CC_MFB_DATA,
        TX_META    => CC_MFB_META,
        TX_SOF_POS => CC_MFB_SOF_POS,
        TX_EOF_POS => CC_MFB_EOF_POS,
        TX_SOF     => CC_MFB_SOF,
        TX_EOF     => CC_MFB_EOF,
        TX_SRC_RDY => CC_MFB_SRC_RDY,
        TX_DST_RDY => CC_MFB_DST_RDY
    );

end architecture;
