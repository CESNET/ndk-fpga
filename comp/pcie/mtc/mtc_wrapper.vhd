-- mtc_wrapper.vhd: MI transaction controler wrapper
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

entity MTC_WRAPPER is
    generic(
        -- AXI bus: width of data word in bits
        AXI_DATA_WIDTH    : natural := 512;
        -- AXI bus: width of CQ user word in bits
        AXI_CQUSER_WIDTH  : natural := 183;
        -- AXI bus: width of CC user word in bits
        AXI_CCUSER_WIDTH  : natural := 81;
        -- MFB bus: number of regions in word
        MFB_REGIONS       : natural := 2;
        -- MFB bus: number of blocks in region, must be 1
        MFB_REGION_SIZE   : natural := 1;
        -- MFB bus: number of items in block, must be 8
        MFB_BLOCK_SIZE    : natural := 8;
        -- MFB bus: width of one item in bits, must be 32 (dword)
        MFB_ITEM_WIDTH    : natural := 32;
        -- MFB bus: width of CQ meta item in bits (BAR index + PCIe Prefix + PCIe Header)
        MFB_CQ_META_WIDTH : natural := 3+32+128;
        -- MFB bus: width of CQ meta item in bits (PCIe Prefix + PCIe Header)
        MFB_CC_META_WIDTH : natural := 32+128;
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
        -- Intel PCIe endpoint type (Intel only): "H_TILE", "P_TILE", "R_TILE"
        ENDPOINT_TYPE     : string := "H_TILE"
    );
    port (
        -- Clock signal for the whole MTC module.
        -- Must be used clock from PCIe Hard IP!
        CLK               : in  std_logic;
        -- Reset synchronized with CLK.
        RESET             : in  std_logic;

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
        -- MFB Completer Request Interface (CQ) - Intel FPGA Only
        -- =====================================================================

        -- CQ_MFB: data word with frames (packets)
        CQ_MFB_DATA       : in  std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
        -- CQ_MFB: meta word with metadata for each frame. In each region
        -- from LSB: 128b PCIe Header, 32b PCIe Prefix, 3b BAR index.
        CQ_MFB_META       : in  std_logic_vector(MFB_REGIONS*MFB_CQ_META_WIDTH-1 downto 0);
        -- CQ_TPH_PRESENT    : in std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CQ_TPH_TYPE       : in std_logic_vector(MFB_REGIONS*2-1 downto 0);
        -- CQ_TPH_ST_TAG     : in std_logic_vector(MFB_REGIONS*8-1 downto 0);
        -- CQ_FBE            : in std_logic_vector(MFB_REGIONS*4-1 downto 0);
        -- CQ_LBE            : in std_logic_vector(MFB_REGIONS*4-1 downto 0);
        -- CQ_MFB: Start Of Frame (SOF) flag for each MFB region
        CQ_MFB_SOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CQ_MFB: End Of Frame (EOF) flag for each MFB region
        CQ_MFB_EOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CQ_MFB: SOF position for each MFB region in MFB blocks
        CQ_MFB_SOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        -- CQ_MFB: EOF position for each MFB region in MFB items
        CQ_MFB_EOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- CQ_MFB: source ready of each MFB bus
        CQ_MFB_SRC_RDY    : in  std_logic;
        -- CQ_MFB: destination ready of each MFB bus
        CQ_MFB_DST_RDY    : out std_logic;

        -- =====================================================================
        -- MFB Completer Completion Interface (CC) - Intel FPGA Only
        -- =====================================================================

        -- CC_MFB: data word with frames (packets)
        CC_MFB_DATA       : out std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
        -- CC_MFB: meta word with metadata for each frame. In each region
        -- from LSB: 128b PCIe Header, 32b PCIe Prefix.
        CC_MFB_META       : out std_logic_vector(MFB_REGIONS*MFB_CC_META_WIDTH-1 downto 0) := (others => '0');
        -- CC_MFB: Start Of Frame (SOF) flag for each MFB region
        CC_MFB_SOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CC_MFB: End Of Frame (EOF) flag for each MFB region
        CC_MFB_EOF        : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CC_MFB: SOF position for each MFB region in MFB blocks
        CC_MFB_SOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        -- CC_MFB: EOF position for each MFB region in MFB items
        CC_MFB_EOF_POS    : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- CC_MFB: source ready of each MFB bus
        CC_MFB_SRC_RDY    : out std_logic;
        -- CC_MFB: destination ready of each MFB bus
        CC_MFB_DST_RDY    : in  std_logic;

        -- =====================================================================
        -- AXI Completer Request Interface (CQ) - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================

        -- CQ_AXI: Data word. For detailed specifications, see Xilinx PG213.
        CQ_AXI_DATA       : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        -- CQ_AXI: Set of signals with sideband information about trasferred
        -- transaction. For detailed specifications, see Xilinx PG213.
        CQ_AXI_USER       : in  std_logic_vector(AXI_CQUSER_WIDTH-1 downto 0);
        -- CQ_AXI: Indication of the last word of a transaction. For detailed
        -- specifications, see Xilinx PG213.
        CQ_AXI_LAST       : in  std_logic;
        -- CQ_AXI: Indication of valid data: each bit determines validity of
        -- different Dword. For detailed specifications, see Xilinx PG213.
        CQ_AXI_KEEP       : in  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        -- CQ_AXI: Indication of valid data: i.e. completer is ready to send a
        -- transaction. For detailed specifications, see Xilinx PG213.
        CQ_AXI_VALID      : in  std_logic;
        -- CQ_AXI: User application is ready to receive a transaction.
        -- For detailed specifications, see Xilinx PG213.
        CQ_AXI_READY      : out std_logic;

        -- =====================================================================
        -- AXI Completer Completion Interface (CC) - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================

        -- CC_AXI: Data word. For detailed specifications, see Xilinx PG213.
        CC_AXI_DATA       : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        -- CC_AXI: Set of signals with sideband information about trasferred
        -- transaction. For detailed specifications, see Xilinx PG213.
        CC_AXI_USER       : out std_logic_vector(AXI_CCUSER_WIDTH-1 downto 0);
        -- CC_AXI: Indication of the last word of a transaction. For detailed
        -- specifications, see Xilinx PG213.
        CC_AXI_LAST       : out std_logic;
        -- CC_AXI: Indication of valid data: each bit determines validity of
        -- different Dword. For detailed specifications, see Xilinx PG213.
        CC_AXI_KEEP       : out std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        -- CC_AXI: Indication of valid data: i.e. completer is ready to send a
        -- transaction. For detailed specifications, see Xilinx PG213.
        CC_AXI_VALID      : out std_logic;
        -- CC_AXI: User application is ready to receive a transaction.
        -- For detailed specifications, see Xilinx PG213.
        CC_AXI_READY      : in  std_logic;

        -- =====================================================================
        -- MI32 interface (master)
        -- =====================================================================

        -- MI bus: PCIe function number that generated the current MI request
        MI_FUNCTION       : out std_logic_vector(7 downto 0);
        -- MI bus: data from master to slave (write data)
        MI_DWR            : out std_logic_vector(31 downto 0);
        -- MI bus: slave address
        MI_ADDR           : out std_logic_vector(31 downto 0);
        -- MI bus: byte enable
        MI_BE             : out std_logic_vector(3 downto 0);
        -- MI bus: read request
        MI_RD             : out std_logic;
        -- MI bus: write request
        MI_WR             : out std_logic;
        -- MI bus: ready of slave module
        MI_ARDY           : in  std_logic;
        -- MI bus: data from slave to master (read data)
        MI_DRD            : in  std_logic_vector(31 downto 0);
        -- MI bus: valid of MI_DRD data signal
        MI_DRDY           : in  std_logic
    );
end entity;

architecture full of MTC_WRAPPER is

    constant IS_XILINX_DEV   : boolean := DEVICE="ULTRASCALE" or DEVICE="7SERIES";
    constant IS_INTEL_DEV    : boolean := DEVICE="STRATIX10" or DEVICE="AGILEX";

    -- CQ MFB output

    signal cq_mfb_data_out        : std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
    signal cq_mfb_meta_out        : std_logic_vector(MFB_REGIONS*MFB_CQ_META_WIDTH-1 downto 0);
    signal cq_mfb_sof_out         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_mfb_eof_out         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_mfb_sof_pos_out     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal cq_mfb_eof_pos_out     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal cq_mfb_src_rdy_out     : std_logic;
    signal cq_mfb_dst_rdy_out     : std_logic;

    signal cq_user_tph_present    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_user_tph_type       : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal cq_user_tph_st_tag     : std_logic_vector(MFB_REGIONS*8-1 downto 0);
    signal cq_user_fbe            : std_logic_vector(MFB_REGIONS*4-1 downto 0);
    signal cq_user_lbe            : std_logic_vector(MFB_REGIONS*4-1 downto 0);

    signal cc_mfb_dst_rdy_out     : std_logic;

    signal cq_mfb_meta_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_CQ_META_WIDTH-1 downto 0);
    signal cq_mfb_meta_new_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(PCIE_CQ_META_WIDTH-1 downto 0);
    signal cc_mfb_meta_new        : std_logic_vector(MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);

begin

    ---------------------------------------------------------------------------
    -- MFB to PCIe-AXI interface convertor
    ---------------------------------------------------------------------------

    cq_mfb_xilinx_g: if IS_XILINX_DEV generate
        mfb2pcie_axi_i : entity work.PCIE_CQ_AXI2MFB
        generic map(
            MFB_REGIONS      => MFB_REGIONS,
            MFB_REGION_SIZE  => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,

            AXI_CQUSER_WIDTH => AXI_CQUSER_WIDTH,
            AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
            STRADDLING       => false
        )
        port map(

            CQ_AXI_DATA    => CQ_AXI_DATA,
            CQ_AXI_USER    => CQ_AXI_USER,
            CQ_AXI_LAST    => CQ_AXI_LAST,
            CQ_AXI_KEEP    => CQ_AXI_KEEP,
            CQ_AXI_VALID   => CQ_AXI_VALID,
            CQ_AXI_READY   => CQ_AXI_READY,

            CQ_MFB_DATA    => cq_mfb_data_out,
            --CQ_MFB_META    => cq_mfb_meta_out,
            CQ_MFB_SOF     => cq_mfb_sof_out,
            CQ_MFB_EOF     => cq_mfb_eof_out,
            CQ_MFB_SOF_POS => cq_mfb_sof_pos_out,
            CQ_MFB_EOF_POS => cq_mfb_eof_pos_out,
            CQ_MFB_SRC_RDY => cq_mfb_src_rdy_out,
            CQ_MFB_DST_RDY => cq_mfb_dst_rdy_out,
            CQ_TPH_PRESENT => cq_user_tph_present,
            CQ_TPH_TYPE    => cq_user_tph_type,
            CQ_TPH_ST_TAG  => cq_user_tph_st_tag,
            CQ_FBE         => cq_user_fbe,
            CQ_LBE         => cq_user_lbe
        );

        mfb_cc2axi_i : entity work.PCIE_CC_MFB2AXI
        generic map(
            MFB_REGIONS      => MFB_REGIONS,
            MFB_REGION_SIZE  => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,

            AXI_CCUSER_WIDTH => AXI_CCUSER_WIDTH,
            AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
            STRADDLING       => false
        )
        port map(

            CC_MFB_DATA    => CC_MFB_DATA,
            CC_MFB_SOF     => CC_MFB_SOF,
            CC_MFB_EOF     => CC_MFB_EOF,
            CC_MFB_SOF_POS => CC_MFB_SOF_POS,
            CC_MFB_EOF_POS => CC_MFB_EOF_POS,
            CC_MFB_SRC_RDY => CC_MFB_SRC_RDY,
            CC_MFB_DST_RDY => cc_mfb_dst_rdy_out,

            CC_AXI_DATA    => CC_AXI_DATA,
            CC_AXI_USER    => CC_AXI_USER,
            CC_AXI_LAST    => CC_AXI_LAST,
            CC_AXI_KEEP    => CC_AXI_KEEP,
            CC_AXI_VALID   => CC_AXI_VALID,
            CC_AXI_READY   => CC_AXI_READY
        );
    end generate;

    cq_mfb_intel_g: if IS_INTEL_DEV generate
        cq_mfb_data_out     <= CQ_MFB_DATA;
        cq_mfb_sof_out      <= CQ_MFB_SOF;
        cq_mfb_eof_out      <= CQ_MFB_EOF;
        cq_mfb_sof_pos_out  <= CQ_MFB_SOF_POS;
        cq_mfb_eof_pos_out  <= CQ_MFB_EOF_POS;
        cq_mfb_src_rdy_out  <= CQ_MFB_SRC_RDY;
        CQ_MFB_DST_RDY      <= cq_mfb_dst_rdy_out;
        cc_mfb_dst_rdy_out  <= CC_MFB_DST_RDY;
        cq_user_tph_present <= (others => '0');
        cq_user_tph_type    <= (others => '0');
        cq_user_tph_st_tag  <= (others => '0');
        cq_user_fbe         <= (others => '0');
        cq_user_lbe         <= (others => '0');
    end generate;

    cq_mfb_meta_arr <= slv_array_deser(CQ_MFB_META,MFB_REGIONS);

    cq_mfb_meta_g: for i in 0 to MFB_REGIONS-1 generate
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_HEADER)        <= cq_mfb_meta_arr(i)(127 downto 0);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_PREFIX)        <= cq_mfb_meta_arr(i)(159 downto 128);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_BAR)           <= cq_mfb_meta_arr(i)(162 downto 160);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_FBE)           <= cq_user_fbe((i+1)*PCIE_META_FBE_W-1 downto i*PCIE_META_FBE_W);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_LBE)           <= cq_user_lbe((i+1)*PCIE_META_LBE_W-1 downto i*PCIE_META_LBE_W);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_TPH_PRESENT_O) <= cq_user_tph_present(i);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_TPH_TYPE)      <= cq_user_tph_type((i+1)*PCIE_META_TPH_TYPE_W-1 downto i*PCIE_META_TPH_TYPE_W);
        cq_mfb_meta_new_arr(i)(PCIE_CQ_META_TPH_ST_TAG)    <= cq_user_tph_st_tag((i+1)*PCIE_META_TPH_ST_TAG_W-1 downto i*PCIE_META_TPH_ST_TAG_W);
    end generate;

    mtc_i : entity work.MTC
    generic map(
        MFB_REGIONS       => MFB_REGIONS,
        MFB_REGION_SIZE   => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE    => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH    => MFB_ITEM_WIDTH,
        MFB_REGION_WIDTH  => MFB_REGION_WIDTH,
        BAR0_BASE_ADDR    => BAR0_BASE_ADDR,
        BAR1_BASE_ADDR    => BAR1_BASE_ADDR,
        BAR2_BASE_ADDR    => BAR2_BASE_ADDR,
        BAR3_BASE_ADDR    => BAR3_BASE_ADDR,
        BAR4_BASE_ADDR    => BAR4_BASE_ADDR,
        BAR5_BASE_ADDR    => BAR5_BASE_ADDR,
        EXP_ROM_BASE_ADDR => EXP_ROM_BASE_ADDR,
        CC_PIPE           => CC_PIPE,
        CQ_PIPE           => CQ_PIPE,
        MI_PIPE           => MI_PIPE,
        MI_DATA_WIDTH     => MI_DATA_WIDTH,
        MI_ADDR_WIDTH     => MI_ADDR_WIDTH,
        DEVICE            => DEVICE,
        ENDPOINT_TYPE     => ENDPOINT_TYPE
    )
    port map(
        CLK                  => CLK,
        RESET                => RESET,

        CTL_MAX_PAYLOAD_SIZE => CTL_MAX_PAYLOAD_SIZE,
        CTL_BAR_APERTURE     => CTL_BAR_APERTURE,
        CQ_MFB_DATA          => cq_mfb_data_out,
        CQ_MFB_META          => slv_array_ser(cq_mfb_meta_new_arr),
        CQ_MFB_SOF           => cq_mfb_sof_out,
        CQ_MFB_EOF           => cq_mfb_eof_out,
        CQ_MFB_SOF_POS       => cq_mfb_sof_pos_out,
        CQ_MFB_EOF_POS       => cq_mfb_eof_pos_out,
        CQ_MFB_SRC_RDY       => cq_mfb_src_rdy_out,
        CQ_MFB_DST_RDY       => cq_mfb_dst_rdy_out,

        CC_MFB_DATA          => CC_MFB_DATA,
        CC_MFB_META          => cc_mfb_meta_new,
        CC_MFB_SOF           => CC_MFB_SOF,
        CC_MFB_EOF           => CC_MFB_EOF,
        CC_MFB_SOF_POS       => CC_MFB_SOF_POS,
        CC_MFB_EOF_POS       => CC_MFB_EOF_POS,
        CC_MFB_SRC_RDY       => CC_MFB_SRC_RDY,
        CC_MFB_DST_RDY       => cc_mfb_dst_rdy_out,

        MI_FUNCTION          => MI_FUNCTION,
        MI_DWR               => MI_DWR,
        MI_ADDR              => MI_ADDR,
        MI_BE                => MI_BE,
        MI_RD                => MI_RD,
        MI_WR                => MI_WR,
        MI_ARDY              => MI_ARDY,
        MI_DRD               => MI_DRD,
        MI_DRDY              => MI_DRDY
    );

    CC_MFB_META(95 downto 0) <= cc_mfb_meta_new(95 downto 0);

end architecture;
