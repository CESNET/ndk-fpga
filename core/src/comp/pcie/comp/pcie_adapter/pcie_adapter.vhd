-- pcie_adapter.vhd: PCIe adapter
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

entity PCIE_ADAPTER is
    generic(
        -- =====================================================================
        -- MFB configuration
        -- =====================================================================
        CQ_MFB_REGIONS     : natural := 2;
        CQ_MFB_REGION_SIZE : natural := 1;
        CQ_MFB_BLOCK_SIZE  : natural := 8;
        CQ_MFB_ITEM_WIDTH  : natural := 32;
        RC_MFB_REGIONS     : natural := 2;
        RC_MFB_REGION_SIZE : natural := 1;
        RC_MFB_BLOCK_SIZE  : natural := 8;
        RC_MFB_ITEM_WIDTH  : natural := 32;
        CC_MFB_REGIONS     : natural := 2;
        CC_MFB_REGION_SIZE : natural := 1;
        CC_MFB_BLOCK_SIZE  : natural := 8;
        CC_MFB_ITEM_WIDTH  : natural := 32;
        RQ_MFB_REGIONS     : natural := 2;
        RQ_MFB_REGION_SIZE : natural := 1;
        RQ_MFB_BLOCK_SIZE  : natural := 8;
        RQ_MFB_ITEM_WIDTH  : natural := 32;

        -- =====================================================================
        -- Common configuration
        -- =====================================================================
        -- Connected PCIe endpoint type
        ENDPOINT_TYPE      : string  := "P_TILE";
        -- FPGA device
        DEVICE             : string  := "STRATIX10";
        -- Depth of CQ FIFO (R-Tile only)
        CQ_FIFO_ITEMS      : natural := 512;
        -- Maximum write request (payload) size (in DWORDs)
        PCIE_MPS_DW        : natural := 512/4;

        -- =====================================================================
        -- AXI configuration
        -- =====================================================================
        AXI_DATA_WIDTH     : natural := CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH;
        -- Allowed values: 183 (USP Gen3x16), 88 (USP Gen3x8), 85 (V7 Gen3x8)
        AXI_CQUSER_WIDTH   : natural := 183;
        -- Allowed values: 81 (USP Gen3x16), 33 (USP Gen3x8), 33 (V7 Gen3x8)
        AXI_CCUSER_WIDTH   : natural := 81;
        -- Allowed values: 137 (USP Gen3x16), 62 (USP Gen3x8), 60 (V7 Gen3x8)
        AXI_RQUSER_WIDTH   : natural := 137;
        -- Allowed values: 161 (USP Gen3x16), 75 (USP Gen3x8), 75 (V7 Gen3x8)
        AXI_RCUSER_WIDTH   : natural := 161;
        AXI_STRADDLING     : boolean := false;

        -- =====================================================================
        -- AVST configuration (set automatically)
        -- =====================================================================
        AVST_DOWN_SEG      : natural := CQ_MFB_REGIONS;
        AVST_UP_SEG        : natural := CC_MFB_REGIONS
    );
    port(
        -- =====================================================================
        --  CLOCK AND RESET
        -- =====================================================================
        PCIE_CLK            : in  std_logic;
        PCIE_RESET          : in  std_logic;

        -- =====================================================================
        -- Avalon-ST DOWN (CQ+RC) Interface - Intel FPGA Only
        -- =====================================================================
        AVST_DOWN_DATA      : in  std_logic_vector(AVST_DOWN_SEG*256-1 downto 0);
        AVST_DOWN_HDR       : in  std_logic_vector(AVST_DOWN_SEG*128-1 downto 0);
        AVST_DOWN_PREFIX    : in  std_logic_vector(AVST_DOWN_SEG*32-1 downto 0);
        AVST_DOWN_SOP       : in  std_logic_vector(AVST_DOWN_SEG-1 downto 0);
        AVST_DOWN_EOP       : in  std_logic_vector(AVST_DOWN_SEG-1 downto 0);
        AVST_DOWN_EMPTY     : in  std_logic_vector(AVST_DOWN_SEG*3-1 downto 0);
        AVST_DOWN_BAR_RANGE : in  std_logic_vector(AVST_DOWN_SEG*3-1 downto 0);
        AVST_DOWN_VALID     : in  std_logic_vector(AVST_DOWN_SEG-1 downto 0);
        AVST_DOWN_READY     : out std_logic;

        -- =====================================================================
        -- Avalon-ST UP (CC+RQ) Interface - Intel FPGA Only
        -- =====================================================================
        AVST_UP_DATA        : out std_logic_vector(AVST_UP_SEG*256-1 downto 0);
        AVST_UP_HDR         : out std_logic_vector(AVST_UP_SEG*128-1 downto 0);
        AVST_UP_PREFIX      : out std_logic_vector(AVST_UP_SEG*32-1 downto 0);
        AVST_UP_SOP         : out std_logic_vector(AVST_UP_SEG-1 downto 0);
        AVST_UP_EOP         : out std_logic_vector(AVST_UP_SEG-1 downto 0);
        AVST_UP_ERROR       : out std_logic_vector(AVST_UP_SEG-1 downto 0);
        AVST_UP_VALID       : out std_logic_vector(AVST_UP_SEG-1 downto 0);
        AVST_UP_READY       : in  std_logic;

        -- =====================================================================
        -- CREDIT FLOW CONTROL UP INTERFACE - Intel R-Tile Only
        -- =====================================================================
        CRDT_DOWN_INIT_DONE : in  std_logic := '0';
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_DOWN_UPDATE    : out std_logic_vector(6-1 downto 0);
        -- Update count of PH credits
        CRDT_DOWN_CNT_PH    : out std_logic_vector(2-1 downto 0);
        -- Update count of NPH credits
        CRDT_DOWN_CNT_NPH   : out std_logic_vector(2-1 downto 0);
        -- Update count of CPLH credits
        CRDT_DOWN_CNT_CPLH  : out std_logic_vector(2-1 downto 0);
        -- Update count of PD credits
        CRDT_DOWN_CNT_PD    : out std_logic_vector(4-1 downto 0);
        -- Update count of NPD credits
        CRDT_DOWN_CNT_NPD   : out std_logic_vector(4-1 downto 0);
        -- Update count of CPLD credits
        CRDT_DOWN_CNT_CPLD  : out std_logic_vector(4-1 downto 0);

        -- =====================================================================
        -- CREDIT FLOW CONTROL DOWN INTERFACE - Intel R-Tile Only
        -- =====================================================================
        -- In init phase must the receiver must set the total number of credits
        -- using incremental credit updates. The user logic only receives the
        -- credit updates and waits for CRDT_UP_INIT_DONE to be high.
        CRDT_UP_INIT_DONE   : in  std_logic := '0';
        -- Update valid flags vector (from MSB to LSB: CPLD,NPD,PD,CPLH,NPH,PH)
        CRDT_UP_UPDATE      : in  std_logic_vector(6-1 downto 0);
        -- Update count of PH credits
        CRDT_UP_CNT_PH      : in  std_logic_vector(2-1 downto 0);
        -- Update count of NPH credits
        CRDT_UP_CNT_NPH     : in  std_logic_vector(2-1 downto 0);
        -- Update count of CPLH credits
        CRDT_UP_CNT_CPLH    : in  std_logic_vector(2-1 downto 0);
        -- Update count of PD credits
        CRDT_UP_CNT_PD      : in  std_logic_vector(4-1 downto 0);
        -- Update count of NPD credits
        CRDT_UP_CNT_NPD     : in  std_logic_vector(4-1 downto 0);
        -- Update count of CPLD credits
        CRDT_UP_CNT_CPLD    : in  std_logic_vector(4-1 downto 0);

        -- =====================================================================
        -- AXI Completer Request (CQ) Interface - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================
        CQ_AXI_DATA       : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        CQ_AXI_USER       : in  std_logic_vector(AXI_CQUSER_WIDTH-1 downto 0);
        CQ_AXI_LAST       : in  std_logic;
        CQ_AXI_KEEP       : in  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        CQ_AXI_VALID      : in  std_logic;
        CQ_AXI_READY      : out std_logic;

        -- =====================================================================
        -- AXI Requester Completion (RC) Interface - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================
        RC_AXI_DATA       : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        RC_AXI_USER       : in  std_logic_vector(AXI_RCUSER_WIDTH-1 downto 0);
        RC_AXI_LAST       : in  std_logic;
        RC_AXI_KEEP       : in  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        RC_AXI_VALID      : in  std_logic;
        RC_AXI_READY      : out std_logic;

        -- =====================================================================
        -- AXI Completer Completion (CC) Interface - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================
        CC_AXI_DATA       : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        CC_AXI_USER       : out std_logic_vector(AXI_CCUSER_WIDTH-1 downto 0);
        CC_AXI_LAST       : out std_logic;
        CC_AXI_KEEP       : out std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        CC_AXI_VALID      : out std_logic;
        CC_AXI_READY      : in  std_logic;

        -- =====================================================================
        -- AXI Requester Request (RQ) Interface - Xilinx FPGA Only
        -- 
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================
        RQ_AXI_DATA       : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        RQ_AXI_USER       : out std_logic_vector(AXI_RQUSER_WIDTH-1 downto 0);
        RQ_AXI_LAST       : out std_logic;
        RQ_AXI_KEEP       : out std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        RQ_AXI_VALID      : out std_logic;
        RQ_AXI_READY      : in  std_logic;

        -- =====================================================================
        -- RQ MFB interface
        --
        -- MFB bus for transferring PCIe transactions (format according to the
        -- PCIe IP used). Compared to the standard MFB specification, it does
        -- not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        RQ_MFB_DATA       : in  std_logic_vector(RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
        RQ_MFB_META       : in  std_logic_vector(RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH-1 downto 0);
        RQ_MFB_SOF        : in  std_logic_vector(RQ_MFB_REGIONS-1 downto 0);
        RQ_MFB_EOF        : in  std_logic_vector(RQ_MFB_REGIONS-1 downto 0);
        RQ_MFB_SOF_POS    : in  std_logic_vector(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
        RQ_MFB_EOF_POS    : in  std_logic_vector(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
        RQ_MFB_SRC_RDY    : in  std_logic;
        RQ_MFB_DST_RDY    : out std_logic;

        -- =====================================================================
        -- RC MFB interface
        --
        -- MFB bus for transferring PCIe transactions (format according to the
        -- PCIe IP used). Compared to the standard MFB specification, it does
        -- not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        RC_MFB_DATA       : out std_logic_vector(RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
        RC_MFB_META       : out std_logic_vector(RC_MFB_REGIONS*PCIE_RC_META_WIDTH-1 downto 0);
        RC_MFB_SOF        : out std_logic_vector(RC_MFB_REGIONS-1 downto 0);
        RC_MFB_EOF        : out std_logic_vector(RC_MFB_REGIONS-1 downto 0);
        RC_MFB_SOF_POS    : out std_logic_vector(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
        RC_MFB_EOF_POS    : out std_logic_vector(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
        RC_MFB_SRC_RDY    : out std_logic;
        RC_MFB_DST_RDY    : in  std_logic;

        -- =====================================================================
        -- CQ MFB interface
        --
        -- MFB bus for transferring PCIe transactions (format according to the
        -- PCIe IP used). Compared to the standard MFB specification, it does
        -- not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        CQ_MFB_DATA       : out std_logic_vector(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
        CQ_MFB_META       : out std_logic_vector(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
        CQ_MFB_SOF        : out std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
        CQ_MFB_EOF        : out std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
        CQ_MFB_SOF_POS    : out std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
        CQ_MFB_EOF_POS    : out std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
        CQ_MFB_SRC_RDY    : out std_logic;
        CQ_MFB_DST_RDY    : in  std_logic;

        -- =====================================================================
        -- CC MFB interface
        --
        -- MFB bus for transferring PCIe transactions (format according to the
        -- PCIe IP used). Compared to the standard MFB specification, it does
        -- not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        CC_MFB_DATA       : in  std_logic_vector(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
        CC_MFB_META       : in  std_logic_vector(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
        CC_MFB_SOF        : in  std_logic_vector(CC_MFB_REGIONS-1 downto 0);
        CC_MFB_EOF        : in  std_logic_vector(CC_MFB_REGIONS-1 downto 0);
        CC_MFB_SOF_POS    : in  std_logic_vector(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
        CC_MFB_EOF_POS    : in  std_logic_vector(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
        CC_MFB_SRC_RDY    : in  std_logic;
        CC_MFB_DST_RDY    : out std_logic
    );
end entity;

architecture FULL of PCIE_ADAPTER is

    constant IS_XILINX_DEVICE : boolean := (DEVICE="ULTRASCALE");
    constant IS_INTEL_DEVICE  : boolean := (DEVICE="STRATIX10") or (DEVICE="AGILEX");

    signal cq_tph_present       : std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
    signal cq_tph_type          : std_logic_vector(CQ_MFB_REGIONS*2-1 downto 0);
    signal cq_tph_st_tag        : std_logic_vector(CQ_MFB_REGIONS*8-1 downto 0);
    signal cq_fbe               : std_logic_vector(CQ_MFB_REGIONS*4-1 downto 0);
    signal cq_lbe               : std_logic_vector(CQ_MFB_REGIONS*4-1 downto 0);
    signal rq_mfb_be_arr        : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(8-1 downto 0);

    signal cq_mfb_meta_arr      : slv_array_t(CQ_MFB_REGIONS-1 downto 0)(PCIE_CQ_META_WIDTH-1 downto 0);
    signal rc_mfb_meta_arr      : slv_array_t(RC_MFB_REGIONS-1 downto 0)(PCIE_RC_META_WIDTH-1 downto 0);
    signal cc_mfb_meta_arr      : slv_array_t(CC_MFB_REGIONS-1 downto 0)(PCIE_CC_META_WIDTH-1 downto 0);
    signal rq_mfb_meta_arr      : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(PCIE_RQ_META_WIDTH-1 downto 0);

    signal cblk_cq_mfb_meta     : std_logic_vector(CQ_MFB_REGIONS*(128+32+3)-1 downto 0);
    signal cblk_cq_mfb_meta_arr : slv_array_t(CQ_MFB_REGIONS-1 downto 0)(128+32+3-1 downto 0);
    signal cblk_rc_mfb_meta     : std_logic_vector(RC_MFB_REGIONS*(128+32+3)-1 downto 0);
    signal cblk_rc_mfb_meta_arr : slv_array_t(RC_MFB_REGIONS-1 downto 0)(128+32+3-1 downto 0);
    signal cblk_cc_mfb_meta_arr : slv_array_t(CC_MFB_REGIONS-1 downto 0)(128+32-1 downto 0);
    signal cblk_rq_mfb_meta_arr : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(128+32-1 downto 0);

begin

    xilinx_g: if IS_XILINX_DEVICE generate
        AVST_DOWN_READY    <= '0';
        AVST_UP_DATA       <= (others => '0');
        AVST_UP_HDR        <= (others => '0');
        AVST_UP_PREFIX     <= (others => '0');
        AVST_UP_SOP        <= (others => '0');
        AVST_UP_EOP        <= (others => '0');
        AVST_UP_ERROR      <= (others => '0');
        AVST_UP_VALID      <= (others => '0');
        CRDT_DOWN_UPDATE   <= (others => '0');
        CRDT_DOWN_CNT_PH   <= (others => '0');
        CRDT_DOWN_CNT_NPH  <= (others => '0');
        CRDT_DOWN_CNT_CPLH <= (others => '0');
        CRDT_DOWN_CNT_PD   <= (others => '0');
        CRDT_DOWN_CNT_NPD  <= (others => '0');
        CRDT_DOWN_CNT_CPLD <= (others => '0');

        cq_axi2mfb_i : entity work.PCIE_CQ_AXI2MFB
        generic map (
            MFB_REGIONS      => CQ_MFB_REGIONS,
            MFB_REGION_SIZE  => CQ_MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => CQ_MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => CQ_MFB_ITEM_WIDTH,
            AXI_CQUSER_WIDTH => AXI_CQUSER_WIDTH,
            AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
            STRADDLING       => AXI_STRADDLING,
            DEVICE           => DEVICE
        )
        port map (
            CQ_AXI_DATA    => CQ_AXI_DATA,
            CQ_AXI_USER    => CQ_AXI_USER,
            CQ_AXI_LAST    => CQ_AXI_LAST,
            CQ_AXI_KEEP    => CQ_AXI_KEEP,
            CQ_AXI_VALID   => CQ_AXI_VALID,
            CQ_AXI_READY   => CQ_AXI_READY,

            CQ_MFB_DATA    => CQ_MFB_DATA,
            CQ_MFB_SOF     => CQ_MFB_SOF,
            CQ_MFB_EOF     => CQ_MFB_EOF,
            CQ_MFB_SOF_POS => CQ_MFB_SOF_POS,
            CQ_MFB_EOF_POS => CQ_MFB_EOF_POS,
            CQ_MFB_SRC_RDY => CQ_MFB_SRC_RDY,
            CQ_MFB_DST_RDY => CQ_MFB_DST_RDY,

            CQ_TPH_PRESENT => cq_tph_present,
            CQ_TPH_TYPE    => cq_tph_type,
            CQ_TPH_ST_TAG  => cq_tph_st_tag,
            CQ_FBE         => cq_fbe,
            CQ_LBE         => cq_lbe
        );

        cq_mfb_meta_g: for i in 0 to CQ_MFB_REGIONS-1 generate
            cq_mfb_meta_arr(i)(PCIE_CQ_META_HEADER)        <= (others => '0');
            cq_mfb_meta_arr(i)(PCIE_CQ_META_PREFIX)        <= (others => '0');
            cq_mfb_meta_arr(i)(PCIE_CQ_META_BAR)           <= (others => '0'); 
            cq_mfb_meta_arr(i)(PCIE_CQ_META_FBE)           <= cq_fbe((i+1)*PCIE_META_FBE_W-1 downto i*PCIE_META_FBE_W);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_LBE)           <= cq_lbe((i+1)*PCIE_META_LBE_W-1 downto i*PCIE_META_LBE_W);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_TPH_PRESENT_O) <= cq_tph_present(i);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_TPH_TYPE)      <= cq_tph_type((i+1)*PCIE_META_TPH_TYPE_W-1 downto i*PCIE_META_TPH_TYPE_W);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_TPH_ST_TAG)    <= cq_tph_st_tag((i+1)*PCIE_META_TPH_ST_TAG_W-1 downto i*PCIE_META_TPH_ST_TAG_W);
        end generate;

        CQ_MFB_META <= slv_array_ser(cq_mfb_meta_arr);

        rc_mfb2axi_i : entity work.PTC_PCIE_AXI2MFB
        generic map (
            MFB_REGIONS      => RC_MFB_REGIONS,
            MFB_REG_SIZE     => RC_MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => RC_MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => RC_MFB_ITEM_WIDTH,
            AXI_RCUSER_WIDTH => AXI_RCUSER_WIDTH,
            AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
            DEVICE           => DEVICE
        )
        port map (
            CLK            => PCIE_CLK,
            RESET          => PCIE_RESET,

            RX_AXI_TDATA   => RC_AXI_DATA,
            RX_AXI_TUSER   => RC_AXI_USER,
            RX_AXI_TVALID  => RC_AXI_VALID,
            RX_AXI_TREADY  => RC_AXI_READY,
      
            TX_MFB_DATA    => RC_MFB_DATA,
            TX_MFB_SOF     => RC_MFB_SOF,
            TX_MFB_EOF     => RC_MFB_EOF,
            TX_MFB_SOF_POS => RC_MFB_SOF_POS,
            TX_MFB_EOF_POS => RC_MFB_EOF_POS,
            TX_MFB_SRC_RDY => RC_MFB_SRC_RDY,
            TX_MFB_DST_RDY => RC_MFB_DST_RDY
        );

        rc_mfb_meta_g: for i in 0 to RC_MFB_REGIONS-1 generate
            rc_mfb_meta_arr(i)(PCIE_CC_META_HEADER) <= (others => '0');
            rc_mfb_meta_arr(i)(PCIE_CC_META_PREFIX) <= (others => '0');
        end generate;

        RC_MFB_META <= slv_array_ser(rc_mfb_meta_arr);

        cc_mfb2axi_i : entity work.PCIE_CC_MFB2AXI
        generic map (
            MFB_REGIONS      => CC_MFB_REGIONS,
            MFB_REGION_SIZE  => CC_MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => CC_MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => CC_MFB_ITEM_WIDTH,
            AXI_CCUSER_WIDTH => AXI_CCUSER_WIDTH,
            AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
            STRADDLING       => AXI_STRADDLING
        )
        port map (
            CC_MFB_DATA    => CC_MFB_DATA,
            CC_MFB_SOF     => CC_MFB_SOF,
            CC_MFB_EOF     => CC_MFB_EOF,
            CC_MFB_SOF_POS => CC_MFB_SOF_POS,
            CC_MFB_EOF_POS => CC_MFB_EOF_POS,
            CC_MFB_SRC_RDY => CC_MFB_SRC_RDY,
            CC_MFB_DST_RDY => CC_MFB_DST_RDY,

            CC_AXI_DATA    => CC_AXI_DATA,
            CC_AXI_USER    => CC_AXI_USER,
            CC_AXI_LAST    => CC_AXI_LAST,
            CC_AXI_KEEP    => CC_AXI_KEEP,
            CC_AXI_VALID   => CC_AXI_VALID,
            CC_AXI_READY   => CC_AXI_READY
        );

        rq_mfb2axi_i : entity work.PTC_MFB2PCIE_AXI
        generic map (
            MFB_REGIONS      => RQ_MFB_REGIONS,
            MFB_REGION_SIZE  => RQ_MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => RQ_MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => RQ_MFB_ITEM_WIDTH,
            AXI_RQUSER_WIDTH => AXI_RQUSER_WIDTH
        )
        port map (
            RX_MFB_DATA    => RQ_MFB_DATA,
            RX_MFB_SOF_POS => RQ_MFB_SOF_POS,
            RX_MFB_EOF_POS => RQ_MFB_EOF_POS,
            RX_MFB_SOF     => RQ_MFB_SOF,
            RX_MFB_EOF     => RQ_MFB_EOF,
            RX_MFB_SRC_RDY => RQ_MFB_SRC_RDY,
            RX_MFB_DST_RDY => RQ_MFB_DST_RDY,
            RX_MFB_BE      => slv_array_ser(rq_mfb_be_arr),

            RQ_DATA        => RQ_AXI_DATA,
            RQ_USER        => RQ_AXI_USER,
            RQ_LAST        => RQ_AXI_LAST,
            RQ_KEEP        => RQ_AXI_KEEP,
            RQ_READY       => RQ_AXI_READY,
            RQ_VALID       => RQ_AXI_VALID
        );

        rq_mfb_meta_arr <= slv_array_deser(RQ_MFB_META, RQ_MFB_REGIONS);

        rq_mfb_be_arr_g: for i in 0 to RQ_MFB_REGIONS-1 generate
            rq_mfb_be_arr(i) <= rq_mfb_meta_arr(i)(PCIE_RQ_META_LBE) & rq_mfb_meta_arr(i)(PCIE_RQ_META_FBE);
        end generate;

    end generate;

    intel_g: if IS_INTEL_DEVICE generate
        CQ_AXI_READY <= '0';
        RC_AXI_READY <= '0';
        CC_AXI_DATA  <= (others => '0');
        CC_AXI_USER  <= (others => '0');
        CC_AXI_LAST  <= '0';
        CC_AXI_KEEP  <= (others => '0');
        CC_AXI_VALID <= '0';
        RQ_AXI_DATA  <= (others => '0');
        RQ_AXI_USER  <= (others => '0');
        RQ_AXI_LAST  <= '0';
        RQ_AXI_KEEP  <= (others => '0');
        RQ_AXI_VALID <= '0';

        conn_block_i : entity work.PCIE_CONNECTION_BLOCK
        generic map (
            MFB_REGIONS         => CQ_MFB_REGIONS,
            MFB_REGION_SIZE     => CQ_MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => CQ_MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => CQ_MFB_ITEM_WIDTH,
            MFB_UP_META_WIDTH   => 128+32,
            MFB_DOWN_META_WIDTH => 128+32+3,
            MTC_FIFO_DEPTH      => CQ_FIFO_ITEMS,
            PCIE_MPS_DW         => PCIE_MPS_DW,
            ENDPOINT_TYPE       => ENDPOINT_TYPE,
            DEVICE              => DEVICE
        )
        port map (
            CLK                 => PCIE_CLK,
            RESET               => PCIE_RESET,
            -- DOWN stream
            RX_AVST_DATA        => AVST_DOWN_DATA,
            RX_AVST_HDR         => AVST_DOWN_HDR,
            RX_AVST_PREFIX      => AVST_DOWN_PREFIX,
            RX_AVST_BAR_RANGE   => AVST_DOWN_BAR_RANGE,
            RX_AVST_SOP         => AVST_DOWN_SOP,
            RX_AVST_EOP         => AVST_DOWN_EOP,
            RX_AVST_EMPTY       => AVST_DOWN_EMPTY,
            RX_AVST_VALID       => AVST_DOWN_VALID,
            RX_AVST_READY       => AVST_DOWN_READY,
            -- UP stream
            TX_AVST_DATA        => AVST_UP_DATA,
            TX_AVST_HDR         => AVST_UP_HDR,
            TX_AVST_PREFIX      => AVST_UP_PREFIX,
            TX_AVST_SOP         => AVST_UP_SOP,
            TX_AVST_EOP         => AVST_UP_EOP, 
            TX_AVST_ERROR       => AVST_UP_ERROR, 
            TX_AVST_VALID       => AVST_UP_VALID,
            TX_AVST_READY       => AVST_UP_READY,
            -- DOWN stream credits - R-TILE only
            CRDT_DOWN_INIT_DONE => CRDT_DOWN_INIT_DONE,
            CRDT_DOWN_UPDATE    => CRDT_DOWN_UPDATE,
            CRDT_DOWN_CNT_PH    => CRDT_DOWN_CNT_PH,
            CRDT_DOWN_CNT_NPH   => CRDT_DOWN_CNT_NPH,
            CRDT_DOWN_CNT_CPLH  => CRDT_DOWN_CNT_CPLH,
            CRDT_DOWN_CNT_PD    => CRDT_DOWN_CNT_PD,
            CRDT_DOWN_CNT_NPD   => CRDT_DOWN_CNT_NPD,
            CRDT_DOWN_CNT_CPLD  => CRDT_DOWN_CNT_CPLD,
            -- UP stream credits - R-TILE only
            CRDT_UP_INIT_DONE   => CRDT_UP_INIT_DONE,
            CRDT_UP_UPDATE      => CRDT_UP_UPDATE,
            CRDT_UP_CNT_PH      => CRDT_UP_CNT_PH,
            CRDT_UP_CNT_NPH     => CRDT_UP_CNT_NPH,
            CRDT_UP_CNT_CPLH    => CRDT_UP_CNT_CPLH,
            CRDT_UP_CNT_PD      => CRDT_UP_CNT_PD,
            CRDT_UP_CNT_NPD     => CRDT_UP_CNT_NPD,
            CRDT_UP_CNT_CPLD    => CRDT_UP_CNT_CPLD,
            -- RQ stream
            RQ_MFB_DATA         => RQ_MFB_DATA,
            RQ_MFB_META         => slv_array_ser(cblk_rq_mfb_meta_arr),
            RQ_MFB_SOF          => RQ_MFB_SOF,
            RQ_MFB_EOF          => RQ_MFB_EOF,
            RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS,
            RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS,
            RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY,
            RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY,
            -- RC stream
            RC_MFB_DATA         => RC_MFB_DATA,
            RC_MFB_META         => cblk_rc_mfb_meta,
            RC_MFB_SOF          => RC_MFB_SOF,
            RC_MFB_EOF          => RC_MFB_EOF,
            RC_MFB_SOF_POS      => RC_MFB_SOF_POS,
            RC_MFB_EOF_POS      => RC_MFB_EOF_POS,
            RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY,
            RC_MFB_DST_RDY      => RC_MFB_DST_RDY,
            -- CC stream
            CC_MFB_DATA         => CC_MFB_DATA,
            CC_MFB_META         => slv_array_ser(cblk_cc_mfb_meta_arr),
            CC_MFB_SOF          => CC_MFB_SOF,
            CC_MFB_EOF          => CC_MFB_EOF,
            CC_MFB_SOF_POS      => CC_MFB_SOF_POS,
            CC_MFB_EOF_POS      => CC_MFB_EOF_POS,
            CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY,
            CC_MFB_DST_RDY      => CC_MFB_DST_RDY,
            -- CQ stream
            CQ_MFB_DATA         => CQ_MFB_DATA,
            CQ_MFB_META         => cblk_cq_mfb_meta,
            CQ_MFB_SOF          => CQ_MFB_SOF,
            CQ_MFB_EOF          => CQ_MFB_EOF,
            CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS,
            CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS,
            CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY,
            CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY
        );

        cblk_cq_mfb_meta_arr <= slv_array_deser(cblk_cq_mfb_meta, CQ_MFB_REGIONS);
        cblk_rc_mfb_meta_arr <= slv_array_deser(cblk_rc_mfb_meta, RC_MFB_REGIONS);
        cc_mfb_meta_arr      <= slv_array_deser(CC_MFB_META, CC_MFB_REGIONS);
        rq_mfb_meta_arr      <= slv_array_deser(RQ_MFB_META, RQ_MFB_REGIONS);

        cq_mfb_meta_g: for i in 0 to CQ_MFB_REGIONS-1 generate
            cq_mfb_meta_arr(i)(PCIE_CQ_META_HEADER)        <= cblk_cq_mfb_meta_arr(i)(PCIE_CQ_META_HEADER);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_PREFIX)        <= cblk_cq_mfb_meta_arr(i)(PCIE_CQ_META_PREFIX);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_BAR)           <= cblk_cq_mfb_meta_arr(i)(PCIE_CQ_META_BAR);
            cq_mfb_meta_arr(i)(PCIE_CQ_META_FBE)           <= (others => '0');
            cq_mfb_meta_arr(i)(PCIE_CQ_META_LBE)           <= (others => '0');
            cq_mfb_meta_arr(i)(PCIE_CQ_META_TPH_PRESENT_O) <= '0';
            cq_mfb_meta_arr(i)(PCIE_CQ_META_TPH_TYPE)      <= (others => '0');
            cq_mfb_meta_arr(i)(PCIE_CQ_META_TPH_ST_TAG)    <= (others => '0');
        end generate;

        rc_mfb_meta_g: for i in 0 to RC_MFB_REGIONS-1 generate    
            rc_mfb_meta_arr(i)(PCIE_RC_META_HEADER) <= cblk_rc_mfb_meta_arr(i)(96-1 downto 0);
            rc_mfb_meta_arr(i)(PCIE_RC_META_PREFIX) <= cblk_rc_mfb_meta_arr(i)(128-1 downto 96);
        end generate;

        cc_mfb_meta_g: for i in 0 to CC_MFB_REGIONS-1 generate    
            cblk_cc_mfb_meta_arr(i)(96-1 downto 0)   <= cc_mfb_meta_arr(i)(PCIE_CC_META_HEADER);
            cblk_cc_mfb_meta_arr(i)(128-1 downto 96) <= cc_mfb_meta_arr(i)(PCIE_CC_META_PREFIX);
        end generate;

        rq_mfb_meta_g: for i in 0 to RQ_MFB_REGIONS-1 generate    
            cblk_rq_mfb_meta_arr(i)(PCIE_RQ_META_HEADER) <= rq_mfb_meta_arr(i)(PCIE_RQ_META_HEADER);
            cblk_rq_mfb_meta_arr(i)(PCIE_RQ_META_PREFIX) <= rq_mfb_meta_arr(i)(PCIE_RQ_META_PREFIX);
        end generate;

        CQ_MFB_META <= slv_array_ser(cq_mfb_meta_arr);
        RC_MFB_META <= slv_array_ser(rc_mfb_meta_arr);
    end generate;

end architecture;
