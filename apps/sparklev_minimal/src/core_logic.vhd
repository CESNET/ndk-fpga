-- core_logic.vhd: Common top level architecture
-- Copyright 2025 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
--
-- SPDX-License-Identifier: CERN-OHL-P-2.0

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
-- use ieee.fixed_pkg.all;

use work.combo_const.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;
use work.mi_addr_space_pack.all;

use unisim.vcomponents.MMCME4_BASE;
use unisim.vcomponents.IBUFDS;
use unisim.vcomponents.BUFG;

entity CORE_LOGIC is
    generic (
        DEVICE : string := "ULTRASCALE";
        -- System clock period in ns
        -- PCIE clock period in ns
        SYSCLK_PERIOD   : real    := 10.0;
        -- Settings of the MMCM
        -- Multiply factor of main clock (Xilinx: 2-64)
        PLL_MULT_F      : real    := 12.0;
        -- Division factor of main clock (Xilinx: 1-106)
        PLL_MASTER_DIV  : natural := 3;
        -- Output clock dividers (Xilinx: 1-128)
        PLL_OUT0_DIV_F  : real    := 3.0;
        PLL_OUT1_DIV    : natural := 4;
        PLL_OUT2_DIV    : natural := 6;
        PLL_OUT3_DIV    : natural := 12;

        -- Number of PCIe connectors present on board
        PCIE_CONS               : natural := 1;
        -- Number of PCIe lanes per connector
        PCIE_LANES              : natural := 16;
        -- Number of instantiated PCIe endpoints
        PCIE_ENDPOINTS          : natural := 1;
        -- Connected PCIe endpoint type: P_TILE, R_TILE, USP
        PCIE_ENDPOINT_TYPE      : string  := "R_TILE";
        -- Connected PCIe endpoint mode: 0 = 1x16 lanes, 1 = 2x8 lanes
        PCIE_ENDPOINT_MODE      : natural := 0;

        -- Number of DMA channels per DMA module
        C2H_DMA_CHANNELS         : natural := 4;
        H2C_DMA_CHANNELS         : natural := 4;

        -- Amount of status LEDs to the Top-Level FPGA design
        STATUS_LEDS             : natural := 2;
        -- Width of MISC signal between Top-Level FPGA design and CORE_LOGIC
        MISC_IN_WIDTH           : natural := 0;
        -- Width of MISC signal between CORE_LOGIC and Top-Level FPGA design
        MISC_OUT_WIDTH          : natural := 0
    );
    port (
        SYSCLK                  : in    std_logic;
        SYSRST                  : in    std_logic;

        HBM_REFCLK_P : in std_logic;
        HBM_REFCLK_N : in std_logic;

        -- PCIe interface
        PCIE_SYSCLK_P           : in    std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
        PCIE_SYSCLK_N           : in    std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
        PCIE_SYSRST_N           : in    std_logic_vector(PCIE_CONS-1 downto 0);
        PCIE_RX_P               : in    std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_RX_N               : in    std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_TX_P               : out   std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_TX_N               : out   std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);

        STATUS_LEDS             : out std_logic_vector(STATUS_LEDS-1 downto 0);

        BOOT_MI_CLK             : out std_logic;
        BOOT_MI_RESET           : out std_logic;
        BOOT_MI_DWR             : out std_logic_vector(31 downto 0);
        BOOT_MI_ADDR            : out std_logic_vector(31 downto 0);
        BOOT_MI_RD              : out std_logic;
        BOOT_MI_WR              : out std_logic;
        BOOT_MI_BE              : out std_logic_vector(3 downto 0);
        BOOT_MI_DRD             : in  std_logic_vector(31 downto 0) := (others => '0');
        BOOT_MI_ARDY            : in  std_logic := '0';
        BOOT_MI_DRDY            : in  std_logic := '0';

        -- =========================================================================
        -- MISC SIGNALS (the clock signal is not defined)
        -- =========================================================================
        HBM_CATTRIP             : in    std_logic;
        -- Optional signal for MISC connection from Top-Level FPGA design to CORE_LOGIC.
        MISC_IN                 : in    std_logic_vector(MISC_IN_WIDTH-1 downto 0) := (others => '0');
        -- Optional signal for MISC connection from CORE_LOGIC to Top-Level FPGA design.
        MISC_OUT                : out   std_logic_vector(MISC_OUT_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of CORE_LOGIC is
    constant HEARTBEAT_CNT_W : natural := 27;
    constant CLK_COUNT       : natural := 3;
    constant DMA_STREAMS     : natural := PCIE_ENDPOINTS;
    constant PCIE_MPS        : natural := 256;
    constant PCIE_MRRS       : natural := 512;
    constant IS_USP_PCIE_EP : boolean := (PCIE_ENDPOINT_TYPE = "USP" or PCIE_ENDPOINT_TYPE = "USP_PCIE4" or PCIE_ENDPOINT_TYPE = "USP_PCIE4C");
    constant RESET_WIDTH       : natural := 10;
    constant FPGA_ID_WIDTH : natural := tsel(DEVICE = "ULTRASCALE", 96, 64);
    constant MI_DATA_WIDTH      : integer := 32;
    constant MI_ADDR_WIDTH      : integer := 32;
    constant DMA_HDR_META_WIDTH     : integer := 12;

    function pcie_mfb_regions_calc_f (PCIE_DIR : string) return natural is
        variable pcie_mfb_regions : natural;
    begin
        pcie_mfb_regions := 0;

        if (PCIE_ENDPOINT_MODE = 0) then    -- x16
            pcie_mfb_regions := 2;          -- 1x512b
        elsif (PCIE_ENDPOINT_MODE = 1) then -- x8x8
            pcie_mfb_regions := 2;          -- 2x512b
        elsif (PCIE_ENDPOINT_MODE = 2) then -- x8
            pcie_mfb_regions := 1;          -- 1x256b
        end if;
        if (PCIE_DIR = "RC") then           -- USP RC support up to 4 TLP in word
            pcie_mfb_regions := pcie_mfb_regions*2;
        end if;

        return pcie_mfb_regions;
    end function;

    constant DMA_MFB_REGIONS     : natural := 1;
    constant DMA_MFB_REGION_SIZE : natural := ????;
    constant DMA_MFB_BLOCK_SIZE   : natural := 8;  -- Number of items in block
    constant DMA_MFB_ITEM_WIDTH   : natural := 8;  -- Width of one item in bits

    -- DMA MFB RQ parameters
    constant PCIE_RQ_MFB_REGIONS       : natural := pcie_mfb_regions_calc_f("RQ");
    constant PCIE_RQ_MFB_REGION_SIZE   : natural := 1;
    constant PCIE_RQ_MFB_BLOCK_SIZE    : natural := 8;
    constant PCIE_RQ_MFB_ITEM_WIDTH    : natural := 32;

    -- DMA MFB RC parameters
    constant PCIE_RC_MFB_REGIONS     : natural := pcie_mfb_regions_calc_f("RC");
    constant PCIE_RC_MFB_REGION_SIZE : natural := 1;
    constant PCIE_RC_MFB_BLOCK_SIZE  : natural := 4;
    constant PCIE_RC_MFB_ITEM_WIDTH  : natural := 32;

    constant PCIE_CQ_MFB_REGIONS     : natural := pcie_mfb_regions_calc_f("CQ");
    constant PCIE_CQ_MFB_REGION_SIZE : natural := PCIE_RQ_MFB_REGION_SIZE;
    constant PCIE_CQ_MFB_BLOCK_SIZE  : natural := PCIE_RQ_MFB_BLOCK_SIZE;
    constant PCIE_CQ_MFB_ITEM_WIDTH  : natural := PCIE_RQ_MFB_ITEM_WIDTH;

    constant PCIE_CC_MFB_REGIONS     : natural := pcie_mfb_regions_calc_f("CC");
    constant PCIE_CC_MFB_REGION_SIZE : natural := PCIE_CQ_MFB_REGION_SIZE;
    -- this remains the same as RQ interface beacuse on straddling option enabled, the core supports
    -- only two TLPs on CC interface
    constant PCIE_CC_MFB_BLOCK_SIZE  : natural := PCIE_CQ_MFB_BLOCK_SIZE;
    constant PCIE_CC_MFB_ITEM_WIDTH  : natural := PCIE_CQ_MFB_ITEM_WIDTH;

    signal heartbeat_cnt                 : unsigned(HEARTBEAT_CNT_W-1 downto 0);
     
    signal pll_locked                    : std_logic;
    signal clkfbout                      : std_logic;
    signal mmcm_usr_clks                 : std_logic_vector(7-1 downto 0);

    signal global_reset                  : std_logic;
    signal rst_vector                    : std_logic_vector(CLK_COUNT*RESET_WIDTH-1 downto 0);

    constant MI_CLK_IDX   : natural := 2;
    constant BOOT_CLK_IDX : natural := 1;
    constant APP_CLK_IDX  : natural := 0;

    signal usr_clks                      : std_logic_vector(CLK_COUNT-1 downto 0);
    signal pcie_clks                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal clk_mi                        : std_logic;
    signal clk_dma                       : std_logic;
    signal clk_dma_x2                    : std_logic;
    signal clk_app                       : std_logic;

    signal usr_rsts                      : slv_array_t(CLK_COUNT -1 downto 0)(RESET_WIDTH -1 downto 0);
    signal pcie_rsts                     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal rst_mi                        : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_dma                       : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_dma_x2                    : std_logic_vector(RESET_WIDTH-1 downto 0);
    signal rst_app                       : std_logic_vector(RESET_WIDTH-1 downto 0);

    signal pcie_link_up                  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal app_pcie_link_up              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');

    signal fpga_id                       : std_logic_vector(FPGA_ID_WIDTH-1 downto 0);
    signal fpga_id_vld                   : std_logic := '0';
    signal pcie_fpga_id                  : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(FPGA_ID_WIDTH-1 downto 0);

    -- MI32 interface signals
    signal mi_dwr                        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal mi_addr                       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal mi_be                         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal mi_rd                         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_wr                         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_drd                        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal mi_ardy                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_drdy                       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    -- MI interfaces for individual components (clocked at clk_mi)
    signal mi_adc_dwr                    : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_adc_addr                   : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_adc_be                     : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32/8-1 downto 0);
    signal mi_adc_rd                     : std_logic_vector(MI_ADC_PORTS-1 downto 0);
    signal mi_adc_wr                     : std_logic_vector(MI_ADC_PORTS-1 downto 0);
    signal mi_adc_drd                    : slv_array_t     (MI_ADC_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_adc_ardy                   : std_logic_vector(MI_ADC_PORTS-1 downto 0);
    signal mi_adc_drdy                   : std_logic_vector(MI_ADC_PORTS-1 downto 0);

    signal dma_mi_dwr                    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal dma_mi_addr                   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal dma_mi_be                     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal dma_mi_rd                     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_mi_wr                     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_mi_drd                    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal dma_mi_ardy                   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dma_mi_drdy                   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_rq_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE*PCIE_RQ_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_rq_mfb_meta               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
    signal pcie_rq_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RQ_MFB_REGIONS-1 downto 0);
    signal pcie_rq_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RQ_MFB_REGIONS-1 downto 0);
    signal pcie_rq_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1,log2(PCIE_RQ_MFB_REGION_SIZE))-1 downto 0);
    signal pcie_rq_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1,log2(PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal pcie_rq_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal pcie_rq_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal pcie_rc_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RC_MFB_REGIONS*PCIE_RC_MFB_REGION_SIZE*PCIE_RC_MFB_BLOCK_SIZE*PCIE_RC_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_rc_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RC_MFB_REGIONS-1 downto 0);
    signal pcie_rc_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RC_MFB_REGIONS-1 downto 0);
    signal pcie_rc_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RC_MFB_REGIONS*max(1,log2(PCIE_RC_MFB_REGION_SIZE))-1 downto 0);
    signal pcie_rc_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_RC_MFB_REGIONS*max(1,log2(PCIE_RC_MFB_REGION_SIZE*PCIE_RC_MFB_BLOCK_SIZE))-1 downto 0);
    signal pcie_rc_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal pcie_rc_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal pcie_cq_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE*PCIE_CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_cq_mfb_meta               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
    signal pcie_cq_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CQ_MFB_REGIONS-1 downto 0);
    signal pcie_cq_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CQ_MFB_REGIONS-1 downto 0);
    signal pcie_cq_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1,log2(PCIE_CQ_MFB_REGION_SIZE))-1 downto 0);
    signal pcie_cq_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1,log2(PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal pcie_cq_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal pcie_cq_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal pcie_cc_mfb_data               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CC_MFB_REGIONS*PCIE_CC_MFB_REGION_SIZE*PCIE_CC_MFB_BLOCK_SIZE*PCIE_CC_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_cc_mfb_meta               : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CC_MFB_REGIONS*PCIE_CC_META_WIDTH -1 downto 0);
    signal pcie_cc_mfb_sof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CC_MFB_REGIONS-1 downto 0);
    signal pcie_cc_mfb_eof                : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CC_MFB_REGIONS-1 downto 0);
    signal pcie_cc_mfb_sof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CC_MFB_REGIONS*max(1,log2(PCIE_CC_MFB_REGION_SIZE))-1 downto 0);
    signal pcie_cc_mfb_eof_pos            : slv_array_t(DMA_ENDPOINTS-1 downto 0)(PCIE_CC_MFB_REGIONS*max(1,log2(PCIE_CC_MFB_REGION_SIZE*PCIE_CC_MFB_BLOCK_SIZE))-1 downto 0);
    signal pcie_cc_mfb_src_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);
    signal pcie_cc_mfb_dst_rdy            : std_logic_vector(DMA_ENDPOINTS-1 downto 0);

    signal c2h_dma_mfb_meta_hdr_meta    : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal c2h_dma_mfb_meta_chan        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*log2(C2H_DMA_CHANNELS)-1 downto 0);

    signal c2h_dma_mfb_data           : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal c2h_dma_mfb_sof            : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS-1 downto 0);
    signal c2h_dma_mfb_eof            : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS-1 downto 0);
    signal c2h_dma_mfb_sof_pos        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE))-1 downto 0);
    signal c2h_dma_mfb_eof_pos        : std_logic_vector(DMA_STREAMS*DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE))-1 downto 0);
    signal c2h_dma_mfb_src_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal c2h_dma_mfb_dst_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal h2c_dma_mfb_meta_size            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(DMA_PKT_SIZE_MAX+1)-1 downto 0);
    signal h2c_dma_mfb_meta_hdr_meta       : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal h2c_dma_mfb_meta_chan        : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(H2C_DMA_CHANNELS)-1 downto 0);

    signal h2c_dma_mfb_data           : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal h2c_dma_mfb_sof            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
    signal h2c_dma_mfb_eof            : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS-1 downto 0);
    signal h2c_dma_mfb_sof_pos        : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE))-1 downto 0);
    signal h2c_dma_mfb_eof_pos        : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1,log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE))-1 downto 0);
    signal h2c_dma_mfb_src_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal h2c_dma_mfb_dst_rdy        : std_logic_vector(DMA_STREAMS -1 downto 0);

    constant HBM_DATA_WIDTH  : natural := 256;
    constant HBM_ADDR_WIDTH  : natural := 34;
    constant HBM_BURST_WIDTH : natural := 2;
    constant HBM_ID_WIDTH    : natural := 6;
    constant HBM_LEN_WIDTH   : natural := 4;
    constant HBM_SIZE_WIDTH  : natural := 3;
    constant HBM_RESP_WIDTH  : natural := 2;

    signal hbm_refclk_ibuf  : std_logic;
    signal hbm_refclk_bufg  : std_logic;
    signal hbm_refclk       : std_logic;
    signal hbm_rst          : std_logic;
    signal hbm_axi_aclk     : std_logic_vector(HBM_PORTS -1 downto 0);
    signal hbm_axi_areset_n : std_logic_vector(HBM_PORTS -1 downto 0);
    signal hbm_ready        : std_logic_vector(1 downto 0);
    signal hbm_cattrip_int  : std_logic_vector(1 downto 0);

    signal app_hbm_clk : std_logic_vector(HBM_PORTS -1 downto 0);
    signal app_hbm_rst : std_logic_vector(HBM_PORTS -1 downto 0);

    signal hbm_axi_araddr       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_arburst      : slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    signal hbm_axi_arid         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_arlen        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    signal hbm_axi_arsize       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_arvalid      : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_arready      : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_axi_rdata        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_rdata_parity : slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_rid          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_rlast        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rresp        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_rvalid       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rready       : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_axi_awaddr       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_awburst      : slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    signal hbm_axi_awid         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_awlen        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    signal hbm_axi_awsize       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_awvalid      : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_awready      : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_axi_wdata        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_wdata_parity : slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_wlast        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wstrb        : slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_wvalid       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wready       : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_axi_bid          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_bresp        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_bvalid       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bready       : std_logic_vector(HBM_PORTS-1 downto 0);

    component hbm_ip
    port (
        HBM_REF_CLK_0 : IN STD_LOGIC;
        HBM_REF_CLK_1 : IN STD_LOGIC;
        AXI_00_ACLK : IN STD_LOGIC;
        AXI_00_ARESET_N : IN STD_LOGIC;
        AXI_00_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_00_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_00_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_00_ARVALID : IN STD_LOGIC;
        AXI_00_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_00_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_00_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_00_AWVALID : IN STD_LOGIC;
        AXI_00_RREADY : IN STD_LOGIC;
        AXI_00_BREADY : IN STD_LOGIC;
        AXI_00_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_00_WLAST : IN STD_LOGIC;
        AXI_00_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_00_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_00_WVALID : IN STD_LOGIC;
        AXI_01_ACLK : IN STD_LOGIC;
        AXI_01_ARESET_N : IN STD_LOGIC;
        AXI_01_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_01_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_01_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_01_ARVALID : IN STD_LOGIC;
        AXI_01_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_01_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_01_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_01_AWVALID : IN STD_LOGIC;
        AXI_01_RREADY : IN STD_LOGIC;
        AXI_01_BREADY : IN STD_LOGIC;
        AXI_01_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_01_WLAST : IN STD_LOGIC;
        AXI_01_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_01_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_01_WVALID : IN STD_LOGIC;
        AXI_02_ACLK : IN STD_LOGIC;
        AXI_02_ARESET_N : IN STD_LOGIC;
        AXI_02_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_02_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_02_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_02_ARVALID : IN STD_LOGIC;
        AXI_02_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_02_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_02_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_02_AWVALID : IN STD_LOGIC;
        AXI_02_RREADY : IN STD_LOGIC;
        AXI_02_BREADY : IN STD_LOGIC;
        AXI_02_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_02_WLAST : IN STD_LOGIC;
        AXI_02_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_02_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_02_WVALID : IN STD_LOGIC;
        AXI_03_ACLK : IN STD_LOGIC;
        AXI_03_ARESET_N : IN STD_LOGIC;
        AXI_03_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_03_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_03_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_03_ARVALID : IN STD_LOGIC;
        AXI_03_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_03_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_03_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_03_AWVALID : IN STD_LOGIC;
        AXI_03_RREADY : IN STD_LOGIC;
        AXI_03_BREADY : IN STD_LOGIC;
        AXI_03_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_03_WLAST : IN STD_LOGIC;
        AXI_03_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_03_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_03_WVALID : IN STD_LOGIC;
        AXI_04_ACLK : IN STD_LOGIC;
        AXI_04_ARESET_N : IN STD_LOGIC;
        AXI_04_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_04_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_04_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_04_ARVALID : IN STD_LOGIC;
        AXI_04_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_04_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_04_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_04_AWVALID : IN STD_LOGIC;
        AXI_04_RREADY : IN STD_LOGIC;
        AXI_04_BREADY : IN STD_LOGIC;
        AXI_04_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_04_WLAST : IN STD_LOGIC;
        AXI_04_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_04_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_04_WVALID : IN STD_LOGIC;
        AXI_05_ACLK : IN STD_LOGIC;
        AXI_05_ARESET_N : IN STD_LOGIC;
        AXI_05_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_05_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_05_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_05_ARVALID : IN STD_LOGIC;
        AXI_05_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_05_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_05_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_05_AWVALID : IN STD_LOGIC;
        AXI_05_RREADY : IN STD_LOGIC;
        AXI_05_BREADY : IN STD_LOGIC;
        AXI_05_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_05_WLAST : IN STD_LOGIC;
        AXI_05_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_05_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_05_WVALID : IN STD_LOGIC;
        AXI_06_ACLK : IN STD_LOGIC;
        AXI_06_ARESET_N : IN STD_LOGIC;
        AXI_06_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_06_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_06_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_06_ARVALID : IN STD_LOGIC;
        AXI_06_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_06_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_06_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_06_AWVALID : IN STD_LOGIC;
        AXI_06_RREADY : IN STD_LOGIC;
        AXI_06_BREADY : IN STD_LOGIC;
        AXI_06_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_06_WLAST : IN STD_LOGIC;
        AXI_06_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_06_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_06_WVALID : IN STD_LOGIC;
        AXI_07_ACLK : IN STD_LOGIC;
        AXI_07_ARESET_N : IN STD_LOGIC;
        AXI_07_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_07_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_07_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_07_ARVALID : IN STD_LOGIC;
        AXI_07_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_07_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_07_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_07_AWVALID : IN STD_LOGIC;
        AXI_07_RREADY : IN STD_LOGIC;
        AXI_07_BREADY : IN STD_LOGIC;
        AXI_07_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_07_WLAST : IN STD_LOGIC;
        AXI_07_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_07_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_07_WVALID : IN STD_LOGIC;
        AXI_08_ACLK : IN STD_LOGIC;
        AXI_08_ARESET_N : IN STD_LOGIC;
        AXI_08_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_08_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_08_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_08_ARVALID : IN STD_LOGIC;
        AXI_08_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_08_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_08_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_08_AWVALID : IN STD_LOGIC;
        AXI_08_RREADY : IN STD_LOGIC;
        AXI_08_BREADY : IN STD_LOGIC;
        AXI_08_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_08_WLAST : IN STD_LOGIC;
        AXI_08_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_08_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_08_WVALID : IN STD_LOGIC;
        AXI_09_ACLK : IN STD_LOGIC;
        AXI_09_ARESET_N : IN STD_LOGIC;
        AXI_09_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_09_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_09_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_09_ARVALID : IN STD_LOGIC;
        AXI_09_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_09_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_09_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_09_AWVALID : IN STD_LOGIC;
        AXI_09_RREADY : IN STD_LOGIC;
        AXI_09_BREADY : IN STD_LOGIC;
        AXI_09_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_09_WLAST : IN STD_LOGIC;
        AXI_09_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_09_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_09_WVALID : IN STD_LOGIC;
        AXI_10_ACLK : IN STD_LOGIC;
        AXI_10_ARESET_N : IN STD_LOGIC;
        AXI_10_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_10_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_10_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_10_ARVALID : IN STD_LOGIC;
        AXI_10_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_10_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_10_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_10_AWVALID : IN STD_LOGIC;
        AXI_10_RREADY : IN STD_LOGIC;
        AXI_10_BREADY : IN STD_LOGIC;
        AXI_10_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_10_WLAST : IN STD_LOGIC;
        AXI_10_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_10_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_10_WVALID : IN STD_LOGIC;
        AXI_11_ACLK : IN STD_LOGIC;
        AXI_11_ARESET_N : IN STD_LOGIC;
        AXI_11_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_11_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_11_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_11_ARVALID : IN STD_LOGIC;
        AXI_11_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_11_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_11_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_11_AWVALID : IN STD_LOGIC;
        AXI_11_RREADY : IN STD_LOGIC;
        AXI_11_BREADY : IN STD_LOGIC;
        AXI_11_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_11_WLAST : IN STD_LOGIC;
        AXI_11_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_11_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_11_WVALID : IN STD_LOGIC;
        AXI_12_ACLK : IN STD_LOGIC;
        AXI_12_ARESET_N : IN STD_LOGIC;
        AXI_12_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_12_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_12_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_12_ARVALID : IN STD_LOGIC;
        AXI_12_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_12_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_12_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_12_AWVALID : IN STD_LOGIC;
        AXI_12_RREADY : IN STD_LOGIC;
        AXI_12_BREADY : IN STD_LOGIC;
        AXI_12_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_12_WLAST : IN STD_LOGIC;
        AXI_12_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_12_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_12_WVALID : IN STD_LOGIC;
        AXI_13_ACLK : IN STD_LOGIC;
        AXI_13_ARESET_N : IN STD_LOGIC;
        AXI_13_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_13_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_13_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_13_ARVALID : IN STD_LOGIC;
        AXI_13_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_13_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_13_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_13_AWVALID : IN STD_LOGIC;
        AXI_13_RREADY : IN STD_LOGIC;
        AXI_13_BREADY : IN STD_LOGIC;
        AXI_13_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_13_WLAST : IN STD_LOGIC;
        AXI_13_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_13_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_13_WVALID : IN STD_LOGIC;
        AXI_14_ACLK : IN STD_LOGIC;
        AXI_14_ARESET_N : IN STD_LOGIC;
        AXI_14_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_14_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_14_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_14_ARVALID : IN STD_LOGIC;
        AXI_14_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_14_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_14_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_14_AWVALID : IN STD_LOGIC;
        AXI_14_RREADY : IN STD_LOGIC;
        AXI_14_BREADY : IN STD_LOGIC;
        AXI_14_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_14_WLAST : IN STD_LOGIC;
        AXI_14_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_14_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_14_WVALID : IN STD_LOGIC;
        AXI_15_ACLK : IN STD_LOGIC;
        AXI_15_ARESET_N : IN STD_LOGIC;
        AXI_15_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_15_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_15_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_15_ARVALID : IN STD_LOGIC;
        AXI_15_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_15_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_15_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_15_AWVALID : IN STD_LOGIC;
        AXI_15_RREADY : IN STD_LOGIC;
        AXI_15_BREADY : IN STD_LOGIC;
        AXI_15_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_15_WLAST : IN STD_LOGIC;
        AXI_15_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_15_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_15_WVALID : IN STD_LOGIC;
        AXI_16_ACLK : IN STD_LOGIC;
        AXI_16_ARESET_N : IN STD_LOGIC;
        AXI_16_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_16_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_16_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_16_ARVALID : IN STD_LOGIC;
        AXI_16_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_16_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_16_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_16_AWVALID : IN STD_LOGIC;
        AXI_16_RREADY : IN STD_LOGIC;
        AXI_16_BREADY : IN STD_LOGIC;
        AXI_16_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_16_WLAST : IN STD_LOGIC;
        AXI_16_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_16_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_16_WVALID : IN STD_LOGIC;
        AXI_17_ACLK : IN STD_LOGIC;
        AXI_17_ARESET_N : IN STD_LOGIC;
        AXI_17_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_17_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_17_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_17_ARVALID : IN STD_LOGIC;
        AXI_17_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_17_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_17_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_17_AWVALID : IN STD_LOGIC;
        AXI_17_RREADY : IN STD_LOGIC;
        AXI_17_BREADY : IN STD_LOGIC;
        AXI_17_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_17_WLAST : IN STD_LOGIC;
        AXI_17_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_17_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_17_WVALID : IN STD_LOGIC;
        AXI_18_ACLK : IN STD_LOGIC;
        AXI_18_ARESET_N : IN STD_LOGIC;
        AXI_18_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_18_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_18_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_18_ARVALID : IN STD_LOGIC;
        AXI_18_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_18_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_18_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_18_AWVALID : IN STD_LOGIC;
        AXI_18_RREADY : IN STD_LOGIC;
        AXI_18_BREADY : IN STD_LOGIC;
        AXI_18_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_18_WLAST : IN STD_LOGIC;
        AXI_18_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_18_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_18_WVALID : IN STD_LOGIC;
        AXI_19_ACLK : IN STD_LOGIC;
        AXI_19_ARESET_N : IN STD_LOGIC;
        AXI_19_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_19_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_19_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_19_ARVALID : IN STD_LOGIC;
        AXI_19_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_19_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_19_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_19_AWVALID : IN STD_LOGIC;
        AXI_19_RREADY : IN STD_LOGIC;
        AXI_19_BREADY : IN STD_LOGIC;
        AXI_19_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_19_WLAST : IN STD_LOGIC;
        AXI_19_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_19_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_19_WVALID : IN STD_LOGIC;
        AXI_20_ACLK : IN STD_LOGIC;
        AXI_20_ARESET_N : IN STD_LOGIC;
        AXI_20_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_20_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_20_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_20_ARVALID : IN STD_LOGIC;
        AXI_20_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_20_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_20_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_20_AWVALID : IN STD_LOGIC;
        AXI_20_RREADY : IN STD_LOGIC;
        AXI_20_BREADY : IN STD_LOGIC;
        AXI_20_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_20_WLAST : IN STD_LOGIC;
        AXI_20_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_20_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_20_WVALID : IN STD_LOGIC;
        AXI_21_ACLK : IN STD_LOGIC;
        AXI_21_ARESET_N : IN STD_LOGIC;
        AXI_21_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_21_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_21_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_21_ARVALID : IN STD_LOGIC;
        AXI_21_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_21_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_21_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_21_AWVALID : IN STD_LOGIC;
        AXI_21_RREADY : IN STD_LOGIC;
        AXI_21_BREADY : IN STD_LOGIC;
        AXI_21_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_21_WLAST : IN STD_LOGIC;
        AXI_21_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_21_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_21_WVALID : IN STD_LOGIC;
        AXI_22_ACLK : IN STD_LOGIC;
        AXI_22_ARESET_N : IN STD_LOGIC;
        AXI_22_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_22_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_22_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_22_ARVALID : IN STD_LOGIC;
        AXI_22_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_22_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_22_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_22_AWVALID : IN STD_LOGIC;
        AXI_22_RREADY : IN STD_LOGIC;
        AXI_22_BREADY : IN STD_LOGIC;
        AXI_22_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_22_WLAST : IN STD_LOGIC;
        AXI_22_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_22_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_22_WVALID : IN STD_LOGIC;
        AXI_23_ACLK : IN STD_LOGIC;
        AXI_23_ARESET_N : IN STD_LOGIC;
        AXI_23_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_23_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_23_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_23_ARVALID : IN STD_LOGIC;
        AXI_23_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_23_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_23_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_23_AWVALID : IN STD_LOGIC;
        AXI_23_RREADY : IN STD_LOGIC;
        AXI_23_BREADY : IN STD_LOGIC;
        AXI_23_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_23_WLAST : IN STD_LOGIC;
        AXI_23_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_23_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_23_WVALID : IN STD_LOGIC;
        AXI_24_ACLK : IN STD_LOGIC;
        AXI_24_ARESET_N : IN STD_LOGIC;
        AXI_24_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_24_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_24_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_24_ARVALID : IN STD_LOGIC;
        AXI_24_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_24_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_24_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_24_AWVALID : IN STD_LOGIC;
        AXI_24_RREADY : IN STD_LOGIC;
        AXI_24_BREADY : IN STD_LOGIC;
        AXI_24_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_24_WLAST : IN STD_LOGIC;
        AXI_24_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_24_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_24_WVALID : IN STD_LOGIC;
        AXI_25_ACLK : IN STD_LOGIC;
        AXI_25_ARESET_N : IN STD_LOGIC;
        AXI_25_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_25_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_25_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_25_ARVALID : IN STD_LOGIC;
        AXI_25_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_25_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_25_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_25_AWVALID : IN STD_LOGIC;
        AXI_25_RREADY : IN STD_LOGIC;
        AXI_25_BREADY : IN STD_LOGIC;
        AXI_25_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_25_WLAST : IN STD_LOGIC;
        AXI_25_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_25_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_25_WVALID : IN STD_LOGIC;
        AXI_26_ACLK : IN STD_LOGIC;
        AXI_26_ARESET_N : IN STD_LOGIC;
        AXI_26_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_26_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_26_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_26_ARVALID : IN STD_LOGIC;
        AXI_26_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_26_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_26_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_26_AWVALID : IN STD_LOGIC;
        AXI_26_RREADY : IN STD_LOGIC;
        AXI_26_BREADY : IN STD_LOGIC;
        AXI_26_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_26_WLAST : IN STD_LOGIC;
        AXI_26_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_26_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_26_WVALID : IN STD_LOGIC;
        AXI_27_ACLK : IN STD_LOGIC;
        AXI_27_ARESET_N : IN STD_LOGIC;
        AXI_27_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_27_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_27_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_27_ARVALID : IN STD_LOGIC;
        AXI_27_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_27_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_27_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_27_AWVALID : IN STD_LOGIC;
        AXI_27_RREADY : IN STD_LOGIC;
        AXI_27_BREADY : IN STD_LOGIC;
        AXI_27_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_27_WLAST : IN STD_LOGIC;
        AXI_27_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_27_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_27_WVALID : IN STD_LOGIC;
        AXI_28_ACLK : IN STD_LOGIC;
        AXI_28_ARESET_N : IN STD_LOGIC;
        AXI_28_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_28_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_28_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_28_ARVALID : IN STD_LOGIC;
        AXI_28_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_28_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_28_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_28_AWVALID : IN STD_LOGIC;
        AXI_28_RREADY : IN STD_LOGIC;
        AXI_28_BREADY : IN STD_LOGIC;
        AXI_28_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_28_WLAST : IN STD_LOGIC;
        AXI_28_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_28_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_28_WVALID : IN STD_LOGIC;
        AXI_29_ACLK : IN STD_LOGIC;
        AXI_29_ARESET_N : IN STD_LOGIC;
        AXI_29_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_29_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_29_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_29_ARVALID : IN STD_LOGIC;
        AXI_29_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_29_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_29_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_29_AWVALID : IN STD_LOGIC;
        AXI_29_RREADY : IN STD_LOGIC;
        AXI_29_BREADY : IN STD_LOGIC;
        AXI_29_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_29_WLAST : IN STD_LOGIC;
        AXI_29_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_29_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_29_WVALID : IN STD_LOGIC;
        AXI_30_ACLK : IN STD_LOGIC;
        AXI_30_ARESET_N : IN STD_LOGIC;
        AXI_30_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_30_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_30_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_30_ARVALID : IN STD_LOGIC;
        AXI_30_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_30_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_30_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_30_AWVALID : IN STD_LOGIC;
        AXI_30_RREADY : IN STD_LOGIC;
        AXI_30_BREADY : IN STD_LOGIC;
        AXI_30_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_30_WLAST : IN STD_LOGIC;
        AXI_30_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_30_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_30_WVALID : IN STD_LOGIC;
        AXI_31_ACLK : IN STD_LOGIC;
        AXI_31_ARESET_N : IN STD_LOGIC;
        AXI_31_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_31_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_31_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_31_ARVALID : IN STD_LOGIC;
        AXI_31_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_31_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_31_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_31_AWVALID : IN STD_LOGIC;
        AXI_31_RREADY : IN STD_LOGIC;
        AXI_31_BREADY : IN STD_LOGIC;
        AXI_31_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_31_WLAST : IN STD_LOGIC;
        AXI_31_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_31_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_31_WVALID : IN STD_LOGIC;
        APB_0_PCLK : IN STD_LOGIC;
        APB_0_PRESET_N : IN STD_LOGIC;
        APB_1_PCLK : IN STD_LOGIC;
        APB_1_PRESET_N : IN STD_LOGIC;
        AXI_00_ARREADY : OUT STD_LOGIC;
        AXI_00_AWREADY : OUT STD_LOGIC;
        AXI_00_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_00_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_00_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_RLAST : OUT STD_LOGIC;
        AXI_00_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_RVALID : OUT STD_LOGIC;
        AXI_00_WREADY : OUT STD_LOGIC;
        AXI_00_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_BVALID : OUT STD_LOGIC;
        AXI_01_ARREADY : OUT STD_LOGIC;
        AXI_01_AWREADY : OUT STD_LOGIC;
        AXI_01_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_01_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_01_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_RLAST : OUT STD_LOGIC;
        AXI_01_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_RVALID : OUT STD_LOGIC;
        AXI_01_WREADY : OUT STD_LOGIC;
        AXI_01_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_BVALID : OUT STD_LOGIC;
        AXI_02_ARREADY : OUT STD_LOGIC;
        AXI_02_AWREADY : OUT STD_LOGIC;
        AXI_02_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_02_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_02_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_RLAST : OUT STD_LOGIC;
        AXI_02_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_RVALID : OUT STD_LOGIC;
        AXI_02_WREADY : OUT STD_LOGIC;
        AXI_02_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_BVALID : OUT STD_LOGIC;
        AXI_03_ARREADY : OUT STD_LOGIC;
        AXI_03_AWREADY : OUT STD_LOGIC;
        AXI_03_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_03_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_03_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_RLAST : OUT STD_LOGIC;
        AXI_03_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_RVALID : OUT STD_LOGIC;
        AXI_03_WREADY : OUT STD_LOGIC;
        AXI_03_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_BVALID : OUT STD_LOGIC;
        AXI_04_ARREADY : OUT STD_LOGIC;
        AXI_04_AWREADY : OUT STD_LOGIC;
        AXI_04_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_04_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_04_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_RLAST : OUT STD_LOGIC;
        AXI_04_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_RVALID : OUT STD_LOGIC;
        AXI_04_WREADY : OUT STD_LOGIC;
        AXI_04_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_BVALID : OUT STD_LOGIC;
        AXI_05_ARREADY : OUT STD_LOGIC;
        AXI_05_AWREADY : OUT STD_LOGIC;
        AXI_05_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_05_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_05_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_RLAST : OUT STD_LOGIC;
        AXI_05_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_RVALID : OUT STD_LOGIC;
        AXI_05_WREADY : OUT STD_LOGIC;
        AXI_05_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_BVALID : OUT STD_LOGIC;
        AXI_06_ARREADY : OUT STD_LOGIC;
        AXI_06_AWREADY : OUT STD_LOGIC;
        AXI_06_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_06_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_06_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_RLAST : OUT STD_LOGIC;
        AXI_06_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_RVALID : OUT STD_LOGIC;
        AXI_06_WREADY : OUT STD_LOGIC;
        AXI_06_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_BVALID : OUT STD_LOGIC;
        AXI_07_ARREADY : OUT STD_LOGIC;
        AXI_07_AWREADY : OUT STD_LOGIC;
        AXI_07_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_07_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_07_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_RLAST : OUT STD_LOGIC;
        AXI_07_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_RVALID : OUT STD_LOGIC;
        AXI_07_WREADY : OUT STD_LOGIC;
        AXI_07_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_BVALID : OUT STD_LOGIC;
        AXI_08_ARREADY : OUT STD_LOGIC;
        AXI_08_AWREADY : OUT STD_LOGIC;
        AXI_08_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_08_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_08_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_RLAST : OUT STD_LOGIC;
        AXI_08_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_RVALID : OUT STD_LOGIC;
        AXI_08_WREADY : OUT STD_LOGIC;
        AXI_08_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_BVALID : OUT STD_LOGIC;
        AXI_09_ARREADY : OUT STD_LOGIC;
        AXI_09_AWREADY : OUT STD_LOGIC;
        AXI_09_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_09_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_09_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_RLAST : OUT STD_LOGIC;
        AXI_09_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_RVALID : OUT STD_LOGIC;
        AXI_09_WREADY : OUT STD_LOGIC;
        AXI_09_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_BVALID : OUT STD_LOGIC;
        AXI_10_ARREADY : OUT STD_LOGIC;
        AXI_10_AWREADY : OUT STD_LOGIC;
        AXI_10_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_10_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_10_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_RLAST : OUT STD_LOGIC;
        AXI_10_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_RVALID : OUT STD_LOGIC;
        AXI_10_WREADY : OUT STD_LOGIC;
        AXI_10_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_BVALID : OUT STD_LOGIC;
        AXI_11_ARREADY : OUT STD_LOGIC;
        AXI_11_AWREADY : OUT STD_LOGIC;
        AXI_11_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_11_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_11_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_RLAST : OUT STD_LOGIC;
        AXI_11_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_RVALID : OUT STD_LOGIC;
        AXI_11_WREADY : OUT STD_LOGIC;
        AXI_11_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_BVALID : OUT STD_LOGIC;
        AXI_12_ARREADY : OUT STD_LOGIC;
        AXI_12_AWREADY : OUT STD_LOGIC;
        AXI_12_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_12_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_12_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_RLAST : OUT STD_LOGIC;
        AXI_12_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_RVALID : OUT STD_LOGIC;
        AXI_12_WREADY : OUT STD_LOGIC;
        AXI_12_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_BVALID : OUT STD_LOGIC;
        AXI_13_ARREADY : OUT STD_LOGIC;
        AXI_13_AWREADY : OUT STD_LOGIC;
        AXI_13_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_13_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_13_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_RLAST : OUT STD_LOGIC;
        AXI_13_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_RVALID : OUT STD_LOGIC;
        AXI_13_WREADY : OUT STD_LOGIC;
        AXI_13_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_BVALID : OUT STD_LOGIC;
        AXI_14_ARREADY : OUT STD_LOGIC;
        AXI_14_AWREADY : OUT STD_LOGIC;
        AXI_14_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_14_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_14_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_RLAST : OUT STD_LOGIC;
        AXI_14_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_RVALID : OUT STD_LOGIC;
        AXI_14_WREADY : OUT STD_LOGIC;
        AXI_14_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_BVALID : OUT STD_LOGIC;
        AXI_15_ARREADY : OUT STD_LOGIC;
        AXI_15_AWREADY : OUT STD_LOGIC;
        AXI_15_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_15_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_15_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_RLAST : OUT STD_LOGIC;
        AXI_15_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_RVALID : OUT STD_LOGIC;
        AXI_15_WREADY : OUT STD_LOGIC;
        AXI_15_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_BVALID : OUT STD_LOGIC;
        AXI_16_ARREADY : OUT STD_LOGIC;
        AXI_16_AWREADY : OUT STD_LOGIC;
        AXI_16_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_16_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_16_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_RLAST : OUT STD_LOGIC;
        AXI_16_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_RVALID : OUT STD_LOGIC;
        AXI_16_WREADY : OUT STD_LOGIC;
        AXI_16_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_BVALID : OUT STD_LOGIC;
        AXI_17_ARREADY : OUT STD_LOGIC;
        AXI_17_AWREADY : OUT STD_LOGIC;
        AXI_17_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_17_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_17_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_RLAST : OUT STD_LOGIC;
        AXI_17_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_RVALID : OUT STD_LOGIC;
        AXI_17_WREADY : OUT STD_LOGIC;
        AXI_17_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_BVALID : OUT STD_LOGIC;
        AXI_18_ARREADY : OUT STD_LOGIC;
        AXI_18_AWREADY : OUT STD_LOGIC;
        AXI_18_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_18_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_18_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_RLAST : OUT STD_LOGIC;
        AXI_18_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_RVALID : OUT STD_LOGIC;
        AXI_18_WREADY : OUT STD_LOGIC;
        AXI_18_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_BVALID : OUT STD_LOGIC;
        AXI_19_ARREADY : OUT STD_LOGIC;
        AXI_19_AWREADY : OUT STD_LOGIC;
        AXI_19_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_19_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_19_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_RLAST : OUT STD_LOGIC;
        AXI_19_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_RVALID : OUT STD_LOGIC;
        AXI_19_WREADY : OUT STD_LOGIC;
        AXI_19_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_BVALID : OUT STD_LOGIC;
        AXI_20_ARREADY : OUT STD_LOGIC;
        AXI_20_AWREADY : OUT STD_LOGIC;
        AXI_20_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_20_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_20_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_RLAST : OUT STD_LOGIC;
        AXI_20_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_RVALID : OUT STD_LOGIC;
        AXI_20_WREADY : OUT STD_LOGIC;
        AXI_20_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_BVALID : OUT STD_LOGIC;
        AXI_21_ARREADY : OUT STD_LOGIC;
        AXI_21_AWREADY : OUT STD_LOGIC;
        AXI_21_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_21_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_21_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_RLAST : OUT STD_LOGIC;
        AXI_21_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_RVALID : OUT STD_LOGIC;
        AXI_21_WREADY : OUT STD_LOGIC;
        AXI_21_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_BVALID : OUT STD_LOGIC;
        AXI_22_ARREADY : OUT STD_LOGIC;
        AXI_22_AWREADY : OUT STD_LOGIC;
        AXI_22_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_22_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_22_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_RLAST : OUT STD_LOGIC;
        AXI_22_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_RVALID : OUT STD_LOGIC;
        AXI_22_WREADY : OUT STD_LOGIC;
        AXI_22_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_BVALID : OUT STD_LOGIC;
        AXI_23_ARREADY : OUT STD_LOGIC;
        AXI_23_AWREADY : OUT STD_LOGIC;
        AXI_23_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_23_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_23_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_RLAST : OUT STD_LOGIC;
        AXI_23_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_RVALID : OUT STD_LOGIC;
        AXI_23_WREADY : OUT STD_LOGIC;
        AXI_23_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_BVALID : OUT STD_LOGIC;
        AXI_24_ARREADY : OUT STD_LOGIC;
        AXI_24_AWREADY : OUT STD_LOGIC;
        AXI_24_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_24_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_24_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_RLAST : OUT STD_LOGIC;
        AXI_24_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_RVALID : OUT STD_LOGIC;
        AXI_24_WREADY : OUT STD_LOGIC;
        AXI_24_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_BVALID : OUT STD_LOGIC;
        AXI_25_ARREADY : OUT STD_LOGIC;
        AXI_25_AWREADY : OUT STD_LOGIC;
        AXI_25_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_25_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_25_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_RLAST : OUT STD_LOGIC;
        AXI_25_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_RVALID : OUT STD_LOGIC;
        AXI_25_WREADY : OUT STD_LOGIC;
        AXI_25_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_BVALID : OUT STD_LOGIC;
        AXI_26_ARREADY : OUT STD_LOGIC;
        AXI_26_AWREADY : OUT STD_LOGIC;
        AXI_26_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_26_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_26_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_RLAST : OUT STD_LOGIC;
        AXI_26_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_RVALID : OUT STD_LOGIC;
        AXI_26_WREADY : OUT STD_LOGIC;
        AXI_26_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_BVALID : OUT STD_LOGIC;
        AXI_27_ARREADY : OUT STD_LOGIC;
        AXI_27_AWREADY : OUT STD_LOGIC;
        AXI_27_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_27_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_27_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_RLAST : OUT STD_LOGIC;
        AXI_27_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_RVALID : OUT STD_LOGIC;
        AXI_27_WREADY : OUT STD_LOGIC;
        AXI_27_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_BVALID : OUT STD_LOGIC;
        AXI_28_ARREADY : OUT STD_LOGIC;
        AXI_28_AWREADY : OUT STD_LOGIC;
        AXI_28_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_28_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_28_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_RLAST : OUT STD_LOGIC;
        AXI_28_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_RVALID : OUT STD_LOGIC;
        AXI_28_WREADY : OUT STD_LOGIC;
        AXI_28_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_BVALID : OUT STD_LOGIC;
        AXI_29_ARREADY : OUT STD_LOGIC;
        AXI_29_AWREADY : OUT STD_LOGIC;
        AXI_29_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_29_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_29_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_RLAST : OUT STD_LOGIC;
        AXI_29_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_RVALID : OUT STD_LOGIC;
        AXI_29_WREADY : OUT STD_LOGIC;
        AXI_29_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_BVALID : OUT STD_LOGIC;
        AXI_30_ARREADY : OUT STD_LOGIC;
        AXI_30_AWREADY : OUT STD_LOGIC;
        AXI_30_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_30_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_30_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_RLAST : OUT STD_LOGIC;
        AXI_30_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_RVALID : OUT STD_LOGIC;
        AXI_30_WREADY : OUT STD_LOGIC;
        AXI_30_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_BVALID : OUT STD_LOGIC;
        AXI_31_ARREADY : OUT STD_LOGIC;
        AXI_31_AWREADY : OUT STD_LOGIC;
        AXI_31_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_31_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_31_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_RLAST : OUT STD_LOGIC;
        AXI_31_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_RVALID : OUT STD_LOGIC;
        AXI_31_WREADY : OUT STD_LOGIC;
        AXI_31_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_BVALID : OUT STD_LOGIC;
        apb_complete_0 : OUT STD_LOGIC;
        apb_complete_1 : OUT STD_LOGIC;
        DRAM_0_STAT_CATTRIP : OUT STD_LOGIC;
        DRAM_0_STAT_TEMP : OUT STD_LOGIC_VECTOR(6 DOWNTO 0);
        DRAM_1_STAT_CATTRIP : OUT STD_LOGIC;
        DRAM_1_STAT_TEMP : OUT STD_LOGIC_VECTOR(6 DOWNTO 0)
    );
    end component;
begin
    mmcm_i : component MMCME4_BASE
    generic map (
        BANDWIDTH        => "OPTIMIZED",
        DIVCLK_DIVIDE    => PLL_MASTER_DIV,
        CLKFBOUT_MULT_F  => PLL_MULT_F,
        CLKOUT0_DIVIDE_F => PLL_OUT0_DIV_F,
        CLKOUT1_DIVIDE   => PLL_OUT1_DIV,
        CLKOUT2_DIVIDE   => PLL_OUT2_DIV,
        CLKOUT3_DIVIDE   => PLL_OUT3_DIV,
        CLKOUT4_DIVIDE   => 10,
        CLKOUT5_DIVIDE   => 10,
        CLKOUT6_DIVIDE   => 10,
        CLKIN1_PERIOD    => REFCLK_PERIOD
    ) port map (
        CLKFBOUT  => clkfbout,
        CLKFBOUTB => open,
        CLKOUT0   => mmcm_usr_clks(0),
        CLKOUT0B  => open,
        CLKOUT1   => mmcm_usr_clks(1),
        CLKOUT1B  => open,
        CLKOUT2   => mmcm_usr_clks(2),
        CLKOUT2B  => open,
        CLKOUT3   => mmcm_usr_clks(3),
        CLKOUT3B  => open,
        CLKOUT4   => mmcm_usr_clks(4),
        CLKOUT5   => mmcm_usr_clks(5),
        CLKOUT6   => mmcm_usr_clks(6),
        CLKFBIN   => clkfbout,
        CLKIN1    => SYSCLK,
        LOCKED    => pll_locked,
        PWRDWN    => '0',
        RST       => SYSRST 
    );

    usr_clk_bufg_g: for clk_idx in 0 to (CLK_COUNT -1) generate
        usr_clk_bufg_i : component BUFG
        port map (
            I => mmcm_usr_clks(clk_idx),
            O => usr_clks(clk_idx));
    end generate;

    global_reset_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => SYSCLK,
        ASYNC_RST  => not pll_locked,
        OUT_RST(0) => global_reset
    );

    reset_tree_gen_i : entity work.RESET_TREE_GEN
    generic map (
        CLK_COUNT    => CLK_COUNT,
        RST_REPLICAS => RESET_WIDTH
    )
    port map (
        STABLE_CLK   => SYSCLK,
        GLOBAL_RESET => global_reset,
        CLK_VECTOR   => clk_vector,
        RST_VECTOR   => rst_vector
    );

    usr_rsts <= slv_array_deser(rst_vector, CLK_COUNT);
    
    -- usefull clocks for boot control in top-level
    MISC_OUT(0) <= usr_clks(MI_CLK_IDX);  -- AXI SPI clock (around 100 MHz)
    MISC_OUT(1) <= usr_rsts(MI_CLK_IDX)(0);
    MISC_OUT(2) <= usr_clks(BOOT_CLK_IDX);  -- BOOT_CTRL clock (around 200 MHz)
    MISC_OUT(3) <= usr_rsts(BOOT_CLK_IDX)(0);

    -- =========================================================================
    --                      PCIe module instance and connections
    -- =========================================================================
    pcie_i : entity work.PCIE
    generic map (
        BAR0_BASE_ADDR      => BAR0_BASE_ADDR,
        BAR1_BASE_ADDR      => BAR1_BASE_ADDR,
        BAR2_BASE_ADDR      => BAR2_BASE_ADDR,
        BAR3_BASE_ADDR      => BAR3_BASE_ADDR,
        BAR4_BASE_ADDR      => BAR4_BASE_ADDR,
        BAR5_BASE_ADDR      => BAR5_BASE_ADDR,
        EXP_ROM_BASE_ADDR   => EXP_ROM_BASE_ADDR,

        CQ_MFB_REGIONS      => PCIE_CQ_MFB_REGIONS,
        CQ_MFB_REGION_SIZE  => PCIE_CQ_MFB_REGION_SIZE,
        CQ_MFB_BLOCK_SIZE   => PCIE_CQ_MFB_BLOCK_SIZE,
        CQ_MFB_ITEM_WIDTH   => PCIE_CQ_MFB_ITEM_WIDTH,

        RC_MFB_REGIONS      => PCIE_RC_MFB_REGIONS,
        RC_MFB_REGION_SIZE  => PCIE_RC_MFB_REGION_SIZE,
        RC_MFB_BLOCK_SIZE   => PCIE_RC_MFB_BLOCK_SIZE,
        RC_MFB_ITEM_WIDTH   => PCIE_RC_MFB_ITEM_WIDTH,

        CC_MFB_REGIONS      => PCIE_CC_MFB_REGIONS,
        CC_MFB_REGION_SIZE  => PCIE_CC_MFB_REGION_SIZE,
        CC_MFB_BLOCK_SIZE   => PCIE_CC_MFB_BLOCK_SIZE,
        CC_MFB_ITEM_WIDTH   => PCIE_CC_MFB_ITEM_WIDTH,

        RQ_MFB_REGIONS      => PCIE_RQ_MFB_REGIONS,
        RQ_MFB_REGION_SIZE  => PCIE_RQ_MFB_REGION_SIZE,
        RQ_MFB_BLOCK_SIZE   => PCIE_RQ_MFB_BLOCK_SIZE,
        RQ_MFB_ITEM_WIDTH   => PCIE_RQ_MFB_ITEM_WIDTH,

        DMA_PORTS           => PCIE_ENDPOINTS,
        PCIE_ENDPOINT_TYPE  => PCIE_ENDPOINT_TYPE,
        PCIE_ENDPOINT_MODE  => PCIE_ENDPOINT_MODE,
        PCIE_ENDPOINTS      => PCIE_ENDPOINTS,
        PCIE_CLKS           => PCIE_ENDPOINTS,
        PCIE_CONS           => PCIE_CONS,
        PCIE_LANES          => PCIE_LANES,
        PCIE_GEN            => 4,

        PTC_DISABLE         => true,
        DMA_BAR_ENABLE      => true,
        XVC_ENABLE          => false,
        CARD_ID_WIDTH       => FPGA_ID_WIDTH,
        MISC_TOP2PCIE_WIDTH => 10,
        MISC_PCIE2TOP_WIDTH => 10,
        DEVICE              => DEVICE
    )
    port map (
        PCIE_SYSCLK_P      => PCIE_SYSCLK_P,
        PCIE_SYSCLK_N      => PCIE_SYSCLK_N,
        PCIE_SYSRST_N      => PCIE_SYSRST_N,
        INIT_DONE_N        => '0',
        PCIE_RX_P          => PCIE_RX_P,
        PCIE_RX_N          => PCIE_RX_N,
        PCIE_TX_P          => PCIE_TX_P,
        PCIE_TX_N          => PCIE_TX_N,
        PCIE_USER_CLK      => pcie_clks,
        PCIE_USER_RESET    => pcie_rsts,
        PCIE_LINK_UP       => pcie_link_up,

        CARD_ID            => pcie_fpga_id,

        DMA_CLK            => pcie_clks(0),
        DMA_RESET          => pcie_rsts(0),

        DMA_RQ_MFB_DATA    => pcie_rq_mfb_data,
        DMA_RQ_MFB_META    => pcie_rq_mfb_meta,
        DMA_RQ_MFB_SOF     => pcie_rq_mfb_sof,
        DMA_RQ_MFB_EOF     => pcie_rq_mfb_eof,
        DMA_RQ_MFB_SOF_POS => pcie_rq_mfb_sof_pos,
        DMA_RQ_MFB_EOF_POS => pcie_rq_mfb_eof_pos,
        DMA_RQ_MFB_SRC_RDY => pcie_rq_mfb_src_rdy,
        DMA_RQ_MFB_DST_RDY => pcie_rq_mfb_dst_rdy,

        DMA_RQ_MVB_DATA    => (others => (others => '0')),
        DMA_RQ_MVB_VLD     => (others => (others => '0')),
        DMA_RQ_MVB_SRC_RDY => (others => '0'),
        DMA_RQ_MVB_DST_RDY => open,

        DMA_RC_MFB_DATA    => pcie_rc_mfb_data,
        DMA_RC_MFB_META    => open,
        DMA_RC_MFB_SOF     => pcie_rc_mfb_sof,
        DMA_RC_MFB_EOF     => pcie_rc_mfb_eof,
        DMA_RC_MFB_SOF_POS => pcie_rc_mfb_sof_pos,
        DMA_RC_MFB_EOF_POS => pcie_rc_mfb_eof_pos,
        DMA_RC_MFB_SRC_RDY => pcie_rc_mfb_src_rdy,
        DMA_RC_MFB_DST_RDY => pcie_rc_mfb_dst_rdy,

        DMA_RC_MVB_DATA    => open,
        DMA_RC_MVB_VLD     => open,
        DMA_RC_MVB_SRC_RDY => open,
        DMA_RC_MVB_DST_RDY => (others => '0'),

        DMA_CQ_MFB_DATA    => pcie_cq_mfb_data,
        DMA_CQ_MFB_META    => pcie_cq_mfb_meta,
        DMA_CQ_MFB_SOF     => pcie_cq_mfb_sof,
        DMA_CQ_MFB_EOF     => pcie_cq_mfb_eof,
        DMA_CQ_MFB_SOF_POS => pcie_cq_mfb_sof_pos,
        DMA_CQ_MFB_EOF_POS => pcie_cq_mfb_eof_pos,
        DMA_CQ_MFB_SRC_RDY => pcie_cq_mfb_src_rdy,
        DMA_CQ_MFB_DST_RDY => pcie_cq_mfb_dst_rdy,

        DMA_CC_MFB_DATA    => pcie_cc_mfb_data,
        DMA_CC_MFB_META    => pcie_cc_mfb_meta,
        DMA_CC_MFB_SOF     => pcie_cc_mfb_sof,
        DMA_CC_MFB_EOF     => pcie_cc_mfb_eof,
        DMA_CC_MFB_SOF_POS => pcie_cc_mfb_sof_pos,
        DMA_CC_MFB_EOF_POS => pcie_cc_mfb_eof_pos,
        DMA_CC_MFB_SRC_RDY => pcie_cc_mfb_src_rdy,
        DMA_CC_MFB_DST_RDY => pcie_cc_mfb_dst_rdy,

        MI_CLK             => usr_clks(MI_CLK_IDX),
        MI_RESET           => usr_rsts(MI_CLK_IDX)(1),

        MI_DWR             => mi_dwr,
        MI_ADDR            => mi_addr,
        MI_BE              => mi_be,
        MI_RD              => mi_rd,
        MI_WR              => mi_wr,
        MI_DRD             => mi_drd,
        MI_ARDY            => mi_ardy,
        MI_DRDY            => mi_drdy,

        MI_DBG_DWR         => mi_adc_dwr (MI_ADC_PORT_PCI_DBG),
        MI_DBG_ADDR        => mi_adc_addr(MI_ADC_PORT_PCI_DBG),
        MI_DBG_BE          => mi_adc_be  (MI_ADC_PORT_PCI_DBG),
        MI_DBG_RD          => mi_adc_rd  (MI_ADC_PORT_PCI_DBG),
        MI_DBG_WR          => mi_adc_wr  (MI_ADC_PORT_PCI_DBG),
        MI_DBG_DRD         => mi_adc_drd (MI_ADC_PORT_PCI_DBG),
        MI_DBG_ARDY        => mi_adc_ardy(MI_ADC_PORT_PCI_DBG),
        MI_DBG_DRDY        => mi_adc_drdy(MI_ADC_PORT_PCI_DBG),

        MISC_TOP2PCIE      => (others => '0'),
        MISC_PCIE2TOP      => open 
    );

    cdc_pcie_up_g: for i in 0 to PCIE_ENDPOINTS-1 generate
        cdc_pcie_up_app_i: entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG  => true,
            TWO_REG => false
        )
        port map (
            ACLK     => pcie_clks(i),
            BCLK     => usr_clks(APP_CLK_IDX),
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => pcie_link_up(i),
            BDATAOUT => app_pcie_link_up(i)
        );

        cdc_pcie_fpga_id_i: entity work.ASYNC_OPEN_LOOP_SMD
        generic map (
            DATA_WIDTH => FPGA_ID_WIDTH
        )
        port map (
            ACLK     => usr_clks(MI_CLK_IDX),
            BCLK     => pcie_clks(i),
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => fpga_id,
            BDATAOUT => pcie_fpga_id(i)
        );
    end generate;

    -- =========================================================================
    --  MI ADDRESS DECODER
    -- =========================================================================
    mi_adc_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map (
        ADDR_WIDTH    => 32,
        DATA_WIDTH    => 32,
        -- defined in mi_addr_space_pack
        PORTS         => MI_ADC_PORTS,
        ADDR_BASE     => MI_ADC_ADDR_BASE,
        DEVICE        => DEVICE
    )
    port map (
        CLK        => usr_clks(MI_CLK_IDX),
        RESET      => usr_rsts(MI_CLK_IDX)(2),

        RX_DWR     => mi_dwr (0),
        RX_ADDR    => mi_addr(0),
        RX_BE      => mi_be  (0),
        RX_RD      => mi_rd  (0),
        RX_WR      => mi_wr  (0),
        RX_ARDY    => mi_ardy(0),
        RX_DRD     => mi_drd (0),
        RX_DRDY    => mi_drdy(0),

        TX_DWR     => mi_adc_dwr,
        TX_ADDR    => mi_adc_addr,
        TX_BE      => mi_adc_be,
        TX_RD      => mi_adc_rd,
        TX_WR      => mi_adc_wr,
        TX_ARDY    => mi_adc_ardy,
        TX_DRD     => mi_adc_drd,
        TX_DRDY    => mi_adc_drdy
    );

    -- boot control module is in top-level
    BOOT_MI_CLK                   <= usr_clks(MI_CLK_IDX);
    BOOT_MI_RESET                 <= usr_rsts(MI_CLK_IDX)(3);
    BOOT_MI_DWR                   <= mi_adc_dwr (MI_ADC_PORT_BOOT);
    BOOT_MI_ADDR                  <= mi_adc_addr(MI_ADC_PORT_BOOT);
    BOOT_MI_BE                    <= mi_adc_be  (MI_ADC_PORT_BOOT);
    BOOT_MI_RD                    <= mi_adc_rd  (MI_ADC_PORT_BOOT);
    BOOT_MI_WR                    <= mi_adc_wr  (MI_ADC_PORT_BOOT);
    mi_adc_ardy(MI_ADC_PORT_BOOT) <= BOOT_MI_ARDY;
    mi_adc_drd (MI_ADC_PORT_BOOT) <= BOOT_MI_DRD;
    mi_adc_drdy(MI_ADC_PORT_BOOT) <= BOOT_MI_DRDY;

    -- =========================================================================
    --  MI TEST SPACE AND SDM/SYSMON INTERFACE
    -- =========================================================================
    mi_test_space_i : entity work.MI_TEST_SPACE
    generic map (
        DEVICE  => DEVICE
    )
    port map (
        CLK     => usr_clks(MI_CLK_IDX),
        RESET   => usr_rsts(MI_CLK_IDX)(4),
        MI_DWR  => mi_adc_dwr(MI_ADC_PORT_TEST),
        MI_ADDR => mi_adc_addr(MI_ADC_PORT_TEST),
        MI_BE   => mi_adc_be(MI_ADC_PORT_TEST),
        MI_RD   => mi_adc_rd(MI_ADC_PORT_TEST),
        MI_WR   => mi_adc_wr(MI_ADC_PORT_TEST),
        MI_DRD  => mi_adc_drd(MI_ADC_PORT_TEST),
        MI_ARDY => mi_adc_ardy(MI_ADC_PORT_TEST),
        MI_DRDY => mi_adc_drdy(MI_ADC_PORT_TEST)
    );

    sdm_ctrl_i: entity work.SDM_CTRL
    generic map (
        DATA_WIDTH => 32,
        ADDR_WIDTH => 32,
        DEVICE     => DEVICE
    )
    port map (
        CLK     => usr_clks(MI_CLK_IDX),
        RESET   => usr_rsts(MI_CLK_IDX)(5),
        MI_DWR  => mi_adc_dwr(MI_ADC_PORT_SENSOR),
        MI_ADDR => mi_adc_addr(MI_ADC_PORT_SENSOR),
        MI_RD   => mi_adc_rd(MI_ADC_PORT_SENSOR),
        MI_WR   => mi_adc_wr(MI_ADC_PORT_SENSOR),
        MI_BE   => mi_adc_be(MI_ADC_PORT_SENSOR),
        MI_DRD  => mi_adc_drd(MI_ADC_PORT_SENSOR),
        MI_ARDY => mi_adc_ardy(MI_ADC_PORT_SENSOR),
        MI_DRDY => mi_adc_drdy(MI_ADC_PORT_SENSOR),

        CHIP_ID     => open,
        CHIP_ID_VLD => open 
    );

    -- =========================================================================
    -- FPGA ID LOGIC
    -- =========================================================================
    hwid_i : entity work.HWID
    generic map (
        DEVICE          => DEVICE
    )
    port map (
        CLK             => usr_clks(MI_CLK_IDX),
        XILINX_DNA      => fpga_id,
        XILINX_DNA_VLD  => fpga_id_vld 
    );

    -- =========================================================================
    --  DMA MODULE
    -- =========================================================================
    dma_i : entity work.DMA
    generic map (
        DEVICE               => DEVICE,

        DMA_MFB_REGIONS      => DMA_MFB_REGIONS,
        DMA_MFB_REGION_SIZE  => DMA_MFB_REGION_SIZE,
        DMA_MFB_BLOCK_SIZE   => DMA_MFB_BLOCK_SIZE,
        DMA_MFB_ITEM_WIDTH   => DMA_MFB_ITEM_WIDTH,

        PCIE_RQ_MFB_REGIONS     => PCIE_RQ_MFB_REGIONS,
        PCIE_RQ_MFB_REGION_SIZE => PCIE_RQ_MFB_REGION_SIZE,
        PCIE_RQ_MFB_BLOCK_SIZE  => PCIE_RQ_MFB_BLOCK_SIZE,
        PCIE_RQ_MFB_ITEM_WIDTH  => PCIE_RQ_MFB_ITEM_WIDTH,

        PCIE_RC_MFB_REGIONS     => PCIE_RC_MFB_REGIONS,
        PCIE_RC_MFB_REGION_SIZE => PCIE_RC_MFB_REGION_SIZE,
        PCIE_RC_MFB_BLOCK_SIZE  => PCIE_RC_MFB_BLOCK_SIZE,
        PCIE_RC_MFB_ITEM_WIDTH  => PCIE_RC_MFB_ITEM_WIDTH,

        PCIE_CQ_MFB_REGIONS     => PCIE_CQ_MFB_REGIONS,
        PCIE_CQ_MFB_REGION_SIZE => PCIE_CQ_MFB_REGION_SIZE,
        PCIE_CQ_MFB_BLOCK_SIZE  => PCIE_CQ_MFB_BLOCK_SIZE,
        PCIE_CQ_MFB_ITEM_WIDTH  => PCIE_CQ_MFB_ITEM_WIDTH,

        PCIE_CC_MFB_REGIONS     => PCIE_CC_MFB_REGIONS,
        PCIE_CC_MFB_REGION_SIZE => PCIE_CC_MFB_REGION_SIZE,
        PCIE_CC_MFB_BLOCK_SIZE  => PCIE_CC_MFB_BLOCK_SIZE,
        PCIE_CC_MFB_ITEM_WIDTH  => PCIE_CC_MFB_ITEM_WIDTH,

        HDR_META_WIDTH       => DMA_HDR_META_WIDTH,
        PKT_SIZE_MAX         => DMA_PKT_SIZE_MAX,

        C2H_CHANNELS          => C2H_DMA_CHANNELS,
        C2H_PTR_WIDTH         => C2H_PTR_WIDTH,

        H2C_CHANNELS          => H2C_DMA_CHANNELS,
        H2C_PTR_WIDTH         => H2C_PTR_WIDTH,

        C2H_GEN_EN            => C2H_GEN_EN,
        H2C_GEN_EN            => H2C_GEN_EN,

        DBG_CNTR_EN          => DMA_DEBUG_ENABLE,
        GEN_LOOP_EN          => DMA_GEN_LOOP_EN
    )
    port map (
        MI_CLK              => usr_clks(MI_CLK_IDX),
        MI_RESET            => usr_rsts(MI_CLK_IDX)(6),

        DMA_CLK             => pcie_clks,
        DMA_RESET           => pcie_rsts,

        C2H_DMA_MFB_META_HDR_META => c2h_dma_mfb_hdr_meta,
        C2H_DMA_MFB_META_CHAN     => c2h_dma_mfb_chan,

        C2H_DMA_MFB_DATA     => c2h_dma_mfb_data,
        C2H_DMA_MFB_SOF      => c2h_dma_mfb_sof,
        C2H_DMA_MFB_EOF      => c2h_dma_mfb_eof,
        C2H_DMA_MFB_SOF_POS  => c2h_dma_mfb_sof_pos,
        C2H_DMA_MFB_EOF_POS  => c2h_dma_mfb_eof_pos,
        C2H_DMA_MFB_SRC_RDY  => c2h_dma_mfb_src_rdy,
        C2H_DMA_MFB_DST_RDY  => c2h_dma_mfb_dst_rdy,

        H2C_DMA_MFB_META_SIZE     => h2c_dma_mfb_size,
        H2C_DMA_MFB_META_HDR_META => h2c_dma_mfb_hdr_meta,
        H2C_DMA_MFB_META_CHAN     => h2c_dma_mfb_chan,

        H2C_DMA_MFB_DATA     => h2c_dma_mfb_data,
        H2C_DMA_MFB_SOF      => h2c_dma_mfb_sof,
        H2C_DMA_MFB_EOF      => h2c_dma_mfb_eof,
        H2C_DMA_MFB_SOF_POS  => h2c_dma_mfb_sof_pos,
        H2C_DMA_MFB_EOF_POS  => h2c_dma_mfb_eof_pos,
        H2C_DMA_MFB_SRC_RDY  => h2c_dma_mfb_src_rdy,
        H2C_DMA_MFB_DST_RDY  => h2c_dma_mfb_dst_rdy,

        PCIE_RQ_MFB_DATA    => pcie_rq_mfb_data,
        PCIE_RQ_MFB_META    => pcie_rq_mfb_meta,
        PCIE_RQ_MFB_SOF     => pcie_rq_mfb_sof,
        PCIE_RQ_MFB_EOF     => pcie_rq_mfb_eof,
        PCIE_RQ_MFB_SOF_POS => pcie_rq_mfb_sof_pos,
        PCIE_RQ_MFB_EOF_POS => pcie_rq_mfb_eof_pos,
        PCIE_RQ_MFB_SRC_RDY => pcie_rq_mfb_src_rdy,
        PCIE_RQ_MFB_DST_RDY => pcie_rq_mfb_dst_rdy,

        PCIE_RC_MFB_DATA    => pcie_rc_mfb_data,
        PCIE_RC_MFB_SOF     => pcie_rc_mfb_sof,
        PCIE_RC_MFB_EOF     => pcie_rc_mfb_eof,
        PCIE_RC_MFB_SOF_POS => pcie_rc_mfb_sof_pos,
        PCIE_RC_MFB_EOF_POS => pcie_rc_mfb_eof_pos,
        PCIE_RC_MFB_SRC_RDY => pcie_rc_mfb_src_rdy,
        PCIE_RC_MFB_DST_RDY => pcie_rc_mfb_dst_rdy,

        PCIE_CQ_MFB_DATA    => pcie_cq_mfb_data,
        PCIE_CQ_MFB_META    => pcie_cq_mfb_meta,
        PCIE_CQ_MFB_SOF     => pcie_cq_mfb_sof,
        PCIE_CQ_MFB_EOF     => pcie_cq_mfb_eof,
        PCIE_CQ_MFB_SOF_POS => pcie_cq_mfb_sof_pos,
        PCIE_CQ_MFB_EOF_POS => pcie_cq_mfb_eof_pos,
        PCIE_CQ_MFB_SRC_RDY => pcie_cq_mfb_src_rdy,
        PCIE_CQ_MFB_DST_RDY => pcie_cq_mfb_dst_rdy,

        PCIE_CC_MFB_DATA    => pcie_cc_mfb_data,
        PCIE_CC_MFB_META    => pcie_cc_mfb_meta,
        PCIE_CC_MFB_SOF     => pcie_cc_mfb_sof,
        PCIE_CC_MFB_EOF     => pcie_cc_mfb_eof,
        PCIE_CC_MFB_SOF_POS => pcie_cc_mfb_sof_pos,
        PCIE_CC_MFB_EOF_POS => pcie_cc_mfb_eof_pos,
        PCIE_CC_MFB_SRC_RDY => pcie_cc_mfb_src_rdy,
        PCIE_CC_MFB_DST_RDY => pcie_cc_mfb_dst_rdy,

        MI_ADDR             => dma_mi_addr,
        MI_DWR              => dma_mi_dwr,
        MI_BE               => dma_mi_be,
        MI_RD               => dma_mi_rd,
        MI_WR               => dma_mi_wr,
        MI_DRD              => dma_mi_drd,
        MI_ARDY             => dma_mi_ardy,
        MI_DRDY             => dma_mi_drdy,

        GEN_LOOP_MI_ADDR    => mi_adc_addr(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_DWR     => mi_adc_dwr(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_BE      => mi_adc_be(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_RD      => mi_adc_rd(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_WR      => mi_adc_wr(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_DRD     => mi_adc_drd(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_ARDY    => mi_adc_ardy(MI_ADC_PORT_GENLOOP),
        GEN_LOOP_MI_DRDY    => mi_adc_drdy(MI_ADC_PORT_GENLOOP)
    );

    -- MI interface connection
    dma_mi_pr : process (all)
    begin
        -- Connect directly to MTC by default
        dma_mi_dwr                         <= mi_dwr;
        dma_mi_addr                        <= mi_addr;
        dma_mi_rd                          <= mi_rd;
        dma_mi_wr                          <= mi_wr;
        dma_mi_be                          <= mi_be;
        mi_drd (PCIE_ENDPOINTS-1 downto 1) <= dma_mi_drd (PCIE_ENDPOINTS-1 downto 1);
        mi_ardy(PCIE_ENDPOINTS-1 downto 1) <= dma_mi_ardy(PCIE_ENDPOINTS-1 downto 1);
        mi_drdy(PCIE_ENDPOINTS-1 downto 1) <= dma_mi_drdy(PCIE_ENDPOINTS-1 downto 1);

        -- Connect to MI ADC for PCIe Endpoint 0
        dma_mi_dwr (0)               <= mi_adc_dwr(MI_ADC_PORT_DMA);
        dma_mi_addr(0)               <= mi_adc_addr(MI_ADC_PORT_DMA);
        dma_mi_rd  (0)               <= mi_adc_rd(MI_ADC_PORT_DMA);
        dma_mi_wr  (0)               <= mi_adc_wr(MI_ADC_PORT_DMA);
        dma_mi_be  (0)               <= mi_adc_be(MI_ADC_PORT_DMA);
        mi_adc_drd(MI_ADC_PORT_DMA)  <= dma_mi_drd (0);
        mi_adc_ardy(MI_ADC_PORT_DMA) <= dma_mi_ardy(0);
        mi_adc_drdy(MI_ADC_PORT_DMA) <= dma_mi_drdy(0);
    end process;

    -- =========================================================================
    --  THE APPLICATION
    -- =========================================================================
    user_core_i : entity work.USER_CORE
    generic map (
        MI_DATA_WIDTH         => MI_DATA_WIDTH,
        MI_ADDR_WIDTH         => MI_ADDR_WIDTH,

        DMA_STREAMS           => DMA_STREAMS,

        C2H_DMA_CHANNELS       => C2H_DMA_CHANNELS,
        H2C_DMA_CHANNELS       => H2C_DMA_CHANNELS,

        DMA_DMA_HDR_META_WIDTH    => DMA_HDR_META_WIDTH,
        DMA_PKT_SIZE_MAX      => DMA_PKT_SIZE_MAX,

        DMA_MFB_REGIONS       => DMA_MFB_REGIONS,
        DMA_MFB_REGION_SIZE   => DMA_MFB_REGION_SIZE,
        DMA_MFB_BLOCK_SIZE    => DMA_MFB_BLOCK_SIZE,
        DMA_MFB_ITEM_WIDTH    => DMA_MFB_ITEM_WIDTH,

        HBM_PORTS             => HBM_PORTS,
        HBM_DATA_WIDTH        => HBM_DATA_WIDTH,
        HBM_ADDR_WIDTH        => HBM_ADDR_WIDTH,
        HBM_BURST_WIDTH       => HBM_BURST_WIDTH,
        HBM_ID_WIDTH          => HBM_ID_WIDTH,
        HBM_LEN_WIDTH         => HBM_LEN_WIDTH,
        HBM_SIZE_WIDTH        => HBM_SIZE_WIDTH,
        HBM_RESP_WIDTH        => HBM_RESP_WIDTH,

        FPGA_ID_WIDTH         => FPGA_ID_WIDTH,
        DEVICE                => DEVICE
    )
    port map (
        MI_CLK             => usr_clks(MI_CLK_IDX),
        MI_RESET           => usr_rsts(MI_CLK_IDX)(7),

        MI_DWR             => mi_adc_dwr(MI_ADC_PORT_USERAPP),
        MI_ADDR            => mi_adc_addr(MI_ADC_PORT_USERAPP),
        MI_BE              => mi_adc_be(MI_ADC_PORT_USERAPP),
        MI_RD              => mi_adc_rd(MI_ADC_PORT_USERAPP),
        MI_WR              => mi_adc_wr(MI_ADC_PORT_USERAPP),
        MI_DRD             => mi_adc_drd(MI_ADC_PORT_USERAPP),
        MI_ARDY            => mi_adc_ardy(MI_ADC_PORT_USERAPP),
        MI_DRDY            => mi_adc_drdy(MI_ADC_PORT_USERAPP),

        DMA_CLK            => pcie_clks,
        DMA_RESET          => pcie_rsts,

        USR_CLK            => usr_clks(APP_CLK_IDX),
        USR_RESET          => usr_rsts(APP_CLK_IDX)(0),

        C2H_DMA_MFB_META_HDR_META => c2h_dma_mfb_meta_hdr_meta,
        C2H_DMA_MFB_META_CHAN     => c2h_dma_mfb_meta_chan,

        C2H_DMA_MFB_DATA     => c2h_dma_mfb_data,
        C2H_DMA_MFB_SOF      => c2h_dma_mfb_sof,
        C2H_DMA_MFB_EOF      => c2h_dma_mfb_eof,
        C2H_DMA_MFB_SOF_POS  => c2h_dma_mfb_sof_pos,
        C2H_DMA_MFB_EOF_POS  => c2h_dma_mfb_eof_pos,
        C2H_DMA_MFB_SRC_RDY  => c2h_dma_mfb_src_rdy,
        C2H_DMA_MFB_DST_RDY  => c2h_dma_mfb_dst_rdy,
        
        H2C_DMA_MFB_META_SIZE     => h2c_dma_mfb_meta_size,
        H2C_DMA_MFB_META_HDR_META => h2c_dma_mfb_meta_hdr_meta,
        H2C_DMA_MFB_META_CHAN     => h2c_dma_mfb_meta_chan,

        H2C_DMA_MFB_DATA     => h2c_dma_mfb_data,
        H2C_DMA_MFB_SOF      => h2c_dma_mfb_sof,
        H2C_DMA_MFB_EOF      => h2c_dma_mfb_eof,
        H2C_DMA_MFB_SOF_POS  => h2c_dma_mfb_sof_pos,
        H2C_DMA_MFB_EOF_POS  => h2c_dma_mfb_eof_pos,
        H2C_DMA_MFB_SRC_RDY  => h2c_dma_mfb_src_rdy,
        H2C_DMA_MFB_DST_RDY  => h2c_dma_mfb_dst_rdy,

        HBM_AXI_CLK          => app_hbm_clk,
        HBM_AXI_RESET        => app_hbm_rst,
        HBM_INIT_DONE        => hbm_init_done,

        HBM_AXI_ARADDR       => hbm_axi_araddr,
        HBM_AXI_ARBURST      => hbm_axi_arburst,
        HBM_AXI_ARID         => hbm_axi_arid,
        HBM_AXI_ARLEN        => hbm_axi_arlen,
        HBM_AXI_ARSIZE       => hbm_axi_arsize,
        HBM_AXI_ARVALID      => hbm_axi_arvalid,
        HBM_AXI_ARREADY      => hbm_axi_arready,

        HBM_AXI_RDATA        => hbm_axi_rdata,
        HBM_AXI_RDATA_PARITY => hbm_axi_rdata_parity,
        HBM_AXI_RID          => hbm_axi_rid,
        HBM_AXI_RLAST        => hbm_axi_rlast,
        HBM_AXI_RRESP        => hbm_axi_rresp,
        HBM_AXI_RVALID       => hbm_axi_rvalid,
        HBM_AXI_RREADY       => hbm_axi_rready,

        HBM_AXI_AWADDR       => hbm_axi_awaddr,
        HBM_AXI_AWBURST      => hbm_axi_awburst,
        HBM_AXI_AWID         => hbm_axi_awid,
        HBM_AXI_AWLEN        => hbm_axi_awlen,
        HBM_AXI_AWSIZE       => hbm_axi_awsize,
        HBM_AXI_AWVALID      => hbm_axi_awvalid,
        HBM_AXI_AWREADY      => hbm_axi_awready,

        HBM_AXI_WDATA        => hbm_axi_wdata,
        HBM_AXI_WDATA_PARITY => hbm_axi_wdata_parity,
        HBM_AXI_WLAST        => hbm_axi_wlast,
        HBM_AXI_WSTRB        => hbm_axi_wstrb,
        HBM_AXI_WVALID       => hbm_axi_wvalid,
        HBM_AXI_WREADY       => hbm_axi_wready,

        HBM_AXI_BID          => hbm_axi_bid,
        HBM_AXI_BRESP        => hbm_axi_bresp,
        HBM_AXI_BVALID       => hbm_axi_bvalid,
        HBM_AXI_BREADY       => hbm_axi_bready,

        PCIE_LINK_UP       => app_pcie_link_up,
        FPGA_ID            => fpga_id,
        FPGA_ID_VLD        => fpga_id_vld
    );

    -- =========================================================================
    --  STATUS LEDs
    -- =========================================================================
    process (clk_usr_x1)
    begin
        if rising_edge(clk_usr_x1) then
            if (rst_usr_x1(0) = '1') then
                heartbeat_cnt <= (others => '0');
            else
                heartbeat_cnt <= heartbeat_cnt + 1;
            end if;
            STATUS_LEDS(0) <= heartbeat_cnt(HEARTBEAT_CNT_W-1);
        end if;
    end process;

    STATUS_LEDS(1) <= (and app_pcie_link_up);

    -- =============================================================================================
    -- HBM Memory Instance
    -- =============================================================================================
    hbm_refclk_ibuf_i : IBUFDS
        port map (
            I => HBM_REFCLK_P,
            IB => HBM_REFCLK_N,
            O => hbm_refclk_ibuf
        );

    hbm_refclk_bufg_i : BUFG
        port map (
            I => hbm_refclk_ibuf,
            O => hbm_refclk
        );

    hbm_refclk_rst_i : xpm_cdc_async_rst
        generic map (
            DEST_SYNC_FF => 4,
            INIT_SYNC_FF => 1,
            RST_ACTIVE_HIGH => 1
        )
        port map (
            src_arst => SYSRST,
            dest_clk => hbm_refclk,
            dest_arst => hbm_rst
        );

    -- Assign clock and reset for each HBM port's AXI interface
    hbm_axi_clk_rst_assign_g : for i in 0 to HBM_PORTS-1 generate
        hbm_axi_aclk(i) <= app_hbm_clk(i);
        hbm_axi_rst_reg_p : process (hbm_axi_aclk(i))
        begin
            if (rising_edge(hbm_axi_aclk(i))) then
                hbm_axi_areset_n(i) <= not app_hbm_rst(i);
            end if;
        end process;
    end generate;

    hbm_ready_sync_g : for i in 0 to 1 generate
        hbm_ready_sync_i : xpm_cdc_single
            generic map (
                DEST_SYNC_FF => 4,
                INIT_SYNC_FF => 0,
                SIM_ASSERT_CHK => 0,
                SRC_INPUT_REG => 0
            )
            port map (
                dest_out => hbm_ready_sync(i),
                dest_clk => app_hbm_clk,
                src_clk => hbm_refclk,
                src_in => hbm_ready(i)
            );
    end generate;

    hbm_init_done <= and hbm_ready_sync;
    HBM_CATTRIP   <= or hbm_cattrip_int;

    hbm_i : hbm_ip
    PORT MAP (
        HBM_REF_CLK_0 => hbm_refclk,
        HBM_REF_CLK_1 => hbm_refclk,
        APB_0_PCLK => hbm_refclk,
        APB_0_PRESET_N => not hbm_rst,
        APB_1_PCLK => hbm_refclk,
        APB_1_PRESET_N => not hbm_rst,
        apb_complete_0 => hbm_ready(0),
        apb_complete_1 => hbm_ready(1),
        DRAM_0_STAT_CATTRIP => hbm_cattrip_int(0),
        DRAM_0_STAT_TEMP => open,
        DRAM_1_STAT_CATTRIP => hbm_cattrip_int(1),
        DRAM_1_STAT_TEMP => open
        AXI_00_ACLK => hbm_axi_aclk(0),
        AXI_00_ARESET_N => hbm_axi_areset_n(0),
        AXI_00_ARADDR => hbm_axi_araddr(0),
        AXI_00_ARBURST => hbm_axi_arburst(0),
        AXI_00_ARID => hbm_axi_arid(0),
        AXI_00_ARLEN => hbm_axi_arlen(0),
        AXI_00_ARSIZE => hbm_axi_arsize(0),
        AXI_00_ARVALID => hbm_axi_arvalid(0),
        AXI_00_AWADDR => hbm_axi_awaddr(0),
        AXI_00_AWBURST => hbm_axi_awburst(0),
        AXI_00_AWID => hbm_axi_awid(0),
        AXI_00_AWLEN => hbm_axi_awlen(0),
        AXI_00_AWSIZE => hbm_axi_awsize(0),
        AXI_00_AWVALID => hbm_axi_awvalid(0),
        AXI_00_RREADY => hbm_axi_rready(0),
        AXI_00_BREADY => hbm_axi_bready(0),
        AXI_00_WDATA => hbm_axi_wdata(0),
        AXI_00_WLAST => hbm_axi_wlast(0),
        AXI_00_WSTRB => hbm_axi_wstrb(0),
        AXI_00_WDATA_PARITY => hbm_axi_wdata_parity(0),
        AXI_00_WVALID => hbm_axi_wvalid(0),
        AXI_01_ACLK => hbm_axi_aclk(1),
        AXI_01_ARESET_N => hbm_axi_areset_n(1),
        AXI_01_ARADDR => hbm_axi_araddr(1),
        AXI_01_ARBURST => hbm_axi_arburst(1),
        AXI_01_ARID => hbm_axi_arid(1),
        AXI_01_ARLEN => hbm_axi_arlen(1),
        AXI_01_ARSIZE => hbm_axi_arsize(1),
        AXI_01_ARVALID => hbm_axi_arvalid(1),
        AXI_01_AWADDR => hbm_axi_awaddr(1),
        AXI_01_AWBURST => hbm_axi_awburst(1),
        AXI_01_AWID => hbm_axi_awid(1),
        AXI_01_AWLEN => hbm_axi_awlen(1),
        AXI_01_AWSIZE => hbm_axi_awsize(1),
        AXI_01_AWVALID => hbm_axi_awvalid(1),
        AXI_01_RREADY => hbm_axi_rready(1),
        AXI_01_BREADY => hbm_axi_bready(1),
        AXI_01_WDATA => hbm_axi_wdata(1),
        AXI_01_WLAST => hbm_axi_wlast(1),
        AXI_01_WSTRB => hbm_axi_wstrb(1),
        AXI_01_WDATA_PARITY => hbm_axi_wdata_parity(1),
        AXI_01_WVALID => hbm_axi_wvalid(1),
        AXI_02_ACLK => hbm_axi_aclk(2),
        AXI_02_ARESET_N => hbm_axi_areset_n(2),
        AXI_02_ARADDR => hbm_axi_araddr(2),
        AXI_02_ARBURST => hbm_axi_arburst(2),
        AXI_02_ARID => hbm_axi_arid(2),
        AXI_02_ARLEN => hbm_axi_arlen(2),
        AXI_02_ARSIZE => hbm_axi_arsize(2),
        AXI_02_ARVALID => hbm_axi_arvalid(2),
        AXI_02_AWADDR => hbm_axi_awaddr(2),
        AXI_02_AWBURST => hbm_axi_awburst(2),
        AXI_02_AWID => hbm_axi_awid(2),
        AXI_02_AWLEN => hbm_axi_awlen(2),
        AXI_02_AWSIZE => hbm_axi_awsize(2),
        AXI_02_AWVALID => hbm_axi_awvalid(2),
        AXI_02_RREADY => hbm_axi_rready(2),
        AXI_02_BREADY => hbm_axi_bready(2),
        AXI_02_WDATA => hbm_axi_wdata(2),
        AXI_02_WLAST => hbm_axi_wlast(2),
        AXI_02_WSTRB => hbm_axi_wstrb(2),
        AXI_02_WDATA_PARITY => hbm_axi_wdata_parity(2),
        AXI_02_WVALID => hbm_axi_wvalid(2),
        AXI_03_ACLK => hbm_axi_aclk(3),
        AXI_03_ARESET_N => hbm_axi_areset_n(3),
        AXI_03_ARADDR => hbm_axi_araddr(3),
        AXI_03_ARBURST => hbm_axi_arburst(3),
        AXI_03_ARID => hbm_axi_arid(3),
        AXI_03_ARLEN => hbm_axi_arlen(3),
        AXI_03_ARSIZE => hbm_axi_arsize(3),
        AXI_03_ARVALID => hbm_axi_arvalid(3),
        AXI_03_AWADDR => hbm_axi_awaddr(3),
        AXI_03_AWBURST => hbm_axi_awburst(3),
        AXI_03_AWID => hbm_axi_awid(3),
        AXI_03_AWLEN => hbm_axi_awlen(3),
        AXI_03_AWSIZE => hbm_axi_awsize(3),
        AXI_03_AWVALID => hbm_axi_awvalid(3),
        AXI_03_RREADY => hbm_axi_rready(3),
        AXI_03_BREADY => hbm_axi_bready(3),
        AXI_03_WDATA => hbm_axi_wdata(3),
        AXI_03_WLAST => hbm_axi_wlast(3),
        AXI_03_WSTRB => hbm_axi_wstrb(3),
        AXI_03_WDATA_PARITY => hbm_axi_wdata_parity(3),
        AXI_03_WVALID => hbm_axi_wvalid(3),
        AXI_04_ACLK => hbm_axi_aclk(4),
        AXI_04_ARESET_N => hbm_axi_areset_n(4),
        AXI_04_ARADDR => hbm_axi_araddr(4),
        AXI_04_ARBURST => hbm_axi_arburst(4),
        AXI_04_ARID => hbm_axi_arid(4),
        AXI_04_ARLEN => hbm_axi_arlen(4),
        AXI_04_ARSIZE => hbm_axi_arsize(4),
        AXI_04_ARVALID => hbm_axi_arvalid(4),
        AXI_04_AWADDR => hbm_axi_awaddr(4),
        AXI_04_AWBURST => hbm_axi_awburst(4),
        AXI_04_AWID => hbm_axi_awid(4),
        AXI_04_AWLEN => hbm_axi_awlen(4),
        AXI_04_AWSIZE => hbm_axi_awsize(4),
        AXI_04_AWVALID => hbm_axi_awvalid(4),
        AXI_04_RREADY => hbm_axi_rready(4),
        AXI_04_BREADY => hbm_axi_bready(4),
        AXI_04_WDATA => hbm_axi_wdata(4),
        AXI_04_WLAST => hbm_axi_wlast(4),
        AXI_04_WSTRB => hbm_axi_wstrb(4),
        AXI_04_WDATA_PARITY => hbm_axi_wdata_parity(4),
        AXI_04_WVALID => hbm_axi_wvalid(4),
        AXI_05_ACLK => hbm_axi_aclk(5),
        AXI_05_ARESET_N => hbm_axi_areset_n(5),
        AXI_05_ARADDR => hbm_axi_araddr(5),
        AXI_05_ARBURST => hbm_axi_arburst(5),
        AXI_05_ARID => hbm_axi_arid(5),
        AXI_05_ARLEN => hbm_axi_arlen(5),
        AXI_05_ARSIZE => hbm_axi_arsize(5),
        AXI_05_ARVALID => hbm_axi_arvalid(5),
        AXI_05_AWADDR => hbm_axi_awaddr(5),
        AXI_05_AWBURST => hbm_axi_awburst(5),
        AXI_05_AWID => hbm_axi_awid(5),
        AXI_05_AWLEN => hbm_axi_awlen(5),
        AXI_05_AWSIZE => hbm_axi_awsize(5),
        AXI_05_AWVALID => hbm_axi_awvalid(5),
        AXI_05_RREADY => hbm_axi_rready(5),
        AXI_05_BREADY => hbm_axi_bready(5),
        AXI_05_WDATA => hbm_axi_wdata(5),
        AXI_05_WLAST => hbm_axi_wlast(5),
        AXI_05_WSTRB => hbm_axi_wstrb(5),
        AXI_05_WDATA_PARITY => hbm_axi_wdata_parity(5),
        AXI_05_WVALID => hbm_axi_wvalid(5),
        AXI_06_ACLK => hbm_axi_aclk(6),
        AXI_06_ARESET_N => hbm_axi_areset_n(6),
        AXI_06_ARADDR => hbm_axi_araddr(6),
        AXI_06_ARBURST => hbm_axi_arburst(6),
        AXI_06_ARID => hbm_axi_arid(6),
        AXI_06_ARLEN => hbm_axi_arlen(6),
        AXI_06_ARSIZE => hbm_axi_arsize(6),
        AXI_06_ARVALID => hbm_axi_arvalid(6),
        AXI_06_AWADDR => hbm_axi_awaddr(6),
        AXI_06_AWBURST => hbm_axi_awburst(6),
        AXI_06_AWID => hbm_axi_awid(6),
        AXI_06_AWLEN => hbm_axi_awlen(6),
        AXI_06_AWSIZE => hbm_axi_awsize(6),
        AXI_06_AWVALID => hbm_axi_awvalid(6),
        AXI_06_RREADY => hbm_axi_rready(6),
        AXI_06_BREADY => hbm_axi_bready(6),
        AXI_06_WDATA => hbm_axi_wdata(6),
        AXI_06_WLAST => hbm_axi_wlast(6),
        AXI_06_WSTRB => hbm_axi_wstrb(6),
        AXI_06_WDATA_PARITY => hbm_axi_wdata_parity(6),
        AXI_06_WVALID => hbm_axi_wvalid(6),
        AXI_07_ACLK => hbm_axi_aclk(7),
        AXI_07_ARESET_N => hbm_axi_areset_n(7),
        AXI_07_ARADDR => hbm_axi_araddr(7),
        AXI_07_ARBURST => hbm_axi_arburst(7),
        AXI_07_ARID => hbm_axi_arid(7),
        AXI_07_ARLEN => hbm_axi_arlen(7),
        AXI_07_ARSIZE => hbm_axi_arsize(7),
        AXI_07_ARVALID => hbm_axi_arvalid(7),
        AXI_07_AWADDR => hbm_axi_awaddr(7),
        AXI_07_AWBURST => hbm_axi_awburst(7),
        AXI_07_AWID => hbm_axi_awid(7),
        AXI_07_AWLEN => hbm_axi_awlen(7),
        AXI_07_AWSIZE => hbm_axi_awsize(7),
        AXI_07_AWVALID => hbm_axi_awvalid(7),
        AXI_07_RREADY => hbm_axi_rready(7),
        AXI_07_BREADY => hbm_axi_bready(7),
        AXI_07_WDATA => hbm_axi_wdata(7),
        AXI_07_WLAST => hbm_axi_wlast(7),
        AXI_07_WSTRB => hbm_axi_wstrb(7),
        AXI_07_WDATA_PARITY => hbm_axi_wdata_parity(7),
        AXI_07_WVALID => hbm_axi_wvalid(7),
        AXI_08_ACLK => hbm_axi_aclk(8),
        AXI_08_ARESET_N => hbm_axi_areset_n(8),
        AXI_08_ARADDR => hbm_axi_araddr(8),
        AXI_08_ARBURST => hbm_axi_arburst(8),
        AXI_08_ARID => hbm_axi_arid(8),
        AXI_08_ARLEN => hbm_axi_arlen(8),
        AXI_08_ARSIZE => hbm_axi_arsize(8),
        AXI_08_ARVALID => hbm_axi_arvalid(8),
        AXI_08_AWADDR => hbm_axi_awaddr(8),
        AXI_08_AWBURST => hbm_axi_awburst(8),
        AXI_08_AWID => hbm_axi_awid(8),
        AXI_08_AWLEN => hbm_axi_awlen(8),
        AXI_08_AWSIZE => hbm_axi_awsize(8),
        AXI_08_AWVALID => hbm_axi_awvalid(8),
        AXI_08_RREADY => hbm_axi_rready(8),
        AXI_08_BREADY => hbm_axi_bready(8),
        AXI_08_WDATA => hbm_axi_wdata(8),
        AXI_08_WLAST => hbm_axi_wlast(8),
        AXI_08_WSTRB => hbm_axi_wstrb(8),
        AXI_08_WDATA_PARITY => hbm_axi_wdata_parity(8),
        AXI_08_WVALID => hbm_axi_wvalid(8),
        AXI_09_ACLK => hbm_axi_aclk(9),
        AXI_09_ARESET_N => hbm_axi_areset_n(9),
        AXI_09_ARADDR => hbm_axi_araddr(9),
        AXI_09_ARBURST => hbm_axi_arburst(9),
        AXI_09_ARID => hbm_axi_arid(9),
        AXI_09_ARLEN => hbm_axi_arlen(9),
        AXI_09_ARSIZE => hbm_axi_arsize(9),
        AXI_09_ARVALID => hbm_axi_arvalid(9),
        AXI_09_AWADDR => hbm_axi_awaddr(9),
        AXI_09_AWBURST => hbm_axi_awburst(9),
        AXI_09_AWID => hbm_axi_awid(9),
        AXI_09_AWLEN => hbm_axi_awlen(9),
        AXI_09_AWSIZE => hbm_axi_awsize(9),
        AXI_09_AWVALID => hbm_axi_awvalid(9),
        AXI_09_RREADY => hbm_axi_rready(9),
        AXI_09_BREADY => hbm_axi_bready(9),
        AXI_09_WDATA => hbm_axi_wdata(9),
        AXI_09_WLAST => hbm_axi_wlast(9),
        AXI_09_WSTRB => hbm_axi_wstrb(9),
        AXI_09_WDATA_PARITY => hbm_axi_wdata_parity(9),
        AXI_09_WVALID => hbm_axi_wvalid(9),
        AXI_10_ACLK => hbm_axi_aclk(10),
        AXI_10_ARESET_N => hbm_axi_areset_n(10),
        AXI_10_ARADDR => hbm_axi_araddr(10),
        AXI_10_ARBURST => hbm_axi_arburst(10),
        AXI_10_ARID => hbm_axi_arid(10),
        AXI_10_ARLEN => hbm_axi_arlen(10),
        AXI_10_ARSIZE => hbm_axi_arsize(10),
        AXI_10_ARVALID => hbm_axi_arvalid(10),
        AXI_10_AWADDR => hbm_axi_awaddr(10),
        AXI_10_AWBURST => hbm_axi_awburst(10),
        AXI_10_AWID => hbm_axi_awid(10),
        AXI_10_AWLEN => hbm_axi_awlen(10),
        AXI_10_AWSIZE => hbm_axi_awsize(10),
        AXI_10_AWVALID => hbm_axi_awvalid(10),
        AXI_10_RREADY => hbm_axi_rready(10),
        AXI_10_BREADY => hbm_axi_bready(10),
        AXI_10_WDATA => hbm_axi_wdata(10),
        AXI_10_WLAST => hbm_axi_wlast(10),
        AXI_10_WSTRB => hbm_axi_wstrb(10),
        AXI_10_WDATA_PARITY => hbm_axi_wdata_parity(10),
        AXI_10_WVALID => hbm_axi_wvalid(10),
        AXI_11_ACLK => hbm_axi_aclk(11),
        AXI_11_ARESET_N => hbm_axi_areset_n(11),
        AXI_11_ARADDR => hbm_axi_araddr(11),
        AXI_11_ARBURST => hbm_axi_arburst(11),
        AXI_11_ARID => hbm_axi_arid(11),
        AXI_11_ARLEN => hbm_axi_arlen(11),
        AXI_11_ARSIZE => hbm_axi_arsize(11),
        AXI_11_ARVALID => hbm_axi_arvalid(11),
        AXI_11_AWADDR => hbm_axi_awaddr(11),
        AXI_11_AWBURST => hbm_axi_awburst(11),
        AXI_11_AWID => hbm_axi_awid(11),
        AXI_11_AWLEN => hbm_axi_awlen(11),
        AXI_11_AWSIZE => hbm_axi_awsize(11),
        AXI_11_AWVALID => hbm_axi_awvalid(11),
        AXI_11_RREADY => hbm_axi_rready(11),
        AXI_11_BREADY => hbm_axi_bready(11),
        AXI_11_WDATA => hbm_axi_wdata(11),
        AXI_11_WLAST => hbm_axi_wlast(11),
        AXI_11_WSTRB => hbm_axi_wstrb(11),
        AXI_11_WDATA_PARITY => hbm_axi_wdata_parity(11),
        AXI_11_WVALID => hbm_axi_wvalid(11),
        AXI_12_ACLK => hbm_axi_aclk(12),
        AXI_12_ARESET_N => hbm_axi_areset_n(12),
        AXI_12_ARADDR => hbm_axi_araddr(12),
        AXI_12_ARBURST => hbm_axi_arburst(12),
        AXI_12_ARID => hbm_axi_arid(12),
        AXI_12_ARLEN => hbm_axi_arlen(12),
        AXI_12_ARSIZE => hbm_axi_arsize(12),
        AXI_12_ARVALID => hbm_axi_arvalid(12),
        AXI_12_AWADDR => hbm_axi_awaddr(12),
        AXI_12_AWBURST => hbm_axi_awburst(12),
        AXI_12_AWID => hbm_axi_awid(12),
        AXI_12_AWLEN => hbm_axi_awlen(12),
        AXI_12_AWSIZE => hbm_axi_awsize(12),
        AXI_12_AWVALID => hbm_axi_awvalid(12),
        AXI_12_RREADY => hbm_axi_rready(12),
        AXI_12_BREADY => hbm_axi_bready(12),
        AXI_12_WDATA => hbm_axi_wdata(12),
        AXI_12_WLAST => hbm_axi_wlast(12),
        AXI_12_WSTRB => hbm_axi_wstrb(12),
        AXI_12_WDATA_PARITY => hbm_axi_wdata_parity(12),
        AXI_12_WVALID => hbm_axi_wvalid(12),
        AXI_13_ACLK => hbm_axi_aclk(13),
        AXI_13_ARESET_N => hbm_axi_areset_n(13),
        AXI_13_ARADDR => hbm_axi_araddr(13),
        AXI_13_ARBURST => hbm_axi_arburst(13),
        AXI_13_ARID => hbm_axi_arid(13),
        AXI_13_ARLEN => hbm_axi_arlen(13),
        AXI_13_ARSIZE => hbm_axi_arsize(13),
        AXI_13_ARVALID => hbm_axi_arvalid(13),
        AXI_13_AWADDR => hbm_axi_awaddr(13),
        AXI_13_AWBURST => hbm_axi_awburst(13),
        AXI_13_AWID => hbm_axi_awid(13),
        AXI_13_AWLEN => hbm_axi_awlen(13),
        AXI_13_AWSIZE => hbm_axi_awsize(13),
        AXI_13_AWVALID => hbm_axi_awvalid(13),
        AXI_13_RREADY => hbm_axi_rready(13),
        AXI_13_BREADY => hbm_axi_bready(13),
        AXI_13_WDATA => hbm_axi_wdata(13),
        AXI_13_WLAST => hbm_axi_wlast(13),
        AXI_13_WSTRB => hbm_axi_wstrb(13),
        AXI_13_WDATA_PARITY => hbm_axi_wdata_parity(13),
        AXI_13_WVALID => hbm_axi_wvalid(13),
        AXI_14_ACLK => hbm_axi_aclk(14),
        AXI_14_ARESET_N => hbm_axi_areset_n(14),
        AXI_14_ARADDR => hbm_axi_araddr(14),
        AXI_14_ARBURST => hbm_axi_arburst(14),
        AXI_14_ARID => hbm_axi_arid(14),
        AXI_14_ARLEN => hbm_axi_arlen(14),
        AXI_14_ARSIZE => hbm_axi_arsize(14),
        AXI_14_ARVALID => hbm_axi_arvalid(14),
        AXI_14_AWADDR => hbm_axi_awaddr(14),
        AXI_14_AWBURST => hbm_axi_awburst(14),
        AXI_14_AWID => hbm_axi_awid(14),
        AXI_14_AWLEN => hbm_axi_awlen(14),
        AXI_14_AWSIZE => hbm_axi_awsize(14),
        AXI_14_AWVALID => hbm_axi_awvalid(14),
        AXI_14_RREADY => hbm_axi_rready(14),
        AXI_14_BREADY => hbm_axi_bready(14),
        AXI_14_WDATA => hbm_axi_wdata(14),
        AXI_14_WLAST => hbm_axi_wlast(14),
        AXI_14_WSTRB => hbm_axi_wstrb(14),
        AXI_14_WDATA_PARITY => hbm_axi_wdata_parity(14),
        AXI_14_WVALID => hbm_axi_wvalid(14),
        AXI_15_ACLK => hbm_axi_aclk(15),
        AXI_15_ARESET_N => hbm_axi_areset_n(15),
        AXI_15_ARADDR => hbm_axi_araddr(15),
        AXI_15_ARBURST => hbm_axi_arburst(15),
        AXI_15_ARID => hbm_axi_arid(15),
        AXI_15_ARLEN => hbm_axi_arlen(15),
        AXI_15_ARSIZE => hbm_axi_arsize(15),
        AXI_15_ARVALID => hbm_axi_arvalid(15),
        AXI_15_AWADDR => hbm_axi_awaddr(15),
        AXI_15_AWBURST => hbm_axi_awburst(15),
        AXI_15_AWID => hbm_axi_awid(15),
        AXI_15_AWLEN => hbm_axi_awlen(15),
        AXI_15_AWSIZE => hbm_axi_awsize(15),
        AXI_15_AWVALID => hbm_axi_awvalid(15),
        AXI_15_RREADY => hbm_axi_rready(15),
        AXI_15_BREADY => hbm_axi_bready(15),
        AXI_15_WDATA => hbm_axi_wdata(15),
        AXI_15_WLAST => hbm_axi_wlast(15),
        AXI_15_WSTRB => hbm_axi_wstrb(15),
        AXI_15_WDATA_PARITY => hbm_axi_wdata_parity(15),
        AXI_15_WVALID => hbm_axi_wvalid(15),
        AXI_16_ACLK => hbm_axi_aclk(16),
        AXI_16_ARESET_N => hbm_axi_areset_n(16),
        AXI_16_ARADDR => hbm_axi_araddr(16),
        AXI_16_ARBURST => hbm_axi_arburst(16),
        AXI_16_ARID => hbm_axi_arid(16),
        AXI_16_ARLEN => hbm_axi_arlen(16),
        AXI_16_ARSIZE => hbm_axi_arsize(16),
        AXI_16_ARVALID => hbm_axi_arvalid(16),
        AXI_16_AWADDR => hbm_axi_awaddr(16),
        AXI_16_AWBURST => hbm_axi_awburst(16),
        AXI_16_AWID => hbm_axi_awid(16),
        AXI_16_AWLEN => hbm_axi_awlen(16),
        AXI_16_AWSIZE => hbm_axi_awsize(16),
        AXI_16_AWVALID => hbm_axi_awvalid(16),
        AXI_16_RREADY => hbm_axi_rready(16),
        AXI_16_BREADY => hbm_axi_bready(16),
        AXI_16_WDATA => hbm_axi_wdata(16),
        AXI_16_WLAST => hbm_axi_wlast(16),
        AXI_16_WSTRB => hbm_axi_wstrb(16),
        AXI_16_WDATA_PARITY => hbm_axi_wdata_parity(16),
        AXI_16_WVALID => hbm_axi_wvalid(16),
        AXI_17_ACLK => hbm_axi_aclk(17),
        AXI_17_ARESET_N => hbm_axi_areset_n(17),
        AXI_17_ARADDR => hbm_axi_araddr(17),
        AXI_17_ARBURST => hbm_axi_arburst(17),
        AXI_17_ARID => hbm_axi_arid(17),
        AXI_17_ARLEN => hbm_axi_arlen(17),
        AXI_17_ARSIZE => hbm_axi_arsize(17),
        AXI_17_ARVALID => hbm_axi_arvalid(17),
        AXI_17_AWADDR => hbm_axi_awaddr(17),
        AXI_17_AWBURST => hbm_axi_awburst(17),
        AXI_17_AWID => hbm_axi_awid(17),
        AXI_17_AWLEN => hbm_axi_awlen(17),
        AXI_17_AWSIZE => hbm_axi_awsize(17),
        AXI_17_AWVALID => hbm_axi_awvalid(17),
        AXI_17_RREADY => hbm_axi_rready(17),
        AXI_17_BREADY => hbm_axi_bready(17),
        AXI_17_WDATA => hbm_axi_wdata(17),
        AXI_17_WLAST => hbm_axi_wlast(17),
        AXI_17_WSTRB => hbm_axi_wstrb(17),
        AXI_17_WDATA_PARITY => hbm_axi_wdata_parity(17),
        AXI_17_WVALID => hbm_axi_wvalid(17),
        AXI_18_ACLK => hbm_axi_aclk(18),
        AXI_18_ARESET_N => hbm_axi_areset_n(18),
        AXI_18_ARADDR => hbm_axi_araddr(18),
        AXI_18_ARBURST => hbm_axi_arburst(18),
        AXI_18_ARID => hbm_axi_arid(18),
        AXI_18_ARLEN => hbm_axi_arlen(18),
        AXI_18_ARSIZE => hbm_axi_arsize(18),
        AXI_18_ARVALID => hbm_axi_arvalid(18),
        AXI_18_AWADDR => hbm_axi_awaddr(18),
        AXI_18_AWBURST => hbm_axi_awburst(18),
        AXI_18_AWID => hbm_axi_awid(18),
        AXI_18_AWLEN => hbm_axi_awlen(18),
        AXI_18_AWSIZE => hbm_axi_awsize(18),
        AXI_18_AWVALID => hbm_axi_awvalid(18),
        AXI_18_RREADY => hbm_axi_rready(18),
        AXI_18_BREADY => hbm_axi_bready(18),
        AXI_18_WDATA => hbm_axi_wdata(18),
        AXI_18_WLAST => hbm_axi_wlast(18),
        AXI_18_WSTRB => hbm_axi_wstrb(18),
        AXI_18_WDATA_PARITY => hbm_axi_wdata_parity(18),
        AXI_18_WVALID => hbm_axi_wvalid(18),
        AXI_19_ACLK => hbm_axi_aclk(19),
        AXI_19_ARESET_N => hbm_axi_areset_n(19),
        AXI_19_ARADDR => hbm_axi_araddr(19),
        AXI_19_ARBURST => hbm_axi_arburst(19),
        AXI_19_ARID => hbm_axi_arid(19),
        AXI_19_ARLEN => hbm_axi_arlen(19),
        AXI_19_ARSIZE => hbm_axi_arsize(19),
        AXI_19_ARVALID => hbm_axi_arvalid(19),
        AXI_19_AWADDR => hbm_axi_awaddr(19),
        AXI_19_AWBURST => hbm_axi_awburst(19),
        AXI_19_AWID => hbm_axi_awid(19),
        AXI_19_AWLEN => hbm_axi_awlen(19),
        AXI_19_AWSIZE => hbm_axi_awsize(19),
        AXI_19_AWVALID => hbm_axi_awvalid(19),
        AXI_19_RREADY => hbm_axi_rready(19),
        AXI_19_BREADY => hbm_axi_bready(19),
        AXI_19_WDATA => hbm_axi_wdata(19),
        AXI_19_WLAST => hbm_axi_wlast(19),
        AXI_19_WSTRB => hbm_axi_wstrb(19),
        AXI_19_WDATA_PARITY => hbm_axi_wdata_parity(19),
        AXI_19_WVALID => hbm_axi_wvalid(19),
        AXI_20_ACLK => hbm_axi_aclk(20),
        AXI_20_ARESET_N => hbm_axi_areset_n(20),
        AXI_20_ARADDR => hbm_axi_araddr(20),
        AXI_20_ARBURST => hbm_axi_arburst(20),
        AXI_20_ARID => hbm_axi_arid(20),
        AXI_20_ARLEN => hbm_axi_arlen(20),
        AXI_20_ARSIZE => hbm_axi_arsize(20),
        AXI_20_ARVALID => hbm_axi_arvalid(20),
        AXI_20_AWADDR => hbm_axi_awaddr(20),
        AXI_20_AWBURST => hbm_axi_awburst(20),
        AXI_20_AWID => hbm_axi_awid(20),
        AXI_20_AWLEN => hbm_axi_awlen(20),
        AXI_20_AWSIZE => hbm_axi_awsize(20),
        AXI_20_AWVALID => hbm_axi_awvalid(20),
        AXI_20_RREADY => hbm_axi_rready(20),
        AXI_20_BREADY => hbm_axi_bready(20),
        AXI_20_WDATA => hbm_axi_wdata(20),
        AXI_20_WLAST => hbm_axi_wlast(20),
        AXI_20_WSTRB => hbm_axi_wstrb(20),
        AXI_20_WDATA_PARITY => hbm_axi_wdata_parity(20),
        AXI_20_WVALID => hbm_axi_wvalid(20),
        AXI_21_ACLK => hbm_axi_aclk(21),
        AXI_21_ARESET_N => hbm_axi_areset_n(21),
        AXI_21_ARADDR => hbm_axi_araddr(21),
        AXI_21_ARBURST => hbm_axi_arburst(21),
        AXI_21_ARID => hbm_axi_arid(21),
        AXI_21_ARLEN => hbm_axi_arlen(21),
        AXI_21_ARSIZE => hbm_axi_arsize(21),
        AXI_21_ARVALID => hbm_axi_arvalid(21),
        AXI_21_AWADDR => hbm_axi_awaddr(21),
        AXI_21_AWBURST => hbm_axi_awburst(21),
        AXI_21_AWID => hbm_axi_awid(21),
        AXI_21_AWLEN => hbm_axi_awlen(21),
        AXI_21_AWSIZE => hbm_axi_awsize(21),
        AXI_21_AWVALID => hbm_axi_awvalid(21),
        AXI_21_RREADY => hbm_axi_rready(21),
        AXI_21_BREADY => hbm_axi_bready(21),
        AXI_21_WDATA => hbm_axi_wdata(21),
        AXI_21_WLAST => hbm_axi_wlast(21),
        AXI_21_WSTRB => hbm_axi_wstrb(21),
        AXI_21_WDATA_PARITY => hbm_axi_wdata_parity(21),
        AXI_21_WVALID => hbm_axi_wvalid(21),
        AXI_22_ACLK => hbm_axi_aclk(22),
        AXI_22_ARESET_N => hbm_axi_areset_n(22),
        AXI_22_ARADDR => hbm_axi_araddr(22),
        AXI_22_ARBURST => hbm_axi_arburst(22),
        AXI_22_ARID => hbm_axi_arid(22),
        AXI_22_ARLEN => hbm_axi_arlen(22),
        AXI_22_ARSIZE => hbm_axi_arsize(22),
        AXI_22_ARVALID => hbm_axi_arvalid(22),
        AXI_22_AWADDR => hbm_axi_awaddr(22),
        AXI_22_AWBURST => hbm_axi_awburst(22),
        AXI_22_AWID => hbm_axi_awid(22),
        AXI_22_AWLEN => hbm_axi_awlen(22),
        AXI_22_AWSIZE => hbm_axi_awsize(22),
        AXI_22_AWVALID => hbm_axi_awvalid(22),
        AXI_22_RREADY => hbm_axi_rready(22),
        AXI_22_BREADY => hbm_axi_bready(22),
        AXI_22_WDATA => hbm_axi_wdata(22),
        AXI_22_WLAST => hbm_axi_wlast(22),
        AXI_22_WSTRB => hbm_axi_wstrb(22),
        AXI_22_WDATA_PARITY => hbm_axi_wdata_parity(22),
        AXI_22_WVALID => hbm_axi_wvalid(22),
        AXI_23_ACLK => hbm_axi_aclk(23),
        AXI_23_ARESET_N => hbm_axi_areset_n(23),
        AXI_23_ARADDR => hbm_axi_araddr(23),
        AXI_23_ARBURST => hbm_axi_arburst(23),
        AXI_23_ARID => hbm_axi_arid(23),
        AXI_23_ARLEN => hbm_axi_arlen(23),
        AXI_23_ARSIZE => hbm_axi_arsize(23),
        AXI_23_ARVALID => hbm_axi_arvalid(23),
        AXI_23_AWADDR => hbm_axi_awaddr(23),
        AXI_23_AWBURST => hbm_axi_awburst(23),
        AXI_23_AWID => hbm_axi_awid(23),
        AXI_23_AWLEN => hbm_axi_awlen(23),
        AXI_23_AWSIZE => hbm_axi_awsize(23),
        AXI_23_AWVALID => hbm_axi_awvalid(23),
        AXI_23_RREADY => hbm_axi_rready(23),
        AXI_23_BREADY => hbm_axi_bready(23),
        AXI_23_WDATA => hbm_axi_wdata(23),
        AXI_23_WLAST => hbm_axi_wlast(23),
        AXI_23_WSTRB => hbm_axi_wstrb(23),
        AXI_23_WDATA_PARITY => hbm_axi_wdata_parity(23),
        AXI_23_WVALID => hbm_axi_wvalid(23),
        AXI_24_ACLK => hbm_axi_aclk(24),
        AXI_24_ARESET_N => hbm_axi_areset_n(24),
        AXI_24_ARADDR => hbm_axi_araddr(24),
        AXI_24_ARBURST => hbm_axi_arburst(24),
        AXI_24_ARID => hbm_axi_arid(24),
        AXI_24_ARLEN => hbm_axi_arlen(24),
        AXI_24_ARSIZE => hbm_axi_arsize(24),
        AXI_24_ARVALID => hbm_axi_arvalid(24),
        AXI_24_AWADDR => hbm_axi_awaddr(24),
        AXI_24_AWBURST => hbm_axi_awburst(24),
        AXI_24_AWID => hbm_axi_awid(24),
        AXI_24_AWLEN => hbm_axi_awlen(24),
        AXI_24_AWSIZE => hbm_axi_awsize(24),
        AXI_24_AWVALID => hbm_axi_awvalid(24),
        AXI_24_RREADY => hbm_axi_rready(24),
        AXI_24_BREADY => hbm_axi_bready(24),
        AXI_24_WDATA => hbm_axi_wdata(24),
        AXI_24_WLAST => hbm_axi_wlast(24),
        AXI_24_WSTRB => hbm_axi_wstrb(24),
        AXI_24_WDATA_PARITY => hbm_axi_wdata_parity(24),
        AXI_24_WVALID => hbm_axi_wvalid(24),
        AXI_25_ACLK => hbm_axi_aclk(25),
        AXI_25_ARESET_N => hbm_axi_areset_n(25),
        AXI_25_ARADDR => hbm_axi_araddr(25),
        AXI_25_ARBURST => hbm_axi_arburst(25),
        AXI_25_ARID => hbm_axi_arid(25),
        AXI_25_ARLEN => hbm_axi_arlen(25),
        AXI_25_ARSIZE => hbm_axi_arsize(25),
        AXI_25_ARVALID => hbm_axi_arvalid(25),
        AXI_25_AWADDR => hbm_axi_awaddr(25),
        AXI_25_AWBURST => hbm_axi_awburst(25),
        AXI_25_AWID => hbm_axi_awid(25),
        AXI_25_AWLEN => hbm_axi_awlen(25),
        AXI_25_AWSIZE => hbm_axi_awsize(25),
        AXI_25_AWVALID => hbm_axi_awvalid(25),
        AXI_25_RREADY => hbm_axi_rready(25),
        AXI_25_BREADY => hbm_axi_bready(25),
        AXI_25_WDATA => hbm_axi_wdata(25),
        AXI_25_WLAST => hbm_axi_wlast(25),
        AXI_25_WSTRB => hbm_axi_wstrb(25),
        AXI_25_WDATA_PARITY => hbm_axi_wdata_parity(25),
        AXI_25_WVALID => hbm_axi_wvalid(25),
        AXI_26_ACLK => hbm_axi_aclk(26),
        AXI_26_ARESET_N => hbm_axi_areset_n(26),
        AXI_26_ARADDR => hbm_axi_araddr(26),
        AXI_26_ARBURST => hbm_axi_arburst(26),
        AXI_26_ARID => hbm_axi_arid(26),
        AXI_26_ARLEN => hbm_axi_arlen(26),
        AXI_26_ARSIZE => hbm_axi_arsize(26),
        AXI_26_ARVALID => hbm_axi_arvalid(26),
        AXI_26_AWADDR => hbm_axi_awaddr(26),
        AXI_26_AWBURST => hbm_axi_awburst(26),
        AXI_26_AWID => hbm_axi_awid(26),
        AXI_26_AWLEN => hbm_axi_awlen(26),
        AXI_26_AWSIZE => hbm_axi_awsize(26),
        AXI_26_AWVALID => hbm_axi_awvalid(26),
        AXI_26_RREADY => hbm_axi_rready(26),
        AXI_26_BREADY => hbm_axi_bready(26),
        AXI_26_WDATA => hbm_axi_wdata(26),
        AXI_26_WLAST => hbm_axi_wlast(26),
        AXI_26_WSTRB => hbm_axi_wstrb(26),
        AXI_26_WDATA_PARITY => hbm_axi_wdata_parity(26),
        AXI_26_WVALID => hbm_axi_wvalid(26),
        AXI_27_ACLK => hbm_axi_aclk(27),
        AXI_27_ARESET_N => hbm_axi_areset_n(27),
        AXI_27_ARADDR => hbm_axi_araddr(27),
        AXI_27_ARBURST => hbm_axi_arburst(27),
        AXI_27_ARID => hbm_axi_arid(27),
        AXI_27_ARLEN => hbm_axi_arlen(27),
        AXI_27_ARSIZE => hbm_axi_arsize(27),
        AXI_27_ARVALID => hbm_axi_arvalid(27),
        AXI_27_AWADDR => hbm_axi_awaddr(27),
        AXI_27_AWBURST => hbm_axi_awburst(27),
        AXI_27_AWID => hbm_axi_awid(27),
        AXI_27_AWLEN => hbm_axi_awlen(27),
        AXI_27_AWSIZE => hbm_axi_awsize(27),
        AXI_27_AWVALID => hbm_axi_awvalid(27),
        AXI_27_RREADY => hbm_axi_rready(27),
        AXI_27_BREADY => hbm_axi_bready(27),
        AXI_27_WDATA => hbm_axi_wdata(27),
        AXI_27_WLAST => hbm_axi_wlast(27),
        AXI_27_WSTRB => hbm_axi_wstrb(27),
        AXI_27_WDATA_PARITY => hbm_axi_wdata_parity(27),
        AXI_27_WVALID => hbm_axi_wvalid(27),
        AXI_28_ACLK => hbm_axi_aclk(28),
        AXI_28_ARESET_N => hbm_axi_areset_n(28),
        AXI_28_ARADDR => hbm_axi_araddr(28),
        AXI_28_ARBURST => hbm_axi_arburst(28),
        AXI_28_ARID => hbm_axi_arid(28),
        AXI_28_ARLEN => hbm_axi_arlen(28),
        AXI_28_ARSIZE => hbm_axi_arsize(28),
        AXI_28_ARVALID => hbm_axi_arvalid(28),
        AXI_28_AWADDR => hbm_axi_awaddr(28),
        AXI_28_AWBURST => hbm_axi_awburst(28),
        AXI_28_AWID => hbm_axi_awid(28),
        AXI_28_AWLEN => hbm_axi_awlen(28),
        AXI_28_AWSIZE => hbm_axi_awsize(28),
        AXI_28_AWVALID => hbm_axi_awvalid(28),
        AXI_28_RREADY => hbm_axi_rready(28),
        AXI_28_BREADY => hbm_axi_bready(28),
        AXI_28_WDATA => hbm_axi_wdata(28),
        AXI_28_WLAST => hbm_axi_wlast(28),
        AXI_28_WSTRB => hbm_axi_wstrb(28),
        AXI_28_WDATA_PARITY => hbm_axi_wdata_parity(28),
        AXI_28_WVALID => hbm_axi_wvalid(28),
        AXI_29_ACLK => hbm_axi_aclk(29),
        AXI_29_ARESET_N => hbm_axi_areset_n(29),
        AXI_29_ARADDR => hbm_axi_araddr(29),
        AXI_29_ARBURST => hbm_axi_arburst(29),
        AXI_29_ARID => hbm_axi_arid(29),
        AXI_29_ARLEN => hbm_axi_arlen(29),
        AXI_29_ARSIZE => hbm_axi_arsize(29),
        AXI_29_ARVALID => hbm_axi_arvalid(29),
        AXI_29_AWADDR => hbm_axi_awaddr(29),
        AXI_29_AWBURST => hbm_axi_awburst(29),
        AXI_29_AWID => hbm_axi_awid(29),
        AXI_29_AWLEN => hbm_axi_awlen(29),
        AXI_29_AWSIZE => hbm_axi_awsize(29),
        AXI_29_AWVALID => hbm_axi_awvalid(29),
        AXI_29_RREADY => hbm_axi_rready(29),
        AXI_29_BREADY => hbm_axi_bready(29),
        AXI_29_WDATA => hbm_axi_wdata(29),
        AXI_29_WLAST => hbm_axi_wlast(29),
        AXI_29_WSTRB => hbm_axi_wstrb(29),
        AXI_29_WDATA_PARITY => hbm_axi_wdata_parity(29),
        AXI_29_WVALID => hbm_axi_wvalid(29),
        AXI_30_ACLK => hbm_axi_aclk(30),
        AXI_30_ARESET_N => hbm_axi_areset_n(30),
        AXI_30_ARADDR => hbm_axi_araddr(30),
        AXI_30_ARBURST => hbm_axi_arburst(30),
        AXI_30_ARID => hbm_axi_arid(30),
        AXI_30_ARLEN => hbm_axi_arlen(30),
        AXI_30_ARSIZE => hbm_axi_arsize(30),
        AXI_30_ARVALID => hbm_axi_arvalid(30),
        AXI_30_AWADDR => hbm_axi_awaddr(30),
        AXI_30_AWBURST => hbm_axi_awburst(30),
        AXI_30_AWID => hbm_axi_awid(30),
        AXI_30_AWLEN => hbm_axi_awlen(30),
        AXI_30_AWSIZE => hbm_axi_awsize(30),
        AXI_30_AWVALID => hbm_axi_awvalid(30),
        AXI_30_RREADY => hbm_axi_rready(30),
        AXI_30_BREADY => hbm_axi_bready(30),
        AXI_30_WDATA => hbm_axi_wdata(30),
        AXI_30_WLAST => hbm_axi_wlast(30),
        AXI_30_WSTRB => hbm_axi_wstrb(30),
        AXI_30_WDATA_PARITY => hbm_axi_wdata_parity(30),
        AXI_30_WVALID => hbm_axi_wvalid(30),
        AXI_31_ACLK => hbm_axi_aclk(31),
        AXI_31_ARESET_N => hbm_axi_areset_n(31),
        AXI_31_ARADDR => hbm_axi_araddr(31),
        AXI_31_ARBURST => hbm_axi_arburst(31),
        AXI_31_ARID => hbm_axi_arid(31),
        AXI_31_ARLEN => hbm_axi_arlen(31),
        AXI_31_ARSIZE => hbm_axi_arsize(31),
        AXI_31_ARVALID => hbm_axi_arvalid(31),
        AXI_31_AWADDR => hbm_axi_awaddr(31),
        AXI_31_AWBURST => hbm_axi_awburst(31),
        AXI_31_AWID => hbm_axi_awid(31),
        AXI_31_AWLEN => hbm_axi_awlen(31),
        AXI_31_AWSIZE => hbm_axi_awsize(31),
        AXI_31_AWVALID => hbm_axi_awvalid(31),
        AXI_31_RREADY => hbm_axi_rready(31),
        AXI_31_BREADY => hbm_axi_bready(31),
        AXI_31_WDATA => hbm_axi_wdata(31),
        AXI_31_WLAST => hbm_axi_wlast(31),
        AXI_31_WSTRB => hbm_axi_wstrb(31),
        AXI_31_WDATA_PARITY => hbm_axi_wdata_parity(31),
        AXI_31_WVALID => hbm_axi_wvalid(31),
        AXI_00_ARREADY => hbm_axi_arready(0),
        AXI_00_AWREADY => hbm_axi_awready(0),
        AXI_00_RDATA_PARITY => hbm_axi_rdata_parity(0),
        AXI_00_RDATA => hbm_axi_rdata(0),
        AXI_00_RID => hbm_axi_rid(0),
        AXI_00_RLAST => hbm_axi_rlast(0),
        AXI_00_RRESP => hbm_axi_rresp(0),
        AXI_00_RVALID => hbm_axi_rvalid(0),
        AXI_00_WREADY => hbm_axi_wready(0),
        AXI_00_BID => hbm_axi_bid(0),
        AXI_00_BRESP => hbm_axi_bresp(0),
        AXI_00_BVALID => hbm_axi_bvalid(0),
        AXI_01_ARREADY => hbm_axi_arready(1),
        AXI_01_AWREADY => hbm_axi_awready(1),
        AXI_01_RDATA_PARITY => hbm_axi_rdata_parity(1),
        AXI_01_RDATA => hbm_axi_rdata(1),
        AXI_01_RID => hbm_axi_rid(1),
        AXI_01_RLAST => hbm_axi_rlast(1),
        AXI_01_RRESP => hbm_axi_rresp(1),
        AXI_01_RVALID => hbm_axi_rvalid(1),
        AXI_01_WREADY => hbm_axi_wready(1),
        AXI_01_BID => hbm_axi_bid(1),
        AXI_01_BRESP => hbm_axi_bresp(1),
        AXI_01_BVALID => hbm_axi_bvalid(1),
        AXI_02_ARREADY => hbm_axi_arready(2),
        AXI_02_AWREADY => hbm_axi_awready(2),
        AXI_02_RDATA_PARITY => hbm_axi_rdata_parity(2),
        AXI_02_RDATA => hbm_axi_rdata(2),
        AXI_02_RID => hbm_axi_rid(2),
        AXI_02_RLAST => hbm_axi_rlast(2),
        AXI_02_RRESP => hbm_axi_rresp(2),
        AXI_02_RVALID => hbm_axi_rvalid(2),
        AXI_02_WREADY => hbm_axi_wready(2),
        AXI_02_BID => hbm_axi_bid(2),
        AXI_02_BRESP => hbm_axi_bresp(2),
        AXI_02_BVALID => hbm_axi_bvalid(2),
        AXI_03_ARREADY => hbm_axi_arready(3),
        AXI_03_AWREADY => hbm_axi_awready(3),
        AXI_03_RDATA_PARITY => hbm_axi_rdata_parity(3),
        AXI_03_RDATA => hbm_axi_rdata(3),
        AXI_03_RID => hbm_axi_rid(3),
        AXI_03_RLAST => hbm_axi_rlast(3),
        AXI_03_RRESP => hbm_axi_rresp(3),
        AXI_03_RVALID => hbm_axi_rvalid(3),
        AXI_03_WREADY => hbm_axi_wready(3),
        AXI_03_BID => hbm_axi_bid(3),
        AXI_03_BRESP => hbm_axi_bresp(3),
        AXI_03_BVALID => hbm_axi_bvalid(3),
        AXI_04_ARREADY => hbm_axi_arready(4),
        AXI_04_AWREADY => hbm_axi_awready(4),
        AXI_04_RDATA_PARITY => hbm_axi_rdata_parity(4),
        AXI_04_RDATA => hbm_axi_rdata(4),
        AXI_04_RID => hbm_axi_rid(4),
        AXI_04_RLAST => hbm_axi_rlast(4),
        AXI_04_RRESP => hbm_axi_rresp(4),
        AXI_04_RVALID => hbm_axi_rvalid(4),
        AXI_04_WREADY => hbm_axi_wready(4),
        AXI_04_BID => hbm_axi_bid(4),
        AXI_04_BRESP => hbm_axi_bresp(4),
        AXI_04_BVALID => hbm_axi_bvalid(4),
        AXI_05_ARREADY => hbm_axi_arready(5),
        AXI_05_AWREADY => hbm_axi_awready(5),
        AXI_05_RDATA_PARITY => hbm_axi_rdata_parity(5),
        AXI_05_RDATA => hbm_axi_rdata(5),
        AXI_05_RID => hbm_axi_rid(5),
        AXI_05_RLAST => hbm_axi_rlast(5),
        AXI_05_RRESP => hbm_axi_rresp(5),
        AXI_05_RVALID => hbm_axi_rvalid(5),
        AXI_05_WREADY => hbm_axi_wready(5),
        AXI_05_BID => hbm_axi_bid(5),
        AXI_05_BRESP => hbm_axi_bresp(5),
        AXI_05_BVALID => hbm_axi_bvalid(5),
        AXI_06_ARREADY => hbm_axi_arready(6),
        AXI_06_AWREADY => hbm_axi_awready(6),
        AXI_06_RDATA_PARITY => hbm_axi_rdata_parity(6),
        AXI_06_RDATA => hbm_axi_rdata(6),
        AXI_06_RID => hbm_axi_rid(6),
        AXI_06_RLAST => hbm_axi_rlast(6),
        AXI_06_RRESP => hbm_axi_rresp(6),
        AXI_06_RVALID => hbm_axi_rvalid(6),
        AXI_06_WREADY => hbm_axi_wready(6),
        AXI_06_BID => hbm_axi_bid(6),
        AXI_06_BRESP => hbm_axi_bresp(6),
        AXI_06_BVALID => hbm_axi_bvalid(6),
        AXI_07_ARREADY => hbm_axi_arready(7),
        AXI_07_AWREADY => hbm_axi_awready(7),
        AXI_07_RDATA_PARITY => hbm_axi_rdata_parity(7),
        AXI_07_RDATA => hbm_axi_rdata(7),
        AXI_07_RID => hbm_axi_rid(7),
        AXI_07_RLAST => hbm_axi_rlast(7),
        AXI_07_RRESP => hbm_axi_rresp(7),
        AXI_07_RVALID => hbm_axi_rvalid(7),
        AXI_07_WREADY => hbm_axi_wready(7),
        AXI_07_BID => hbm_axi_bid(7),
        AXI_07_BRESP => hbm_axi_bresp(7),
        AXI_07_BVALID => hbm_axi_bvalid(7),
        AXI_08_ARREADY => hbm_axi_arready(8),
        AXI_08_AWREADY => hbm_axi_awready(8),
        AXI_08_RDATA_PARITY => hbm_axi_rdata_parity(8),
        AXI_08_RDATA => hbm_axi_rdata(8),
        AXI_08_RID => hbm_axi_rid(8),
        AXI_08_RLAST => hbm_axi_rlast(8),
        AXI_08_RRESP => hbm_axi_rresp(8),
        AXI_08_RVALID => hbm_axi_rvalid(8),
        AXI_08_WREADY => hbm_axi_wready(8),
        AXI_08_BID => hbm_axi_bid(8),
        AXI_08_BRESP => hbm_axi_bresp(8),
        AXI_08_BVALID => hbm_axi_bvalid(8),
        AXI_09_ARREADY => hbm_axi_arready(9),
        AXI_09_AWREADY => hbm_axi_awready(9),
        AXI_09_RDATA_PARITY => hbm_axi_rdata_parity(9),
        AXI_09_RDATA => hbm_axi_rdata(9),
        AXI_09_RID => hbm_axi_rid(9),
        AXI_09_RLAST => hbm_axi_rlast(9),
        AXI_09_RRESP => hbm_axi_rresp(9),
        AXI_09_RVALID => hbm_axi_rvalid(9),
        AXI_09_WREADY => hbm_axi_wready(9),
        AXI_09_BID => hbm_axi_bid(9),
        AXI_09_BRESP => hbm_axi_bresp(9),
        AXI_09_BVALID => hbm_axi_bvalid(9),
        AXI_10_ARREADY => hbm_axi_arready(10),
        AXI_10_AWREADY => hbm_axi_awready(10),
        AXI_10_RDATA_PARITY => hbm_axi_rdata_parity(10),
        AXI_10_RDATA => hbm_axi_rdata(10),
        AXI_10_RID => hbm_axi_rid(10),
        AXI_10_RLAST => hbm_axi_rlast(10),
        AXI_10_RRESP => hbm_axi_rresp(10),
        AXI_10_RVALID => hbm_axi_rvalid(10),
        AXI_10_WREADY => hbm_axi_wready(10),
        AXI_10_BID => hbm_axi_bid(10),
        AXI_10_BRESP => hbm_axi_bresp(10),
        AXI_10_BVALID => hbm_axi_bvalid(10),
        AXI_11_ARREADY => hbm_axi_arready(11),
        AXI_11_AWREADY => hbm_axi_awready(11),
        AXI_11_RDATA_PARITY => hbm_axi_rdata_parity(11),
        AXI_11_RDATA => hbm_axi_rdata(11),
        AXI_11_RID => hbm_axi_rid(11),
        AXI_11_RLAST => hbm_axi_rlast(11),
        AXI_11_RRESP => hbm_axi_rresp(11),
        AXI_11_RVALID => hbm_axi_rvalid(11),
        AXI_11_WREADY => hbm_axi_wready(11),
        AXI_11_BID => hbm_axi_bid(11),
        AXI_11_BRESP => hbm_axi_bresp(11),
        AXI_11_BVALID => hbm_axi_bvalid(11),
        AXI_12_ARREADY => hbm_axi_arready(12),
        AXI_12_AWREADY => hbm_axi_awready(12),
        AXI_12_RDATA_PARITY => hbm_axi_rdata_parity(12),
        AXI_12_RDATA => hbm_axi_rdata(12),
        AXI_12_RID => hbm_axi_rid(12),
        AXI_12_RLAST => hbm_axi_rlast(12),
        AXI_12_RRESP => hbm_axi_rresp(12),
        AXI_12_RVALID => hbm_axi_rvalid(12),
        AXI_12_WREADY => hbm_axi_wready(12),
        AXI_12_BID => hbm_axi_bid(12),
        AXI_12_BRESP => hbm_axi_bresp(12),
        AXI_12_BVALID => hbm_axi_bvalid(12),
        AXI_13_ARREADY => hbm_axi_arready(13),
        AXI_13_AWREADY => hbm_axi_awready(13),
        AXI_13_RDATA_PARITY => hbm_axi_rdata_parity(13),
        AXI_13_RDATA => hbm_axi_rdata(13),
        AXI_13_RID => hbm_axi_rid(13),
        AXI_13_RLAST => hbm_axi_rlast(13),
        AXI_13_RRESP => hbm_axi_rresp(13),
        AXI_13_RVALID => hbm_axi_rvalid(13),
        AXI_13_WREADY => hbm_axi_wready(13),
        AXI_13_BID => hbm_axi_bid(13),
        AXI_13_BRESP => hbm_axi_bresp(13),
        AXI_13_BVALID => hbm_axi_bvalid(13),
        AXI_14_ARREADY => hbm_axi_arready(14),
        AXI_14_AWREADY => hbm_axi_awready(14),
        AXI_14_RDATA_PARITY => hbm_axi_rdata_parity(14),
        AXI_14_RDATA => hbm_axi_rdata(14),
        AXI_14_RID => hbm_axi_rid(14),
        AXI_14_RLAST => hbm_axi_rlast(14),
        AXI_14_RRESP => hbm_axi_rresp(14),
        AXI_14_RVALID => hbm_axi_rvalid(14),
        AXI_14_WREADY => hbm_axi_wready(14),
        AXI_14_BID => hbm_axi_bid(14),
        AXI_14_BRESP => hbm_axi_bresp(14),
        AXI_14_BVALID => hbm_axi_bvalid(14),
        AXI_15_ARREADY => hbm_axi_arready(15),
        AXI_15_AWREADY => hbm_axi_awready(15),
        AXI_15_RDATA_PARITY => hbm_axi_rdata_parity(15),
        AXI_15_RDATA => hbm_axi_rdata(15),
        AXI_15_RID => hbm_axi_rid(15),
        AXI_15_RLAST => hbm_axi_rlast(15),
        AXI_15_RRESP => hbm_axi_rresp(15),
        AXI_15_RVALID => hbm_axi_rvalid(15),
        AXI_15_WREADY => hbm_axi_wready(15),
        AXI_15_BID => hbm_axi_bid(15),
        AXI_15_BRESP => hbm_axi_bresp(15),
        AXI_15_BVALID => hbm_axi_bvalid(15),
        AXI_16_ARREADY => hbm_axi_arready(16),
        AXI_16_AWREADY => hbm_axi_awready(16),
        AXI_16_RDATA_PARITY => hbm_axi_rdata_parity(16),
        AXI_16_RDATA => hbm_axi_rdata(16),
        AXI_16_RID => hbm_axi_rid(16),
        AXI_16_RLAST => hbm_axi_rlast(16),
        AXI_16_RRESP => hbm_axi_rresp(16),
        AXI_16_RVALID => hbm_axi_rvalid(16),
        AXI_16_WREADY => hbm_axi_wready(16),
        AXI_16_BID => hbm_axi_bid(16),
        AXI_16_BRESP => hbm_axi_bresp(16),
        AXI_16_BVALID => hbm_axi_bvalid(16),
        AXI_17_ARREADY => hbm_axi_arready(17),
        AXI_17_AWREADY => hbm_axi_awready(17),
        AXI_17_RDATA_PARITY => hbm_axi_rdata_parity(17),
        AXI_17_RDATA => hbm_axi_rdata(17),
        AXI_17_RID => hbm_axi_rid(17),
        AXI_17_RLAST => hbm_axi_rlast(17),
        AXI_17_RRESP => hbm_axi_rresp(17),
        AXI_17_RVALID => hbm_axi_rvalid(17),
        AXI_17_WREADY => hbm_axi_wready(17),
        AXI_17_BID => hbm_axi_bid(17),
        AXI_17_BRESP => hbm_axi_bresp(17),
        AXI_17_BVALID => hbm_axi_bvalid(17),
        AXI_18_ARREADY => hbm_axi_arready(18),
        AXI_18_AWREADY => hbm_axi_awready(18),
        AXI_18_RDATA_PARITY => hbm_axi_rdata_parity(18),
        AXI_18_RDATA => hbm_axi_rdata(18),
        AXI_18_RID => hbm_axi_rid(18),
        AXI_18_RLAST => hbm_axi_rlast(18),
        AXI_18_RRESP => hbm_axi_rresp(18),
        AXI_18_RVALID => hbm_axi_rvalid(18),
        AXI_18_WREADY => hbm_axi_wready(18),
        AXI_18_BID => hbm_axi_bid(18),
        AXI_18_BRESP => hbm_axi_bresp(18),
        AXI_18_BVALID => hbm_axi_bvalid(18),
        AXI_19_ARREADY => hbm_axi_arready(19),
        AXI_19_AWREADY => hbm_axi_awready(19),
        AXI_19_RDATA_PARITY => hbm_axi_rdata_parity(19),
        AXI_19_RDATA => hbm_axi_rdata(19),
        AXI_19_RID => hbm_axi_rid(19),
        AXI_19_RLAST => hbm_axi_rlast(19),
        AXI_19_RRESP => hbm_axi_rresp(19),
        AXI_19_RVALID => hbm_axi_rvalid(19),
        AXI_19_WREADY => hbm_axi_wready(19),
        AXI_19_BID => hbm_axi_bid(19),
        AXI_19_BRESP => hbm_axi_bresp(19),
        AXI_19_BVALID => hbm_axi_bvalid(19),
        AXI_20_ARREADY => hbm_axi_arready(20),
        AXI_20_AWREADY => hbm_axi_awready(20),
        AXI_20_RDATA_PARITY => hbm_axi_rdata_parity(20),
        AXI_20_RDATA => hbm_axi_rdata(20),
        AXI_20_RID => hbm_axi_rid(20),
        AXI_20_RLAST => hbm_axi_rlast(20),
        AXI_20_RRESP => hbm_axi_rresp(20),
        AXI_20_RVALID => hbm_axi_rvalid(20),
        AXI_20_WREADY => hbm_axi_wready(20),
        AXI_20_BID => hbm_axi_bid(20),
        AXI_20_BRESP => hbm_axi_bresp(20),
        AXI_20_BVALID => hbm_axi_bvalid(20),
        AXI_21_ARREADY => hbm_axi_arready(21),
        AXI_21_AWREADY => hbm_axi_awready(21),
        AXI_21_RDATA_PARITY => hbm_axi_rdata_parity(21),
        AXI_21_RDATA => hbm_axi_rdata(21),
        AXI_21_RID => hbm_axi_rid(21),
        AXI_21_RLAST => hbm_axi_rlast(21),
        AXI_21_RRESP => hbm_axi_rresp(21),
        AXI_21_RVALID => hbm_axi_rvalid(21),
        AXI_21_WREADY => hbm_axi_wready(21),
        AXI_21_BID => hbm_axi_bid(21),
        AXI_21_BRESP => hbm_axi_bresp(21),
        AXI_21_BVALID => hbm_axi_bvalid(21),
        AXI_22_ARREADY => hbm_axi_arready(22),
        AXI_22_AWREADY => hbm_axi_awready(22),
        AXI_22_RDATA_PARITY => hbm_axi_rdata_parity(22),
        AXI_22_RDATA => hbm_axi_rdata(22),
        AXI_22_RID => hbm_axi_rid(22),
        AXI_22_RLAST => hbm_axi_rlast(22),
        AXI_22_RRESP => hbm_axi_rresp(22),
        AXI_22_RVALID => hbm_axi_rvalid(22),
        AXI_22_WREADY => hbm_axi_wready(22),
        AXI_22_BID => hbm_axi_bid(22),
        AXI_22_BRESP => hbm_axi_bresp(22),
        AXI_22_BVALID => hbm_axi_bvalid(22),
        AXI_23_ARREADY => hbm_axi_arready(23),
        AXI_23_AWREADY => hbm_axi_awready(23),
        AXI_23_RDATA_PARITY => hbm_axi_rdata_parity(23),
        AXI_23_RDATA => hbm_axi_rdata(23),
        AXI_23_RID => hbm_axi_rid(23),
        AXI_23_RLAST => hbm_axi_rlast(23),
        AXI_23_RRESP => hbm_axi_rresp(23),
        AXI_23_RVALID => hbm_axi_rvalid(23),
        AXI_23_WREADY => hbm_axi_wready(23),
        AXI_23_BID => hbm_axi_bid(23),
        AXI_23_BRESP => hbm_axi_bresp(23),
        AXI_23_BVALID => hbm_axi_bvalid(23),
        AXI_24_ARREADY => hbm_axi_arready(24),
        AXI_24_AWREADY => hbm_axi_awready(24),
        AXI_24_RDATA_PARITY => hbm_axi_rdata_parity(24),
        AXI_24_RDATA => hbm_axi_rdata(24),
        AXI_24_RID => hbm_axi_rid(24),
        AXI_24_RLAST => hbm_axi_rlast(24),
        AXI_24_RRESP => hbm_axi_rresp(24),
        AXI_24_RVALID => hbm_axi_rvalid(24),
        AXI_24_WREADY => hbm_axi_wready(24),
        AXI_24_BID => hbm_axi_bid(24),
        AXI_24_BRESP => hbm_axi_bresp(24),
        AXI_24_BVALID => hbm_axi_bvalid(24),
        AXI_25_ARREADY => hbm_axi_arready(25),
        AXI_25_AWREADY => hbm_axi_awready(25),
        AXI_25_RDATA_PARITY => hbm_axi_rdata_parity(25),
        AXI_25_RDATA => hbm_axi_rdata(25),
        AXI_25_RID => hbm_axi_rid(25),
        AXI_25_RLAST => hbm_axi_rlast(25),
        AXI_25_RRESP => hbm_axi_rresp(25),
        AXI_25_RVALID => hbm_axi_rvalid(25),
        AXI_25_WREADY => hbm_axi_wready(25),
        AXI_25_BID => hbm_axi_bid(25),
        AXI_25_BRESP => hbm_axi_bresp(25),
        AXI_25_BVALID => hbm_axi_bvalid(25),
        AXI_26_ARREADY => hbm_axi_arready(26),
        AXI_26_AWREADY => hbm_axi_awready(26),
        AXI_26_RDATA_PARITY => hbm_axi_rdata_parity(26),
        AXI_26_RDATA => hbm_axi_rdata(26),
        AXI_26_RID => hbm_axi_rid(26),
        AXI_26_RLAST => hbm_axi_rlast(26),
        AXI_26_RRESP => hbm_axi_rresp(26),
        AXI_26_RVALID => hbm_axi_rvalid(26),
        AXI_26_WREADY => hbm_axi_wready(26),
        AXI_26_BID => hbm_axi_bid(26),
        AXI_26_BRESP => hbm_axi_bresp(26),
        AXI_26_BVALID => hbm_axi_bvalid(26),
        AXI_27_ARREADY => hbm_axi_arready(27),
        AXI_27_AWREADY => hbm_axi_awready(27),
        AXI_27_RDATA_PARITY => hbm_axi_rdata_parity(27),
        AXI_27_RDATA => hbm_axi_rdata(27),
        AXI_27_RID => hbm_axi_rid(27),
        AXI_27_RLAST => hbm_axi_rlast(27),
        AXI_27_RRESP => hbm_axi_rresp(27),
        AXI_27_RVALID => hbm_axi_rvalid(27),
        AXI_27_WREADY => hbm_axi_wready(27),
        AXI_27_BID => hbm_axi_bid(27),
        AXI_27_BRESP => hbm_axi_bresp(27),
        AXI_27_BVALID => hbm_axi_bvalid(27),
        AXI_28_ARREADY => hbm_axi_arready(28),
        AXI_28_AWREADY => hbm_axi_awready(28),
        AXI_28_RDATA_PARITY => hbm_axi_rdata_parity(28),
        AXI_28_RDATA => hbm_axi_rdata(28),
        AXI_28_RID => hbm_axi_rid(28),
        AXI_28_RLAST => hbm_axi_rlast(28),
        AXI_28_RRESP => hbm_axi_rresp(28),
        AXI_28_RVALID => hbm_axi_rvalid(28),
        AXI_28_WREADY => hbm_axi_wready(28),
        AXI_28_BID => hbm_axi_bid(28),
        AXI_28_BRESP => hbm_axi_bresp(28),
        AXI_28_BVALID => hbm_axi_bvalid(28),
        AXI_29_ARREADY => hbm_axi_arready(29),
        AXI_29_AWREADY => hbm_axi_awready(29),
        AXI_29_RDATA_PARITY => hbm_axi_rdata_parity(29),
        AXI_29_RDATA => hbm_axi_rdata(29),
        AXI_29_RID => hbm_axi_rid(29),
        AXI_29_RLAST => hbm_axi_rlast(29),
        AXI_29_RRESP => hbm_axi_rresp(29),
        AXI_29_RVALID => hbm_axi_rvalid(29),
        AXI_29_WREADY => hbm_axi_wready(29),
        AXI_29_BID => hbm_axi_bid(29),
        AXI_29_BRESP => hbm_axi_bresp(29),
        AXI_29_BVALID => hbm_axi_bvalid(29),
        AXI_30_ARREADY => hbm_axi_arready(30),
        AXI_30_AWREADY => hbm_axi_awready(30),
        AXI_30_RDATA_PARITY => hbm_axi_rdata_parity(30),
        AXI_30_RDATA => hbm_axi_rdata(30),
        AXI_30_RID => hbm_axi_rid(30),
        AXI_30_RLAST => hbm_axi_rlast(30),
        AXI_30_RRESP => hbm_axi_rresp(30),
        AXI_30_RVALID => hbm_axi_rvalid(30),
        AXI_30_WREADY => hbm_axi_wready(30),
        AXI_30_BID => hbm_axi_bid(30),
        AXI_30_BRESP => hbm_axi_bresp(30),
        AXI_30_BVALID => hbm_axi_bvalid(30),
        AXI_31_ARREADY => hbm_axi_arready(31),
        AXI_31_AWREADY => hbm_axi_awready(31),
        AXI_31_RDATA_PARITY => hbm_axi_rdata_parity(31),
        AXI_31_RDATA => hbm_axi_rdata(31),
        AXI_31_RID => hbm_axi_rid(31),
        AXI_31_RLAST => hbm_axi_rlast(31),
        AXI_31_RRESP => hbm_axi_rresp(31),
        AXI_31_RVALID => hbm_axi_rvalid(31),
        AXI_31_WREADY => hbm_axi_wready(31),
        AXI_31_BID => hbm_axi_bid(31),
        AXI_31_BRESP => hbm_axi_bresp(31),
        AXI_31_BVALID => hbm_axi_bvalid(31)
    );
end architecture;
