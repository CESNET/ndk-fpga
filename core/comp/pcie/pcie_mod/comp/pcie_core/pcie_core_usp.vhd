-- pcie_core_usp.vhd: PCIe module for USP devices
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;

library unisim;
use unisim.vcomponents.all;

-- ============================================================================
--                                Description
-- ============================================================================

-- This is the specific wrapper around the Xilinx UlstraScale PCIe IP core.
--
architecture USP of PCIE_CORE is

    constant VSEC_BASE_ADDRESS : natural := tsel(ENDPOINT_TYPE = "USP_PCIE4C", 16#E80#, 16#480#);
    constant XVC_BASE_ADDRESS  : natural := tsel(ENDPOINT_TYPE = "USP_PCIE4C", 16#EA0#, 16#4A0#);
    constant DTB_NEXT_POINTER  : natural := tsel(XVC_ENABLE, XVC_BASE_ADDRESS, 0);

    constant PCIE_HIPS         : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1 or ENDPOINT_MODE = 2),PCIE_ENDPOINTS,PCIE_ENDPOINTS/2);
    constant PCIE_IP_LANES     : natural := tsel(ENDPOINT_MODE = 1, PCIE_LANES/2, PCIE_LANES);
    constant AXI_DATA_WIDTH    : natural := CQ_MFB_REGIONS*256;
    constant AXI_CQUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 183, 88);
    constant AXI_CCUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 81, 33);
    constant AXI_RQUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 137, 62);
    constant AXI_RCUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 161, 75);

    component pcie4_uscale_plus is
        port (
            USER_CLK                               :  out  std_logic;
            USER_RESET                             :  out  std_logic;
            USER_LNK_UP                            :  out  std_logic;

            PCI_EXP_RXP                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
            PCI_EXP_RXN                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
            PCI_EXP_TXP                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);
            PCI_EXP_TXN                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);

            S_AXIS_RQ_TDATA                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            S_AXIS_RQ_TKEEP                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            S_AXIS_RQ_TLAST                        :  in   std_logic;
            S_AXIS_RQ_TREADY                       :  out  std_logic_vector(3     downto  0);
            S_AXIS_RQ_TUSER                        :  in   std_logic_vector(AXI_RQUSER_WIDTH-1  downto 0);
            S_AXIS_RQ_TVALID                       :  in   std_logic;
            M_AXIS_RC_TDATA                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            M_AXIS_RC_TKEEP                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            M_AXIS_RC_TLAST                        :  out  std_logic;
            M_AXIS_RC_TREADY                       :  in   std_logic;
            M_AXIS_RC_TUSER                        :  out  std_logic_vector(AXI_RCUSER_WIDTH-1  downto 0);
            M_AXIS_RC_TVALID                       :  out  std_logic;
            M_AXIS_CQ_TDATA                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            M_AXIS_CQ_TKEEP                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            M_AXIS_CQ_TLAST                        :  out  std_logic;
            M_AXIS_CQ_TREADY                       :  in   std_logic;
            M_AXIS_CQ_TUSER                        :  out  std_logic_vector(AXI_CQUSER_WIDTH-1  downto 0);
            M_AXIS_CQ_TVALID                       :  out  std_logic;
            S_AXIS_CC_TDATA                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            S_AXIS_CC_TKEEP                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            S_AXIS_CC_TLAST                        :  in   std_logic;
            S_AXIS_CC_TREADY                       :  out  std_logic_vector(3     downto  0);
            S_AXIS_CC_TUSER                        :  in   std_logic_vector(AXI_CCUSER_WIDTH-1  downto 0);
            S_AXIS_CC_TVALID                       :  in   std_logic;
            PCIE_RQ_SEQ_NUM0                       :  out  std_logic_vector(5     downto  0);
            PCIE_RQ_SEQ_NUM_VLD0                   :  out  std_logic;
            PCIE_RQ_SEQ_NUM1                       :  out  std_logic_vector(5     downto  0);
            PCIE_RQ_SEQ_NUM_VLD1                   :  out  std_logic;
            PCIE_RQ_TAG0                           :  out  std_logic_vector(7     downto  0);
            PCIE_RQ_TAG1                           :  out  std_logic_vector(7     downto  0);
            PCIE_RQ_TAG_AV                         :  out  std_logic_vector(3     downto  0);
            PCIE_RQ_TAG_VLD0                       :  out  std_logic;
            PCIE_RQ_TAG_VLD1                       :  out  std_logic;
            PCIE_CQ_NP_REQ                         :  in   std_logic_vector(1     downto  0);
            PCIE_CQ_NP_REQ_COUNT                   :  out  std_logic_vector(5     downto  0);
            CFG_PHY_LINK_DOWN                      :  out  std_logic;
            CFG_PHY_LINK_STATUS                    :  out  std_logic_vector(1     downto  0);
            CFG_NEGOTIATED_WIDTH                   :  out  std_logic_vector(2     downto  0);
            CFG_CURRENT_SPEED                      :  out  std_logic_vector(1     downto  0);
            CFG_MAX_PAYLOAD                        :  out  std_logic_vector(1     downto  0);
            CFG_MAX_READ_REQ                       :  out  std_logic_vector(2     downto  0);
            CFG_FUNCTION_STATUS                    :  out  std_logic_vector(15    downto  0);
            CFG_FUNCTION_POWER_STATE               :  out  std_logic_vector(11    downto  0);
            CFG_VF_STATUS                          :  out  std_logic_vector(503   downto  0);
            CFG_VF_POWER_STATE                     :  out  std_logic_vector(755   downto  0);
            CFG_LINK_POWER_STATE                   :  out  std_logic_vector(1     downto  0);
            CFG_ERR_COR_OUT                        :  out  std_logic;
            CFG_ERR_NONFATAL_OUT                   :  out  std_logic;
            CFG_ERR_FATAL_OUT                      :  out  std_logic;
            CFG_LOCAL_ERROR_VALID                  :  out  std_logic;
            CFG_LOCAL_ERROR_OUT                    :  out  std_logic_vector(4     downto  0);
            CFG_LTSSM_STATE                        :  out  std_logic_vector(5     downto  0);
            CFG_RX_PM_STATE                        :  out  std_logic_vector(1     downto  0);
            CFG_TX_PM_STATE                        :  out  std_logic_vector(1     downto  0);
            CFG_RCB_STATUS                         :  out  std_logic_vector(3     downto  0);
            CFG_OBFF_ENABLE                        :  out  std_logic_vector(1     downto  0);
            CFG_PL_STATUS_CHANGE                   :  out  std_logic;
            CFG_TPH_REQUESTER_ENABLE               :  out  std_logic_vector(3     downto  0);
            CFG_TPH_ST_MODE                        :  out  std_logic_vector(11    downto  0);
            CFG_VF_TPH_REQUESTER_ENABLE            :  out  std_logic_vector(251   downto  0);
            CFG_VF_TPH_ST_MODE                     :  out  std_logic_vector(755   downto  0);
            CFG_DSN                                :  in   std_logic_vector(63    downto  0);
            CFG_BUS_NUMBER                         :  out  std_logic_vector(7     downto  0);
            CFG_FC_PH                              :  out  std_logic_vector(7    downto  0);
            CFG_FC_PD                              :  out  std_logic_vector(11   downto  0);
            CFG_FC_NPH                             :  out  std_logic_vector(7    downto  0);
            CFG_FC_NPD                             :  out  std_logic_vector(11   downto  0);
            CFG_FC_CPLH                            :  out  std_logic_vector(7    downto  0);
            CFG_FC_CPLD                            :  out  std_logic_vector(11   downto  0);
            CFG_FC_SEL                             :  in   std_logic_vector(2    downto  0);
            CFG_POWER_STATE_CHANGE_ACK             :  in   std_logic;
            CFG_POWER_STATE_CHANGE_INTERRUPT       :  out  std_logic;
            CFG_ERR_COR_IN                         :  in   std_logic;
            CFG_ERR_UNCOR_IN                       :  in   std_logic;
            CFG_FLR_IN_PROCESS                     :  out  std_logic_vector(3     downto  0);
            CFG_FLR_DONE                           :  in   std_logic_vector(3     downto  0);
            CFG_VF_FLR_IN_PROCESS                  :  out  std_logic_vector(251   downto  0);
            CFG_VF_FLR_FUNC_NUM                    :  in   std_logic_vector(7     downto  0);
            CFG_VF_FLR_DONE                        :  in   std_logic_vector(0     downto  0);
            CFG_LINK_TRAINING_ENABLE               :  in   std_logic;
            CFG_EXT_READ_RECEIVED                  :  out  std_logic;
            CFG_EXT_WRITE_RECEIVED                 :  out  std_logic;
            CFG_EXT_REGISTER_NUMBER                :  out  std_logic_vector(9     downto  0);
            CFG_EXT_FUNCTION_NUMBER                :  out  std_logic_vector(7     downto  0);
            CFG_EXT_WRITE_DATA                     :  out  std_logic_vector(31    downto  0);
            CFG_EXT_WRITE_BYTE_ENABLE              :  out  std_logic_vector(3     downto  0);
            CFG_EXT_READ_DATA                      :  in   std_logic_vector(31    downto  0);
            CFG_EXT_READ_DATA_VALID                :  in   std_logic;
            CFG_INTERRUPT_INT                      :  in   std_logic_vector(3    downto  0);
            CFG_INTERRUPT_PENDING                  :  in   std_logic_vector(3    downto  0);
            CFG_INTERRUPT_SENT                     :  out  std_logic;
            CFG_HOT_RESET_OUT                      :  out  std_logic;
            CFG_CONFIG_SPACE_ENABLE                :  in   std_logic;
            CFG_REQ_PM_TRANSITION_L23_READY        :  in   std_logic;
            CFG_HOT_RESET_IN                       :  in   std_logic;
            CFG_DS_PORT_NUMBER                     :  in   std_logic_vector(7     downto  0);
            CFG_DS_BUS_NUMBER                      :  in   std_logic_vector(7     downto  0);
            CFG_DS_DEVICE_NUMBER                   :  in   std_logic_vector(4     downto  0);
            SYS_CLK                                :  in   std_logic;
            SYS_CLK_GT                             :  in   std_logic;
            SYS_RESET                              :  in   std_logic;
            PHY_RDY_OUT                            :  out  std_logic
        );
    end component;

    component pcie4_uscale_plus_1 is
        port (
            USER_CLK                               :  out  std_logic;
            USER_RESET                             :  out  std_logic;
            USER_LNK_UP                            :  out  std_logic;

            PCI_EXP_RXP                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
            PCI_EXP_RXN                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
            PCI_EXP_TXP                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);
            PCI_EXP_TXN                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);

            S_AXIS_RQ_TDATA                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            S_AXIS_RQ_TKEEP                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            S_AXIS_RQ_TLAST                        :  in   std_logic;
            S_AXIS_RQ_TREADY                       :  out  std_logic_vector(3     downto  0);
            S_AXIS_RQ_TUSER                        :  in   std_logic_vector(AXI_RQUSER_WIDTH-1  downto 0);
            S_AXIS_RQ_TVALID                       :  in   std_logic;
            M_AXIS_RC_TDATA                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            M_AXIS_RC_TKEEP                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            M_AXIS_RC_TLAST                        :  out  std_logic;
            M_AXIS_RC_TREADY                       :  in   std_logic;
            M_AXIS_RC_TUSER                        :  out  std_logic_vector(AXI_RCUSER_WIDTH-1  downto 0);
            M_AXIS_RC_TVALID                       :  out  std_logic;
            M_AXIS_CQ_TDATA                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            M_AXIS_CQ_TKEEP                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            M_AXIS_CQ_TLAST                        :  out  std_logic;
            M_AXIS_CQ_TREADY                       :  in   std_logic;
            M_AXIS_CQ_TUSER                        :  out  std_logic_vector(AXI_CQUSER_WIDTH-1  downto 0);
            M_AXIS_CQ_TVALID                       :  out  std_logic;
            S_AXIS_CC_TDATA                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
            S_AXIS_CC_TKEEP                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
            S_AXIS_CC_TLAST                        :  in   std_logic;
            S_AXIS_CC_TREADY                       :  out  std_logic_vector(3     downto  0);
            S_AXIS_CC_TUSER                        :  in   std_logic_vector(AXI_CCUSER_WIDTH-1  downto 0);
            S_AXIS_CC_TVALID                       :  in   std_logic;
            PCIE_RQ_SEQ_NUM0                       :  out  std_logic_vector(5     downto  0);
            PCIE_RQ_SEQ_NUM_VLD0                   :  out  std_logic;
            PCIE_RQ_SEQ_NUM1                       :  out  std_logic_vector(5     downto  0);
            PCIE_RQ_SEQ_NUM_VLD1                   :  out  std_logic;
            PCIE_RQ_TAG0                           :  out  std_logic_vector(7     downto  0);
            PCIE_RQ_TAG1                           :  out  std_logic_vector(7     downto  0);
            PCIE_RQ_TAG_AV                         :  out  std_logic_vector(3     downto  0);
            PCIE_RQ_TAG_VLD0                       :  out  std_logic;
            PCIE_RQ_TAG_VLD1                       :  out  std_logic;
            PCIE_CQ_NP_REQ                         :  in   std_logic_vector(1     downto  0);
            PCIE_CQ_NP_REQ_COUNT                   :  out  std_logic_vector(5     downto  0);
            CFG_PHY_LINK_DOWN                      :  out  std_logic;
            CFG_PHY_LINK_STATUS                    :  out  std_logic_vector(1     downto  0);
            CFG_NEGOTIATED_WIDTH                   :  out  std_logic_vector(2     downto  0);
            CFG_CURRENT_SPEED                      :  out  std_logic_vector(1     downto  0);
            CFG_MAX_PAYLOAD                        :  out  std_logic_vector(1     downto  0);
            CFG_MAX_READ_REQ                       :  out  std_logic_vector(2     downto  0);
            CFG_FUNCTION_STATUS                    :  out  std_logic_vector(15    downto  0);
            CFG_FUNCTION_POWER_STATE               :  out  std_logic_vector(11    downto  0);
            CFG_VF_STATUS                          :  out  std_logic_vector(503   downto  0);
            CFG_VF_POWER_STATE                     :  out  std_logic_vector(755   downto  0);
            CFG_LINK_POWER_STATE                   :  out  std_logic_vector(1     downto  0);
            CFG_ERR_COR_OUT                        :  out  std_logic;
            CFG_ERR_NONFATAL_OUT                   :  out  std_logic;
            CFG_ERR_FATAL_OUT                      :  out  std_logic;
            CFG_LOCAL_ERROR_VALID                  :  out  std_logic;
            CFG_LOCAL_ERROR_OUT                    :  out  std_logic_vector(4     downto  0);
            CFG_LTSSM_STATE                        :  out  std_logic_vector(5     downto  0);
            CFG_RX_PM_STATE                        :  out  std_logic_vector(1     downto  0);
            CFG_TX_PM_STATE                        :  out  std_logic_vector(1     downto  0);
            CFG_RCB_STATUS                         :  out  std_logic_vector(3     downto  0);
            CFG_OBFF_ENABLE                        :  out  std_logic_vector(1     downto  0);
            CFG_PL_STATUS_CHANGE                   :  out  std_logic;
            CFG_TPH_REQUESTER_ENABLE               :  out  std_logic_vector(3     downto  0);
            CFG_TPH_ST_MODE                        :  out  std_logic_vector(11    downto  0);
            CFG_VF_TPH_REQUESTER_ENABLE            :  out  std_logic_vector(251   downto  0);
            CFG_VF_TPH_ST_MODE                     :  out  std_logic_vector(755   downto  0);
            CFG_DSN                                :  in   std_logic_vector(63    downto  0);
            CFG_BUS_NUMBER                         :  out  std_logic_vector(7     downto  0);
            CFG_FC_PH                              :  out  std_logic_vector(7    downto  0);
            CFG_FC_PD                              :  out  std_logic_vector(11   downto  0);
            CFG_FC_NPH                             :  out  std_logic_vector(7    downto  0);
            CFG_FC_NPD                             :  out  std_logic_vector(11   downto  0);
            CFG_FC_CPLH                            :  out  std_logic_vector(7    downto  0);
            CFG_FC_CPLD                            :  out  std_logic_vector(11   downto  0);
            CFG_FC_SEL                             :  in   std_logic_vector(2    downto  0);
            CFG_POWER_STATE_CHANGE_ACK             :  in   std_logic;
            CFG_POWER_STATE_CHANGE_INTERRUPT       :  out  std_logic;
            CFG_ERR_COR_IN                         :  in   std_logic;
            CFG_ERR_UNCOR_IN                       :  in   std_logic;
            CFG_FLR_IN_PROCESS                     :  out  std_logic_vector(3     downto  0);
            CFG_FLR_DONE                           :  in   std_logic_vector(3     downto  0);
            CFG_VF_FLR_IN_PROCESS                  :  out  std_logic_vector(251   downto  0);
            CFG_VF_FLR_FUNC_NUM                    :  in   std_logic_vector(7     downto  0);
            CFG_VF_FLR_DONE                        :  in   std_logic_vector(0     downto  0);
            CFG_LINK_TRAINING_ENABLE               :  in   std_logic;
            CFG_EXT_READ_RECEIVED                  :  out  std_logic;
            CFG_EXT_WRITE_RECEIVED                 :  out  std_logic;
            CFG_EXT_REGISTER_NUMBER                :  out  std_logic_vector(9     downto  0);
            CFG_EXT_FUNCTION_NUMBER                :  out  std_logic_vector(7     downto  0);
            CFG_EXT_WRITE_DATA                     :  out  std_logic_vector(31    downto  0);
            CFG_EXT_WRITE_BYTE_ENABLE              :  out  std_logic_vector(3     downto  0);
            CFG_EXT_READ_DATA                      :  in   std_logic_vector(31    downto  0);
            CFG_EXT_READ_DATA_VALID                :  in   std_logic;
            CFG_INTERRUPT_INT                      :  in   std_logic_vector(3    downto  0);
            CFG_INTERRUPT_PENDING                  :  in   std_logic_vector(3    downto  0);
            CFG_INTERRUPT_SENT                     :  out  std_logic;
            CFG_HOT_RESET_OUT                      :  out  std_logic;
            CFG_CONFIG_SPACE_ENABLE                :  in   std_logic;
            CFG_REQ_PM_TRANSITION_L23_READY        :  in   std_logic;
            CFG_HOT_RESET_IN                       :  in   std_logic;
            CFG_DS_PORT_NUMBER                     :  in   std_logic_vector(7     downto  0);
            CFG_DS_BUS_NUMBER                      :  in   std_logic_vector(7     downto  0);
            CFG_DS_DEVICE_NUMBER                   :  in   std_logic_vector(4     downto  0);
            SYS_CLK                                :  in   std_logic;
            SYS_CLK_GT                             :  in   std_logic;
            SYS_RESET                              :  in   std_logic;
            PHY_RDY_OUT                            :  out  std_logic
        );
    end component;

    component xvc_vsec is
        port (
            CLK                                : in    std_logic;
            PCIE3_CFG_EXT_FUNCTION_NUMBER      : in    std_logic_vector(7 downto 0);
            PCIE3_CFG_EXT_READ_DATA            : out   std_logic_vector(31 downto 0);
            PCIE3_CFG_EXT_READ_DATA_VALID      : out   std_logic;
            PCIE3_CFG_EXT_READ_RECEIVED        : in    std_logic;
            PCIE3_CFG_EXT_REGISTER_NUMBER      : in    std_logic_vector(9 downto 0);
            PCIE3_CFG_EXT_WRITE_BYTE_ENABLE    : in    std_logic_vector(3 downto 0);
            PCIE3_CFG_EXT_WRITE_DATA           : in    std_logic_vector(31 downto 0);
            PCIE3_CFG_EXT_WRITE_RECEIVED       : in    std_logic
        );
    end component;

    signal pcie_sysclk_buf          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_sysclk_gt_buf       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_hip_clk             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_hip_rst             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst_async           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);

    signal cfg_rcb_status           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_max_payload          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal cfg_max_read_req         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal cfg_phy_link_status      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal user_lnk_up              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_function         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_xvc_data    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_xvc_dv      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal cfg_ext_read_dtb_data    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dtb_dv      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cq_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cq_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CQUSER_WIDTH-1 downto 0);
    signal pcie_cq_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cq_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cc_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CCUSER_WIDTH-1 downto 0);
    signal pcie_cc_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cc_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rq_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RQUSER_WIDTH-1 downto 0);
    signal pcie_rq_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rq_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rc_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RCUSER_WIDTH-1 downto 0);
    signal pcie_rc_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rc_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal s_axis_rq_tready         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal s_axis_cc_tready         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);

    signal tag_assign_int       : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(16 -1 downto 0);
    signal tag_assign_vld_int   : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(2 -1 downto 0);

    --==============================================================================================
    -- Inserting Debug nets:
    --==============================================================================================
    signal cfg_phy_link_down        : std_logic_vector(PCIE_ENDPOINTS -1 downto 0);
    signal pcie_phy_rdy_out         : std_logic_vector(PCIE_ENDPOINTS -1 downto 0);
    signal cfg_negotiated_width     : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(2 downto 0);
    signal cfg_current_speed        : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_function_status      : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(15 downto 0);
    signal cfg_function_power_state : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(11 downto 0);
    signal cfg_link_power_state     : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_local_error_out      : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(4 downto 0);
    signal cfg_local_error_valid    : std_logic_vector(PCIE_ENDPOINTS -1 downto 0);
    signal cfg_rx_pm_state          : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_tx_pm_state          : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_ltssm_state          : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(5 downto 0);

    -- attribute mark_debug                 : string;
    -- special signals for debugging
    -- attribute mark_debug of pcie_cq_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_valid : signal is "true";

    -- attribute mark_debug of pcie_cc_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_valid : signal is "true";

    -- attribute mark_debug of pcie_rc_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_valid : signal is "true";

    -- attribute mark_debug of cfg_phy_link_down        : signal is "true";
    -- attribute mark_debug of cfg_phy_link_status      : signal is "true";
    -- attribute mark_debug of pcie_phy_rdy_out         : signal is "true";
    -- attribute mark_debug of cfg_max_payload          : signal is "true";
    -- attribute mark_debug of cfg_max_read_req         : signal is "true";

    -- attribute mark_debug of cfg_negotiated_width     : signal is "true";
    -- attribute mark_debug of cfg_current_speed        : signal is "true";
    -- attribute mark_debug of cfg_function_status      : signal is "true";
    -- attribute mark_debug of cfg_function_power_state : signal is "true";
    -- attribute mark_debug of cfg_link_power_state     : signal is "true";
    -- attribute mark_debug of cfg_rx_pm_state          : signal is "true";
    -- attribute mark_debug of cfg_tx_pm_state          : signal is "true";
    -- attribute mark_debug of cfg_ltssm_state          : signal is "true";
    -- attribute mark_debug of cfg_local_error_out      : signal is "true";
    -- attribute mark_debug of cfg_local_error_valid    : signal is "true";

    --==============================================================================================
    -- Other debug signals
    --==============================================================================================
    signal dbg_credits_ph     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)( 7 downto 0);
    signal dbg_credits_pd     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal dbg_credits_nph    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)( 7 downto 0);
    signal dbg_credits_npd    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    --==============================================================================================

begin

    assert (ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1 or ENDPOINT_MODE = 2)
        report "Xilinx USP PCIe Wrapper: Only values 0, 1 and 2 are supported for parameter ENDPOINT_MODE!"
        severity failure;

    assert (PCIE_ENDPOINTS = 1 or PCIE_ENDPOINTS = 2)
        report "Xilinx USP PCIe Wrapper: Only values 0 and 1 are supported for parameter PCIE_ENDPOINTS!"
        severity failure;

    assert DEVICE = "ULTRASCALE"
        report "Xilinx USP PCIe Wrapper: Only ULTRASCALE+ device is supported!"
        severity failure;

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_mode_0_2_g : if (ENDPOINT_MODE = 0 or ENDPOINT_MODE = 2) generate

        pcie_hip_g : for i in 0 to PCIE_HIPS-1 generate
            pcie_ibuf_i : component ibufds_gte4
            generic map (
                REFCLK_HROW_CK_SEL => "00"
            )
            port map (
                I     => PCIE_SYSCLK_P(i*PCIE_CLKS),
                IB    => PCIE_SYSCLK_N(i*PCIE_CLKS),
                O     => pcie_sysclk_gt_buf(i),
                ODIV2 => pcie_sysclk_buf(i),
                CEB   => '0'
            );

            pcie_rq_axi_ready(i) <= s_axis_rq_tready(i)(0);
            pcie_cc_axi_ready(i) <= s_axis_cc_tready(i)(0);

            pcie_clk(i) <= pcie_hip_clk(i);

            TAG_ASSIGN(i)     <= tag_assign_int(i)(RQ_MFB_REGIONS*8 -1 downto 0);
            TAG_ASSIGN_VLD(i) <= tag_assign_vld_int(i)(RQ_MFB_REGIONS -1 downto 0);

            pcie0_g : if (i = 0) generate
                pcie_i : component pcie4_uscale_plus
                port map (
                    sys_clk                           => pcie_sysclk_buf(i),
                    sys_clk_gt                        => pcie_sysclk_gt_buf(i),
                    sys_reset                         => PCIE_SYSRST_N(i),

                    pci_exp_txn                       => PCIE_TX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_txp                       => PCIE_TX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxn                       => PCIE_RX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxp                       => PCIE_RX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),

                    user_clk                          => pcie_hip_clk(i),
                    user_reset                        => pcie_hip_rst(i),
                    user_lnk_up                       => user_lnk_up(i),

                    s_axis_rq_tlast                   => pcie_rq_axi_last(i),
                    s_axis_rq_tdata                   => pcie_rq_axi_data(i),
                    s_axis_rq_tuser                   => pcie_rq_axi_user(i),
                    s_axis_rq_tkeep                   => pcie_rq_axi_keep(i),
                    s_axis_rq_tready                  => s_axis_rq_tready(i),
                    s_axis_rq_tvalid                  => pcie_rq_axi_valid(i),
                    m_axis_rc_tdata                   => pcie_rc_axi_data(i),
                    m_axis_rc_tuser                   => pcie_rc_axi_user(i),
                    m_axis_rc_tlast                   => pcie_rc_axi_last(i),
                    m_axis_rc_tkeep                   => pcie_rc_axi_keep(i),
                    m_axis_rc_tvalid                  => pcie_rc_axi_valid(i),
                    m_axis_rc_tready                  => pcie_rc_axi_ready(i),
                    m_axis_cq_tdata                   => pcie_cq_axi_data(i),
                    m_axis_cq_tuser                   => pcie_cq_axi_user(i),
                    m_axis_cq_tlast                   => pcie_cq_axi_last(i),
                    m_axis_cq_tkeep                   => pcie_cq_axi_keep(i),
                    m_axis_cq_tvalid                  => pcie_cq_axi_valid(i),
                    m_axis_cq_tready                  => pcie_cq_axi_ready(i),
                    s_axis_cc_tdata                   => pcie_cc_axi_data(i),
                    s_axis_cc_tuser                   => pcie_cc_axi_user(i),
                    s_axis_cc_tlast                   => pcie_cc_axi_last(i),
                    s_axis_cc_tkeep                   => pcie_cc_axi_keep(i),
                    s_axis_cc_tvalid                  => pcie_cc_axi_valid(i),
                    s_axis_cc_tready                  => s_axis_cc_tready(i),

                    pcie_rq_seq_num0                  => open,
                    pcie_rq_seq_num_vld0              => open,
                    pcie_rq_tag0                      => tag_assign_int(i)(7 downto 0),
                    pcie_rq_tag_vld0                  => tag_assign_vld_int(i)(0),
                    pcie_rq_tag1                      => tag_assign_int(i)(15 downto 8),
                    pcie_rq_tag_vld1                  => tag_assign_vld_int(i)(1),

                    pcie_cq_np_req                    => (others => '1'),
                    pcie_cq_np_req_count              => open,

                    cfg_phy_link_down                 => cfg_phy_link_down(i),
                    cfg_phy_link_status               => cfg_phy_link_status(i),
                    cfg_negotiated_width              => cfg_negotiated_width(i),
                    cfg_current_speed                 => cfg_current_speed(i),
                    cfg_max_payload                   => cfg_max_payload(i),
                    cfg_max_read_req                  => cfg_max_read_req(i),
                    cfg_function_status               => cfg_function_status(i),
                    cfg_function_power_state          => cfg_function_power_state(i),
                    cfg_vf_status                     => open,
                    cfg_vf_power_state                => open,
                    cfg_link_power_state              => cfg_link_power_state(i),
                    cfg_err_cor_out                   => open,
                    cfg_err_nonfatal_out              => open,
                    cfg_err_fatal_out                 => open,
                    cfg_local_error_valid             => cfg_local_error_valid(i),
                    cfg_local_error_out               => cfg_local_error_out(i),
                    cfg_ltssm_state                   => cfg_ltssm_state(i),
                    cfg_rx_pm_state                   => cfg_rx_pm_state(i),
                    cfg_tx_pm_state                   => cfg_tx_pm_state(i),
                    cfg_rcb_status                    => cfg_rcb_status(i),
                    cfg_obff_enable                   => open,
                    cfg_pl_status_change              => open,
                    cfg_tph_requester_enable          => open,
                    cfg_tph_st_mode                   => open,
                    cfg_vf_tph_requester_enable       => open,
                    cfg_vf_tph_st_mode                => open,
                    cfg_dsn                           => (others => '0'),
                    cfg_bus_number                    => open,
                    cfg_fc_ph                         => dbg_credits_ph (i),
                    cfg_fc_pd                         => dbg_credits_pd (i),
                    cfg_fc_nph                        => dbg_credits_nph(i),
                    cfg_fc_npd                        => dbg_credits_npd(i),
                    cfg_fc_cplh                       => open,
                    cfg_fc_cpld                       => open,
                    cfg_fc_sel                        => (others => '0'),
                    cfg_power_state_change_ack        => '0',
                    cfg_power_state_change_interrupt  => open,
                    cfg_err_cor_in                    => '0',
                    cfg_err_uncor_in                  => '0',
                    cfg_flr_in_process                => open,
                    cfg_flr_done                      => (others => '0'),
                    cfg_vf_flr_in_process             => open,
                    cfg_vf_flr_func_num               => (others => '0'),
                    cfg_vf_flr_done                   => (others => '0'),
                    cfg_link_training_enable          => '1',
                    cfg_ext_read_received             => cfg_ext_read(i),
                    cfg_ext_write_received            => cfg_ext_write(i),
                    cfg_ext_register_number           => cfg_ext_register(i),
                    cfg_ext_function_number           => cfg_ext_function(i),
                    cfg_ext_write_data                => cfg_ext_write_data(i),
                    cfg_ext_write_byte_enable         => cfg_ext_write_be(i),
                    cfg_ext_read_data                 => cfg_ext_read_data(i),
                    cfg_ext_read_data_valid           => cfg_ext_read_dv(i),
                    cfg_interrupt_int                 => (others => '0'),
                    cfg_interrupt_pending             => (others => '0'),
                    cfg_interrupt_sent                => open,
                    cfg_hot_reset_out                 => open,
                    cfg_config_space_enable           => '1',
                    cfg_req_pm_transition_l23_ready   => '0',
                    cfg_hot_reset_in                  => '0',
                    cfg_ds_port_number                => (others => '0'),
                    cfg_ds_bus_number                 => (others => '0'),
                    cfg_ds_device_number              => (others => '0'),
                    phy_rdy_out                       => pcie_phy_rdy_out(i)
                );
            end generate;
            pcie1_g : if (i = 1) generate
                pcie_i : component pcie4_uscale_plus_1
                port map (
                    sys_clk                           => pcie_sysclk_buf(i),
                    sys_clk_gt                        => pcie_sysclk_gt_buf(i),
                    sys_reset                         => PCIE_SYSRST_N(i),

                    pci_exp_txn                       => PCIE_TX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_txp                       => PCIE_TX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxn                       => PCIE_RX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxp                       => PCIE_RX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),

                    user_clk                          => pcie_hip_clk(i),
                    user_reset                        => pcie_hip_rst(i),
                    user_lnk_up                       => user_lnk_up(i),

                    s_axis_rq_tlast                   => pcie_rq_axi_last(i),
                    s_axis_rq_tdata                   => pcie_rq_axi_data(i),
                    s_axis_rq_tuser                   => pcie_rq_axi_user(i),
                    s_axis_rq_tkeep                   => pcie_rq_axi_keep(i),
                    s_axis_rq_tready                  => s_axis_rq_tready(i),
                    s_axis_rq_tvalid                  => pcie_rq_axi_valid(i),
                    m_axis_rc_tdata                   => pcie_rc_axi_data(i),
                    m_axis_rc_tuser                   => pcie_rc_axi_user(i),
                    m_axis_rc_tlast                   => pcie_rc_axi_last(i),
                    m_axis_rc_tkeep                   => pcie_rc_axi_keep(i),
                    m_axis_rc_tvalid                  => pcie_rc_axi_valid(i),
                    m_axis_rc_tready                  => pcie_rc_axi_ready(i),
                    m_axis_cq_tdata                   => pcie_cq_axi_data(i),
                    m_axis_cq_tuser                   => pcie_cq_axi_user(i),
                    m_axis_cq_tlast                   => pcie_cq_axi_last(i),
                    m_axis_cq_tkeep                   => pcie_cq_axi_keep(i),
                    m_axis_cq_tvalid                  => pcie_cq_axi_valid(i),
                    m_axis_cq_tready                  => pcie_cq_axi_ready(i),
                    s_axis_cc_tdata                   => pcie_cc_axi_data(i),
                    s_axis_cc_tuser                   => pcie_cc_axi_user(i),
                    s_axis_cc_tlast                   => pcie_cc_axi_last(i),
                    s_axis_cc_tkeep                   => pcie_cc_axi_keep(i),
                    s_axis_cc_tvalid                  => pcie_cc_axi_valid(i),
                    s_axis_cc_tready                  => s_axis_cc_tready(i),

                    pcie_rq_seq_num0                  => open,
                    pcie_rq_seq_num_vld0              => open,
                    pcie_rq_tag0                      => tag_assign_int(i)(7 downto 0),
                    pcie_rq_tag_vld0                  => tag_assign_vld_int(i)(0),
                    pcie_rq_tag1                      => tag_assign_int(i)(15 downto 8),
                    pcie_rq_tag_vld1                  => tag_assign_vld_int(i)(1),

                    pcie_cq_np_req                    => (others => '1'),
                    pcie_cq_np_req_count              => open,

                    cfg_phy_link_down                 => cfg_phy_link_down(i),
                    cfg_phy_link_status               => cfg_phy_link_status(i),
                    cfg_negotiated_width              => cfg_negotiated_width(i),
                    cfg_current_speed                 => cfg_current_speed(i),
                    cfg_max_payload                   => cfg_max_payload(i),
                    cfg_max_read_req                  => cfg_max_read_req(i),
                    cfg_function_status               => cfg_function_status(i),
                    cfg_function_power_state          => cfg_function_power_state(i),
                    cfg_vf_status                     => open,
                    cfg_vf_power_state                => open,
                    cfg_link_power_state              => cfg_link_power_state(i),
                    cfg_err_cor_out                   => open,
                    cfg_err_nonfatal_out              => open,
                    cfg_err_fatal_out                 => open,
                    cfg_local_error_valid             => cfg_local_error_valid(i),
                    cfg_local_error_out               => cfg_local_error_out(i),
                    cfg_ltssm_state                   => cfg_ltssm_state(i),
                    cfg_rx_pm_state                   => cfg_rx_pm_state(i),
                    cfg_tx_pm_state                   => cfg_tx_pm_state(i),
                    cfg_rcb_status                    => cfg_rcb_status(i),
                    cfg_obff_enable                   => open,
                    cfg_pl_status_change              => open,
                    cfg_tph_requester_enable          => open,
                    cfg_tph_st_mode                   => open,
                    cfg_vf_tph_requester_enable       => open,
                    cfg_vf_tph_st_mode                => open,
                    cfg_dsn                           => (others => '0'),
                    cfg_bus_number                    => open,
                    cfg_fc_ph                         => open,
                    cfg_fc_pd                         => open,
                    cfg_fc_nph                        => open,
                    cfg_fc_npd                        => open,
                    cfg_fc_cplh                       => open,
                    cfg_fc_cpld                       => open,
                    cfg_fc_sel                        => (others => '0'),
                    cfg_power_state_change_ack        => '0',
                    cfg_power_state_change_interrupt  => open,
                    cfg_err_cor_in                    => '0',
                    cfg_err_uncor_in                  => '0',
                    cfg_flr_in_process                => open,
                    cfg_flr_done                      => (others => '0'),
                    cfg_vf_flr_in_process             => open,
                    cfg_vf_flr_func_num               => (others => '0'),
                    cfg_vf_flr_done                   => (others => '0'),
                    cfg_link_training_enable          => '1',
                    cfg_ext_read_received             => cfg_ext_read(i),
                    cfg_ext_write_received            => cfg_ext_write(i),
                    cfg_ext_register_number           => cfg_ext_register(i),
                    cfg_ext_function_number           => cfg_ext_function(i),
                    cfg_ext_write_data                => cfg_ext_write_data(i),
                    cfg_ext_write_byte_enable         => cfg_ext_write_be(i),
                    cfg_ext_read_data                 => cfg_ext_read_data(i),
                    cfg_ext_read_data_valid           => cfg_ext_read_dv(i),
                    cfg_interrupt_int                 => (others => '0'),
                    cfg_interrupt_pending             => (others => '0'),
                    cfg_interrupt_sent                => open,
                    cfg_hot_reset_out                 => open,
                    cfg_config_space_enable           => '1',
                    cfg_req_pm_transition_l23_ready   => '0',
                    cfg_hot_reset_in                  => '0',
                    cfg_ds_port_number                => (others => '0'),
                    cfg_ds_bus_number                 => (others => '0'),
                    cfg_ds_device_number              => (others => '0'),
                    phy_rdy_out                       => pcie_phy_rdy_out(i)
                );
            end generate;
        end generate;
    end generate;

    pcie_mode_1_g : if (ENDPOINT_MODE = 1) generate

        pcie_hip_g : for i in 0 to PCIE_HIPS/2-1 generate

            pcie_i : for j in 0 to 1 generate

                pcie_ibuf_i_j : component ibufds_gte4
                generic map (
                    REFCLK_HROW_CK_SEL => "00"
                )
                port map (
                    I     => PCIE_SYSCLK_P(i*PCIE_CLKS+j),
                    IB    => PCIE_SYSCLK_N(i*PCIE_CLKS+j),
                    O     => pcie_sysclk_gt_buf(2*i+j),
                    ODIV2 => pcie_sysclk_buf(2*i+j),
                    CEB   => '0'
                );

                pcie_rq_axi_ready(2*i+j) <= s_axis_rq_tready(2*i+j)(0);
                pcie_cc_axi_ready(2*i+j) <= s_axis_cc_tready(2*i+j)(0);

                pcie_clk(2*i+j) <= pcie_hip_clk(2*i+j);

                TAG_ASSIGN(2*i+j)     <= tag_assign_int(2*i+j)(RQ_MFB_REGIONS*8 -1 downto 0);
                TAG_ASSIGN_VLD(2*i+j) <= tag_assign_vld_int(2*i+j)(RQ_MFB_REGIONS -1 downto 0);

                pcie0_i : if (j = 0) generate
                    pcie4_uscale_plus_0_i : component pcie4_uscale_plus
                    port map (
                        sys_clk                           => pcie_sysclk_buf(2*i+j),
                        sys_clk_gt                        => pcie_sysclk_gt_buf(2*i+j),
                        sys_reset                         => PCIE_SYSRST_N(i),

                        pci_exp_txn                       => PCIE_TX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_txp                       => PCIE_TX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxn                       => PCIE_RX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxp                       => PCIE_RX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),

                        user_clk                          => pcie_hip_clk(2*i+j),
                        user_reset                        => pcie_hip_rst(2*i+j),
                        user_lnk_up                       => user_lnk_up(2*i+j),

                        s_axis_rq_tlast                   => pcie_rq_axi_last(2*i+j),
                        s_axis_rq_tdata                   => pcie_rq_axi_data(2*i+j),
                        s_axis_rq_tuser                   => pcie_rq_axi_user(2*i+j),
                        s_axis_rq_tkeep                   => pcie_rq_axi_keep(2*i+j),
                        s_axis_rq_tready                  => s_axis_rq_tready(2*i+j),
                        s_axis_rq_tvalid                  => pcie_rq_axi_valid(2*i+j),
                        m_axis_rc_tdata                   => pcie_rc_axi_data(2*i+j),
                        m_axis_rc_tuser                   => pcie_rc_axi_user(2*i+j),
                        m_axis_rc_tlast                   => pcie_rc_axi_last(2*i+j),
                        m_axis_rc_tkeep                   => pcie_rc_axi_keep(2*i+j),
                        m_axis_rc_tvalid                  => pcie_rc_axi_valid(2*i+j),
                        m_axis_rc_tready                  => pcie_rc_axi_ready(2*i+j),
                        m_axis_cq_tdata                   => pcie_cq_axi_data(2*i+j),
                        m_axis_cq_tuser                   => pcie_cq_axi_user(2*i+j),
                        m_axis_cq_tlast                   => pcie_cq_axi_last(2*i+j),
                        m_axis_cq_tkeep                   => pcie_cq_axi_keep(2*i+j),
                        m_axis_cq_tvalid                  => pcie_cq_axi_valid(2*i+j),
                        m_axis_cq_tready                  => pcie_cq_axi_ready(2*i+j),
                        s_axis_cc_tdata                   => pcie_cc_axi_data(2*i+j),
                        s_axis_cc_tuser                   => pcie_cc_axi_user(2*i+j),
                        s_axis_cc_tlast                   => pcie_cc_axi_last(2*i+j),
                        s_axis_cc_tkeep                   => pcie_cc_axi_keep(2*i+j),
                        s_axis_cc_tvalid                  => pcie_cc_axi_valid(2*i+j),
                        s_axis_cc_tready                  => s_axis_cc_tready(2*i+j),

                        pcie_rq_seq_num0                  => open,
                        pcie_rq_seq_num_vld0              => open,
                        pcie_rq_tag0                      => tag_assign_int(2*i+j)(7 downto 0),
                        pcie_rq_tag_vld0                  => tag_assign_vld_int(2*i+j)(0),
                        pcie_rq_tag1                      => tag_assign_int(2*i+j)(15 downto 8),
                        pcie_rq_tag_vld1                  => tag_assign_vld_int(2*i+j)(1),

                        pcie_cq_np_req                    => (others => '1'),
                        pcie_cq_np_req_count              => open,

                        cfg_phy_link_down                 => cfg_phy_link_down(2*i+j),
                        cfg_phy_link_status               => cfg_phy_link_status(2*i+j),
                        cfg_negotiated_width              => cfg_negotiated_width(2*i+j),
                        cfg_current_speed                 => cfg_current_speed(2*i+j),
                        cfg_max_payload                   => cfg_max_payload(2*i+j),
                        cfg_max_read_req                  => cfg_max_read_req(2*i+j),
                        cfg_function_status               => cfg_function_status(2*i+j),
                        cfg_function_power_state          => cfg_function_power_state(2*i+j),
                        cfg_vf_status                     => open,
                        cfg_vf_power_state                => open,
                        cfg_link_power_state              => cfg_link_power_state(2*i+j),
                        cfg_err_cor_out                   => open,
                        cfg_err_nonfatal_out              => open,
                        cfg_err_fatal_out                 => open,
                        cfg_local_error_valid             => cfg_local_error_valid(2*i+j),
                        cfg_local_error_out               => cfg_local_error_out(2*i+j),
                        cfg_ltssm_state                   => cfg_ltssm_state(2*i+j),
                        cfg_rx_pm_state                   => cfg_rx_pm_state(2*i+j),
                        cfg_tx_pm_state                   => cfg_tx_pm_state(2*i+j),
                        cfg_rcb_status                    => cfg_rcb_status(2*i+j),
                        cfg_obff_enable                   => open,
                        cfg_pl_status_change              => open,
                        cfg_tph_requester_enable          => open,
                        cfg_tph_st_mode                   => open,
                        cfg_vf_tph_requester_enable       => open,
                        cfg_vf_tph_st_mode                => open,
                        cfg_dsn                           => (others => '0'),
                        cfg_bus_number                    => open,
                        cfg_fc_ph                         => dbg_credits_ph (2*i+j),
                        cfg_fc_pd                         => dbg_credits_pd (2*i+j),
                        cfg_fc_nph                        => dbg_credits_nph(2*i+j),
                        cfg_fc_npd                        => dbg_credits_npd(2*i+j),
                        cfg_fc_cplh                       => open,
                        cfg_fc_cpld                       => open,
                        cfg_fc_sel                        => (others => '0'),
                        cfg_power_state_change_ack        => '0',
                        cfg_power_state_change_interrupt  => open,
                        cfg_err_cor_in                    => '0',
                        cfg_err_uncor_in                  => '0',
                        cfg_flr_in_process                => open,
                        cfg_flr_done                      => (others => '0'),
                        cfg_vf_flr_in_process             => open,
                        cfg_vf_flr_func_num               => (others => '0'),
                        cfg_vf_flr_done                   => (others => '0'),
                        cfg_link_training_enable          => '1',
                        cfg_ext_read_received             => cfg_ext_read(2*i+j),
                        cfg_ext_write_received            => cfg_ext_write(2*i+j),
                        cfg_ext_register_number           => cfg_ext_register(2*i+j),
                        cfg_ext_function_number           => cfg_ext_function(2*i+j),
                        cfg_ext_write_data                => cfg_ext_write_data(2*i+j),
                        cfg_ext_write_byte_enable         => cfg_ext_write_be(2*i+j),
                        cfg_ext_read_data                 => cfg_ext_read_data(2*i+j),
                        cfg_ext_read_data_valid           => cfg_ext_read_dv(2*i+j),
                        cfg_interrupt_int                 => (others => '0'),
                        cfg_interrupt_pending             => (others => '0'),
                        cfg_interrupt_sent                => open,
                        cfg_hot_reset_out                 => open,
                        cfg_config_space_enable           => '1',
                        cfg_req_pm_transition_l23_ready   => '0',
                        cfg_hot_reset_in                  => '0',
                        cfg_ds_port_number                => (others => '0'),
                        cfg_ds_bus_number                 => (others => '0'),
                        cfg_ds_device_number              => (others => '0'),
                        phy_rdy_out                       => pcie_phy_rdy_out(2*i+j)
                    );
                end generate;
                pcie1_i : if (j = 1) generate
                    pcie4_uscale_plus_1_i : component pcie4_uscale_plus_1
                    port map (
                        sys_clk                           => pcie_sysclk_buf(2*i+j),
                        sys_clk_gt                        => pcie_sysclk_gt_buf(2*i+j),
                        sys_reset                         => PCIE_SYSRST_N(i),

                        pci_exp_txn                       => PCIE_TX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_txp                       => PCIE_TX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxn                       => PCIE_RX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxp                       => PCIE_RX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),

                        user_clk                          => pcie_hip_clk(2*i+j),
                        user_reset                        => pcie_hip_rst(2*i+j),
                        user_lnk_up                       => user_lnk_up(2*i+j),

                        s_axis_rq_tlast                   => pcie_rq_axi_last(2*i+j),
                        s_axis_rq_tdata                   => pcie_rq_axi_data(2*i+j),
                        s_axis_rq_tuser                   => pcie_rq_axi_user(2*i+j),
                        s_axis_rq_tkeep                   => pcie_rq_axi_keep(2*i+j),
                        s_axis_rq_tready                  => s_axis_rq_tready(2*i+j),
                        s_axis_rq_tvalid                  => pcie_rq_axi_valid(2*i+j),
                        m_axis_rc_tdata                   => pcie_rc_axi_data(2*i+j),
                        m_axis_rc_tuser                   => pcie_rc_axi_user(2*i+j),
                        m_axis_rc_tlast                   => pcie_rc_axi_last(2*i+j),
                        m_axis_rc_tkeep                   => pcie_rc_axi_keep(2*i+j),
                        m_axis_rc_tvalid                  => pcie_rc_axi_valid(2*i+j),
                        m_axis_rc_tready                  => pcie_rc_axi_ready(2*i+j),
                        m_axis_cq_tdata                   => pcie_cq_axi_data(2*i+j),
                        m_axis_cq_tuser                   => pcie_cq_axi_user(2*i+j),
                        m_axis_cq_tlast                   => pcie_cq_axi_last(2*i+j),
                        m_axis_cq_tkeep                   => pcie_cq_axi_keep(2*i+j),
                        m_axis_cq_tvalid                  => pcie_cq_axi_valid(2*i+j),
                        m_axis_cq_tready                  => pcie_cq_axi_ready(2*i+j),
                        s_axis_cc_tdata                   => pcie_cc_axi_data(2*i+j),
                        s_axis_cc_tuser                   => pcie_cc_axi_user(2*i+j),
                        s_axis_cc_tlast                   => pcie_cc_axi_last(2*i+j),
                        s_axis_cc_tkeep                   => pcie_cc_axi_keep(2*i+j),
                        s_axis_cc_tvalid                  => pcie_cc_axi_valid(2*i+j),
                        s_axis_cc_tready                  => s_axis_cc_tready(2*i+j),

                        pcie_rq_seq_num0                  => open,
                        pcie_rq_seq_num_vld0              => open,
                        pcie_rq_tag0                      => tag_assign_int(2*i+j)(7 downto 0),
                        pcie_rq_tag_vld0                  => tag_assign_vld_int(2*i+j)(0),
                        pcie_rq_tag1                      => tag_assign_int(2*i+j)(15 downto 8),
                        pcie_rq_tag_vld1                  => tag_assign_vld_int(2*i+j)(1),

                        pcie_cq_np_req                    => (others => '1'),
                        pcie_cq_np_req_count              => open,

                        cfg_phy_link_down                 => cfg_phy_link_down(2*i+j),
                        cfg_phy_link_status               => cfg_phy_link_status(2*i+j),
                        cfg_negotiated_width              => cfg_negotiated_width(2*i+j),
                        cfg_current_speed                 => cfg_current_speed(2*i+j),
                        cfg_max_payload                   => cfg_max_payload(2*i+j),
                        cfg_max_read_req                  => cfg_max_read_req(2*i+j),
                        cfg_function_status               => cfg_function_status(2*i+j),
                        cfg_function_power_state          => cfg_function_power_state(2*i+j),
                        cfg_vf_status                     => open,
                        cfg_vf_power_state                => open,
                        cfg_link_power_state              => cfg_link_power_state(2*i+j),
                        cfg_err_cor_out                   => open,
                        cfg_err_nonfatal_out              => open,
                        cfg_err_fatal_out                 => open,
                        cfg_local_error_valid             => cfg_local_error_valid(2*i+j),
                        cfg_local_error_out               => cfg_local_error_out(2*i+j),
                        cfg_ltssm_state                   => cfg_ltssm_state(2*i+j),
                        cfg_rx_pm_state                   => cfg_rx_pm_state(2*i+j),
                        cfg_tx_pm_state                   => cfg_tx_pm_state(2*i+j),
                        cfg_rcb_status                    => cfg_rcb_status(2*i+j),
                        cfg_obff_enable                   => open,
                        cfg_pl_status_change              => open,
                        cfg_tph_requester_enable          => open,
                        cfg_tph_st_mode                   => open,
                        cfg_vf_tph_requester_enable       => open,
                        cfg_vf_tph_st_mode                => open,
                        cfg_dsn                           => (others => '0'),
                        cfg_bus_number                    => open,
                        cfg_fc_ph                         => dbg_credits_ph (2*i+j),
                        cfg_fc_pd                         => dbg_credits_pd (2*i+j),
                        cfg_fc_nph                        => dbg_credits_nph(2*i+j),
                        cfg_fc_npd                        => dbg_credits_npd(2*i+j),
                        cfg_fc_cplh                       => open,
                        cfg_fc_cpld                       => open,
                        cfg_fc_sel                        => (others => '0'),
                        cfg_power_state_change_ack        => '0',
                        cfg_power_state_change_interrupt  => open,
                        cfg_err_cor_in                    => '0',
                        cfg_err_uncor_in                  => '0',
                        cfg_flr_in_process                => open,
                        cfg_flr_done                      => (others => '0'),
                        cfg_vf_flr_in_process             => open,
                        cfg_vf_flr_func_num               => (others => '0'),
                        cfg_vf_flr_done                   => (others => '0'),
                        cfg_link_training_enable          => '1',
                        cfg_ext_read_received             => cfg_ext_read(2*i+j),
                        cfg_ext_write_received            => cfg_ext_write(2*i+j),
                        cfg_ext_register_number           => cfg_ext_register(2*i+j),
                        cfg_ext_function_number           => cfg_ext_function(2*i+j),
                        cfg_ext_write_data                => cfg_ext_write_data(2*i+j),
                        cfg_ext_write_byte_enable         => cfg_ext_write_be(2*i+j),
                        cfg_ext_read_data                 => cfg_ext_read_data(2*i+j),
                        cfg_ext_read_data_valid           => cfg_ext_read_dv(2*i+j),
                        cfg_interrupt_int                 => (others => '0'),
                        cfg_interrupt_pending             => (others => '0'),
                        cfg_interrupt_sent                => open,
                        cfg_hot_reset_out                 => open,
                        cfg_config_space_enable           => '1',
                        cfg_req_pm_transition_l23_ready   => '0',
                        cfg_hot_reset_in                  => '0',
                        cfg_ds_port_number                => (others => '0'),
                        cfg_ds_bus_number                 => (others => '0'),
                        cfg_ds_device_number              => (others => '0'),
                        phy_rdy_out                       => pcie_phy_rdy_out(2*i+j)
                    );
                end generate;
            end generate;
        end generate;
    end generate;

    -- =========================================================================
    --  PCIE ADAPTER
    -- =========================================================================

    pcie_adapter_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        pcie_adapter_i : entity work.PCIE_ADAPTER
        generic map (
            CQ_MFB_REGIONS     => CQ_MFB_REGIONS,
            CQ_MFB_REGION_SIZE => CQ_MFB_REGION_SIZE,
            CQ_MFB_BLOCK_SIZE  => CQ_MFB_BLOCK_SIZE,
            CQ_MFB_ITEM_WIDTH  => CQ_MFB_ITEM_WIDTH,
            RC_MFB_REGIONS     => RC_MFB_REGIONS,
            RC_MFB_REGION_SIZE => RC_MFB_REGION_SIZE,
            RC_MFB_BLOCK_SIZE  => RC_MFB_BLOCK_SIZE,
            RC_MFB_ITEM_WIDTH  => RC_MFB_ITEM_WIDTH,
            CC_MFB_REGIONS     => CC_MFB_REGIONS,
            CC_MFB_REGION_SIZE => CC_MFB_REGION_SIZE,
            CC_MFB_BLOCK_SIZE  => CC_MFB_BLOCK_SIZE,
            CC_MFB_ITEM_WIDTH  => CC_MFB_ITEM_WIDTH,
            RQ_MFB_REGIONS     => RQ_MFB_REGIONS,
            RQ_MFB_REGION_SIZE => RQ_MFB_REGION_SIZE,
            RQ_MFB_BLOCK_SIZE  => RQ_MFB_BLOCK_SIZE,
            RQ_MFB_ITEM_WIDTH  => RQ_MFB_ITEM_WIDTH,
            ENDPOINT_TYPE      => ENDPOINT_TYPE,
            DEVICE             => DEVICE,
            AXI_CQUSER_WIDTH   => AXI_CQUSER_WIDTH,
            AXI_CCUSER_WIDTH   => AXI_CCUSER_WIDTH,
            AXI_RQUSER_WIDTH   => AXI_RQUSER_WIDTH,
            AXI_RCUSER_WIDTH   => AXI_RCUSER_WIDTH,
            AXI_STRADDLING     => false
        )
        port map (
            PCIE_CLK            => pcie_clk(i),
            PCIE_RESET          => pcie_rst(i)(0),

            AVST_DOWN_DATA      => (others => '0'),
            AVST_DOWN_HDR       => (others => '0'),
            AVST_DOWN_PREFIX    => (others => '0'),
            AVST_DOWN_SOP       => (others => '0'),
            AVST_DOWN_EOP       => (others => '0'),
            AVST_DOWN_EMPTY     => (others => '0'),
            AVST_DOWN_BAR_RANGE => (others => '0'),
            AVST_DOWN_VALID     => (others => '0'),
            AVST_DOWN_READY     => open,

            AVST_UP_DATA        => open,
            AVST_UP_HDR         => open,
            AVST_UP_PREFIX      => open,
            AVST_UP_SOP         => open,
            AVST_UP_EOP         => open,
            AVST_UP_ERROR       => open,
            AVST_UP_VALID       => open,
            AVST_UP_READY       => '0',

            CRDT_DOWN_INIT_DONE => '0',
            CRDT_DOWN_UPDATE    => open,
            CRDT_DOWN_CNT_PH    => open,
            CRDT_DOWN_CNT_NPH   => open,
            CRDT_DOWN_CNT_CPLH  => open,
            CRDT_DOWN_CNT_PD    => open,
            CRDT_DOWN_CNT_NPD   => open,
            CRDT_DOWN_CNT_CPLD  => open,

            CRDT_UP_INIT_DONE   => '0',
            CRDT_UP_UPDATE      => (others => '0'),
            CRDT_UP_CNT_PH      => (others => '0'),
            CRDT_UP_CNT_NPH     => (others => '0'),
            CRDT_UP_CNT_CPLH    => (others => '0'),
            CRDT_UP_CNT_PD      => (others => '0'),
            CRDT_UP_CNT_NPD     => (others => '0'),
            CRDT_UP_CNT_CPLD    => (others => '0'),

            CQ_AXI_DATA         => pcie_cq_axi_data(i),
            CQ_AXI_USER         => pcie_cq_axi_user(i),
            CQ_AXI_LAST         => pcie_cq_axi_last(i),
            CQ_AXI_KEEP         => pcie_cq_axi_keep(i),
            CQ_AXI_VALID        => pcie_cq_axi_valid(i),
            CQ_AXI_READY        => pcie_cq_axi_ready(i),

            RC_AXI_DATA         => pcie_rc_axi_data(i),
            RC_AXI_USER         => pcie_rc_axi_user(i),
            RC_AXI_LAST         => pcie_rc_axi_last(i),
            RC_AXI_KEEP         => pcie_rc_axi_keep(i),
            RC_AXI_VALID        => pcie_rc_axi_valid(i),
            RC_AXI_READY        => pcie_rc_axi_ready(i),

            CC_AXI_DATA         => pcie_cc_axi_data(i),
            CC_AXI_USER         => pcie_cc_axi_user(i),
            CC_AXI_LAST         => pcie_cc_axi_last(i),
            CC_AXI_KEEP         => pcie_cc_axi_keep(i),
            CC_AXI_VALID        => pcie_cc_axi_valid(i),
            CC_AXI_READY        => pcie_cc_axi_ready(i),

            RQ_AXI_DATA         => pcie_rq_axi_data(i),
            RQ_AXI_USER         => pcie_rq_axi_user(i),
            RQ_AXI_LAST         => pcie_rq_axi_last(i),
            RQ_AXI_KEEP         => pcie_rq_axi_keep(i),
            RQ_AXI_VALID        => pcie_rq_axi_valid(i),
            RQ_AXI_READY        => pcie_rq_axi_ready(i),

            CQ_MFB_DATA         => CQ_MFB_DATA(i),
            CQ_MFB_META         => CQ_MFB_META(i),
            CQ_MFB_SOF          => CQ_MFB_SOF(i),
            CQ_MFB_EOF          => CQ_MFB_EOF(i),
            CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS(i),
            CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS(i),
            CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY(i),
            CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY(i),

            RC_MFB_DATA         => RC_MFB_DATA(i),
            RC_MFB_META         => RC_MFB_META(i),
            RC_MFB_SOF          => RC_MFB_SOF(i),
            RC_MFB_EOF          => RC_MFB_EOF(i),
            RC_MFB_SOF_POS      => RC_MFB_SOF_POS(i),
            RC_MFB_EOF_POS      => RC_MFB_EOF_POS(i),
            RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY(i),
            RC_MFB_DST_RDY      => RC_MFB_DST_RDY(i),

            CC_MFB_DATA         => CC_MFB_DATA(i),
            CC_MFB_META         => CC_MFB_META(i),
            CC_MFB_SOF          => CC_MFB_SOF(i),
            CC_MFB_EOF          => CC_MFB_EOF(i),
            CC_MFB_SOF_POS      => CC_MFB_SOF_POS(i),
            CC_MFB_EOF_POS      => CC_MFB_EOF_POS(i),
            CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY(i),
            CC_MFB_DST_RDY      => CC_MFB_DST_RDY(i),

            RQ_MFB_DATA         => RQ_MFB_DATA(i),
            RQ_MFB_META         => RQ_MFB_META(i),
            RQ_MFB_SOF          => RQ_MFB_SOF(i),
            RQ_MFB_EOF          => RQ_MFB_EOF(i),
            RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS(i),
            RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS(i),
            RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY(i),
            RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY(i)
        );
    end generate;

    -- =========================================================================
    --  PCIE RESET LOGIC
    -- =========================================================================

    pcie_rst_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        pcie_rst_async(i) <= pcie_hip_rst(i) or not user_lnk_up(i);

        pcie_rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => RESET_WIDTH+1
        )
        port map (
            CLK       => pcie_clk(i),
            ASYNC_RST => pcie_rst_async(i),
            OUT_RST   => pcie_rst(i)
        );

        PCIE_USER_CLK(i)   <= pcie_clk(i);
        PCIE_USER_RESET(i) <= pcie_rst(i)(RESET_WIDTH+1-1 downto 1);
    end generate;

    -- =========================================================================
    --  PCIE CONFIGURATION REGISTERS
    -- =========================================================================

    pcie_cfg_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        process (pcie_clk(i))
        begin
            if (rising_edge(pcie_clk(i))) then
                PCIE_LINK_UP(i)  <= cfg_phy_link_status(i)(0) and cfg_phy_link_status(i)(1);
                PCIE_RCB_SIZE(i) <= cfg_rcb_status(i)(0);
                PCIE_MRRS(i)     <= cfg_max_read_req(i);
                PCIE_MPS(i)      <= '0' & cfg_max_payload(i);
            end if;
        end process;
        PCIE_EXT_TAG_EN(i)     <= '1';
        PCIE_10B_TAG_REQ_EN(i) <= '0';
    end generate;

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    dt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        constant DT_EN : boolean := true;
    begin
        -- Device Tree ROM
        pci_ext_cap_i: entity work.PCI_EXT_CAP
        generic map (
            ENDPOINT_ID            => i,
            ENDPOINT_ID_ENABLE     => true,
            DEVICE_TREE_ENABLE     => dt_en,
            VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
            VSEC_NEXT_POINTER      => DTB_NEXT_POINTER,
            CARD_ID_WIDTH          => CARD_ID_WIDTH,
            CFG_EXT_READ_DV_HOTFIX => false
        )
        port map (
            CLK                    => pcie_clk(i),
            CARD_ID                => CARD_ID(i),
            CFG_EXT_READ           => cfg_ext_read(i),
            CFG_EXT_WRITE          => cfg_ext_write(i),
            CFG_EXT_REGISTER       => cfg_ext_register(i),
            CFG_EXT_FUNCTION       => cfg_ext_function(i),
            CFG_EXT_WRITE_DATA     => cfg_ext_write_data(i),
            CFG_EXT_WRITE_BE       => cfg_ext_write_be(i),
            CFG_EXT_READ_DATA      => cfg_ext_read_dtb_data(i),
            CFG_EXT_READ_DV        => cfg_ext_read_dtb_dv(i)
        );

        xvc_g: if (XVC_ENABLE) generate
            xvc_i : component xvc_vsec
            port map (
                clk                              => pcie_clk(i),
                pcie3_cfg_ext_function_number    => cfg_ext_function(i),
                pcie3_cfg_ext_read_data          => cfg_ext_read_xvc_data(i),
                pcie3_cfg_ext_read_data_valid    => cfg_ext_read_xvc_dv(i),
                pcie3_cfg_ext_read_received      => cfg_ext_read(i),
                pcie3_cfg_ext_register_number    => cfg_ext_register(i),
                pcie3_cfg_ext_write_byte_enable  => cfg_ext_write_be(i),
                pcie3_cfg_ext_write_data         => cfg_ext_write_data(i),
                pcie3_cfg_ext_write_received     => cfg_ext_write(i)
            );
        end generate;

        cfg_ext_read_dv(i)   <= cfg_ext_read_dtb_dv(i) or cfg_ext_read_xvc_dv(i);
        cfg_ext_read_data(i) <= cfg_ext_read_xvc_data(i) when (cfg_ext_read_xvc_dv(i) = '1') else cfg_ext_read_dtb_data(i);
    end generate;

    -- =========================================================================
    --  DEBUG logic
    -- =========================================================================

    debug_i : entity work.PCIE_CORE_DEBUG
    generic map (
        PCIE_ENDPOINTS => PCIE_ENDPOINTS,
        DBG_CRDT_PH_W  => 8,
        DBG_CRDT_NPH_W => 8,
        DBG_CRDT_PD_W  => 12,
        DBG_CRDT_NPD_W => 12,
        DBG_ENABLE     => PCIE_CORE_DEBUG_ENABLE,
        DEVICE         => DEVICE
    )
    port map (
        PCIE_CLK            => pcie_hip_clk,
        PCIE_RESET          => pcie_hip_rst,

        DBG_UP_SRC_RDY      => pcie_rq_axi_valid,
        DBG_UP_DST_RDY      => pcie_rq_axi_ready,
        DBG_DW_SRC_RDY      => pcie_rc_axi_valid,
        DBG_DW_DST_RDY      => pcie_rc_axi_ready,

        DBG_CREDITS_PH      => dbg_credits_ph,
        DBG_CREDITS_NPH     => dbg_credits_nph,
        DBG_CREDITS_PD      => dbg_credits_pd,
        DBG_CREDITS_NPD     => dbg_credits_npd,

        DBG_CREDITS_PH_VLD  => (others => '1'),
        DBG_CREDITS_NPH_VLD => (others => '1'),
        DBG_CREDITS_PD_VLD  => (others => '1'),
        DBG_CREDITS_NPD_VLD => (others => '1'),

        MI_CLK              => MI_CLK,
        MI_RESET            => MI_RESET,
        MI_DWR              => MI_DWR,
        MI_ADDR             => MI_ADDR,
        MI_BE               => MI_BE,
        MI_RD               => MI_RD,
        MI_WR               => MI_WR,
        MI_ARDY             => MI_ARDY,
        MI_DRD              => MI_DRD,
        MI_DRDY             => MI_DRDY
    );

end architecture;
