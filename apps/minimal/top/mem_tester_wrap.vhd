-- mem_tester_wrap.vhd:
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

entity MEM_TESTER_WRAP is
    generic (
        -- HBM parameters: number of physical HBM modules on the chip
        HBM_MODULES           : natural := 0;
        -- HBM parameters: number of HBM ports
        HBM_PORTS             : natural := 0;
        -- HBM parameters: width of AXI address signal
        HBM_ADDR_WIDTH        : natural := 32;
        -- HBM parameters: width of AXI data signal
        HBM_DATA_WIDTH        : natural := 256;
        -- HBM parameters: width of AXI burst signal
        HBM_BURST_WIDTH       : natural := 2;
        -- HBM parameters: width of AXI ID signal
        HBM_ID_WIDTH          : natural := 6;
        -- HBM parameters: width of AXI LEN signal
        HBM_LEN_WIDTH         : natural := 4;
        -- HBM parameters: width of AXI size signal
        HBM_SIZE_WIDTH        : natural := 3;
        -- HBM parameters: width of AXI resp signal
        HBM_RESP_WIDTH        : natural := 2;
        -- HBM parameters: highest address bit of one HBM port (its capacity).
        -- 28 => 256 MB, 29 => 512 MB, 30 => 1 GB per port.
        HBM_PORT_ADDR_HBIT    : natural := 28;
        -- HBM parameters: multiplier for the port ID used to place each port into its own
        -- AXI memory segment. Must be a multiple of 2**HBM_PORT_ADDR_HBIT. Use 0 when
        -- every AXI port has its own address space (e.g. a NoC attached HBM).
        HBM_BASE_ADDR_OFFSET  : natural := 0;
        -- Frequence of the HBM AXI bus
        HBM_FREQ_KHZ          : natural := 266660;
        -- DDR parameters: number of external memory ports (EMIFs)
        DDR_PORTS             : natural := 1;
        -- DDR parameters: width of AVMM address signal
        DDR_ADDR_WIDTH        : natural := 27;
        -- DDR parameters: width of AVMM burst count signal
        DDR_BURST_WIDTH       : natural := 7;
        -- DDR parameters: width of AVMM data signals
        DDR_DATA_WIDTH        : natural := 512;
        -- DDR parameters: width of user refresh period
        DDR_REFR_PERIOD_WIDTH : natural := 32;
        -- DDR parameters: default refresh periods for each interface
        DDR_DEF_REFR_PERIOD   : natural := 0;
        -- Frequence of the DDR AVMM bus
        DDR_FREQ_KHZ          : natural := 266660;
        -- MI parameters: width of data signals
        MI_DATA_WIDTH         : natural := 32;
        -- MI parameters: width of address signal
        MI_ADDR_WIDTH         : natural := 32;
        -- Name of FPGA device
        DEVICE                : string := "AGILEX"
    );
    port (
        -- =========================================================================
        -- Clock and Resets inputs
        -- =========================================================================
        CLK      : in  std_logic;
        RESET    : in  std_logic;

        -- =========================================================================
        -- HBM AXI INTERFACES (clocked at HBM_CLK)
        -- =========================================================================
        HBM_CLK                 : in  std_logic_vector(HBM_MODULES-1 downto 0);
        HBM_RESET               : in  std_logic_vector(HBM_MODULES-1 downto 0);
        HBM_INIT_DONE           : in  std_logic_vector(HBM_MODULES-1 downto 0);

        HBM_AXI_ARADDR          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_ARBURST         : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_ARID            : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_ARLEN           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_ARSIZE          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_ARVALID         : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
        HBM_AXI_ARREADY         : in  std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_RDATA           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
        HBM_AXI_RDATA_PARITY    : in  slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
        HBM_AXI_RID             : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
        HBM_AXI_RLAST           : in  std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_RRESP           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
        HBM_AXI_RVALID          : in  std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_RREADY          : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');

        HBM_AXI_AWADDR          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_AWBURST         : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_AWID            : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_AWLEN           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_AWSIZE          : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_AWVALID         : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
        HBM_AXI_AWREADY         : in  std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_WDATA           : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
        HBM_AXI_WDATA_PARITY    : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => '0'));
        HBM_AXI_WLAST           : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
        HBM_AXI_WSTRB           : out slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => '0'));
        HBM_AXI_WVALID          : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');
        HBM_AXI_WREADY          : in  std_logic_vector(HBM_PORTS-1 downto 0);

        HBM_AXI_BID             : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
        HBM_AXI_BRESP           : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
        HBM_AXI_BVALID          : in  std_logic_vector(HBM_PORTS-1 downto 0);
        HBM_AXI_BREADY          : out std_logic_vector(HBM_PORTS-1 downto 0) := (others => '0');

        -- =========================================================================
        -- DDR AVMM INTERFACES (clocked at DDR_CLK)
        -- =========================================================================
        -- Clock for each memory port
        DDR_CLK                : in  std_logic_vector(DDR_PORTS-1 downto 0);
        -- Reset synchronized with DDR_CLK for each memory port
        DDR_RESET              : in  std_logic_vector(DDR_PORTS-1 downto 0);

        -- MEM Avalon-MM: ready for request
        DDR_AVMM_READY         : in  std_logic_vector(DDR_PORTS-1 downto 0);
        -- MEM Avalon-MM: read request
        DDR_AVMM_READ          : out std_logic_vector(DDR_PORTS-1 downto 0);
        -- MEM Avalon-MM: write request
        DDR_AVMM_WRITE         : out std_logic_vector(DDR_PORTS-1 downto 0);
        -- MEM Avalon-MM: address of r/w request
        DDR_AVMM_ADDRESS       : out slv_array_t(DDR_PORTS-1 downto 0)(DDR_ADDR_WIDTH-1 downto 0);
        -- MEM Avalon-MM: burst count of read/write request
        DDR_AVMM_BURSTCOUNT    : out slv_array_t(DDR_PORTS-1 downto 0)(DDR_BURST_WIDTH-1 downto 0);
        -- MEM Avalon-MM: write data, valid only with write request
        DDR_AVMM_WRITEDATA     : out slv_array_t(DDR_PORTS-1 downto 0)(DDR_DATA_WIDTH-1 downto 0);
        -- MEM Avalon-MM: read data
        DDR_AVMM_READDATA      : in  slv_array_t(DDR_PORTS-1 downto 0)(DDR_DATA_WIDTH-1 downto 0);
        -- MEM Avalon-MM: read data valid flag
        DDR_AVMM_READDATAVALID : in  std_logic_vector(DDR_PORTS-1 downto 0);

        DDR_REFR_PERIOD        : out slv_array_t(DDR_PORTS-1 downto 0)(DDR_REFR_PERIOD_WIDTH - 1 downto 0) := (others => std_logic_vector(to_unsigned(DDR_DEF_REFR_PERIOD, DDR_REFR_PERIOD_WIDTH)));
        DDR_REFR_REQ           : out std_logic_vector(DDR_PORTS - 1 downto 0);
        DDR_REFR_ACK           : in std_logic_vector(DDR_PORTS - 1 downto 0);

        EMIF_RST_REQ           : out std_logic_vector(DDR_PORTS-1 downto 0);
        EMIF_RST_DONE          : in  std_logic_vector(DDR_PORTS-1 downto 0);
        EMIF_ECC_USR_INT       : in  std_logic_vector(DDR_PORTS-1 downto 0);
        EMIF_CAL_SUCCESS       : in  std_logic_vector(DDR_PORTS-1 downto 0);
        EMIF_CAL_FAIL          : in  std_logic_vector(DDR_PORTS-1 downto 0);
        EMIF_AUTO_PRECHARGE    : out std_logic_vector(DDR_PORTS-1 downto 0);

        -- =========================================================================
        -- MI INTERFACE (clocked at CLK)
        -- =========================================================================
        MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
        MI_RD                   : in  std_logic;
        MI_WR                   : in  std_logic;
        MI_ARDY                 : out std_logic;
        MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_DRDY                 : out std_logic
    );
end entity;

architecture FULL of MEM_TESTER_WRAP is

    constant HBM_PORTS_PER_MODULE  : natural := HBM_PORTS / max(1, HBM_MODULES);

    constant MT_RND_GEN_DATA_WIDTH : natural := 64;
    constant MT_RND_GEN_ADDR_WIDTH : natural := 32;

    function ddr_random_data_seed_f return slv_array_t is
        variable v_rnd_seed : slv_array_t(0 to (DDR_DATA_WIDTH/MT_RND_GEN_DATA_WIDTH)-1)(MT_RND_GEN_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    begin
        for ii in 0 to (DDR_DATA_WIDTH/MT_RND_GEN_DATA_WIDTH)-1 loop
            v_rnd_seed(ii) := std_logic_vector(to_unsigned((672 + ii*DDR_DATA_WIDTH), MT_RND_GEN_DATA_WIDTH));
        end loop;
        return v_rnd_seed;
    end function;

    -- MI bus signals distribution --
    -- (DDR_PORTS   -1 downto 0)         ==> DDR-tester
    -- (2*DDR_PORTS -1 downto DDR_PORTS) ==> DDR-logger
    -- (2*DDR_PORTS)                     ==> HBM-tester
    -- One MI port per HBM tester
    constant HBM_MI_PORTS      : natural := tsel(HBM_PORTS > 0, HBM_MODULES, 0);
    constant MI_PORTS_RAW      : natural := 2*DDR_PORTS + HBM_MI_PORTS;
    -- MI_PORTS is rounded up to a power of two, so the address space above the last
    -- tester has no target and has to be terminated.
    constant MI_PORTS          : natural := 2 ** log2(MI_PORTS_RAW);

    function mi_addr_base_f return slv_array_t is
        constant ADDR_W      : natural := 21; -- TODO
        constant SUBADDR_W   : natural := ADDR_W-log2(MI_PORTS);
        variable v_addr_base : slv_array_t(MI_PORTS-1 downto 0)(MI_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));
    begin
        for i in 0 to MI_PORTS-1 loop
            v_addr_base(i) := std_logic_vector(to_unsigned(i*2**SUBADDR_W,MI_ADDR_WIDTH));
        end loop;
        return v_addr_base;
    end function;

    signal split_mi_dwr                  : slv_array_t     (MI_PORTS-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal split_mi_addr                 : slv_array_t     (MI_PORTS-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    signal split_mi_be                   : slv_array_t     (MI_PORTS-1 downto 0)(MI_DATA_WIDTH/8-1 downto 0);
    signal split_mi_rd                   : std_logic_vector(MI_PORTS-1 downto 0);
    signal split_mi_wr                   : std_logic_vector(MI_PORTS-1 downto 0);
    signal split_mi_ardy                 : std_logic_vector(MI_PORTS-1 downto 0) := (others => '0');
    signal split_mi_drd                  : slv_array_t     (MI_PORTS-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal split_mi_drdy                 : std_logic_vector(MI_PORTS-1 downto 0) := (others => '0');

    signal ddr_log_mi_dwr                : slv_array_t     (DDR_PORTS-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal ddr_log_mi_addr               : slv_array_t     (DDR_PORTS-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    signal ddr_log_mi_be                 : slv_array_t     (DDR_PORTS-1 downto 0)(MI_DATA_WIDTH/8-1 downto 0);
    signal ddr_log_mi_rd                 : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_log_mi_wr                 : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_log_mi_drd                : slv_array_t     (DDR_PORTS-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal ddr_log_mi_ardy               : std_logic_vector(DDR_PORTS-1 downto 0) := (others => '0');
    signal ddr_log_mi_drdy               : std_logic_vector(DDR_PORTS-1 downto 0) := (others => '0');

    signal hbm_clk_s                 : std_logic_vector(HBM_MODULES-1 downto 0);
    signal hbm_reset_s               : std_logic_vector(HBM_MODULES-1 downto 0);
    signal hbm_init_done_s           : std_logic_vector(HBM_MODULES-1 downto 0);

    signal hbm_axi_araddr_s          : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_arburst_s         : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_BURST_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_arid_s            : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_arlen_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_LEN_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_arsize_s          : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_arvalid_s         : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0) := (others => (others => '0'));
    signal hbm_axi_arready_s         : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0);

    signal hbm_axi_rdata_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_rdata_parity_s    : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_rid_s             : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_rlast_s           : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0);
    signal hbm_axi_rresp_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_rvalid_s          : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0);
    signal hbm_axi_rready_s          : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0) := (others => (others => '0'));

    signal hbm_axi_awaddr_s          : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_awburst_s         : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_BURST_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_awid_s            : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_ID_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_awlen_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_LEN_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_awsize_s          : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_awvalid_s         : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0) := (others => (others => '0'));
    signal hbm_axi_awready_s         : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0);

    signal hbm_axi_wdata_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_wdata_parity_s    : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_wlast_s           : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0) := (others => (others => '0'));
    signal hbm_axi_wstrb_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0) := (others => (others => (others => '0')));
    signal hbm_axi_wvalid_s          : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0) := (others => (others => '0'));
    signal hbm_axi_wready_s          : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0);

    signal hbm_axi_bid_s             : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_bresp_s           : slv_array_2d_t(HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_bvalid_s          : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0);
    signal hbm_axi_bready_s          : slv_array_t   (HBM_MODULES-1 downto 0)(HBM_PORTS_PER_MODULE-1 downto 0) := (others => (others => '0'));

    signal ddr_reset_repl                : slv_array_t     (DDR_PORTS-1 downto 0)(3-1 downto 0);

begin

    -- Only checked here for a direct or foreign-application instantiation. When going
    -- through core_conf.tcl, core/config/core_const.tcl already enforces this.
    assert (HBM_PORTS mod max(1, HBM_MODULES) = 0)
        report "MEM_TESTER_WRAP: Set HBM_MODULES so that it divides HBM_PORTS without a remainder."
        severity failure;

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map (
        ADDR_WIDTH => MI_ADDR_WIDTH,
        DATA_WIDTH => MI_DATA_WIDTH,
        PORTS      => MI_PORTS,
        ADDR_BASE  => mi_addr_base_f,
        DEVICE     => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DWR     => MI_DWR,
        RX_ADDR    => MI_ADDR,
        RX_BE      => MI_BE,
        RX_RD      => MI_RD,
        RX_WR      => MI_WR,
        RX_ARDY    => MI_ARDY,
        RX_DRD     => MI_DRD,
        RX_DRDY    => MI_DRDY,

        TX_DWR     => split_mi_dwr,
        TX_ADDR    => split_mi_addr,
        TX_BE      => split_mi_be,
        TX_RD      => split_mi_rd,
        TX_WR      => split_mi_wr,
        TX_ARDY    => split_mi_ardy,
        TX_DRD     => split_mi_drd,
        TX_DRDY    => split_mi_drdy
    );

    -- =========================================================================
    -- DDR MEMORY TESTERS
    -- =========================================================================

    ddr_g : for i in DDR_PORTS-1 downto 0 generate
        rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => 3 -- MEM_TESTER + MEM_LOGGER + MI_ASYNC
        )
        port map (
            CLK        => DDR_CLK(i),
            ASYNC_RST  => DDR_RESET(i),
            OUT_RST    => ddr_reset_repl(i)
        );

        ddr_tester_i : entity work.MEM_TESTER
        generic map (
            AMM_DATA_WIDTH              => DDR_DATA_WIDTH,
            AMM_ADDR_WIDTH              => DDR_ADDR_WIDTH,
            AMM_BURST_COUNT_WIDTH       => DDR_BURST_WIDTH,
            AMM_FREQ_KHZ                => DDR_FREQ_KHZ,

            MI_DATA_WIDTH               => MI_DATA_WIDTH,
            MI_ADDR_WIDTH               => MI_ADDR_WIDTH,

            RAND_GEN_DATA_WIDTH         => MT_RND_GEN_DATA_WIDTH,
            RAND_GEN_ADDR_WIDTH         => MT_RND_GEN_ADDR_WIDTH,
            RANDOM_DATA_SEED            => ddr_random_data_seed_f,
            RANDOM_ADDR_SEED            => std_logic_vector(to_unsigned(66844679, MT_RND_GEN_ADDR_WIDTH)),
            -- REFR_REQ_BEFORE_TEST - Requires support for manual memory refresh
            -- control, experimental function only!
            REFR_REQ_BEFORE_TEST        => false,
            REFR_PERIOD_WIDTH           => DDR_REFR_PERIOD_WIDTH,
            DEF_REFR_PERIOD             => std_logic_vector(to_unsigned(DDR_DEF_REFR_PERIOD, DDR_REFR_PERIOD_WIDTH)),

            DEVICE                      => DEVICE
        )
        port map (
            AMM_CLK                     => DDR_CLK                  (i),
            AMM_RST                     => ddr_reset_repl           (i)(0),

            AMM_READY                   => DDR_AVMM_READY           (i),
            AMM_READ                    => DDR_AVMM_READ            (i),
            AMM_WRITE                   => DDR_AVMM_WRITE           (i),
            AMM_ADDRESS                 => DDR_AVMM_ADDRESS         (i),
            AMM_READ_DATA               => DDR_AVMM_READDATA        (i),
            AMM_WRITE_DATA              => DDR_AVMM_WRITEDATA       (i),
            AMM_BURST_COUNT             => DDR_AVMM_BURSTCOUNT      (i),
            AMM_READ_DATA_VALID         => DDR_AVMM_READDATAVALID   (i),

            REFR_PERIOD                 => DDR_REFR_PERIOD          (i),
            REFR_REQ                    => DDR_REFR_REQ             (i),
            REFR_ACK                    => DDR_REFR_ACK             (i),

            EMIF_RST_REQ                => EMIF_RST_REQ             (i),
            EMIF_RST_DONE               => EMIF_RST_DONE            (i),
            EMIF_ECC_ISR                => EMIF_ECC_USR_INT         (i),
            EMIF_CAL_SUCCESS            => EMIF_CAL_SUCCESS         (i),
            EMIF_CAL_FAIL               => EMIF_CAL_FAIL            (i),
            EMIF_AUTO_PRECHARGE         => EMIF_AUTO_PRECHARGE      (i),

            MI_CLK                      => CLK,
            MI_RST                      => RESET,
            MI_DWR                      => split_mi_dwr             (i),
            MI_ADDR                     => split_mi_addr            (i),
            MI_BE                       => split_mi_be              (i),
            MI_RD                       => split_mi_rd              (i),
            MI_WR                       => split_mi_wr              (i),
            MI_ARDY                     => split_mi_ardy            (i),
            MI_DRD                      => split_mi_drd             (i),
            MI_DRDY                     => split_mi_drdy            (i)
        );

        mi_async_i : entity work.MI_ASYNC
        generic map (
            ADDR_WIDTH => MI_ADDR_WIDTH,
            DATA_WIDTH => MI_DATA_WIDTH,
            DEVICE     => DEVICE
        )
        port map (
            CLK_M     => CLK,
            RESET_M   => RESET,
            MI_M_DWR  => split_mi_dwr (DDR_PORTS + i),
            MI_M_ADDR => split_mi_addr(DDR_PORTS + i),
            MI_M_RD   => split_mi_rd  (DDR_PORTS + i),
            MI_M_WR   => split_mi_wr  (DDR_PORTS + i),
            MI_M_BE   => split_mi_be  (DDR_PORTS + i),
            MI_M_DRD  => split_mi_drd (DDR_PORTS + i),
            MI_M_ARDY => split_mi_ardy(DDR_PORTS + i),
            MI_M_DRDY => split_mi_drdy(DDR_PORTS + i),

            CLK_S     => DDR_CLK          (i),
            RESET_S   => ddr_reset_repl   (i)(2),
            MI_S_DWR  => ddr_log_mi_dwr   (i),
            MI_S_ADDR => ddr_log_mi_addr  (i),
            MI_S_RD   => ddr_log_mi_rd    (i),
            MI_S_WR   => ddr_log_mi_wr    (i),
            MI_S_BE   => ddr_log_mi_be    (i),
            MI_S_DRD  => ddr_log_mi_drd   (i),
            MI_S_ARDY => ddr_log_mi_ardy  (i),
            MI_S_DRDY => ddr_log_mi_drdy  (i)
        );

        ddr_logger_i : entity work.MEM_LOGGER
        generic map (
            MEM_DATA_WIDTH          => DDR_DATA_WIDTH,
            MEM_ADDR_WIDTH          => DDR_ADDR_WIDTH,
            MEM_BURST_COUNT_WIDTH   => DDR_BURST_WIDTH,
            MEM_FREQ_KHZ            => DDR_FREQ_KHZ,
            MI_DATA_WIDTH           => MI_DATA_WIDTH,
            MI_ADDR_WIDTH           => MI_ADDR_WIDTH,
            MEM_ASYNC               => False,
            DEVICE                  => DEVICE
        )
        port map (
            CLK                     => DDR_CLK                  (i),
            RST                     => ddr_reset_repl           (i)(1),

            MEM_READY               => DDR_AVMM_READY           (i),
            MEM_READ                => DDR_AVMM_READ            (i),
            MEM_WRITE               => DDR_AVMM_WRITE           (i),
            MEM_ADDRESS             => DDR_AVMM_ADDRESS         (i),
            MEM_READ_DATA           => DDR_AVMM_READDATA        (i),
            MEM_WRITE_DATA          => DDR_AVMM_WRITEDATA       (i),
            MEM_BURST_COUNT         => DDR_AVMM_BURSTCOUNT      (i),
            MEM_READ_DATA_VALID     => DDR_AVMM_READDATAVALID   (i),

            MI_DWR                  => ddr_log_mi_dwr           (i),
            MI_ADDR                 => ddr_log_mi_addr          (i),
            MI_BE                   => ddr_log_mi_be            (i),
            MI_RD                   => ddr_log_mi_rd            (i),
            MI_WR                   => ddr_log_mi_wr            (i),
            MI_ARDY                 => ddr_log_mi_ardy          (i),
            MI_DRD                  => ddr_log_mi_drd           (i),
            MI_DRDY                 => ddr_log_mi_drdy          (i)
        );
    end generate;

    -- =========================================================================
    -- HBM MEMORY TESTER
    -- =========================================================================

    hbm_tester_g: if (HBM_PORTS > 0) generate
        hbm_test_mod_g: for i in 0 to HBM_MODULES-1 generate
            subtype MOD_R is natural range HBM_PORTS_PER_MODULE*(i+1)-1 downto HBM_PORTS_PER_MODULE*i;
        begin

            hbm_clk_s(i)       <= HBM_CLK(i);
            hbm_reset_s(i)     <= HBM_RESET(i);
            hbm_init_done_s(i) <= HBM_INIT_DONE(i);

            HBM_AXI_ARADDR(MOD_R)       <= hbm_axi_araddr_s(i);
            HBM_AXI_ARBURST(MOD_R)      <= hbm_axi_arburst_s(i);
            HBM_AXI_ARID(MOD_R)         <= hbm_axi_arid_s(i);
            HBM_AXI_ARLEN(MOD_R)        <= hbm_axi_arlen_s(i);
            HBM_AXI_ARSIZE(MOD_R)       <= hbm_axi_arsize_s(i);
            HBM_AXI_ARVALID(MOD_R)      <= hbm_axi_arvalid_s(i);
            hbm_axi_arready_s(i)        <= HBM_AXI_ARREADY(MOD_R);

            hbm_axi_rdata_s(i)          <= HBM_AXI_RDATA(MOD_R);
            hbm_axi_rdata_parity_s(i)   <= HBM_AXI_RDATA_PARITY(MOD_R);
            hbm_axi_rid_s(i)            <= HBM_AXI_RID(MOD_R);
            hbm_axi_rlast_s(i)          <= HBM_AXI_RLAST(MOD_R);
            hbm_axi_rresp_s(i)          <= HBM_AXI_RRESP(MOD_R);
            hbm_axi_rvalid_s(i)         <= HBM_AXI_RVALID(MOD_R);
            HBM_AXI_RREADY(MOD_R)       <= hbm_axi_rready_s(i);

            HBM_AXI_AWADDR(MOD_R)       <= hbm_axi_awaddr_s(i);
            HBM_AXI_AWBURST(MOD_R)      <= hbm_axi_awburst_s(i);
            HBM_AXI_AWID(MOD_R)         <= hbm_axi_awid_s(i);
            HBM_AXI_AWLEN(MOD_R)        <= hbm_axi_awlen_s(i);
            HBM_AXI_AWSIZE(MOD_R)       <= hbm_axi_awsize_s(i);
            HBM_AXI_AWVALID(MOD_R)      <= hbm_axi_awvalid_s(i);
            hbm_axi_awready_s(i)        <= HBM_AXI_AWREADY(MOD_R);

            HBM_AXI_WDATA(MOD_R)        <= hbm_axi_wdata_s(i);
            HBM_AXI_WDATA_PARITY(MOD_R) <= hbm_axi_wdata_parity_s(i);
            HBM_AXI_WLAST(MOD_R)        <= hbm_axi_wlast_s(i);
            HBM_AXI_WSTRB(MOD_R)        <= hbm_axi_wstrb_s(i);
            HBM_AXI_WVALID(MOD_R)       <= hbm_axi_wvalid_s(i);
            hbm_axi_wready_s(i)         <= HBM_AXI_WREADY(MOD_R);

            hbm_axi_bid_s(i)            <= HBM_AXI_BID(MOD_R);
            hbm_axi_bresp_s(i)          <= HBM_AXI_BRESP(MOD_R);
            hbm_axi_bvalid_s(i)         <= HBM_AXI_BVALID(MOD_R);
            HBM_AXI_BREADY(MOD_R)       <= hbm_axi_bready_s(i);

            hbm_tester_i : entity work.HBM_TESTER
            generic map (
                DEBUG            => True,
                PORTS            => HBM_PORTS_PER_MODULE,
                CNT_WIDTH        => 24,
                AXI_ADDR_WIDTH   => HBM_ADDR_WIDTH,
                AXI_DATA_WIDTH   => HBM_DATA_WIDTH,
                AXI_BURST_WIDTH  => HBM_BURST_WIDTH,
                AXI_ID_WIDTH     => HBM_ID_WIDTH,
                AXI_LEN_WIDTH    => HBM_LEN_WIDTH,
                AXI_SIZE_WIDTH   => HBM_SIZE_WIDTH,
                AXI_RESP_WIDTH   => HBM_RESP_WIDTH,
                USR_DATA_WIDTH   => HBM_DATA_WIDTH,
                PORT_ADDR_HBIT   => HBM_PORT_ADDR_HBIT,
                BASE_ADDR_OFFSET => HBM_BASE_ADDR_OFFSET,
                DEVICE           => DEVICE
            )
            port map (
                HBM_CLK             => hbm_clk_s(i),
                HBM_RESET           => hbm_reset_s(i),
                HBM_INIT_DONE       => hbm_init_done_s(i),

                MI_CLK              => CLK,
                MI_RESET            => RESET,
                MI_DWR              => split_mi_dwr(2*DDR_PORTS + i),
                MI_ADDR             => split_mi_addr(2*DDR_PORTS + i),
                MI_BE               => split_mi_be(2*DDR_PORTS + i),
                MI_RD               => split_mi_rd(2*DDR_PORTS + i),
                MI_WR               => split_mi_wr(2*DDR_PORTS + i),
                MI_ARDY             => split_mi_ardy(2*DDR_PORTS + i),
                MI_DRD              => split_mi_drd(2*DDR_PORTS + i),
                MI_DRDY             => split_mi_drdy(2*DDR_PORTS + i),

                WR_ADDR             => (others => (others => '0')),
                WR_DATA             => (others => (others => '0')),
                WR_DATA_LAST        => (others => '0'),
                WR_VALID            => (others => '0'),
                WR_READY            => open,
                WR_RSP_ACK          => open,
                WR_RSP_VALID        => open,
                WR_RSP_READY        => (others => '1'),
                RD_ADDR             => (others => (others => '0')),
                RD_ADDR_VALID       => (others => '0'),
                RD_ADDR_READY       => open,
                RD_DATA             => open,
                RD_DATA_LAST        => open,
                RD_DATA_VALID       => open,
                RD_DATA_READY       => (others => '1'),

                AXI_AWID            => hbm_axi_awid_s(i),
                AXI_AWADDR          => hbm_axi_awaddr_s(i),
                AXI_AWLEN           => hbm_axi_awlen_s(i),
                AXI_AWSIZE          => hbm_axi_awsize_s(i),
                AXI_AWBURST         => hbm_axi_awburst_s(i),
                AXI_AWPROT          => open,
                AXI_AWQOS           => open,
                AXI_AWUSER          => open,
                AXI_AWVALID         => hbm_axi_awvalid_s(i),
                AXI_AWREADY         => hbm_axi_awready_s(i),
                AXI_WDATA           => hbm_axi_wdata_s(i),
                AXI_WSTRB           => hbm_axi_wstrb_s(i),
                AXI_WUSER_DATA      => hbm_axi_wdata_parity_s(i),
                AXI_WUSER_STRB      => open,
                AXI_WLAST           => hbm_axi_wlast_s(i),
                AXI_WVALID          => hbm_axi_wvalid_s(i),
                AXI_WREADY          => hbm_axi_wready_s(i),
                AXI_BID             => hbm_axi_bid_s(i),
                AXI_BRESP           => hbm_axi_bresp_s(i),
                AXI_BVALID          => hbm_axi_bvalid_s(i),
                AXI_BREADY          => hbm_axi_bready_s(i),
                AXI_ARID            => hbm_axi_arid_s(i),
                AXI_ARADDR          => hbm_axi_araddr_s(i),
                AXI_ARLEN           => hbm_axi_arlen_s(i),
                AXI_ARSIZE          => hbm_axi_arsize_s(i),
                AXI_ARBURST         => hbm_axi_arburst_s(i),
                AXI_ARPROT          => open,
                AXI_ARQOS           => open,
                AXI_ARUSER          => open,
                AXI_ARVALID         => hbm_axi_arvalid_s(i),
                AXI_ARREADY         => hbm_axi_arready_s(i),
                AXI_RID             => hbm_axi_rid_s(i),
                AXI_RDATA           => hbm_axi_rdata_s(i),
                AXI_RUSER_DATA      => hbm_axi_rdata_parity_s(i),
                AXI_RUSER_ERR_DBE   => (others => '0'),
                AXI_RRESP           => hbm_axi_rresp_s(i),
                AXI_RLAST           => hbm_axi_rlast_s(i),
                AXI_RVALID          => hbm_axi_rvalid_s(i),
                AXI_RREADY          => hbm_axi_rready_s(i)
            );
        end generate;
    end generate;

    -- =========================================================================
    -- TERMINATION OF UNUSED MI PORTS
    -- =========================================================================
    mi_unused_g : for i in MI_PORTS_RAW to MI_PORTS-1 generate
        split_mi_ardy(i) <= split_mi_rd(i) or split_mi_wr(i);
        split_mi_drd (i) <= (others => '0');
        split_mi_drdy(i) <= split_mi_rd(i);
    end generate;

end architecture;
