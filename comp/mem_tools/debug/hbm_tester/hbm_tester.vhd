-- hbm_tester.vhd:
-- Copyright (C) 2024 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity HBM_TESTER is
    generic(
        DEBUG           : boolean := True;
        PORTS           : natural := 32;
        BL8_MODE        : std_logic_vector(PORTS-1 downto 0) := (others => '1');
        CNT_WIDTH       : natural := 24; -- max = 32, min 8
        AXI_ADDR_WIDTH  : natural := 32;
        AXI_DATA_WIDTH  : natural := 256;
        AXI_BURST_WIDTH : natural := 2;
        AXI_ID_WIDTH    : natural := 6;
        AXI_LEN_WIDTH   : natural := 4;
        AXI_SIZE_WIDTH  : natural := 3;
        AXI_RESP_WIDTH  : natural := 2;
        USR_DATA_WIDTH  : natural := 256;
        PORT_ADDR_HBIT  : natural := AXI_ADDR_WIDTH;
        DEVICE          : string := "AGILEX"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        HBM_CLK             : in  std_logic;
        HBM_RESET           : in  std_logic;

        -- =====================================================================
        -- COMMON MI32 INTERFACE (MI_CLK)
        -- =====================================================================
        MI_CLK              : in  std_logic;
        MI_RESET            : in  std_logic;
        MI_DWR              : in  std_logic_vector(31 downto 0);
        MI_ADDR             : in  std_logic_vector(31 downto 0);
        MI_BE               : in  std_logic_vector(3 downto 0);
        MI_RD               : in  std_logic;
        MI_WR               : in  std_logic;
        MI_ARDY             : out std_logic;
        MI_DRD              : out std_logic_vector(31 downto 0);
        MI_DRDY             : out std_logic;

        -- =====================================================================
        -- USER HBM SIMPLE INTERFACE (HSI) PER HBM PORT (HBM_CLK)
        -- =====================================================================
        -- WRITE ADDR/DATA SIGNALS
        WR_ADDR             : in  slv_array_t(PORTS-1 downto 0)(AXI_ADDR_WIDTH-1 downto 0);
        WR_DATA             : in  slv_array_t(PORTS-1 downto 0)(USR_DATA_WIDTH-1 downto 0);
        WR_DATA_LAST        : in  std_logic_vector(PORTS-1 downto 0);
        WR_VALID            : in  std_logic_vector(PORTS-1 downto 0);
        WR_READY            : out std_logic_vector(PORTS-1 downto 0);
        -- WRITE RESPONSE SIGNALS
        WR_RSP_ACK          : out std_logic_vector(PORTS-1 downto 0);
        WR_RSP_VALID        : out std_logic_vector(PORTS-1 downto 0);
        WR_RSP_READY        : in  std_logic_vector(PORTS-1 downto 0);
        -- READ ADDRESS SIGNALS
        RD_ADDR             : in  slv_array_t(PORTS-1 downto 0)(AXI_ADDR_WIDTH-1 downto 0);
        RD_ADDR_VALID       : in  std_logic_vector(PORTS-1 downto 0);
        RD_ADDR_READY       : out std_logic_vector(PORTS-1 downto 0);
        -- READ DATA SIGNALS
        RD_DATA             : out slv_array_t(PORTS-1 downto 0)(USR_DATA_WIDTH-1 downto 0);
        RD_DATA_LAST        : out std_logic_vector(PORTS-1 downto 0);
        RD_DATA_VALID       : out std_logic_vector(PORTS-1 downto 0);
        RD_DATA_READY       : in  std_logic_vector(PORTS-1 downto 0);

        -- =====================================================================
        -- AXI INTERFACE PER HBM PORT (HBM_CLK)
        -- =====================================================================
        -- WRITE ADDRESS SIGNALS
        AXI_AWID            : out slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
        AXI_AWADDR          : out slv_array_t(PORTS-1 downto 0)(AXI_ADDR_WIDTH-1 downto 0);
        AXI_AWLEN           : out slv_array_t(PORTS-1 downto 0)(AXI_LEN_WIDTH-1 downto 0);
        AXI_AWSIZE          : out slv_array_t(PORTS-1 downto 0)(AXI_SIZE_WIDTH-1 downto 0);
        AXI_AWBURST         : out slv_array_t(PORTS-1 downto 0)(AXI_BURST_WIDTH-1 downto 0);
        AXI_AWPROT          : out slv_array_t(PORTS-1 downto 0)(3-1 downto 0);
        AXI_AWQOS           : out slv_array_t(PORTS-1 downto 0)(4-1 downto 0);
        AXI_AWUSER          : out slv_array_t(PORTS-1 downto 0)(1-1 downto 0);
        AXI_AWVALID         : out std_logic_vector(PORTS-1 downto 0);
        AXI_AWREADY         : in  std_logic_vector(PORTS-1 downto 0);
        -- WRITE DATA SIGNALS
        AXI_WDATA           : out slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB           : out slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH/8-1 downto 0);
        AXI_WUSER_DATA      : out slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH/8-1 downto 0);
        AXI_WUSER_STRB      : out slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH/64-1 downto 0);
        AXI_WLAST           : out std_logic_vector(PORTS-1 downto 0);
        AXI_WVALID          : out std_logic_vector(PORTS-1 downto 0);
        AXI_WREADY          : in  std_logic_vector(PORTS-1 downto 0);
        -- WRITE RESPONSE SIGNALS
        AXI_BID             : in  slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
        AXI_BRESP           : in  slv_array_t(PORTS-1 downto 0)(AXI_RESP_WIDTH-1 downto 0);
        AXI_BVALID          : in  std_logic_vector(PORTS-1 downto 0);
        AXI_BREADY          : out std_logic_vector(PORTS-1 downto 0);
        -- READ ADDRESS SIGNALS
        AXI_ARID            : out slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
        AXI_ARADDR          : out slv_array_t(PORTS-1 downto 0)(AXI_ADDR_WIDTH-1 downto 0);
        AXI_ARLEN           : out slv_array_t(PORTS-1 downto 0)(AXI_LEN_WIDTH-1 downto 0);
        AXI_ARSIZE          : out slv_array_t(PORTS-1 downto 0)(AXI_SIZE_WIDTH-1 downto 0);
        AXI_ARBURST         : out slv_array_t(PORTS-1 downto 0)(AXI_BURST_WIDTH-1 downto 0);
        AXI_ARPROT          : out slv_array_t(PORTS-1 downto 0)(3-1 downto 0);
        AXI_ARQOS           : out slv_array_t(PORTS-1 downto 0)(4-1 downto 0);
        AXI_ARUSER          : out slv_array_t(PORTS-1 downto 0)(1-1 downto 0);
        AXI_ARVALID         : out std_logic_vector(PORTS-1 downto 0);
        AXI_ARREADY         : in  std_logic_vector(PORTS-1 downto 0);
        -- READ DATA SIGNALS
        AXI_RID             : in  slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
        AXI_RDATA           : in  slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
        AXI_RUSER_DATA      : in  slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH/8-1 downto 0);
        AXI_RUSER_ERR_DBE   : in  std_logic_vector(PORTS-1 downto 0);
        AXI_RRESP           : in  slv_array_t(PORTS-1 downto 0)(AXI_RESP_WIDTH-1 downto 0);
        AXI_RLAST           : in  std_logic_vector(PORTS-1 downto 0);
        AXI_RVALID          : in  std_logic_vector(PORTS-1 downto 0);
        AXI_RREADY          : out std_logic_vector(PORTS-1 downto 0)
    );
end HBM_TESTER;

architecture FULL of HBM_TESTER is

    signal s_gen_addr_mode : std_logic;
    signal s_gen_connect   : std_logic;
    signal s_gen_bl8_mode  : std_logic;
    signal s_gen_run_mode  : std_logic_vector(1 downto 0);
    signal s_gen_run       : std_logic_vector(PORTS-1 downto 0);
    signal s_gen_rw_switch : std_logic;
    signal s_gen_wr_dead   : std_logic;

    signal s_mon_done      : std_logic_vector(PORTS-1 downto 0);
    signal s_mon_reset     : std_logic_vector(PORTS-1 downto 0);
    signal s_mon_time      : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal s_mon_cnt0_mode : std_logic_vector(3-1 downto 0);
    signal s_mon_cnt1_mode : std_logic_vector(3-1 downto 0);
    signal s_mon_cnt0      : slv_array_t(PORTS-1 downto 0)(CNT_WIDTH-1 downto 0);
    signal s_mon_cnt1      : slv_array_t(PORTS-1 downto 0)(CNT_WIDTH-1 downto 0);

    signal s_synced_mi_dwr  : std_logic_vector(31 downto 0);
    signal s_synced_mi_addr : std_logic_vector(31 downto 0);
    signal s_synced_mi_rd   : std_logic;
    signal s_synced_mi_wr   : std_logic;
    signal s_synced_mi_be   : std_logic_vector(3 downto 0);
    signal s_synced_mi_drd  : std_logic_vector(31 downto 0);
    signal s_synced_mi_ardy : std_logic;
    signal s_synced_mi_drdy : std_logic;

begin

    port_g : for i in 0 to PORTS-1 generate
        port_i : entity work.HBM_TESTER_PORT
        generic map(
            DEBUG           => DEBUG,
            CNT_WIDTH       => CNT_WIDTH,
            PORT_ID         => i,
            AXI_ADDR_WIDTH  => AXI_ADDR_WIDTH,
            AXI_DATA_WIDTH  => AXI_DATA_WIDTH,
            AXI_BURST_WIDTH => AXI_BURST_WIDTH,
            AXI_ID_WIDTH    => AXI_ID_WIDTH,
            AXI_LEN_WIDTH   => AXI_LEN_WIDTH,
            AXI_SIZE_WIDTH  => AXI_SIZE_WIDTH,
            AXI_RESP_WIDTH  => AXI_RESP_WIDTH,
            USR_DATA_WIDTH  => USR_DATA_WIDTH,
            PORT_ADDR_HBIT  => PORT_ADDR_HBIT,
            DEVICE          => DEVICE
        )
        port map(
            CLK               => HBM_CLK,
            RESET             => HBM_RESET,

            WR_ADDR           => WR_ADDR(i),
            WR_DATA           => WR_DATA(i),
            WR_DATA_LAST      => WR_DATA_LAST(i),
            WR_VALID          => WR_VALID(i),
            WR_READY          => WR_READY(i),
            WR_RSP_ACK        => WR_RSP_ACK(i),
            WR_RSP_VALID      => WR_RSP_VALID(i),
            WR_RSP_READY      => WR_RSP_READY(i),
            RD_ADDR           => RD_ADDR(i),
            RD_ADDR_VALID     => RD_ADDR_VALID(i),
            RD_ADDR_READY     => RD_ADDR_READY(i),
            RD_DATA           => RD_DATA(i),
            RD_DATA_LAST      => RD_DATA_LAST(i),
            RD_DATA_VALID     => RD_DATA_VALID(i),
            RD_DATA_READY     => RD_DATA_READY(i),

            AXI_AWID          => AXI_AWID(i),
            AXI_AWADDR        => AXI_AWADDR(i),
            AXI_AWLEN         => AXI_AWLEN(i),
            AXI_AWSIZE        => AXI_AWSIZE(i),
            AXI_AWBURST       => AXI_AWBURST(i),
            AXI_AWPROT        => AXI_AWPROT(i),
            AXI_AWQOS         => AXI_AWQOS(i),
            AXI_AWUSER        => AXI_AWUSER(i),
            AXI_AWVALID       => AXI_AWVALID(i),
            AXI_AWREADY       => AXI_AWREADY(i),

            AXI_WDATA         => AXI_WDATA(i),
            AXI_WSTRB         => AXI_WSTRB(i),
            AXI_WUSER_DATA    => AXI_WUSER_DATA(i),
            AXI_WUSER_STRB    => AXI_WUSER_STRB(i),
            AXI_WLAST         => AXI_WLAST(i),
            AXI_WVALID        => AXI_WVALID(i),
            AXI_WREADY        => AXI_WREADY(i),

            AXI_BID           => AXI_BID(i),
            AXI_BRESP         => AXI_BRESP(i),
            AXI_BVALID        => AXI_BVALID(i),
            AXI_BREADY        => AXI_BREADY(i),

            AXI_ARID          => AXI_ARID(i),
            AXI_ARADDR        => AXI_ARADDR(i),
            AXI_ARLEN         => AXI_ARLEN(i),
            AXI_ARSIZE        => AXI_ARSIZE(i),
            AXI_ARBURST       => AXI_ARBURST(i),
            AXI_ARPROT        => AXI_ARPROT(i),
            AXI_ARQOS         => AXI_ARQOS(i),
            AXI_ARUSER        => AXI_ARUSER(i),
            AXI_ARVALID       => AXI_ARVALID(i),
            AXI_ARREADY       => AXI_ARREADY(i),

            AXI_RID           => AXI_RID(i),
            AXI_RDATA         => AXI_RDATA(i),
            AXI_RUSER_DATA    => AXI_RUSER_DATA(i),
            AXI_RUSER_ERR_DBE => AXI_RUSER_ERR_DBE(i),
            AXI_RRESP         => AXI_RRESP(i),
            AXI_RLAST         => AXI_RLAST(i),
            AXI_RVALID        => AXI_RVALID(i),
            AXI_RREADY        => AXI_RREADY(i),

            DB_GEN_ADDR_MODE  => s_gen_addr_mode,
            DB_GEN_CONNECT    => s_gen_connect,
            DB_GEN_BL8_MODE   => s_gen_bl8_mode,
            DB_GEN_RUN_MODE   => s_gen_run_mode,
            DB_GEN_RUN        => s_gen_run(i),
            DB_GEN_RW_SWITCH  => s_gen_rw_switch,
            DB_GEN_WR_DEAD    => s_gen_wr_dead,
            DB_MON_DONE       => s_mon_done(i),
            DB_MON_RESET      => s_mon_reset(i),
            DB_MON_TIME       => s_mon_time,
            DB_MON_CNT0_MODE  => s_mon_cnt0_mode,
            DB_MON_CNT1_MODE  => s_mon_cnt1_mode,
            DB_STAT_CNT0      => s_mon_cnt0(i),
            DB_STAT_CNT1      => s_mon_cnt1(i)
        );
    end generate;

    mi32_async_i : entity work.MI_ASYNC
    generic map(
        DEVICE => DEVICE
    )
    port map(
        CLK_M     => MI_CLK,
        RESET_M   => MI_RESET,
        MI_M_DWR  => MI_DWR,
        MI_M_ADDR => MI_ADDR,
        MI_M_RD   => MI_RD,
        MI_M_WR   => MI_WR,
        MI_M_BE   => MI_BE,
        MI_M_DRD  => MI_DRD,
        MI_M_ARDY => MI_ARDY,
        MI_M_DRDY => MI_DRDY,

        CLK_S     => HBM_CLK,
        RESET_S   => HBM_RESET,
        MI_S_DWR  => s_synced_mi_dwr,
        MI_S_ADDR => s_synced_mi_addr,
        MI_S_RD   => s_synced_mi_rd,
        MI_S_WR   => s_synced_mi_wr,
        MI_S_BE   => s_synced_mi_be,
        MI_S_DRD  => s_synced_mi_drd,
        MI_S_ARDY => s_synced_mi_ardy,
        MI_S_DRDY => s_synced_mi_drdy
    );

    adc_i : entity work.HBM_TESTER_ADC
    generic map(
        PORTS     => PORTS,
        CNT_WIDTH => CNT_WIDTH
    )
    port map(
        CLK              => HBM_CLK,
        RESET            => HBM_RESET,

        MI_DWR           => s_synced_mi_dwr,
        MI_ADDR          => s_synced_mi_addr,
        MI_BE            => s_synced_mi_be,
        MI_RD            => s_synced_mi_rd,
        MI_WR            => s_synced_mi_wr,
        MI_ARDY          => s_synced_mi_ardy,
        MI_DRD           => s_synced_mi_drd,
        MI_DRDY          => s_synced_mi_drdy,

        DB_GEN_ADDR_MODE => s_gen_addr_mode,
        DB_GEN_CONNECT   => s_gen_connect,
        DB_GEN_BL8_MODE  => s_gen_bl8_mode,
        DB_GEN_RUN_MODE  => s_gen_run_mode,
        DB_GEN_RUN       => s_gen_run,
        DB_GEN_RW_SWITCH => s_gen_rw_switch,
        DB_GEN_WR_DEAD   => s_gen_wr_dead,
        DB_MON_TIME      => s_mon_time,
        DB_MON_DONE      => s_mon_done,
        DB_MON_RESET     => s_mon_reset,
        DB_MON_CNT0_MODE => s_mon_cnt0_mode,
        DB_MON_CNT1_MODE => s_mon_cnt1_mode,
        DB_STAT_CNT0     => s_mon_cnt0,
        DB_STAT_CNT1     => s_mon_cnt1
    );

end architecture;
