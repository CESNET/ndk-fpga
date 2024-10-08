-- hbm_tester_port.vhd:
-- Copyright (C) 2024 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity HBM_TESTER_PORT is
    generic(
        DEBUG           : boolean := True;
        -- when USE_AXI_ID is false, you can disable Re-order buffer in HBM IP
        USE_AXI_ID      : boolean := True;
        CNT_WIDTH       : natural := 16;
        PORT_ID         : natural := 0;
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
        CLK               : in  std_logic;
        RESET             : in  std_logic;

        -- =====================================================================
        -- HBM SIMPLE INTERFACE (HSI)
        -- =====================================================================
        -- WRITE ADDR/DATA SIGNALS
        WR_ADDR           : in  std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        WR_DATA           : in  std_logic_vector(USR_DATA_WIDTH-1 downto 0);
        WR_DATA_LAST      : in  std_logic;
        WR_VALID          : in  std_logic;
        WR_READY          : out std_logic;
        -- WRITE RESPONSE SIGNALS
        WR_RSP_ACK        : out std_logic;
        WR_RSP_VALID      : out std_logic;
        WR_RSP_READY      : in  std_logic;
        -- READ ADDRESS SIGNALS
        RD_ADDR           : in  std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        RD_ADDR_VALID     : in  std_logic;
        RD_ADDR_READY     : out std_logic;
        -- READ DATA SIGNALS
        RD_DATA           : out std_logic_vector(USR_DATA_WIDTH-1 downto 0);
        RD_DATA_LAST      : out std_logic;
        RD_DATA_VALID     : out std_logic;
        RD_DATA_READY     : in  std_logic;

        -- =====================================================================
        -- HBM PSEUDO CHANNEL AXI INTERFACE
        -- =====================================================================
        -- WRITE ADDRESS SIGNALS
        AXI_AWID          : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_AWADDR        : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_AWLEN         : out std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
        AXI_AWSIZE        : out std_logic_vector(AXI_SIZE_WIDTH-1 downto 0);
        AXI_AWBURST       : out std_logic_vector(AXI_BURST_WIDTH-1 downto 0);
        AXI_AWPROT        : out std_logic_vector(3-1 downto 0);
        AXI_AWQOS         : out std_logic_vector(4-1 downto 0);
        AXI_AWUSER        : out std_logic_vector(1-1 downto 0);
        AXI_AWVALID       : out std_logic;
        AXI_AWREADY       : in  std_logic;
        -- WRITE DATA SIGNALS
        AXI_WDATA         : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB         : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        AXI_WUSER_DATA    : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        AXI_WUSER_STRB    : out std_logic_vector(AXI_DATA_WIDTH/64-1 downto 0);
        AXI_WLAST         : out std_logic;
        AXI_WVALID        : out std_logic;
        AXI_WREADY        : in  std_logic;
        -- WRITE RESPONSE SIGNALS
        AXI_BID           : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_BRESP         : in  std_logic_vector(AXI_RESP_WIDTH-1 downto 0);
        AXI_BVALID        : in  std_logic;
        AXI_BREADY        : out std_logic;
        -- READ ADDRESS SIGNALS
        AXI_ARID          : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_ARADDR        : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_ARLEN         : out std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
        AXI_ARSIZE        : out std_logic_vector(AXI_SIZE_WIDTH-1 downto 0);
        AXI_ARBURST       : out std_logic_vector(AXI_BURST_WIDTH-1 downto 0);
        AXI_ARPROT        : out std_logic_vector(3-1 downto 0);
        AXI_ARQOS         : out std_logic_vector(4-1 downto 0);
        AXI_ARUSER        : out std_logic_vector(1-1 downto 0);
        AXI_ARVALID       : out std_logic;
        AXI_ARREADY       : in  std_logic;
        -- READ DATA SIGNALS
        AXI_RID           : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_RDATA         : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_RUSER_DATA    : in  std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        AXI_RUSER_ERR_DBE : in  std_logic;
        AXI_RRESP         : in  std_logic_vector(AXI_RESP_WIDTH-1 downto 0);
        AXI_RLAST         : in  std_logic;
        AXI_RVALID        : in  std_logic;
        AXI_RREADY        : out std_logic;

        -- =====================================================================
        -- DEBUG INTERFACE
        -- =====================================================================
        -- Mode of increment address: 0 = sequential, 1 = pseudorandom
        DB_GEN_ADDR_MODE  : in  std_logic;
        -- Generator conection control: 0 = USER <-> HBM, 1 = GEN <-> HBM
        DB_GEN_CONNECT    : in  std_logic;
        DB_GEN_BL8_MODE   : in  std_logic;
        -- Generator run mode: "11" = RD and WR,
        --                     "10" = only RD,
        --                     "01" = only WR,
        --                     "00" = no requests
        DB_GEN_RUN_MODE   : in  std_logic_vector(1 downto 0);
        -- Generator control: 0 = stop, 1 = run
        DB_GEN_RUN        : in  std_logic;
        DB_GEN_RW_SWITCH  : in  std_logic;
        -- Generator dead data: 0 = counter value, 1 = dead cafe
        DB_GEN_WR_DEAD    : in  std_logic;
        -- Time of monitoring in clock cycles
        DB_MON_TIME       : in  std_logic_vector(CNT_WIDTH-1 downto 0);
        -- Monitoring is done (monitoring time is out) and statistics are ready,
        -- for next monitoring is need monitor reset
        DB_MON_DONE       : out std_logic;
        -- Monitor reset, this clean statistics counters
        DB_MON_RESET      : in  std_logic;
        -- Counters mode: 000 = monitoring of read data words
        --                001 = monitoring of write data words
        --                010 = monitoring of read latency
        --                011 = monitoring of write latency
        --                100 = monitoring of read data ok
        --                101 = monitoring of read data error
        DB_MON_CNT0_MODE  : in  std_logic_vector(3-1 downto 0);
        DB_MON_CNT1_MODE  : in  std_logic_vector(3-1 downto 0);
        -- Outputs of configurable counters
        DB_STAT_CNT0      : out std_logic_vector(CNT_WIDTH-1 downto 0);
        DB_STAT_CNT1      : out std_logic_vector(CNT_WIDTH-1 downto 0)
   );
end HBM_TESTER_PORT;

architecture FULL of HBM_TESTER_PORT is

    signal s_reset_reg            : std_logic;

    signal s_db_gen_addr_mode_reg : std_logic;
    signal s_db_gen_connect_reg   : std_logic;
    signal s_db_gen_bl8_mode_reg  : std_logic;
    signal s_db_gen_run_mode_reg  : std_logic_vector(1 downto 0);
    signal s_db_gen_run_reg       : std_logic;
    signal s_db_gen_rw_switch_reg : std_logic;
    signal s_db_gen_wr_dead_reg   : std_logic;

    signal s_db_mon_time_reg      : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal s_db_mon_reset_reg     : std_logic;
    signal s_db_mon_cnt0_mode_reg : std_logic_vector(3-1 downto 0);
    signal s_db_mon_cnt1_mode_reg : std_logic_vector(3-1 downto 0);
    signal s_db_mon_done_reg      : std_logic;
    signal s_db_stat_cnt0_reg     : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal s_db_stat_cnt1_reg     : std_logic_vector(CNT_WIDTH-1 downto 0);

    signal s_gen_wr_addr       : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_gen_wr_data       : std_logic_vector(USR_DATA_WIDTH-1 downto 0);
    signal s_gen_wr_data_last  : std_logic;
    signal s_gen_wr_valid      : std_logic;
    signal s_gen_wr_ready      : std_logic;
    signal s_gen_wr_rsp_ack    : std_logic;
    signal s_gen_wr_rsp_valid  : std_logic;
    signal s_gen_wr_rsp_ready  : std_logic;
    signal s_gen_rd_addr       : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_gen_rd_addr_valid : std_logic;
    signal s_gen_rd_addr_ready : std_logic;
    signal s_gen_rd_data       : std_logic_vector(USR_DATA_WIDTH-1 downto 0);
    signal s_gen_rd_data_last  : std_logic;
    signal s_gen_rd_data_valid : std_logic;
    signal s_gen_rd_data_ready : std_logic;

    signal s_gen_data_ok_inc   : std_logic;
    signal s_gen_data_err_inc  : std_logic;

    signal s_mid_wr_addr       : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_mid_wr_data       : std_logic_vector(USR_DATA_WIDTH-1 downto 0);
    signal s_mid_wr_data_last  : std_logic;
    signal s_mid_wr_pdata      : std_logic_vector(AXI_ADDR_WIDTH+USR_DATA_WIDTH+1-1 downto 0);
    signal s_mid_wr_valid      : std_logic;
    signal s_mid_wr_ready      : std_logic;
    signal s_mid_wr_rsp_ack    : std_logic;
    signal s_mid_wr_rsp_valid  : std_logic;
    signal s_mid_wr_rsp_ready  : std_logic;
    signal s_mid_rd_addr       : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_mid_rd_addr_valid : std_logic;
    signal s_mid_rd_addr_ready : std_logic;
    signal s_mid_rd_data       : std_logic_vector(USR_DATA_WIDTH-1 downto 0);
    signal s_mid_rd_data_last  : std_logic;
    signal s_mid_rd_pdata      : std_logic_vector(USR_DATA_WIDTH+1-1 downto 0);
    signal s_mid_rd_data_valid : std_logic;
    signal s_mid_rd_data_ready : std_logic;

    signal s_hbm_wr_addr       : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_hbm_wr_data       : std_logic_vector(USR_DATA_WIDTH-1 downto 0);
    signal s_hbm_wr_data_last  : std_logic;
    signal s_hbm_wr_pdata      : std_logic_vector(AXI_ADDR_WIDTH+USR_DATA_WIDTH+1-1 downto 0);
    signal s_hbm_wr_valid      : std_logic;
    signal s_hbm_wr_ready      : std_logic;
    signal s_hbm_wr_rsp_ack    : std_logic;
    signal s_hbm_wr_rsp_valid  : std_logic;
    signal s_hbm_wr_rsp_ready  : std_logic;
    signal s_hbm_rd_addr       : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_hbm_rd_addr_valid : std_logic;
    signal s_hbm_rd_addr_ready : std_logic;
    signal s_hbm_rd_data       : std_logic_vector(USR_DATA_WIDTH-1 downto 0);
    signal s_hbm_rd_data_last  : std_logic;
    signal s_hbm_rd_pdata      : std_logic_vector(USR_DATA_WIDTH+1-1 downto 0);
    signal s_hbm_rd_data_valid : std_logic;
    signal s_hbm_rd_data_ready : std_logic;

    signal s_hbm_burst_size       : std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
    signal s_hbm_wr_burst_cnt     : unsigned(1 downto 0);
    signal s_hbm_wr_burst_first   : std_logic;
    signal s_hbm_wr_burst_last    : std_logic;
    signal s_hbm_wr_burst_cnt_max : unsigned(1 downto 0);
    signal s_hbm_wr_id_cnt        : unsigned(AXI_ID_WIDTH-1 downto 0);
    signal s_hbm_rd_id_cnt        : unsigned(AXI_ID_WIDTH-1 downto 0);

    signal s_axi_awid             : std_logic_vector(AXI_ID_WIDTH-1 downto 0);
    signal s_axi_awaddr           : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_axi_awlen            : std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
    signal s_axi_awsize           : std_logic_vector(AXI_SIZE_WIDTH-1 downto 0);
    signal s_axi_awburst          : std_logic_vector(AXI_BURST_WIDTH-1 downto 0);
    signal s_axi_awprot           : std_logic_vector(3-1 downto 0);
    signal s_axi_awqos            : std_logic_vector(4-1 downto 0);
    signal s_axi_awuser           : std_logic_vector(1-1 downto 0);
    signal s_axi_awvalid          : std_logic;
    signal s_axi_awready          : std_logic;
    signal s_axi_wdata            : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal s_axi_wstrb            : std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
    signal s_axi_wuser_data       : std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
    signal s_axi_wuser_strb       : std_logic_vector(AXI_DATA_WIDTH/64-1 downto 0);
    signal s_axi_wlast            : std_logic;
    signal s_axi_wvalid           : std_logic;
    signal s_axi_wready           : std_logic;
    signal s_axi_bid              : std_logic_vector(AXI_ID_WIDTH-1 downto 0);
    signal s_axi_bresp            : std_logic_vector(AXI_RESP_WIDTH-1 downto 0);
    signal s_axi_bvalid           : std_logic;
    signal s_axi_bready           : std_logic;
    signal s_axi_arid             : std_logic_vector(AXI_ID_WIDTH-1 downto 0);
    signal s_axi_araddr           : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal s_axi_arlen            : std_logic_vector(AXI_LEN_WIDTH-1 downto 0);
    signal s_axi_arsize           : std_logic_vector(AXI_SIZE_WIDTH-1 downto 0);
    signal s_axi_arburst          : std_logic_vector(AXI_BURST_WIDTH-1 downto 0);
    signal s_axi_arprot           : std_logic_vector(3-1 downto 0);
    signal s_axi_arqos            : std_logic_vector(4-1 downto 0);
    signal s_axi_aruser           : std_logic_vector(1-1 downto 0);
    signal s_axi_arvalid          : std_logic;
    signal s_axi_arready          : std_logic;
    signal s_axi_rid              : std_logic_vector(AXI_ID_WIDTH-1 downto 0);
    signal s_axi_rdata            : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal s_axi_ruser_data       : std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
    signal s_axi_ruser_err_dbe    : std_logic;
    signal s_axi_rresp            : std_logic_vector(AXI_RESP_WIDTH-1 downto 0);
    signal s_axi_rlast            : std_logic;
    signal s_axi_rvalid           : std_logic;
    signal s_axi_rready           : std_logic;

    attribute keep : string;
    attribute keep of s_reset_reg            : signal is "true";
    attribute keep of s_db_gen_addr_mode_reg : signal is "true";
    attribute keep of s_db_gen_connect_reg   : signal is "true";
    attribute keep of s_db_gen_bl8_mode_reg  : signal is "true";
    attribute keep of s_db_gen_run_mode_reg  : signal is "true";
    attribute keep of s_db_gen_run_reg       : signal is "true";
    attribute keep of s_db_gen_rw_switch_reg : signal is "true";
    attribute keep of s_db_gen_wr_dead_reg   : signal is "true";
    attribute keep of s_db_mon_time_reg      : signal is "true";
    attribute keep of s_db_mon_reset_reg     : signal is "true";
    attribute keep of s_db_mon_cnt0_mode_reg : signal is "true";
    attribute keep of s_db_mon_cnt1_mode_reg : signal is "true";
    attribute keep of s_db_mon_done_reg      : signal is "true";
    attribute keep of s_db_stat_cnt0_reg     : signal is "true";
    attribute keep of s_db_stat_cnt1_reg     : signal is "true";

    --attribute mark_debug : string;
    --attribute mark_debug of s_axi_awid : signal is "true";
    --attribute mark_debug of s_axi_awaddr : signal is "true";
    --attribute mark_debug of s_axi_awlen : signal is "true";
    --attribute mark_debug of s_axi_awsize : signal is "true";
    --attribute mark_debug of s_axi_awburst : signal is "true";
    --attribute mark_debug of s_axi_awprot : signal is "true";
    --attribute mark_debug of s_axi_awqos : signal is "true";
    --attribute mark_debug of s_axi_awuser : signal is "true";
    --attribute mark_debug of s_axi_awvalid : signal is "true";
    --attribute mark_debug of s_axi_awready : signal is "true";
    --attribute mark_debug of s_axi_wdata : signal is "true";
    --attribute mark_debug of s_axi_wstrb : signal is "true";
    --attribute mark_debug of s_axi_wuser_data : signal is "true";
    --attribute mark_debug of s_axi_wuser_strb : signal is "true";
    --attribute mark_debug of s_axi_wlast : signal is "true";
    --attribute mark_debug of s_axi_wvalid : signal is "true";
    --attribute mark_debug of s_axi_wready : signal is "true";
    --attribute mark_debug of s_axi_bid : signal is "true";
    --attribute mark_debug of s_axi_bresp : signal is "true";
    --attribute mark_debug of s_axi_bvalid : signal is "true";
    --attribute mark_debug of s_axi_bready : signal is "true";
    --attribute mark_debug of s_axi_arid : signal is "true";
    --attribute mark_debug of s_axi_araddr : signal is "true";
    --attribute mark_debug of s_axi_arlen : signal is "true";
    --attribute mark_debug of s_axi_arsize : signal is "true";
    --attribute mark_debug of s_axi_arburst : signal is "true";
    --attribute mark_debug of s_axi_arprot : signal is "true";
    --attribute mark_debug of s_axi_arqos : signal is "true";
    --attribute mark_debug of s_axi_aruser : signal is "true";
    --attribute mark_debug of s_axi_arvalid : signal is "true";
    --attribute mark_debug of s_axi_arready : signal is "true";
    --attribute mark_debug of s_axi_rid : signal is "true";
    --attribute mark_debug of s_axi_rdata : signal is "true";
    --attribute mark_debug of s_axi_ruser_data : signal is "true";
    --attribute mark_debug of s_axi_ruser_err_dbe : signal is "true";
    --attribute mark_debug of s_axi_rresp : signal is "true";
    --attribute mark_debug of s_axi_rlast : signal is "true";
    --attribute mark_debug of s_axi_rvalid : signal is "true";
    --attribute mark_debug of s_axi_rready : signal is "true";

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reset_reg <= RESET;

            s_db_gen_connect_reg   <= DB_GEN_CONNECT;
            s_db_gen_addr_mode_reg <= DB_GEN_ADDR_MODE;
            s_db_gen_bl8_mode_reg  <= DB_GEN_BL8_MODE;
            s_db_gen_run_mode_reg  <= DB_GEN_RUN_MODE;
            s_db_gen_run_reg       <= DB_GEN_RUN;
            s_db_gen_rw_switch_reg <= DB_GEN_RW_SWITCH;
            s_db_gen_wr_dead_reg   <= DB_GEN_WR_DEAD;

            s_db_mon_time_reg      <= DB_MON_TIME;
            s_db_mon_reset_reg     <= DB_MON_RESET;
            s_db_mon_cnt0_mode_reg <= DB_MON_CNT0_MODE;
            s_db_mon_cnt1_mode_reg <= DB_MON_CNT1_MODE;

            DB_MON_DONE  <= s_db_mon_done_reg;
            DB_STAT_CNT0 <= s_db_stat_cnt0_reg;
            DB_STAT_CNT1 <= s_db_stat_cnt1_reg;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  HMC BURST PARAMETERS
    -- -------------------------------------------------------------------------
    -- Burst Size. This signal indicates the size of each transfer in
    -- the burst: "101" = 32 Bytes (BL4), "110" = 64 Bytes
    -- The 32B and 64B access refers to data corresponding to 64 bits
    -- (one Pseudo Channel) for 4 burst cycles (32B) or 8 burst cycles (64B).
    -- The 64B access granularity is the default for better efficiency.

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_db_gen_bl8_mode_reg = '1') then
                s_hbm_burst_size       <= std_logic_vector(to_unsigned(1, AXI_LEN_WIDTH));
                s_hbm_wr_burst_cnt_max <= "01";
            else
                s_hbm_burst_size       <= std_logic_vector(to_unsigned(0, AXI_LEN_WIDTH));
                s_hbm_wr_burst_cnt_max <= "00";
            end if;
        end if;
    end process;

    -- =========================================================================
    --  CONECTIONS WITHOUT DEBUG MODULES
    -- =========================================================================

    debug_off_g : if not DEBUG generate
        s_mid_wr_addr       <= WR_ADDR;
        s_mid_wr_data       <= WR_DATA;
        s_mid_wr_data_last  <= WR_DATA_LAST;
        s_mid_wr_valid      <= WR_VALID;
        WR_READY            <= s_mid_wr_ready;

        WR_RSP_ACK          <= s_mid_wr_rsp_ack;
        WR_RSP_VALID        <= s_mid_wr_rsp_valid;
        s_mid_wr_rsp_ready  <= WR_RSP_READY;

        s_mid_rd_addr       <= RD_ADDR;
        s_mid_rd_addr_valid <= RD_ADDR_VALID;
        RD_ADDR_READY       <= s_mid_rd_addr_ready;

        RD_DATA             <= s_mid_rd_data;
        RD_DATA_LAST        <= s_mid_rd_data_last;
        RD_DATA_VALID       <= s_mid_rd_data_valid;
        s_mid_rd_data_ready <= RD_DATA_READY;

        -- All output debug signals are set to GND.
        DB_MON_DONE  <= '0';
        DB_STAT_CNT0 <= (others => '0');
        DB_STAT_CNT1 <= (others => '0');
    end generate;

    -- =========================================================================
    --  CONECTIONS WITH DEBUG MODULES
    -- =========================================================================

    debug_on_g : if DEBUG generate

        -- ---------------------------------------------------------------------
        --  TRAFFIC GENERATOR
        -- ---------------------------------------------------------------------

        generator_i : entity work.HBM_TESTER_GEN
        generic map(
            USR_DATA_WIDTH => USR_DATA_WIDTH,
            AXI_ADDR_WIDTH => AXI_ADDR_WIDTH,
            PORT_ADDR_HBIT => PORT_ADDR_HBIT,
            PORT_ID        => PORT_ID
        )
        port map(
            CLK               => CLK,
            RESET             => s_reset_reg,

            CS_GEN_ADDR_MODE  => s_db_gen_addr_mode_reg,
            CS_GEN_BL8_MODE   => s_db_gen_bl8_mode_reg,
            CS_GEN_RUN_MODE   => s_db_gen_run_mode_reg,
            CS_GEN_RUN        => s_db_gen_run_reg,
            CS_GEN_RW_SWITCH  => s_db_gen_rw_switch_reg,
            CS_GEN_WR_DEAD    => s_db_gen_wr_dead_reg,

            STAT_DATA_OK_INC  => s_gen_data_ok_inc,
            STAT_DATA_ERR_INC => s_gen_data_err_inc,

            WR_ADDR           => s_gen_wr_addr,
            WR_DATA           => s_gen_wr_data,
            WR_DATA_LAST      => s_gen_wr_data_last,
            WR_VALID          => s_gen_wr_valid,
            WR_READY          => s_gen_wr_ready,
            WR_RSP_ACK        => s_gen_wr_rsp_ack,
            WR_RSP_VALID      => s_gen_wr_rsp_valid,
            WR_RSP_READY      => s_gen_wr_rsp_ready,
            RD_ADDR           => s_gen_rd_addr,
            RD_ADDR_VALID     => s_gen_rd_addr_valid,
            RD_ADDR_READY     => s_gen_rd_addr_ready,
            RD_DATA           => s_gen_rd_data,
            RD_DATA_LAST      => s_gen_rd_data_last,
            RD_DATA_VALID     => s_gen_rd_data_valid,
            RD_DATA_READY     => s_gen_rd_data_ready
        );

        -- ---------------------------------------------------------------------
        --  TRAFFIC SWITCH
        -- ---------------------------------------------------------------------

        s_mid_wr_addr      <= s_gen_wr_addr when (s_db_gen_connect_reg = '1') else WR_ADDR;
        s_mid_wr_data      <= s_gen_wr_data when (s_db_gen_connect_reg = '1') else WR_DATA;
        s_mid_wr_data_last <= s_gen_wr_data_last when (s_db_gen_connect_reg = '1') else WR_DATA_LAST;
        s_mid_wr_valid     <= s_gen_wr_valid when (s_db_gen_connect_reg = '1') else WR_VALID;
        WR_READY           <= s_mid_wr_ready and not s_db_gen_connect_reg;
        s_gen_wr_ready     <= s_mid_wr_ready and s_db_gen_connect_reg;

        WR_RSP_ACK         <= s_mid_wr_rsp_ack;
        WR_RSP_VALID       <= s_mid_wr_rsp_valid and not s_db_gen_connect_reg;
        s_gen_wr_rsp_ack   <= s_mid_wr_rsp_ack;
        s_gen_wr_rsp_valid <= s_mid_wr_rsp_valid and s_db_gen_connect_reg;
        s_mid_wr_rsp_ready <= s_gen_wr_rsp_ready when (s_db_gen_connect_reg = '1') else WR_RSP_READY;

        s_mid_rd_addr       <= s_gen_rd_addr when (s_db_gen_connect_reg = '1') else RD_ADDR;
        s_mid_rd_addr_valid <= s_gen_rd_addr_valid when (s_db_gen_connect_reg = '1') else RD_ADDR_VALID;
        RD_ADDR_READY       <= s_mid_rd_addr_ready and not s_db_gen_connect_reg;
        s_gen_rd_addr_ready <= s_mid_rd_addr_ready and s_db_gen_connect_reg;

        RD_DATA             <= s_mid_rd_data;
        RD_DATA_LAST        <= s_mid_rd_data_last;
        RD_DATA_VALID       <= s_mid_rd_data_valid and not s_db_gen_connect_reg;
        s_gen_rd_data       <= s_mid_rd_data;
        s_gen_rd_data_last  <= s_mid_rd_data_last;
        s_gen_rd_data_valid <= s_mid_rd_data_valid and s_db_gen_connect_reg;
        s_mid_rd_data_ready <= s_gen_rd_data_ready when (s_db_gen_connect_reg = '1') else RD_DATA_READY;

        -- ---------------------------------------------------------------------
        --  TRAFFIC MONITOR
        -- ---------------------------------------------------------------------

        monitor_i : entity work.HBM_TESTER_MON
        generic map(
            CNT_WIDTH => CNT_WIDTH
        )
        port map(
            CLK              => CLK,
            RESET            => s_reset_reg,

            CS_MONITOR_TIME  => s_db_mon_time_reg,
            CS_MONITOR_DONE  => s_db_mon_done_reg,
            CS_MONITOR_RESET => s_db_mon_reset_reg,
            CS_COUNTER0_MODE => s_db_mon_cnt0_mode_reg,
            CS_COUNTER1_MODE => s_db_mon_cnt1_mode_reg,
            CS_COUNTER0_OUT  => s_db_stat_cnt0_reg,
            CS_COUNTER1_OUT  => s_db_stat_cnt1_reg,

            GEN_DATA_OK_INC  => s_gen_data_ok_inc,
            GEN_DATA_ERR_INC => s_gen_data_err_inc,

            WR_VALID         => s_mid_wr_valid,
            WR_READY         => s_mid_wr_ready,
            WR_RSP_VALID     => s_mid_wr_rsp_valid,
            WR_RSP_READY     => s_mid_wr_rsp_ready,
            RD_ADDR_VALID    => s_mid_rd_addr_valid,
            RD_ADDR_READY    => s_mid_rd_addr_ready,
            RD_DATA_VALID    => s_mid_rd_data_valid,
            RD_DATA_READY    => s_mid_rd_data_ready
        );

    end generate;

    -- =========================================================================
    -- MIDDLE PIPES
    -- =========================================================================

    -- WRITE ADDR/DATA SIGNALS #################################################

    s_mid_wr_pdata <= s_mid_wr_addr & s_mid_wr_data & s_mid_wr_data_last;

    wr_req_pipe_i : entity work.PIPE
    generic map(
        DATA_WIDTH => AXI_ADDR_WIDTH+USR_DATA_WIDTH+1,
        USE_OUTREG => True,
        FAKE_PIPE  => False,
        DEVICE     => DEVICE
    ) port map(
        CLK         => CLK,
        RESET       => s_reset_reg,
        IN_DATA     => s_mid_wr_pdata,
        IN_SRC_RDY  => s_mid_wr_valid,
        IN_DST_RDY  => s_mid_wr_ready,
        OUT_DATA    => s_hbm_wr_pdata,
        OUT_SRC_RDY => s_hbm_wr_valid,
        OUT_DST_RDY => s_hbm_wr_ready
    );

    s_hbm_wr_addr      <= s_hbm_wr_pdata(AXI_ADDR_WIDTH+USR_DATA_WIDTH+1-1 downto USR_DATA_WIDTH+1);
    s_hbm_wr_data      <= s_hbm_wr_pdata(USR_DATA_WIDTH+1-1 downto 1);
    s_hbm_wr_data_last <= s_hbm_wr_pdata(0);

    -- WRITE RESPONSE SIGNALS ##################################################

    wr_resp_pipe_i : entity work.PIPE
    generic map(
        DATA_WIDTH => 1,
        USE_OUTREG => True,
        FAKE_PIPE  => False,
        DEVICE     => DEVICE
    ) port map(
        CLK         => CLK,
        RESET       => s_reset_reg,
        IN_DATA(0)  => s_hbm_wr_rsp_ack,
        IN_SRC_RDY  => s_hbm_wr_rsp_valid,
        IN_DST_RDY  => s_hbm_wr_rsp_ready,
        OUT_DATA(0) => s_mid_wr_rsp_ack,
        OUT_SRC_RDY => s_mid_wr_rsp_valid,
        OUT_DST_RDY => s_mid_wr_rsp_ready
    );

    -- READ ADDR SIGNALS #######################################################

    rd_req_pipe_i : entity work.PIPE
    generic map(
        DATA_WIDTH => AXI_ADDR_WIDTH,
        USE_OUTREG => True,
        FAKE_PIPE  => False,
        DEVICE     => DEVICE
    ) port map(
        CLK         => CLK,
        RESET       => s_reset_reg,
        IN_DATA     => s_mid_rd_addr,
        IN_SRC_RDY  => s_mid_rd_addr_valid,
        IN_DST_RDY  => s_mid_rd_addr_ready,
        OUT_DATA    => s_hbm_rd_addr,
        OUT_SRC_RDY => s_hbm_rd_addr_valid,
        OUT_DST_RDY => s_hbm_rd_addr_ready
    );

    -- READ DATA SIGNALS #######################################################

    s_hbm_rd_pdata <= s_hbm_rd_data & s_hbm_rd_data_last;

    rd_resp_pipe_i : entity work.PIPE
    generic map(
        DATA_WIDTH => USR_DATA_WIDTH+1,
        USE_OUTREG => True,
        FAKE_PIPE  => False,
        DEVICE     => DEVICE
    ) port map(
        CLK         => CLK,
        RESET       => s_reset_reg,
        IN_DATA     => s_hbm_rd_pdata,
        IN_SRC_RDY  => s_hbm_rd_data_valid,
        IN_DST_RDY  => s_hbm_rd_data_ready,
        OUT_DATA    => s_mid_rd_pdata,
        OUT_SRC_RDY => s_mid_rd_data_valid,
        OUT_DST_RDY => s_mid_rd_data_ready
    );

    s_mid_rd_data      <= s_mid_rd_pdata(USR_DATA_WIDTH+1-1 downto 1);
    s_mid_rd_data_last <= s_mid_rd_pdata(0);

    -- =========================================================================
    -- HSI to AXI
    -- =========================================================================

    -- counter of word in burst
    hbm_wr_burst_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_reset_reg = '1') then
                s_hbm_wr_burst_cnt <= (others => '0');
            elsif (s_hbm_wr_valid = '1' and s_hbm_wr_ready = '1') then
                if (s_hbm_wr_burst_last = '1') then
                    s_hbm_wr_burst_cnt <= (others => '0');
                else
                    s_hbm_wr_burst_cnt <= s_hbm_wr_burst_cnt + 1;
                end if;
            end if;
        end if;
    end process;

    axi_awid_on_g : if USE_AXI_ID generate
        -- counter of write id
        hbm_wr_id_cnt_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_reset_reg = '1') then
                    s_hbm_wr_id_cnt <= (others => '0');
                elsif (s_hbm_wr_valid = '1' and s_hbm_wr_ready = '1' and s_hbm_wr_burst_last = '1') then
                    s_hbm_wr_id_cnt <= s_hbm_wr_id_cnt + 1;
                end if;
            end if;
        end process;
    end generate;

    axi_awid_off_g : if not USE_AXI_ID generate
        -- Each trancastion has same ID!
        s_hbm_wr_id_cnt <= (others => '0');
    end generate;

    s_hbm_wr_burst_first <= '1' when (s_hbm_wr_burst_cnt = "00") else '0';
    s_hbm_wr_burst_last  <= '1' when (s_hbm_wr_burst_cnt = s_hbm_wr_burst_cnt_max) else '0';

    -- HBM write address signals
    s_axi_awid    <= std_logic_vector(s_hbm_wr_id_cnt);
    s_axi_awaddr  <= s_hbm_wr_addr;
    s_axi_awlen   <= s_hbm_burst_size;
    s_axi_awsize  <= std_logic_vector(to_unsigned(5, AXI_SIZE_WIDTH)); -- MUST be 32B
    s_axi_awburst <= std_logic_vector(to_unsigned(1, AXI_BURST_WIDTH)); -- INCR mode
    s_axi_awprot  <= (others => '0');
    s_axi_awqos   <= (others => '0');
    s_axi_awuser  <= (others => '0');
    s_axi_awvalid <= s_hbm_wr_burst_first and s_hbm_wr_valid and s_axi_wready;

    -- HBM write data signals
    hbm_wr_data_g: if (USR_DATA_WIDTH = AXI_DATA_WIDTH) generate
        s_axi_wdata      <= s_hbm_wr_data;
        s_axi_wuser_data <= (others => '0');
    else generate
        s_axi_wdata      <= s_hbm_wr_data(AXI_DATA_WIDTH-1 downto 0);
        s_axi_wuser_data <= s_hbm_wr_data(USR_DATA_WIDTH-1 downto AXI_DATA_WIDTH);
    end generate;
    s_axi_wstrb      <= (others => '1');
    s_axi_wuser_strb <= (others => '1');
    s_axi_wlast      <= s_hbm_wr_data_last;
    s_axi_wvalid     <= s_hbm_wr_valid and s_axi_awready;

    -- HBM write signal
    s_hbm_wr_ready <= s_axi_awready and s_axi_wready;

    -- HBM write response signals
    s_hbm_wr_rsp_ack   <= nor s_axi_bresp;
    s_hbm_wr_rsp_valid <= s_axi_bvalid;
    s_axi_bready       <= s_hbm_wr_rsp_ready;

    axi_arid_on_g : if USE_AXI_ID generate
        -- counter of read id
        hbm_rd_id_cnt_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_reset_reg = '1') then
                    s_hbm_rd_id_cnt <= (others => '0');
                elsif (s_hbm_rd_addr_valid = '1' and s_hbm_rd_addr_ready = '1') then
                    s_hbm_rd_id_cnt <= s_hbm_rd_id_cnt + 1;
                end if;
            end if;
        end process;
    end generate;

    axi_arid_off_g : if not USE_AXI_ID generate
        -- Each trancastion has same ID!
        s_hbm_rd_id_cnt <= (others => '0');
    end generate;

    -- HBM read address signals
    s_axi_arid          <= std_logic_vector(s_hbm_rd_id_cnt);
    s_axi_araddr        <= s_hbm_rd_addr;
    s_axi_arlen         <= s_hbm_burst_size;
    s_axi_arsize        <= std_logic_vector(to_unsigned(5, AXI_SIZE_WIDTH)); -- MUST be 32B
    s_axi_arburst       <= std_logic_vector(to_unsigned(1, AXI_BURST_WIDTH)); -- INCR mode
    s_axi_arprot        <= (others => '0');
    s_axi_arqos         <= (others => '0');
    s_axi_aruser        <= (others => '0');
    s_axi_arvalid       <= s_hbm_rd_addr_valid;
    s_hbm_rd_addr_ready <= s_axi_arready;

    -- HBM read data signals
    hbm_rd_data_g: if (USR_DATA_WIDTH = AXI_DATA_WIDTH) generate
        s_hbm_rd_data <= s_axi_rdata;
    else generate
        s_hbm_rd_data(AXI_DATA_WIDTH-1 downto 0) <= s_axi_rdata;
        s_hbm_rd_data(USR_DATA_WIDTH-1 downto AXI_DATA_WIDTH) <= s_axi_ruser_data;
    end generate;
    s_hbm_rd_data_last  <= s_axi_rlast;
    s_hbm_rd_data_valid <= s_axi_rvalid;
    s_axi_rready        <= s_hbm_rd_data_ready;

    -- =========================================================================
    -- AXI connections (due to ILA probe - mark_debug)
    -- =========================================================================

    AXI_AWID      <= s_axi_awid;
    AXI_AWADDR    <= s_axi_awaddr;
    AXI_AWLEN     <= s_axi_awlen;
    AXI_AWSIZE    <= s_axi_awsize;
    AXI_AWBURST   <= s_axi_awburst;
    AXI_AWPROT    <= s_axi_awprot;
    AXI_AWQOS     <= s_axi_awqos;
    AXI_AWUSER    <= s_axi_awuser;
    AXI_AWVALID   <= s_axi_awvalid;
    s_axi_awready <= AXI_AWREADY;

    AXI_WDATA      <= s_axi_wdata;
    AXI_WSTRB      <= s_axi_wstrb;
    AXI_WUSER_DATA <= s_axi_wuser_data;
    AXI_WUSER_STRB <= s_axi_wuser_strb;
    AXI_WLAST      <= s_axi_wlast;
    AXI_WVALID     <= s_axi_wvalid;
    s_axi_wready   <= AXI_WREADY;

    s_axi_bid    <= AXI_BID;
    s_axi_bresp  <= AXI_BRESP;
    s_axi_bvalid <= AXI_BVALID;
    AXI_BREADY   <= s_axi_bready;

    AXI_ARID      <= s_axi_arid;
    AXI_ARADDR    <= s_axi_araddr;
    AXI_ARLEN     <= s_axi_arlen;
    AXI_ARSIZE    <= s_axi_arsize;
    AXI_ARBURST   <= s_axi_arburst;
    AXI_ARPROT    <= s_axi_arprot;
    AXI_ARQOS     <= s_axi_arqos;
    AXI_ARUSER    <= s_axi_aruser;
    AXI_ARVALID   <= s_axi_arvalid;
    s_axi_arready <= AXI_ARREADY;

    s_axi_rid           <= AXI_RID;
    s_axi_rdata         <= AXI_RDATA;
    s_axi_ruser_data    <= AXI_RUSER_DATA;
    s_axi_ruser_err_dbe <= AXI_RUSER_ERR_DBE;
    s_axi_rresp         <= AXI_RRESP;
    s_axi_rlast         <= AXI_RLAST;
    s_axi_rvalid        <= AXI_RVALID;
    AXI_RREADY          <= s_axi_rready;

end architecture;
