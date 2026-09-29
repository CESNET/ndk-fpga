-- axi_pipe.vhd: AXI4 Bus pipeline
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity AXI_PIPE is
    generic (
        -- =========================================================================
        -- AXI4 parameters
        -- =========================================================================

        -- Width of the xDATA signals
        DATA_WIDTH     : natural := 512;
        -- Width of the xADDR signals
        ADDR_WIDTH     : natural := 32;
        -- Width of the xID signals
        ID_WIDTH       : natural := 4;
        -- Width of the xLEN signals (8 for AXI4, 4 for AXI3)
        LEN_WIDTH      : natural := 8;
        -- Width of the xSIZE signals
        SIZE_WIDTH     : natural := 3;
        -- Width of the xBURST signals
        BURST_WIDTH    : natural := 2;
        -- Width of the xRESP signals
        RESP_WIDTH     : natural := 2;

        -- =============================
        -- Others
        -- =============================

        -- Wires only (to disable the pipe easily), affects all channels
        FAKE_PIPE      : boolean := false;

        -- "SHREG" or "REG"
        PIPE_TYPE      : string  := "REG";
        DEVICE         : string  := "AGILEX"
    );
    port (
        -- =============================
        -- Clock and Reset
        -- =============================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =========================================================
        -- AXI4 slave interface
        -- =========================================================

        -- Write Address Channel
        RX_AXI_AWID    : in  std_logic_vector(ID_WIDTH-1 downto 0);
        RX_AXI_AWADDR  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        RX_AXI_AWLEN   : in  std_logic_vector(LEN_WIDTH-1 downto 0);
        RX_AXI_AWSIZE  : in  std_logic_vector(SIZE_WIDTH-1 downto 0);
        RX_AXI_AWBURST : in  std_logic_vector(BURST_WIDTH-1 downto 0);
        RX_AXI_AWVALID : in  std_logic;
        RX_AXI_AWREADY : out std_logic;

        -- Write Data Channel
        RX_AXI_WDATA   : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_AXI_WSTRB   : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
        RX_AXI_WLAST   : in  std_logic;
        RX_AXI_WVALID  : in  std_logic;
        RX_AXI_WREADY  : out std_logic;

        -- Write Response Channel
        RX_AXI_BREADY  : in  std_logic;
        RX_AXI_BID     : out std_logic_vector(ID_WIDTH-1 downto 0);
        RX_AXI_BRESP   : out std_logic_vector(RESP_WIDTH-1 downto 0);
        RX_AXI_BVALID  : out std_logic;

        -- Read Address Channel
        RX_AXI_ARID    : in  std_logic_vector(ID_WIDTH-1 downto 0);
        RX_AXI_ARADDR  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        RX_AXI_ARLEN   : in  std_logic_vector(LEN_WIDTH-1 downto 0);
        RX_AXI_ARSIZE  : in  std_logic_vector(SIZE_WIDTH-1 downto 0);
        RX_AXI_ARBURST : in  std_logic_vector(BURST_WIDTH-1 downto 0);
        RX_AXI_ARVALID : in  std_logic;
        RX_AXI_ARREADY : out std_logic;

        -- Read Data Channel
        RX_AXI_RREADY  : in  std_logic;
        RX_AXI_RVALID  : out std_logic;
        RX_AXI_RLAST   : out std_logic;
        RX_AXI_RRESP   : out std_logic_vector(RESP_WIDTH-1 downto 0);
        RX_AXI_RID     : out std_logic_vector(ID_WIDTH-1 downto 0);
        RX_AXI_RDATA   : out std_logic_vector(DATA_WIDTH-1 downto 0);

        -- =========================================================
        -- AXI4 master interface
        -- =========================================================

        -- Write Address Channel
        TX_AXI_AWID    : out std_logic_vector(ID_WIDTH-1 downto 0);
        TX_AXI_AWADDR  : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        TX_AXI_AWLEN   : out std_logic_vector(LEN_WIDTH-1 downto 0);
        TX_AXI_AWSIZE  : out std_logic_vector(SIZE_WIDTH-1 downto 0);
        TX_AXI_AWBURST : out std_logic_vector(BURST_WIDTH-1 downto 0);
        TX_AXI_AWVALID : out std_logic;
        TX_AXI_AWREADY : in  std_logic;

        -- Write Data Channel
        TX_AXI_WDATA   : out std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_AXI_WSTRB   : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
        TX_AXI_WLAST   : out std_logic;
        TX_AXI_WVALID  : out std_logic;
        TX_AXI_WREADY  : in  std_logic;

        -- Write Response Channel
        TX_AXI_BREADY  : out std_logic;
        TX_AXI_BID     : in  std_logic_vector(ID_WIDTH-1 downto 0);
        TX_AXI_BRESP   : in  std_logic_vector(RESP_WIDTH-1 downto 0);
        TX_AXI_BVALID  : in  std_logic;

        -- Read Address Channel
        TX_AXI_ARID    : out std_logic_vector(ID_WIDTH-1 downto 0);
        TX_AXI_ARADDR  : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        TX_AXI_ARLEN   : out std_logic_vector(LEN_WIDTH-1 downto 0);
        TX_AXI_ARSIZE  : out std_logic_vector(SIZE_WIDTH-1 downto 0);
        TX_AXI_ARBURST : out std_logic_vector(BURST_WIDTH-1 downto 0);
        TX_AXI_ARVALID : out std_logic;
        TX_AXI_ARREADY : in  std_logic;

        -- Read Data Channel
        TX_AXI_RREADY  : out std_logic;
        TX_AXI_RVALID  : in  std_logic;
        TX_AXI_RLAST   : in  std_logic;
        TX_AXI_RRESP   : in  std_logic_vector(RESP_WIDTH-1 downto 0);
        TX_AXI_RID     : in  std_logic_vector(ID_WIDTH-1 downto 0);
        TX_AXI_RDATA   : in  std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;



architecture ARCH of AXI_PIPE is

    constant LAST_WIDTH   : natural := 1;
    constant STRB_WIDTH   : natural := DATA_WIDTH/8;

    -- =========================================================================
    -- Address channel word layout (shared by AW and AR)
    -- =========================================================================

    constant A_PIPE_WIDTH : natural := ID_WIDTH + ADDR_WIDTH + LEN_WIDTH + SIZE_WIDTH + BURST_WIDTH;

    subtype  A_PIPE_BURST is natural range BURST_WIDTH-1                                              downto 0;
    subtype  A_PIPE_SIZE  is natural range BURST_WIDTH + SIZE_WIDTH-1                                 downto BURST_WIDTH;
    subtype  A_PIPE_LEN   is natural range BURST_WIDTH + SIZE_WIDTH + LEN_WIDTH-1                     downto BURST_WIDTH + SIZE_WIDTH;
    subtype  A_PIPE_ADDR  is natural range BURST_WIDTH + SIZE_WIDTH + LEN_WIDTH + ADDR_WIDTH-1        downto BURST_WIDTH + SIZE_WIDTH + LEN_WIDTH;
    subtype  A_PIPE_ID    is natural range A_PIPE_WIDTH-1                                             downto BURST_WIDTH + SIZE_WIDTH + LEN_WIDTH + ADDR_WIDTH;

    -- =========================================================================
    -- Write data channel word layout
    -- =========================================================================

    constant W_PIPE_WIDTH : natural := LAST_WIDTH + STRB_WIDTH + DATA_WIDTH;

    constant W_PIPE_LAST  : natural := 0;
    subtype  W_PIPE_STRB  is natural range LAST_WIDTH + STRB_WIDTH-1                                  downto LAST_WIDTH;
    subtype  W_PIPE_DATA  is natural range W_PIPE_WIDTH-1                                             downto LAST_WIDTH + STRB_WIDTH;

    -- =========================================================================
    -- Write response channel word layout
    -- =========================================================================

    constant B_PIPE_WIDTH : natural := RESP_WIDTH + ID_WIDTH;

    subtype  B_PIPE_RESP  is natural range RESP_WIDTH-1                                               downto 0;
    subtype  B_PIPE_ID    is natural range B_PIPE_WIDTH-1                                             downto RESP_WIDTH;

    -- =========================================================================
    -- Read data channel word layout
    -- =========================================================================

    constant R_PIPE_WIDTH : natural := LAST_WIDTH + RESP_WIDTH + ID_WIDTH + DATA_WIDTH;

    constant R_PIPE_LAST  : natural := 0;
    subtype  R_PIPE_RESP  is natural range LAST_WIDTH + RESP_WIDTH-1                                  downto LAST_WIDTH;
    subtype  R_PIPE_ID    is natural range LAST_WIDTH + RESP_WIDTH + ID_WIDTH-1                       downto LAST_WIDTH + RESP_WIDTH;
    subtype  R_PIPE_DATA  is natural range R_PIPE_WIDTH-1                                             downto LAST_WIDTH + RESP_WIDTH + ID_WIDTH;

    -- =========================================================================
    -- Pipe interconnect signals
    -- =========================================================================

    signal aw_pipe_in     : std_logic_vector(A_PIPE_WIDTH-1 downto 0);
    signal aw_pipe_out    : std_logic_vector(A_PIPE_WIDTH-1 downto 0);

    signal w_pipe_in      : std_logic_vector(W_PIPE_WIDTH-1 downto 0);
    signal w_pipe_out     : std_logic_vector(W_PIPE_WIDTH-1 downto 0);

    signal b_pipe_in      : std_logic_vector(B_PIPE_WIDTH-1 downto 0);
    signal b_pipe_out     : std_logic_vector(B_PIPE_WIDTH-1 downto 0);

    signal ar_pipe_in     : std_logic_vector(A_PIPE_WIDTH-1 downto 0);
    signal ar_pipe_out    : std_logic_vector(A_PIPE_WIDTH-1 downto 0);

    signal r_pipe_in      : std_logic_vector(R_PIPE_WIDTH-1 downto 0);
    signal r_pipe_out     : std_logic_vector(R_PIPE_WIDTH-1 downto 0);

begin

    -- =========================================================================
    -- WRITE ADDRESS CHANNEL (RX -> TX)
    -- =========================================================================

    aw_pipe_in(A_PIPE_BURST) <= RX_AXI_AWBURST;
    aw_pipe_in(A_PIPE_SIZE)  <= RX_AXI_AWSIZE;
    aw_pipe_in(A_PIPE_LEN)   <= RX_AXI_AWLEN;
    aw_pipe_in(A_PIPE_ADDR)  <= RX_AXI_AWADDR;
    aw_pipe_in(A_PIPE_ID)    <= RX_AXI_AWID;

    aw_pipe_i : entity work.PIPE
    generic map (
        DATA_WIDTH      => A_PIPE_WIDTH,
        USE_OUTREG      => not FAKE_PIPE,
        FAKE_PIPE       => FAKE_PIPE,
        PIPE_TYPE       => PIPE_TYPE,
        RESET_BY_INIT   => false,
        DEVICE          => DEVICE
    ) port map (
        CLK          => CLK,
        RESET        => RESET,
        IN_DATA      => aw_pipe_in,
        IN_SRC_RDY   => RX_AXI_AWVALID,
        IN_DST_RDY   => RX_AXI_AWREADY,
        OUT_DATA     => aw_pipe_out,
        OUT_SRC_RDY  => TX_AXI_AWVALID,
        OUT_DST_RDY  => TX_AXI_AWREADY
    );

    TX_AXI_AWBURST <= aw_pipe_out(A_PIPE_BURST);
    TX_AXI_AWSIZE  <= aw_pipe_out(A_PIPE_SIZE);
    TX_AXI_AWLEN   <= aw_pipe_out(A_PIPE_LEN);
    TX_AXI_AWADDR  <= aw_pipe_out(A_PIPE_ADDR);
    TX_AXI_AWID    <= aw_pipe_out(A_PIPE_ID);

    -- =========================================================================
    -- WRITE DATA CHANNEL (RX -> TX)
    -- =========================================================================

    w_pipe_in(W_PIPE_LAST) <= RX_AXI_WLAST;
    w_pipe_in(W_PIPE_STRB) <= RX_AXI_WSTRB;
    w_pipe_in(W_PIPE_DATA) <= RX_AXI_WDATA;

    w_pipe_i : entity work.PIPE
    generic map (
        DATA_WIDTH      => W_PIPE_WIDTH,
        USE_OUTREG      => not FAKE_PIPE,
        FAKE_PIPE       => FAKE_PIPE,
        PIPE_TYPE       => PIPE_TYPE,
        RESET_BY_INIT   => false,
        DEVICE          => DEVICE
    ) port map (
        CLK          => CLK,
        RESET        => RESET,
        IN_DATA      => w_pipe_in,
        IN_SRC_RDY   => RX_AXI_WVALID,
        IN_DST_RDY   => RX_AXI_WREADY,
        OUT_DATA     => w_pipe_out,
        OUT_SRC_RDY  => TX_AXI_WVALID,
        OUT_DST_RDY  => TX_AXI_WREADY
    );

    TX_AXI_WLAST <= w_pipe_out(W_PIPE_LAST);
    TX_AXI_WSTRB <= w_pipe_out(W_PIPE_STRB);
    TX_AXI_WDATA <= w_pipe_out(W_PIPE_DATA);

    -- =========================================================================
    -- WRITE RESPONSE CHANNEL (TX -> RX)
    -- =========================================================================

    b_pipe_in(B_PIPE_RESP) <= TX_AXI_BRESP;
    b_pipe_in(B_PIPE_ID)   <= TX_AXI_BID;

    b_pipe_i : entity work.PIPE
    generic map (
        DATA_WIDTH      => B_PIPE_WIDTH,
        USE_OUTREG      => not FAKE_PIPE,
        FAKE_PIPE       => FAKE_PIPE,
        PIPE_TYPE       => PIPE_TYPE,
        RESET_BY_INIT   => false,
        DEVICE          => DEVICE
    ) port map (
        CLK          => CLK,
        RESET        => RESET,
        IN_DATA      => b_pipe_in,
        IN_SRC_RDY   => TX_AXI_BVALID,
        IN_DST_RDY   => TX_AXI_BREADY,
        OUT_DATA     => b_pipe_out,
        OUT_SRC_RDY  => RX_AXI_BVALID,
        OUT_DST_RDY  => RX_AXI_BREADY
    );

    RX_AXI_BRESP <= b_pipe_out(B_PIPE_RESP);
    RX_AXI_BID   <= b_pipe_out(B_PIPE_ID);

    -- =========================================================================
    -- READ ADDRESS CHANNEL (RX -> TX)
    -- =========================================================================

    ar_pipe_in(A_PIPE_BURST) <= RX_AXI_ARBURST;
    ar_pipe_in(A_PIPE_SIZE)  <= RX_AXI_ARSIZE;
    ar_pipe_in(A_PIPE_LEN)   <= RX_AXI_ARLEN;
    ar_pipe_in(A_PIPE_ADDR)  <= RX_AXI_ARADDR;
    ar_pipe_in(A_PIPE_ID)    <= RX_AXI_ARID;

    ar_pipe_i : entity work.PIPE
    generic map (
        DATA_WIDTH      => A_PIPE_WIDTH,
        USE_OUTREG      => not FAKE_PIPE,
        FAKE_PIPE       => FAKE_PIPE,
        PIPE_TYPE       => PIPE_TYPE,
        RESET_BY_INIT   => false,
        DEVICE          => DEVICE
    ) port map (
        CLK          => CLK,
        RESET        => RESET,
        IN_DATA      => ar_pipe_in,
        IN_SRC_RDY   => RX_AXI_ARVALID,
        IN_DST_RDY   => RX_AXI_ARREADY,
        OUT_DATA     => ar_pipe_out,
        OUT_SRC_RDY  => TX_AXI_ARVALID,
        OUT_DST_RDY  => TX_AXI_ARREADY
    );

    TX_AXI_ARBURST <= ar_pipe_out(A_PIPE_BURST);
    TX_AXI_ARSIZE  <= ar_pipe_out(A_PIPE_SIZE);
    TX_AXI_ARLEN   <= ar_pipe_out(A_PIPE_LEN);
    TX_AXI_ARADDR  <= ar_pipe_out(A_PIPE_ADDR);
    TX_AXI_ARID    <= ar_pipe_out(A_PIPE_ID);

    -- =========================================================================
    -- READ DATA CHANNEL (TX -> RX)
    -- =========================================================================

    r_pipe_in(R_PIPE_LAST) <= TX_AXI_RLAST;
    r_pipe_in(R_PIPE_RESP) <= TX_AXI_RRESP;
    r_pipe_in(R_PIPE_ID)   <= TX_AXI_RID;
    r_pipe_in(R_PIPE_DATA) <= TX_AXI_RDATA;

    r_pipe_i : entity work.PIPE
    generic map (
        DATA_WIDTH      => R_PIPE_WIDTH,
        USE_OUTREG      => not FAKE_PIPE,
        FAKE_PIPE       => FAKE_PIPE,
        PIPE_TYPE       => PIPE_TYPE,
        RESET_BY_INIT   => false,
        DEVICE          => DEVICE
    ) port map (
        CLK          => CLK,
        RESET        => RESET,
        IN_DATA      => r_pipe_in,
        IN_SRC_RDY   => TX_AXI_RVALID,
        IN_DST_RDY   => TX_AXI_RREADY,
        OUT_DATA     => r_pipe_out,
        OUT_SRC_RDY  => RX_AXI_RVALID,
        OUT_DST_RDY  => RX_AXI_RREADY
    );

    RX_AXI_RLAST <= r_pipe_out(R_PIPE_LAST);
    RX_AXI_RRESP <= r_pipe_out(R_PIPE_RESP);
    RX_AXI_RID   <= r_pipe_out(R_PIPE_ID);
    RX_AXI_RDATA <= r_pipe_out(R_PIPE_DATA);

end architecture;
