-- binder_tb.vhd: Testbench for FrameLink Binder
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.fl_binder_decl.all;
use WORK.mi32_pkg.all;
use work.fl_sim_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_INPUT_WIDTH  : integer := 64;
   constant TEST_INPUT_COUNT  : integer := 4;
   constant TEST_OUTPUT_WIDTH : integer := 64;
   constant BLOCK_SIZE        : integer := 512;
   constant LUT_MEMORY        : boolean := false;
   constant TEST_FRAME_PARTS  : integer := 2;
   constant TEST_QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := most_occupied;
   constant TEST_SIMPLE_BINDER : boolean := false;
   constant TEST_STUPID_BINDER : boolean := true;
   constant NFIFO2FIFO_BINDER : boolean := false;

   constant PACKET_BURSTS     : integer := 1000;

   constant clkper            : time := 10 ns;
   constant reset_time        : time := 10 * clkper;


    -- ------------------ Types declaration -----------------------------------
   type t_fl_ctrl_array is array (0 to (TEST_INPUT_COUNT-1)) of t_fl_ctrl;

   -- ------------------ Signals declaration ----------------------------------
   signal clk           : std_logic;
   signal reset         : std_logic;
   -- input FrameLink interface
   signal rx_sof_n      : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal rx_sop_n      : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal rx_eop_n      : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal rx_eof_n      : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal rx_src_rdy_n  : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal rx_dst_rdy_n  : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal rx_data       : std_logic_vector
                           (TEST_INPUT_COUNT*TEST_INPUT_WIDTH-1 downto 0);
   signal rx_rem        : std_logic_vector
                           (TEST_INPUT_COUNT*log2(TEST_INPUT_WIDTH/8)-1
                           downto 0);
   -- output FrameLink interface
   signal tx_sof_n      : std_logic;
   signal tx_sop_n      : std_logic;
   signal tx_eop_n      : std_logic;
   signal tx_eof_n      : std_logic;
   signal tx_src_rdy_n  : std_logic;
   signal tx_dst_rdy_n  : std_logic;
   signal tx_data       : std_logic_vector(TEST_OUTPUT_WIDTH-1 downto 0);
   signal tx_rem        : std_logic_vector(log2(TEST_OUTPUT_WIDTH/8)-1
                                                                     downto 0);

   -- auxiliary signals for packet generator
   signal tst_sof_n     : std_logic;
   signal tst_sop_n     : std_logic;
   signal tst_eop_n     : std_logic;
   signal tst_eof_n     : std_logic;
   signal tst_src_rdy_n : std_logic;
   signal tst_dst_rdy_n : std_logic;
   signal tst_data      : std_logic_vector(TEST_INPUT_WIDTH-1 downto 0);
   signal tst_rem       : std_logic_vector(log2(TEST_INPUT_WIDTH/8)-1
                                                                     downto 0);

   -- aliases to simplify testing
   alias rx_sof_n_0     : std_logic is rx_sof_n(0);
   alias rx_sof_n_1     : std_logic is rx_sof_n(1);
   alias rx_sop_n_0     : std_logic is rx_sop_n(0);
   alias rx_sop_n_1     : std_logic is rx_sop_n(1);
   alias rx_eop_n_0     : std_logic is rx_eop_n(0);
   alias rx_eop_n_1     : std_logic is rx_eop_n(1);
   alias rx_eof_n_0     : std_logic is rx_eof_n(0);
   alias rx_eof_n_1     : std_logic is rx_eof_n(1);
   alias rx_src_rdy_n_0 : std_logic is rx_src_rdy_n(0);
   alias rx_src_rdy_n_1 : std_logic is rx_src_rdy_n(1);
   alias rx_dst_rdy_n_0 : std_logic is rx_dst_rdy_n(0);
   alias rx_dst_rdy_n_1 : std_logic is rx_dst_rdy_n(1);
   alias rx_data_0      : std_logic_vector(TEST_INPUT_WIDTH-1 downto 0)
                          is rx_data(TEST_INPUT_WIDTH-1 downto 0);
   alias rx_data_1      : std_logic_vector(TEST_INPUT_WIDTH-1 downto 0)
                          is rx_data(2*TEST_INPUT_WIDTH-1 downto
                          TEST_INPUT_WIDTH);
   alias rx_rem_0       : std_logic_vector(log2(TEST_INPUT_WIDTH/8)-1 downto 0)
                          is rx_rem(log2(TEST_INPUT_WIDTH/8)-1 downto 0);
   alias rx_rem_1       : std_logic_vector(log2(TEST_INPUT_WIDTH/8)-1 downto 0)
                          is rx_rem(2*log2(TEST_INPUT_WIDTH/8)-1 downto
                          log2(TEST_INPUT_WIDTH/8));

   -- FL Sim signals
   signal filename         : t_fl_ctrl_array;
   signal fl_sim_strobe    : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);
   signal fl_sim_busy      : std_logic_vector(TEST_INPUT_COUNT-1 downto 0);

   -- watcher signals
   signal frame_err        : std_logic;
   signal mi32_watch       : t_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   mi32_watch.rd     <= '0';
   mi32_watch.wr     <= '0';
   mi32_watch.addr   <= (others => '0');

   uut : entity work.FL_BINDER
      generic map(
         INPUT_WIDTH    => TEST_INPUT_WIDTH,
         INPUT_COUNT    => TEST_INPUT_COUNT,
         OUTPUT_WIDTH   => TEST_OUTPUT_WIDTH,
         FRAME_PARTS    => TEST_FRAME_PARTS,
         QUEUE_CHOOSING => TEST_QUEUE_CHOOSING,
         SIMPLE_BINDER  => TEST_SIMPLE_BINDER,
         STUPID_BINDER  => TEST_STUPID_BINDER
       --  NFIFO2FIFO_BINDER => NFIFO2FIFO_BINDER
      )
      port map(
         CLK            => clk,
         RESET          => reset,
         -- input interface
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
         RX_DATA        => rx_data,
         RX_REM         => rx_rem,
         -- output interace
         TX_SOF_N       => tx_sof_n,
         TX_SOP_N       => tx_sop_n,
         TX_EOP_N       => tx_eop_n,
         TX_EOF_N       => tx_eof_n,
         TX_SRC_RDY_N   => tx_src_rdy_n,
         TX_DST_RDY_N   => tx_dst_rdy_n,
         TX_DATA        => tx_data,
         TX_REM         => tx_rem
      );


   FL_WATCH_I : entity work.FL_WATCH
      generic map(
         INTERFACES     => 1,
         CNTR_WIDTH     => 32,
         PIPELINE_LEN   => 1,
         GUARD          => true,
         HEADER         => true,
         FOOTER         => false
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         SOF_N(0)       => tx_sof_n,
         EOF_N(0)       => tx_eof_n,
         SOP_N(0)       => tx_sop_n,
         EOP_N(0)       => tx_eop_n,
         DST_RDY_N(0)   => tx_dst_rdy_n,
         SRC_RDY_N(0)   => tx_src_rdy_n,

         FRAME_ERR(0)   => frame_err,
         MI             => mi32_watch
      );

   -- -------------------------------------------------------------------------
   --                    FL Simulation Components
   -- -------------------------------------------------------------------------
   GEN_FLSIM: for i in 0 to TEST_INPUT_COUNT-1 generate
      fl_sim: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => TEST_INPUT_WIDTH,
         RX_LOG_FILE    => "",
         TX_LOG_FILE    => "",
         FRAME_PARTS    => TEST_FRAME_PARTS
      )
      port map (
         -- Common interface
         FL_RESET       => reset,
         FL_CLK         => clk,
         -- Frame link Interface
         RX_DATA        => (others => '0'),
         RX_REM         => (others => '0'),
         RX_SOF_N       => '1',
         RX_EOF_N       => '1',
         RX_SOP_N       => '1',
         RX_EOP_N       => '1',
         RX_SRC_RDY_N   => '1', -- Source isn't ready
         RX_DST_RDY_N   => open,
         TX_DATA        => rx_data((i+1)*TEST_INPUT_WIDTH-1 downto i*TEST_INPUT_WIDTH),
         TX_REM         => rx_rem((i+1)*log2(TEST_INPUT_WIDTH/8)-1 downto i*log2(TEST_INPUT_WIDTH/8)),
         TX_SOF_N       => rx_sof_n(i),
         TX_EOF_N       => rx_eof_n(i),
         TX_SOP_N       => rx_sop_n(i),
         TX_EOP_N       => rx_eop_n(i),
         TX_SRC_RDY_N   => rx_src_rdy_n(i),
         TX_DST_RDY_N   => rx_dst_rdy_n(i),
         -- FL SIM interface
         CTRL           => filename(i),
         STROBE         => fl_sim_strobe(i),
         BUSY           => fl_sim_busy(i)
      );
   end generate;

   -- clock generator ---------------------------------------------------------
   clk_gen : process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   -- Reset generation --------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;

   dst_rdy_gen : process
   begin
      --wait until clk'event and clk='1';
      tx_dst_rdy_n   <= '0';
      wait;
      --wait until clk'event and clk='1';
      --tx_dst_rdy_n   <= '1';
   end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
   procedure send_packet(ifc : in integer; ctrl : in t_fl_ctrl) is
   begin
      wait until (clk'event and clk='1' and fl_sim_busy(ifc) = '0');
      filename(ifc) <= ctrl;
      fl_sim_strobe(ifc) <= '1';
      wait until (clk'event and clk='1');
      fl_sim_strobe(ifc) <= '0';
   end send_packet;
begin

   wait for reset_time;

   -- generate first packet
   for i in 0 to PACKET_BURSTS-1 loop
      send_packet(0, fl_send32("packet1.txt"));
      send_packet(1, fl_send32("packet2.txt"));
      send_packet(3, fl_send32("packet3.txt"));
      send_packet(3, fl_send32("packet1.txt"));
      send_packet(0, fl_send32("packet2.txt"));
      send_packet(1, fl_send32("packet3.txt"));
      send_packet(2, fl_send32("packet3.txt"));
      send_packet(3, fl_send32("packet2.txt"));
      send_packet(0, fl_send32("packet2.txt"));
      send_packet(1, fl_send32("packet3.txt"));
      send_packet(2, fl_send32("packet2.txt"));
      send_packet(3, fl_send32("packet3.txt"));
      send_packet(0, fl_send32("packet1.txt"));
      send_packet(1, fl_send32("packet2.txt"));
      send_packet(2, fl_send32("packet3.txt"));
      send_packet(3, fl_send32("packet1.txt"));
      send_packet(0, fl_send32("packet3.txt"));
      send_packet(1, fl_send32("packet1.txt"));
      send_packet(2, fl_send32("packet1.txt"));
      send_packet(3, fl_send32("packet2.txt"));
      send_packet(0, fl_send32("packet3.txt"));
      send_packet(1, fl_send32("packet3.txt"));
      send_packet(2, fl_send32("packet1.txt"));
      send_packet(3, fl_send32("packet3.txt"));
   end loop;

   wait;
end process;

end architecture behavioral;
