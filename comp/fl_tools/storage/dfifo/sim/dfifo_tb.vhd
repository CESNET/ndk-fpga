-- dfifo_tb.vhd: FL_DFIFO testbench
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Novotnak <xnovot87@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

-- library containing log2 and min functions
use work.math_pack.all;


LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

library work;

use work.math_pack.all;
-- library with t_flxx data types
use work.fl_pkg.all;

-- Framelink simulation
use work.fl_sim_oper.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_PKG.all;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

-- simulation constants
constant CLKPER      : time      := 10 ns;

constant CTRL_DATA_WIDTH : integer := 1;
constant DATA_WIDTH  : integer   := 128;
constant ITEMS       : integer   := 32;
constant PARTS       : integer   := 1;

constant FL_SEND_FILE  : string := "./tests/fl_input.txt";
constant TX_RDY_DRIVER : RDYSignalDriver := RND;

constant FL_RECV_FILE  : string := "./tests/fl_out.txt";
constant RX_RDY_DRIVER : RDYSignalDriver := RND;

constant RESET_TIME : time := 100 ns;


-- signals from/to tested unit
signal CLK           : std_logic;
signal RESET         : std_logic;

signal rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_rem        : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
signal rx_src_rdy_n  : std_logic;
signal rx_dst_rdy_n  : std_logic;
signal rx_sop_n      : std_logic;
signal rx_eop_n      : std_logic;
signal rx_sof_n      : std_logic;
signal rx_eof_n      : std_logic;

signal tx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_rem        : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
signal tx_src_rdy_n  : std_logic;
signal tx_dst_rdy_n  : std_logic;
signal tx_sop_n      : std_logic;
signal tx_eop_n      : std_logic;
signal tx_sof_n      : std_logic;
signal tx_eof_n      : std_logic;
signal discard       : std_logic;

   signal cnt_discard : std_logic_vector(1 downto 0);
   signal cnt_discard_ce : std_logic;
   signal cnt_discard_in : std_logic_vector(2 downto 0);
   signal cnt_discard_in_ce : std_logic;
   signal cnt_discard_in_ld : std_logic;

begin

-- Unit under test
   fl_dfifo: entity work.fl_dfifo
   generic map(
      ITEMS       => ITEMS,
      PARTS       => PARTS,
      DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,

      -- write interface
      RX_DATA        => rx_data,
      RX_REM         => rx_rem,
      RX_SRC_RDY_N   => rx_src_rdy_n,
      RX_DST_RDY_N   => rx_dst_rdy_n,
      RX_SOP_N       => rx_sop_n,
      RX_EOP_N       => rx_eop_n,
      RX_SOF_N       => rx_sof_n,
      RX_EOF_N       => rx_eof_n,
      DISCARD        => discard,

      -- read interface
      TX_DATA        => tx_data,
      TX_REM         => tx_rem,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => tx_dst_rdy_n,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n
   );

   -- Framelink transmitter
   FL_TRANSMMITER : entity work.FL_BFM
      generic map(
         DATA_WIDTH => DATA_WIDTH,
         FL_BFM_ID  => 0
      )
      port map(
         -- common interface
         CLK   => CLK,
         RESET => RESET,

         -- framelink bus
         TX_DATA      => rx_data,
         TX_REM       => rx_rem,
         TX_SOF_N     => rx_sof_n,
         TX_SOP_N     => rx_sop_n,
         TX_EOP_N     => rx_eop_n,
         TX_EOF_N     => rx_eof_n,
         TX_SRC_RDY_N => rx_src_rdy_n,
         TX_DST_RDY_N => rx_dst_rdy_n
      );

   FL_RECEIVER : entity work.MONITOR
      generic map(
         RX_TX_DATA_WIDTH => DATA_WIDTH,
         FILE_NAME        => FL_RECV_FILE,
         FRAME_PARTS      => PARTS,
         RDY_DRIVER       => RX_RDY_DRIVER
      )
      port map(
         FL_CLK       => CLK,
         FL_RESET     => RESET,

         RX_DATA      => tx_data,
         RX_REM       => tx_rem,
         RX_SOF_N     => tx_sof_n,
         RX_SOP_N     => tx_sop_n,
         RX_EOF_N     => tx_eof_n,
         RX_EOP_N     => tx_eop_n,
         RX_SRC_RDY_N => tx_src_rdy_n,
         RX_DST_RDY_N => tx_dst_rdy_n
      );

-- Clock generation
   local_clock: process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process;

   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process
      variable i,j: integer;
      variable ctrl: std_logic_vector(CTRL_DATA_WIDTH-1 downto 0);
   begin
      wait until RESET = '0';
      SetSeed(123456);
      SendWriteFile(FL_SEND_FILE, tx_rdy_driver, flCmd_0, 0);
      wait;
   end process;

   -- cnt_discard counter
   cnt_discardp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_discard <= (others => '0');
         elsif (cnt_discard_ce = '1') then
               cnt_discard <= cnt_discard + "1";
         end if;
      end if;
   end process;

   cnt_discard_ce <= not (rx_src_rdy_n or rx_dst_rdy_n or rx_eof_n);

   -- cnt_discard_in counter
   cnt_discard_inp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_discard_in <= (others => '0');
         elsif (cnt_discard_in_ce = '1') then
            if (cnt_discard_in_ld = '1') then
               cnt_discard_in <= (others => '0');
            else
               cnt_discard_in <= cnt_discard_in + 1;
            end if;
         end if;
      end if;
   end process;

   cnt_discard_in_ce <= not (rx_src_rdy_n or rx_dst_rdy_n);
   cnt_discard_in_ld <= not rx_eof_n;

   discard <= '1' when ((cnt_discard="11") and (conv_integer(cnt_discard_in)=0)) else
              '0';

end;
