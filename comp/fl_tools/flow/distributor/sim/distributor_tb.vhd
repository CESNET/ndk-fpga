--
-- disp_tb.vhd: Component testbench.
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor xpusvi00@stud.fit.vutbr.cz
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

-- math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DATA_WIDTH     : integer := 64;
	constant INTERFACES_COUNT : integer := 4;
	constant DEFAULT_INTERFACE : integer := 1;
	constant INUM_OFFSET : integer := 0;

   constant clkper      : time      := 10 ns;
   constant INIT_TIME   : time      := 4*clkper + 10*clkper;
   constant RESET_TIME  : time      := 3*clkper;

   -- Packet parameters
   signal clk      : std_logic;
   signal reset    : std_logic;

   signal rx_data      : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal rx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_src_rdy_n : std_logic;
   signal rx_dst_rdy_n : std_logic;
   signal rx_sop_n     : std_logic;
   signal rx_eop_n     : std_logic;
   signal rx_sof_n     : std_logic;
   signal rx_eof_n     : std_logic;

   signal tx_data     : std_logic_vector(INTERFACES_COUNT*DATA_WIDTH - 1 downto 0);
   signal tx_rem      : std_logic_vector(INTERFACES_COUNT*log2(DATA_WIDTH/8) - 1 downto 0);
   signal tx_src_rdy_n: std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_dst_rdy_n: std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_sop_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_eop_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_sof_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_eof_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   UUT: entity work.fl_distributor
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         INTERFACES_COUNT  => INTERFACES_COUNT,
         DEFAULT_INTERFACE => DEFAULT_INTERFACE,
			INUM_OFFSET => INUM_OFFSET,
			PARTS => 1,
         MASK => false
      )
      port map (
         CLK          => CLK,
         RESET        => RESET,

         -- Write interface
         RX_DATA      => rx_data,
         RX_REM       => rx_rem,
         RX_SRC_RDY_N => rx_src_rdy_n,
         RX_DST_RDY_N => rx_dst_rdy_n,
         RX_SOP_N     => rx_sop_n,
         RX_EOP_N     => rx_eop_n,
         RX_SOF_N     => rx_sof_n,
         RX_EOF_N     => rx_eof_n,

         -- Read interface
         TX_DATA     => tx_data,
         TX_REM      => tx_rem,
         TX_SRC_RDY_N=> tx_src_rdy_n,
         TX_DST_RDY_N=> tx_dst_rdy_n,
         TX_SOP_N    => tx_sop_n,
         TX_EOP_N    => tx_eop_n,
         TX_SOF_N    => tx_sof_n,
         TX_EOF_N    => tx_eof_n
		);

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;


-- Data input generator -------------------------------
digen: process
begin
   wait for clkper;
   reset <= '1';

   TX_DST_RDY_N(0) <= '0';
   TX_DST_RDY_N(1) <= '0';
   TX_DST_RDY_N(2) <= '0';
   TX_DST_RDY_N(3) <= '0';

   RX_SRC_RDY_N <= '1';
   RX_SOF_N <= '0';
   RX_EOF_N <= '1';
   RX_SOP_N <= '0';
   RX_EOP_N <= '1';
   RX_REM <= (others => '1');
   RX_DATA <= (others => '0');

   wait for RESET_TIME;
   reset <= '0';
   wait for 10*clkper;
   wait for 1 ns;

   RX_DATA <= X"0000000000000002";
   RX_SRC_RDY_N <= '0';
   wait for clkper;
   RX_DATA <= X"1000000000000000";
   RX_SOF_N <= '1';
   RX_EOF_N <= '1';
   RX_SOP_N <= '1';
   RX_EOP_N <= '0';
   wait for clkper;
   RX_DATA <= X"2000000000000000";
   RX_SOP_N <= '0';
   RX_EOP_N <= '1';
   wait for clkper;
   RX_DATA <= X"3000000000000000";
   wait for clkper;
   RX_DATA <= X"4000000000000000";
   wait for clkper;
   RX_DATA <= X"5000000000000000";
   wait for clkper;
   RX_DATA <= X"6000000000000000";
   RX_SOF_N <= '1';
   RX_EOF_N <= '0';
   RX_SOP_N <= '1';
   RX_EOP_N <= '0';
   wait for clkper;
   RX_SRC_RDY_N <= '1';

   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
