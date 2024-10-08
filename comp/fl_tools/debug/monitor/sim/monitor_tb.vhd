--
-- monitor_tb.vhd: Component testbench.
-- Copyright (C) 2003 CESNET
-- Author(s): Lukas Solanka <solanka@liberouter.org>
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
use work.mi32_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant clkper      : time      := 10 ns;
   constant INIT_TIME   : time      := 4*clkper + 10*clkper;
   constant RESET_TIME  : time      := 3*clkper;

   -- TEST behaviour after RESET asserted
   constant TEST_RESET  : boolean := false;

   -- Packet parameters

   -- Number of words in packet
   constant PAC_LENGTH : integer := 43;

   -- Number of packets to send
   constant PAC_NUM    : integer := 16;

   -- UUT generics
   constant FL_WIDTH       : integer := 64;
   constant WORD_WIDTH     : integer := 64;
   constant WORD_POS       : integer := 4;
   constant DEFAULT_DATA   : std_logic_vector(WORD_WIDTH - 1 downto 0) :=
                                 X"0123456789abcdef";
--    constant DEFAULT_DATA   : std_logic_vector(WORD_WIDTH - 1 downto 0) :=
--             conv_std_logic_vector(WORD_POS / (FL_WIDTH/WORD_WIDTH), WORD_WIDTH);

   signal clk      : std_logic;
   signal reset    : std_logic;

   signal rx_data      : std_logic_vector(FL_WIDTH - 1 downto 0);
   signal rx_rem       : std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);
   signal rx_src_rdy_n : std_logic;
   signal rx_dst_rdy_n : std_logic;
   signal rx_sop_n     : std_logic;
   signal rx_eop_n     : std_logic;
   signal rx_sof_n     : std_logic;
   signal rx_eof_n     : std_logic;

   signal mi           : t_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin


UUT: entity work.fl_monitor
   generic map (
      FL_WIDTH     => FL_WIDTH,
      WORD_WIDTH   => WORD_WIDTH,
      WORD_POS     => WORD_POS
   )
   port map (
      CLK       => clk,
      RESET     => reset,

      DEFAULT_DATA => DEFAULT_DATA,

      -- Framelink interface of transmitting component
      SOF_N     => rx_sof_n,
      SOP_N     => rx_sop_n,
      EOP_N     => rx_eop_n,
      EOF_N     => rx_eof_n,
      SRC_RDY_N => rx_src_rdy_n,
      DST_RDY_N => rx_dst_rdy_n,
      DATA      => rx_data,
      DREM      => rx_rem,

      -- Memory interface
      MI        => mi
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
   RX_DATA        <= (others =>'0');
   RX_REM         <= (others => '0');
   RX_SOP_N       <= '1';
   RX_EOP_N       <= '1';
   RX_SOF_N       <= '1';
   RX_EOF_N       <= '1';
   RX_SRC_RDY_N   <= '1';

   wait for RESET_TIME + INIT_TIME;

   RX_SRC_RDY_N <= '0';

   for pnum in 1 to PAC_NUM - 1 loop
      for ppart in 0 to PAC_LENGTH - 1 loop
         -- Generate SOF/EOF on the packet edges
         if (ppart = 0) then
            RX_SOF_N <= '0';
         else
            RX_SOF_N <= '1';
         end if;

         if (ppart = PAC_LENGTH - 1) then
            RX_EOF_N <= '0';
         else
            RX_EOF_N <= '1';
         end if;


         RX_DATA <= conv_std_logic_vector(ppart, rx_data'length);

         wait for clkper;
         wait until clk'event and clk = '1' and RX_DST_RDY_N = '0';
      end loop;
   end loop;

   RX_SRC_RDY_N <= '1';
   wait;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
   reset <= '1';

   -- Initialize MI32
   mi.addr <= conv_std_logic_vector(16#40#, mi.addr'length);
   mi.be <= (others => '1');
   mi.wr <= '0';
   mi.rd <= '0';
   mi.dwr <= (others => '0');

   wait for RESET_TIME;
   reset <= '0';

   rx_dst_rdy_n <= '0';

   wait for clkper/6;
   mi.dwr <= conv_std_logic_vector(16#100#, 32);
   mi.wr <= '1';
   wait for clkper;
   mi.dwr <= conv_std_logic_vector(0, 32);
   mi.addr <= mi.addr + 4;
   wait for clkper;
   mi.wr <= '0';


   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
