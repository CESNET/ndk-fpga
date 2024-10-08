-- testbench.vhd: testbench of sh_reg_base_dynamic
-- Copyright (C) 2015 CESNET
-- Author(s): Radek Isa <xisara00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--
library ieee;
use ieee.numeric_std.all;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use std.textio.ALL;


use work.all;
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
   ------------------
   --Time constants
   constant CONST_CLK      : time := 2.000 ns;



   ----------------
   -- constant
   constant DATA_WIDTH       : integer := 16;
   constant NUM_BITS         : integer := 3;

   -----------------------
   -- clk signals
   signal CLK    : std_logic;

   -- Signals
   signal in_data  : std_logic_vector(DATA_WIDTH -1 downto 0);
   signal out_data : std_logic_vector(DATA_WIDTH -1 downto 0);
   signal ce : std_logic;

   --testovaci signal
   signal   sig_test     : std_logic;

begin

--------------------------
--	Clocks & Resets
--------------------------
   --CLOCK
   lzss_clkgen: process
   begin
      CLK <= '1';
      wait for CONST_CLK/2;
      CLK <= '0';
      wait for CONST_CLK/2;
   end process;


   -----------
   --  UUT  --
   -----------
   UUT: entity work.sh_reg_base_dynamic
       generic map(
         DATA_WIDTH  => DATA_WIDTH,
         NUM_BITS    => NUM_BITS,

         INIT_TYPE   => 3,
         INIT        => x"B42f01f0FF00FF00",
         IS_CLK_INVERTED => '0' ,

         OPT  => "SRL"
       )
       port map(
         CLK  => CLK,
         CE   => ce,
         ADDR => conv_std_logic_vector(NUM_BITS-1, log2(NUM_BITS)),

         DIN  => in_data,
         DOUT => out_data
      );

   -----------------
   --	Testbench	--
   -----------------
   tb:process

     variable var_end : integer;
     variable test_cnt: integer := 0;
   begin


      --------------------------
      -- start simulation
      sig_test <= '1';
      in_data <= (others => '0');
      wait until CLK = '1';
      ce <= '0';
      wait until CLK = '0';

     while true loop
        wait until CLK = '1';
        in_data <= (others => '0');
        ce      <= '1';
        wait until CLK = '0';
     end loop;


      ----------------------------
      -- EXIT
      wait until CLK = '1';
      in_data   <= (others => '0');
      wait until CLK = '0';


      wait;
   end process;

end architecture behavioral;
