-- testbench.vhd: Testbench for streaming generator
-- # Copyright (C) 2014 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant DATA_WIDTH     : integer := 544; --Clock period
   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset durati

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   signal DATA             : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal SRC_RDY          : std_logic;
   signal DST_RDY          : std_logic;

      --! MI32 input interface -------------------------------------------------
      --! Input Data
     signal MI_DWR                        :  std_logic_vector(31 downto 0);
      --! Address
     signal MI_ADDR                       :  std_logic_vector(31 downto 0);
      --! Read Request
     signal MI_RD                         :  std_logic;
      --! Write Request
     signal MI_WR                         :  std_logic;
      --! Byte Enable
     signal MI_BE                         :  std_logic_vector(3  downto 0);
      --! Output Data
     signal MI_DRD                        :  std_logic_vector(31 downto 0);
      --! Address Ready
     signal MI_ARDY                       :  std_logic;
      --! Data Ready
     signal MI_DRDY                       :  std_logic;

begin

   -- MUL48
   uut : entity work.STREAMING_GENERATOR(full)
   generic map(
      --! Input data width
      DATA_WIDTH => DATA_WIDTH,
      --! Address bus width
      ITEMS  => 1024,
      CNT_WIDTH  => 4
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      DATA        => DATA,
      SRC_RDY     => SRC_RDY,
      DST_RDY     => DST_RDY,
      --! MI32 input interface -------------------------------------------------
      --! Input Data
      MI_DWR                        => MI_DWR,
      --! Address
      MI_ADDR                       => MI_ADDR,
      --! Read Request
      MI_RD                         => MI_RD,
      --! Write Request
      MI_WR                         => MI_WR,
      --! Byte Enable
      MI_BE                         => MI_BE,
      --! Output Data
      MI_DRD                        => MI_DRD,
      --! Address Ready
      MI_ARDY                       => MI_ARDY,
      --! Data Ready
      MI_DRDY                       => MI_DRDY
   );

   --Generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   dst_rdy_gen : process
   begin
      DST_RDY <= '1';
      wait for 472 ns;
      DST_RDY<= '0';
      wait for clkper*4;
   end process dst_rdy_gen;

   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   -- Simulating input flow
   input_flow : process
   begin

      -- Initialize input interface
      MI_DWR                        <= X"00000000";
      --! Address
      MI_ADDR                       <= (others => '0');
      --! Read Request
      MI_RD                         <= '0';
      --! Write Request
      MI_WR                         <= '0';
      --! Byte Enable
      MI_BE                         <= "1111";

      wait for reset_time;
      wait for 3*clkper;
      wait for clkper;

      MI_BE   <= "1111";
      MI_WR   <= '1';

      --! writing data to bram
      --! #1
      MI_ADDR <= (13 => '0', 6 => '1', others => '0');
      MI_DWR  <= X"00000001";
      wait for 2*clkper;

      MI_ADDR <= (13 => '1', 6 => '1', others => '0');
      MI_DWR  <= X"00000001";
      wait for 2*clkper;

      --! #2
      MI_ADDR <= (13 => '0',6 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000002";
      wait for 2*clkper;

      MI_ADDR <= (13 => '1',6 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000002";
      wait for 2*clkper;

      --! #3
      MI_ADDR <= (13 => '0',6 => '1', 3 => '1', others => '0');
      MI_DWR  <= X"00000003";
      wait for 2*clkper;

      MI_ADDR <= (13 => '1',6 => '1', 3 => '1', others => '0');
      MI_DWR  <= X"00000003";
      wait for 2*clkper;

      --! #4
      MI_ADDR <= (13 => '0',6 => '1', 3 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000004";
      wait for 2*clkper;

      MI_ADDR <= (13 => '1',6 => '1', 3 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000004";
      wait for 2*clkper;

       --! #5
      MI_ADDR <= (13 => '0',6 => '1', 4 => '1', others => '0');
      MI_DWR  <= X"00000005";
      wait for 2*clkper;

      MI_ADDR <= (13 => '1',6 => '1', 4 => '1', others => '0');
      MI_DWR  <= X"00000005";
      wait for 2*clkper;

      --! #6
      MI_ADDR <= (13 => '0',6 => '1', 4 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000006";
      wait for 2*clkper;

      MI_ADDR <= (13 => '1',6 => '1', 4 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000006";
      wait for 2*clkper;


      MI_WR   <= '0';
      wait for clkper;

      --! writing config1
      MI_WR   <= '1';
      MI_ADDR <= (3 => '1', others => '0');
      MI_DWR  <= X"000C000C";
      wait for 2*clkper;

      --! writing config2
      MI_ADDR <= (3 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"00000001";
      wait for 2*clkper;

      --! writing config3
      MI_ADDR <= (4 => '1', others => '0');
      MI_DWR  <= X"00000003";
      wait for 2*clkper;

      --! writing config4
      MI_ADDR <= (4 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"1F000000";
      wait for 2*clkper;

      --! run set 1
      MI_ADDR <= (4 => '1', 3 => '1', others => '0');
      MI_DWR  <= X"00000001";
      wait for 2*clkper;
      MI_WR   <= '0';

      wait for 30*clkper;

      MI_WR   <= '1';
      MI_ADDR <= (4 => '1', 2 => '1', others => '0');
      MI_DWR  <= X"1F000002";
      wait for 2*clkper;

       --! run set 1
      MI_ADDR <= (4 => '1', 3 => '1', others => '0');
      MI_DWR  <= X"00000001";
      wait for 2*clkper;
      MI_WR   <= '0';

      wait for 15*clkper;
      wait;

   end process input_flow;
end architecture;
