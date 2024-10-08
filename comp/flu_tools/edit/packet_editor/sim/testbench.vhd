-- testbench.vhd: Testbench for packet editor
-- # Copyright (C) 2015 CESNET
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
use work.math_pack.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset durati
   constant DATA_WIDTH     : integer := 512;
   constant SOP_POS_WIDTH  : integer := 3;
   constant OFFSET_WIDTH   : integer := 10;

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;
   signal NEW_DATA         : std_logic_vector(8*4-1 downto 0);
   signal OFFSET           : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal EN_REPLACE       : std_logic;
   signal EN_SHIFT         : std_logic;
   signal RX_DATA          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal RX_SOP_POS       : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal RX_EOP_POS       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal RX_SOP           : std_logic;
   signal RX_EOP           : std_logic;
   signal RX_SRC_RDY       : std_logic;
   signal RX_DST_RDY       : std_logic;
   signal TX_DATA          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal TX_SOP_POS       : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal TX_EOP_POS       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal TX_SOP           : std_logic;
   signal TX_EOP           : std_logic;
   signal TX_SRC_RDY       : std_logic;
   signal TX_DST_RDY       : std_logic;
   signal MASK             : std_logic_vector(3 downto 0);

begin

   -- packet editor
   uut : entity work.PACKET_EDITOR
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      OFFSET_WIDTH   => OFFSET_WIDTH,
      INPUT_PIPE     => true,
      EN_MASK        => true
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      NEW_DATA       => NEW_DATA,
      OFFSET         => OFFSET,
      EN_REPLACE     => EN_REPLACE,
      EN_SHIFT       => EN_SHIFT,
      RX_DATA        => RX_DATA,
      RX_SOP_POS     => RX_SOP_POS,
      RX_EOP_POS     => RX_EOP_POS,
      RX_SOP         => RX_SOP,
      RX_EOP         => RX_EOP,
      RX_SRC_RDY     => RX_SRC_RDY,
      RX_DST_RDY     => RX_DST_RDY,
      TX_DATA        => TX_DATA,
      TX_SOP_POS     => TX_SOP_POS,
      TX_EOP_POS     => TX_EOP_POS,
      TX_SOP         => TX_SOP,
      TX_EOP         => TX_EOP,
      TX_SRC_RDY     => TX_SRC_RDY,
      TX_DST_RDY     => TX_DST_RDY,
      MASK           => MASK
   );

   --Generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   --Generate reset
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
      MASK        <= (others => '0');
      NEW_DATA    <= (others => '1');
      OFFSET      <= (others => '1');
      EN_REPLACE  <= '0';
      EN_SHIFT    <= '0';
      RX_DATA     <= (others => '0');
      RX_SOP_POS  <= (others => '0');
      RX_EOP_POS  <= (others => '0');
      RX_SOP      <= '0';
      RX_EOP      <= '0';
      RX_SRC_RDY  <= '0';
      TX_DST_RDY  <= '1';
      wait for reset_time;
      wait for clkper;
      wait for 2 ns;

      NEW_DATA    <= X"DDCCBBAA";
      MASK        <= "1101";
      RX_SRC_RDY  <= '1';
      RX_DATA     <= (others => '0');
      EN_SHIFT    <= '1';
      EN_REPLACE  <= '1';
      RX_SOP_POS  <= "000";
      OFFSET      <= conv_std_logic_vector(15, OFFSET'LENGTH);
      RX_SOP      <= '1';
      wait for clkper;

      MASK <= (others => '0');
      NEW_DATA    <= (others => '1');
      OFFSET      <= (others => '1');
      EN_REPLACE  <= '0';
      EN_SHIFT    <= '0';
      RX_DATA     <= (others => '0');
      RX_SOP_POS  <= (others => '0');
      RX_EOP_POS  <= (others => '0');
      RX_SOP      <= '0';
      RX_EOP      <= '0';
      RX_SRC_RDY  <= '0';
      TX_DST_RDY  <= '1';
      wait for clkper;

      MASK        <= "1111";
      RX_SRC_RDY  <= '1';
      RX_DATA     <= (others => '1');
      EN_SHIFT    <= '0';
      EN_REPLACE  <= '1';
      RX_SOP_POS  <= "001";
      OFFSET      <= conv_std_logic_vector(15, OFFSET'LENGTH);
      RX_SOP      <= '1';
      wait for clkper;

      MASK        <= "1111";
      RX_SOP_POS  <= "000";
      EN_SHIFT    <= '1';
      EN_REPLACE  <= '1';
      OFFSET      <= conv_std_logic_vector(0, OFFSET'LENGTH);
      RX_SOP      <= '1';
      RX_EOP      <= '1';
      RX_DATA     <= X"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA";
      NEW_DATA    <= (others => '1');
      wait for clkper;

      MASK        <= "1111";
      RX_SOP_POS  <= "000";
      EN_SHIFT    <= '0';
      EN_REPLACE  <= '1';
      OFFSET      <= conv_std_logic_vector(0, OFFSET'LENGTH);
      RX_SOP      <= '1';
      RX_EOP      <= '1';
      RX_DATA     <= X"CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC";
      NEW_DATA    <= (others => '1');
      wait for clkper;

      MASK        <= "1111";
      RX_SOP_POS  <= "000";
      EN_SHIFT    <= '0';
      EN_REPLACE  <= '1';
      OFFSET      <= conv_std_logic_vector(15, OFFSET'LENGTH);
      RX_SOP      <= '1';
      RX_EOP      <= '1';
      RX_DATA     <= X"BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB";
      NEW_DATA    <= (others => '1');
      wait for clkper;

      MASK        <= "1111";
      RX_SRC_RDY  <= '1';
      RX_SOP_POS  <= "000";
      EN_SHIFT    <= '0';
      EN_REPLACE  <= '1';
      OFFSET      <= conv_std_logic_vector(32, OFFSET'LENGTH);
      RX_SOP      <= '1';
      RX_EOP      <= '1';
      RX_DATA     <= X"EEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE";
      NEW_DATA    <= (others => '1');

      wait for clkper;
      MASK        <= "1111";
      RX_SRC_RDY  <= '0';
      RX_SOP_POS  <= "000";
      EN_SHIFT    <= '0';
      EN_REPLACE  <= '1';
      OFFSET      <= conv_std_logic_vector(32, OFFSET'LENGTH);
      RX_SOP      <= '1';
      RX_EOP      <= '1';
      RX_DATA     <= X"55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555";
      NEW_DATA    <= (others => '1');

      wait for clkper;
      RX_SRC_RDY  <= '1';
      MASK        <= "1111";
      NEW_DATA    <= (others => '1');
      OFFSET      <= (others => '1');
      EN_REPLACE  <= '0';
      EN_SHIFT    <= '0';
      RX_DATA     <= (others => '0');
      RX_SOP_POS  <= (others => '0');
      RX_EOP_POS  <= (others => '0');
      RX_SOP      <= '0';
      RX_EOP      <= '0';
      TX_DST_RDY  <= '0';
      wait for clkper;

      TX_DST_RDY  <= '1';
      wait for clkper*2;

      RX_SRC_RDY  <= '0';
      wait;
   end process input_flow;
end architecture;
