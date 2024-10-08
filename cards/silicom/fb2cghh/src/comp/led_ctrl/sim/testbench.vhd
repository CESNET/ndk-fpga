-- testbench.vhd: Simulation file 
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <benes.david2000@seznam.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE IEEE.std_logic_textio.ALL;
USE ieee.numeric_std.ALL;
USE std.textio.ALL;
 
ENTITY TESTBENCH IS
END TESTBENCH;
 
ARCHITECTURE FULL OF TESTBENCH IS 

    
   --Inputs
   signal CLK        : std_logic := '0';
   signal RST        : std_logic := '0';
   signal GREEN_LED  : std_logic_vector(15 downto 0) := (others => '0');
   signal RED_LED    : std_logic_vector(15 downto 0) := (others => '0');

    --Outputs
   signal LED_SDI    : std_logic;
   signal LED_CLK    : std_logic;
   signal LED_LE     : std_logic;

   -- Clock period definitions
   constant clk_period : time := 20 ns;
                          
BEGIN
 
    -- Instantiate the Unit Under Test (UUT)
   uut_i: entity work.LED_SERIAL_CTRL
    PORT MAP (
          CLK           => CLK,
          RST           => RST,
          RED_LED       => red_LED,
          GREEN_LED     => green_LED,
          LED_SDI       => LED_SDI,
          LED_CLK       => LED_CLK,
          LED_LE        => LED_LE 
        );

   -- Clock process definitions
   clk_process :process
   begin
        clk <= '0';
        wait for clk_period/2;
        clk <= '1';
        wait for clk_period/2;
   end process;
 

   -- Stimulus process
   stim_proc: process
   begin        
      RST <= '1', '0' after CLK_PERIOD*5;
      wait for CLK_PERIOD*5;
      --RST           <= '0';
      green_LED     <= "1111111100000000";
      red_LED       <= "0000000011111111";
      --green_LED     <= x"BEEF";
      --red_LED       <= x"ABCD";
      WAIT;
   end process;

END;
