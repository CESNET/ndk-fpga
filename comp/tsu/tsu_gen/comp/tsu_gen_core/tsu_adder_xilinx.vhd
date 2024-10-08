--! tsu_adder.vhd
--!
--! @file
--! \brief timestamp unit - adder
--! \author Jakub Cabal <jakubcabal@gmail.com>
--! \date 2014
--!
--! @section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

Library UNISIM;
use UNISIM.vcomponents.all;

Library UNIMACRO;
use UNIMACRO.vcomponents.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of tsu_adder is

   signal reg_rtr_we_1      : std_logic;
   signal reg_rtr_we_2      : std_logic;
   signal add_result_low_0  : std_logic_vector(47 downto 0);
   signal add_result_low_1  : std_logic_vector(47 downto 0);
   signal add_input_low     : std_logic_vector(47 downto 0);
   signal add_input_high    : std_logic_vector(47 downto 0);
   signal add_result_high_0 : std_logic_vector(47 downto 0);
   signal add_result_high_1 : std_logic_vector(47 downto 0);
   signal extended_incr     : std_logic_vector(47 downto 0);
   signal carry             : std_logic;
   signal b_input           : std_logic_vector(47 downto 0);

begin

   -- -------------------------------------------------------
   -- Registered rtr_we signal
   reg_rtr_we_register : process(CLK)
   begin
      if (rising_edge(CLK)) then
         reg_rtr_we_1 <= REG_RTR_WE;
         reg_rtr_we_2 <= reg_rtr_we_1;
      end if;
   end process;

   -- -------------------------------------------------------
   -- First adder branch
   -- -------------------------------------------------------
   -- Multiplexor for first dsp adder
   first_adder_input_mux : process(reg_rtr_we_1, REG_RTR, add_result_low_0)
   begin
      case (reg_rtr_we_1) is
         when '1' => add_input_low <= REG_RTR(47 downto 0);
         when others => add_input_low <= add_result_low_0;
      end case;
   end process;

   extended_incr <= X"00" & '0' & INCR_VALUE;

   -- -------------------------------------------------------
   -- First adder
   ADDSUB_MACRO_inst_low : ADDSUB_MACRO
   generic map (
      DEVICE => "7SERIES", -- Target Device: "VIRTEX5", "VIRTEX6", "SPARTAN6", "7SERIES"
      LATENCY => 1,        -- Desired clock cycle latency, 0-2
      WIDTH => 48)         -- Input / Output bus width, 1-48
   port map (
      CARRYOUT => carry,          -- 1-bit carry-out output signal
      RESULT => add_result_low_0, -- Add/sub result output, width defined by WIDTH generic
      A => add_input_low,         -- Input A bus, width defined by WIDTH generic
      ADD_SUB => '1',             -- 1-bit add/sub input, high selects add, low selects subtract
      B => extended_incr,         -- Input B bus, width defined by WIDTH generic
      CARRYIN => '0',             -- 1-bit carry-in input
      CE => '1',                  -- 1-bit clock enable input
      CLK => CLK,                 -- 1-bit clock input
      RST => RESET                -- 1-bit active high synchronous reset
   );

   -- -------------------------------------------------------
   -- Register for first adder branch
   first_adder_branch_reg : process(CLK)
   begin
      if (rising_edge(CLK)) then
         add_result_low_1 <= add_result_low_0;
      end if;
   end process;

   -- -------------------------------------------------------
   -- -------------------------------------------------------
   -- Second adder branch
   -- -------------------------------------------------------
   -- Register for second adder branch
   second_adder_branch_reg : process(CLK)
   begin
      if (rising_edge(CLK)) then
         add_result_high_0 <= REG_RTR(95 downto 48);
      end if;
   end process;

   -- -------------------------------------------------------
   -- Multiplexor for second dsp adder
   second_adder_input_mux : process(reg_rtr_we_2, add_result_high_0, add_result_high_1)
   begin
      case (reg_rtr_we_2) is
         when '1' => add_input_high <= add_result_high_0;
         when others => add_input_high <= add_result_high_1;
      end case;
   end process;

   -- -------------------------------------------------------
   -- Second adder
   ADDSUB_MACRO_inst_high : ADDSUB_MACRO
   generic map (
      DEVICE => "7SERIES", -- Target Device: "VIRTEX5", "VIRTEX6", "SPARTAN6", "7SERIES"
      LATENCY => 1,        -- Desired clock cycle latency, 0-2
      WIDTH => 48)         -- Input / Output bus width, 1-48
   port map (
      CARRYOUT => open,            -- 1-bit carry-out output signal
      RESULT => add_result_high_1, -- Add/sub result output, width defined by WIDTH generic
      A => add_input_high,         -- Input A bus, width defined by WIDTH generic
      ADD_SUB => '1',              -- 1-bit add/sub input, high selects add, low selects subtract
      B => b_input,                -- Input B bus, width defined by WIDTH generic
      CARRYIN => '0',              -- 1-bit carry-in input
      CE => '1',                   -- 1-bit clock enable input
      CLK => CLK,                  -- 1-bit clock input
      RST => RESET                 -- 1-bit active high synchronous reset
   );

   b_input <= X"00000000000" & "000" & carry;

   ADD_RESULT <= add_result_high_1 & add_result_low_1;

end architecture FULL;
