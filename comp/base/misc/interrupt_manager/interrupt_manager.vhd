-- interrupt_manager.vhd: Interrupt agregator module
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

--* Interrupt Manager entity
entity INTERRUPT_MANAGER is
   generic (
      --* If bit is set to 0, input is not single-cycle pulse
      PULSE : std_logic_vector(31 downto 0) := X"FFFFFFFF"
   );
   port (
      --+ Common interface
      CLK            : in std_logic;
      RESET          : in std_logic;

      --* Input interface Interrupt request
      INTERRUPT_IN   : in std_logic_vector(31 downto 0);
      --* Input interface Ready for next request
      INTR_RDY_IN    : out std_logic;

      --* Output interface Interrupt request
      INTERRUPT_OUT  : out std_logic;
      --* Output interface Data
      INTR_DATA_OUT  : out std_logic_vector(4 downto 0);
      --* Output interface Ready for next request
      INTR_RDY_OUT   : in std_logic
   );
end INTERRUPT_MANAGER;

--* Interrupt Manager FULL architecture
architecture full of INTERRUPT_MANAGER is

signal intr_in_pulse    : std_logic_vector(31 downto 0);
signal input_or         : std_logic_vector(32 downto 0);

begin

   input_or(0) <= '0';

   pulse_gen : for i in 0 to 31 generate

      no_pulse : if PULSE(i) = '0' generate
         edge_detect_i : entity work.edge_detect
         port map(
            CLK   => CLK,
            DI    => INTERRUPT_IN(i),
            EDGE  => intr_in_pulse(i)
         );
      end generate;

      yes_pulse : if PULSE(i) = '1' generate
         intr_in_pulse(i) <= INTERRUPT_IN(i);
      end generate;

      input_or(i+1) <= input_or(i) or intr_in_pulse(i);

   end generate;

   --* 1ofN to Binary dedoder instance
   decoder_i : entity work.dec1fn2b
   generic map(
      ITEMS    => 32
   )
   port map(
      ADDR     => INTR_DATA_OUT,
      ENABLE   => '1',
      DI       => intr_in_pulse
   );

   INTR_RDY_IN <= INTR_RDY_OUT;
   INTERRUPT_OUT <= input_or(32);

end full;
