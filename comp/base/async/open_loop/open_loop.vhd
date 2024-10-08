--!
--! open_loop.vhd: Open-loop solution single signal synchronizer.
--! Copyright (C) 2014 CESNET
--! Author(s): Jakub Cabal <cabal@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!

library IEEE;
use IEEE.std_logic_1164.all;

   --! -------------------------------------------------------------------------
   --!                      Readme!!!
   --! -------------------------------------------------------------------------

   --! When you sync from slow to fast clock domain,
   --! you must hold this condition:
   --!                              frequency_fast >= 1.5x frequency_slow

   --! When you sync from fast to slow clock domain,
   --! you must hold this condition:
   --!                              input_pulse_length >= 1.5x period_slow

   --! -------------------------------------------------------------------------
   --!                      Entity declaration
   --! -------------------------------------------------------------------------

entity ASYNC_OPEN_LOOP is
   Generic (
      IN_REG   : BOOLEAN := false; --! For one register on input = true
      TWO_REG  : BOOLEAN := false  --! For two reg = true, for three reg = false
   );
   Port (
      --! A clock domain
      ACLK     : in  STD_LOGIC := '0';    --! Source clock
      ARST     : in  STD_LOGIC := '0';    --! Source reset
      ADATAIN  : in  STD_LOGIC;           --! Data input

      --! B clock domain
      BCLK     : in  STD_LOGIC;           --! Target clock
      BRST     : in  STD_LOGIC := '0';    --! Target reset
      BDATAOUT : out STD_LOGIC            --! Data output
   );
end ASYNC_OPEN_LOOP;

   --! -------------------------------------------------------------------------
   --!                      Architecture declaration
   --! -------------------------------------------------------------------------

architecture FULL of ASYNC_OPEN_LOOP is

   --! -------------------------------------------------------------------------
   --!                      SIGNALS
   --! -------------------------------------------------------------------------

   signal signal_D1   : std_logic := '0';
   signal signal_Q1   : std_logic := '0';
   signal signal_Q2   : std_logic := '0';

   --! Attributes for signal_Q1_reg and signal_Q2_reg
   attribute shreg_extract                : string;
   attribute async_reg                    : string;

   attribute shreg_extract of signal_Q1   : signal is "no";
   attribute async_reg of signal_Q1       : signal is "true";

   attribute shreg_extract of signal_Q2   : signal is "no";
   attribute async_reg of signal_Q2       : signal is "true";

   --! Attributes for Intel FPGA
   attribute ALTERA_ATTRIBUTE  : string;

   attribute ALTERA_ATTRIBUTE of signal_Q1 : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON; -name SYNCHRONIZER_IDENTIFICATION FORCED";
   attribute ALTERA_ATTRIBUTE of signal_Q2 : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";

   --! -------------------------------------------------------------------------

begin

   --! Generics input register
   input_reg : if IN_REG generate

      process(ACLK)
      begin
         if (rising_edge(ACLK)) then
            if (ARST = '1') then
               signal_D1 <= '0';
            else
               signal_D1 <= ADATAIN;
            end if;
         end if;
      end process;

   end generate;

   --! -------------------------------------------------------------------------

   --! Generics input register off
   not_in_reg : if NOT IN_REG generate

      signal_D1 <= ADATAIN;

   end generate;

   --! -------------------------------------------------------------------------

   --! Two synchronization registers
   process(BCLK)
   begin
      if (rising_edge(BCLK)) then
         if (BRST = '1') then
            signal_Q1 <= '0';
            signal_Q2 <= '0';
         else
            signal_Q1 <= signal_D1;
            signal_Q2 <= signal_Q1;
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------------------

   --! Generics two synchronization registers
   two_reg_sync : if TWO_REG generate

      BDATAOUT <= signal_Q2;

   end generate;

   --! -------------------------------------------------------------------------

   --! Generics three synchronization registers
   three_reg_sync : if NOT TWO_REG generate

      --! Signals
      signal signal_Q3                       : std_logic := '0';

      --! Attributes	for signal_Q3_reg
      attribute shreg_extract of signal_Q3    : signal is "no";
      attribute async_reg of signal_Q3        : signal is "true";
      attribute ALTERA_ATTRIBUTE of signal_Q3 : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";

      begin

      process(BCLK)
      begin
         if (rising_edge(BCLK)) then
            if (BRST = '1') then
               signal_Q3 <= '0';
            else
               signal_Q3 <= signal_Q2;
            end if;
         end if;
      end process;

      BDATAOUT <= signal_Q3;

   end generate;

   --! -------------------------------------------------------------------------

end architecture FULL;
