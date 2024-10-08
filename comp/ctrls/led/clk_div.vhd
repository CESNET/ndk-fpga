-- clk_div.vhd: Frequency divider
-- Copyright (C) 2016 CESNET
-- Author(s): Juraj Kubis
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
-- entity declaration
-- ----------------------------------------------------------------------------
entity clk_div is
   generic (
      --! Clk period in ns
      CLK_PERIOD : integer;
      --! Blink period in ms
      PTRN_STEP_PERIOD : integer
   );

   port (
      --! Input clock signal
      CLK : in std_logic;
      --! Global synchronous reset
      RESET : in std_logic;

      --! One-stroke signal with PTRN_STEP_PERIOD
      STATE_CHANGE : out std_logic;
      --! High frequency signal for yellow color
      PWM_YELLOW_SYNC : out std_logic
   );

end entity clk_div;

-- ----------------------------------------------------------------------------
-- architecture declaration
-- ----------------------------------------------------------------------------
architecture clk_div_arch of clk_div is
   constant INTERVAL    : integer := (PTRN_STEP_PERIOD * 500000) / CLK_PERIOD - 1;
   signal cnt_clock     : std_logic_vector(31 downto 0) := (others => '0');
   signal cnt_pwm_sync  : std_logic_vector(16 downto 0) := (others => '0');
   signal out_clk       : std_logic;
begin
   process (RESET, CLK)
   begin
      if (CLK'EVENT and CLK = '1') then
         --! Synchronous reset
         if (RESET = '1') then
            out_clk <= '0';
            cnt_clock <= (others => '0');
         --! Clock dividers
         else
            if (cnt_clock = INTERVAL) then
               out_clk <= '1';
               cnt_clock <= (others => '0');
            else
               out_clk <= '0';
               cnt_clock <= cnt_clock + 1;
            end if;

            if (cnt_pwm_sync(16) = '1') then
               cnt_pwm_sync <= (others => '0');
            else
               cnt_pwm_sync <= cnt_pwm_sync + 1;
            end if;
         end if;
      end if;
   end process;

   STATE_CHANGE <= out_clk;
   PWM_YELLOW_SYNC <= cnt_pwm_sync(15);

end architecture clk_div_arch;
