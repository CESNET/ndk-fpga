-- led_ctrl.vhd: LED controler
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
entity led_ctrl is
   generic (
      --! LED active value ('0' or '1')
      ON_VALUE : std_logic;
      --! Pattern length
      PTRN_LENGTH : integer
   );

   port (
      --! Clock signal
      CLK : in std_logic;
      --! Global synchronous reset
      RESET : in std_logic;

      --! Enable the change of state
      STATE_CHANGE : in std_logic;
      --! High frequency signal for generating yellow color
      PWM_YELLOW_SYNC : in std_logic;

      --! Blink pattern
      PTRN : in std_logic_vector(PTRN_LENGTH*2-1 downto 0);

      --! Green LED control
      LED_GREEN : out std_logic;
      --! Red LED control
      LED_RED : out std_logic
   );

end entity led_ctrl;

-- ----------------------------------------------------------------------------
-- architecture declaration
-- ----------------------------------------------------------------------------
architecture led_ctrl_arch of led_ctrl is
   signal cnt_pattern_step : integer range 0 to PTRN_LENGTH-1 := 0;
begin
   process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            --! No light
            LED_RED <= not ON_VALUE;
            LED_GREEN <= not ON_VALUE;
            --! Reset step counter
            cnt_pattern_step <= 0;
         else
            --! No light
            if (PTRN(2*cnt_pattern_step+1 downto 2*cnt_pattern_step) = "11") then
               LED_RED <= not ON_VALUE;
               LED_GREEN <= not ON_VALUE;

            --! Red
            elsif (PTRN(2*cnt_pattern_step+1 downto 2*cnt_pattern_step) = "10") then
               LED_RED <= ON_VALUE;
               LED_GREEN <= not ON_VALUE;

            --! Green
            elsif (PTRN(2*cnt_pattern_step+1 downto 2*cnt_pattern_step) = "01") then
               LED_RED <= not ON_VALUE;
               LED_GREEN <= ON_VALUE;

            --! Yellow
            elsif (PTRN(2*cnt_pattern_step+1 downto 2*cnt_pattern_step) = "00") then
               LED_RED <= PWM_YELLOW_SYNC;
               LED_GREEN <= not PWM_YELLOW_SYNC;
            end if;

            --! Step counting
            if (STATE_CHANGE = '1') then
               if (cnt_pattern_step = PTRN_LENGTH-1) then
                  cnt_pattern_step <= 0;
               else
                  cnt_pattern_step <= cnt_pattern_step + 1;
               end if;
            end if;
         end if;
      end if;
   end process;

end architecture led_ctrl_arch;
