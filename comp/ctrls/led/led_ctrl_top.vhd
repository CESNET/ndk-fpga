-- led_ctrl_top.vhd: Generic multi LED controler
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
entity led_ctrl_top is
   generic (
      --! Number of LEDs
      LED_COUNT : integer := 8;
      --! LED active value ('0' or '1')
      ON_VALUE : std_logic := '0';
      --! Clk period in ns
      CLK_PERIOD : integer := 8;
      --! Pattern step period in ms
      PTRN_STEP_PERIOD : integer := 100;
      --! Pattern length
      PTRN_LENGTH : integer := 16
   );

   port (
      --! Common clock
      CLK : in std_logic;
      --! Common reset for controlers and divider
      RESET : in std_logic;

      --! Patterns for all LEDs
      PTRNS : in std_logic_vector(LED_COUNT*PTRN_LENGTH*2-1 downto 0);

      --! Green LED control
      LED_GREEN : out std_logic_vector(LED_COUNT - 1 downto 0);
      --! Red LED control
      LED_RED : out std_logic_vector(LED_COUNT - 1 downto 0)
   );

end entity led_ctrl_top;

-- ----------------------------------------------------------------------------
-- architecture declaration
-- ----------------------------------------------------------------------------
architecture led_ctrl_top_arch of led_ctrl_top is
   signal state_change, pwm_yellow_sync : std_logic;
begin
   --! Clock frequency divider for blink states
   clk_div_i: entity work.clk_div
      generic map (
         CLK_PERIOD => CLK_PERIOD,
         PTRN_STEP_PERIOD => PTRN_STEP_PERIOD
      )

      port map (
         CLK => CLK,
         RESET => RESET,

         STATE_CHANGE => state_change,
         PWM_YELLOW_SYNC => pwm_yellow_sync
      );

   --! LED controlers for each LED
   led_ctrl_gen : for x in 0 to LED_COUNT - 1 generate
      led_ctrl_i: entity work.led_ctrl
         generic map (
            ON_VALUE => ON_VALUE,
            PTRN_LENGTH => PTRN_LENGTH
         )

         port map (
            CLK => CLK,
            RESET => RESET,

            STATE_CHANGE => state_change,
            PWM_YELLOW_SYNC => pwm_yellow_sync,

            PTRN => PTRNS (2*(x+1)*PTRN_LENGTH-1 downto 2*x*PTRN_LENGTH),

            LED_GREEN => LED_GREEN(x),
            LED_RED => LED_RED(x)
         );
   end generate;

end led_ctrl_top_arch;
