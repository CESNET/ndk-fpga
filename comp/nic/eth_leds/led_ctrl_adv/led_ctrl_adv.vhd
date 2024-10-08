-- led_ctrl_adv.vhd: Advanced LED link status controler
-- Copyright (C) 2015 CESNET
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Advanced LED link status controler features:
-- 1. interface not implemented - both leds OFF
-- 2. line down, optical module not present - alternating red + off
-- 3. line down, optical signal detected - red + short green pulse
-- 4. line down - red
-- 5. line up, not enabled - yellow
-- 6. line up, enabled, no activity - green
-- 7. line up, enabled, RX activity - green blink
-- 8. line up, enabled, TX activity - yellow blink
-- 9. line up, enabled, TX+RX activity - alternating green and yellow
--
entity LED_CTRL_ADV is
   generic (
      -- Length of the internal counter, determines period of blinks
      -- CLK Period in ns
      CLK_PERIOD        : natural   := 8;
      -- LED On value ('0' or '1')
      ON_VAL            : std_logic := '0'
   );
   port (
      -- Clock signal
      CLK                  : in std_logic;

      -- interface present (MAC, PMA and PCS implemented, at least one of RX or TX directions)
      PRESENT              : in std_logic;
      -- interface enabled by software, async
      ENABLED              : in std_logic;
      -- '1' when coresponding PCS line is up, '0' otherwise, async
      LINE_UP              : in std_logic;
      -- RX acitivity, CLK synchronous pulse !!!
      RX_ACTIVITY          : in std_logic;
      -- TX acitivity, CLK synchronous pulse !!!
      TX_ACTIVITY          : in std_logic;
      -- optical module absent, async
      MOD_ABS              : in std_logic;
      -- optical module RX signal loss, async
      MOD_RX_LOS           : in std_logic;

      -- red LED intesity (PWM): "0000" = almost off, "1111" = full
      INTENSITY_R          : in std_logic_vector(3 downto 0) := "1111";
      -- green LED intesity (PWM): "0000" = almost off, "1111" = full
      INTENSITY_G          : in std_logic_vector(3 downto 0) := "1111";
      --
      LED_RED              : out std_logic;
      LED_GREEN            : out std_logic;
      -- One-cycle pulse synchronization
      SYNC                 : out std_logic
   );

end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ADVANCED of LED_CTRL_ADV is

   constant C_100MILISEC : natural := 50000000/CLK_PERIOD;

   type t_activity_state is (IDLE, RX_TX_ACT, RX_ACT, TX_ACT);

   signal activity_state : t_activity_state;

   constant ptrn_length : natural := 16;

   constant C_ON      : std_logic_vector(ptrn_length-1 downto 0) := "1111111111111111";
   constant OFF       : std_logic_vector(ptrn_length-1 downto 0) := "0000000000000000";
   constant ON_BLINK  : std_logic_vector(ptrn_length-1 downto 0) := "0111111111111111";
   constant OFF_BLINK : std_logic_vector(ptrn_length-1 downto 0) := "1000000000000000";
   constant ON_OFF    : std_logic_vector(ptrn_length-1 downto 0) := "1111111100000000";
   constant BLINK     : std_logic_vector(ptrn_length-1 downto 0) := "1111000011110000";
   constant BLINK_1   : std_logic_vector(ptrn_length-1 downto 0) := "1111000000000000";
   constant BLINK_2   : std_logic_vector(ptrn_length-1 downto 0) := "0000000011110000";


   signal green_mode  : std_logic_vector(ptrn_length-1 downto 0);
   signal red_mode    : std_logic_vector(ptrn_length-1 downto 0);

   signal enabled_sync    : std_logic;
   signal line_up_sync    : std_logic;
   signal mod_abs_sync    : std_logic;
   signal mod_rx_los_sync : std_logic;

   signal led_stat        : std_logic_vector(1 downto 0);

   signal time_cntr   : std_logic_vector(25 downto 0);
   signal state_cycle : natural range 0 to ptrn_length-1;
   signal led_cycle   : natural range 0 to ptrn_length-1;
   signal pwm_on_r    : std_logic;
   signal pwm_on_g    : std_logic;

begin

   SYNC_ENABLED: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG => false, TWO_REG => true)
   port map( ADATAIN => ENABLED, BCLK => CLK, BDATAOUT => enabled_sync);

   SYNC_LINE_UP: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG => false, TWO_REG => true)
   port map( ADATAIN => LINE_UP, BCLK => CLK, BDATAOUT => line_up_sync);

   SYNC_MOD_ABS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG => false, TWO_REG => true)
   port map( ADATAIN => MOD_ABS, BCLK => CLK, BDATAOUT => mod_abs_sync);

   SYNC_RX_LOS: entity work.ASYNC_OPEN_LOOP
   generic map(IN_REG => false, TWO_REG => true)
   port map( ADATAIN => MOD_RX_LOS, BCLK => CLK, BDATAOUT => mod_rx_los_sync);

   -- Priorities:
   -- 1. not implemented
   -- 2. Line UP/DOWN
   -- 3. Transceiver present
   -- 4. Optical signal detected
   -- 5. Interface enabled
   -- 6. RX activity, TX activity

   CONTROL: process(CLK)
   begin

      if rising_edge(CLK) then

         SYNC <= '0';

         if time_cntr = C_100MILISEC then

            time_cntr <= (others => '0');

            if (state_cycle = ptrn_length-1) then
               state_cycle <= 0;
            else
               state_cycle <= state_cycle + 1;
            end if;

            if (led_cycle = ptrn_length-1) then
               led_cycle <= 0;
               SYNC <= '1';
            else
               led_cycle <= led_cycle + 1;
            end if;

         else
            time_cntr <= time_cntr + 1;
         end if;

         -----------------------------------------------------------------------
         -- Main logic for link state indication
         -----------------------------------------------------------------------
         if (PRESENT = '0') then -- Interface not present - turn off all LEDs
            green_mode  <= OFF;
            red_mode    <= OFF;

         elsif (line_up_sync = '0') then -- Line up DOWN -

            if (mod_rx_los_sync = '1') and (mod_abs_sync = '1') then    -- Module not plugged and no signal - alternating red and off
               red_mode    <= ON_OFF;
               green_mode  <= OFF;
            elsif (mod_rx_los_sync = '1') and (mod_abs_sync = '0') then -- Module plugged, no signal - red
               red_mode    <= C_ON;
               green_mode  <= OFF;
            else                                            -- Signal detected - Short green pulse in red
               red_mode    <= ON_BLINK;
               green_mode  <= OFF_BLINK;
            end if;
         else -- line is UP
            activity_state <= IDLE;
            if (enabled_sync = '0') then -- interface is disabled - yellow
               green_mode  <= C_ON;
               red_mode    <= C_ON;
            else

               case activity_state is

                  when IDLE => -- no RX nor TX activity, green
                     green_mode  <= C_ON;
                     red_mode    <= OFF;
                     if    (RX_ACTIVITY = '1') and (TX_ACTIVITY = '1') then
                        activity_state <= RX_TX_ACT;
                        state_cycle <= 0;
                     elsif (RX_ACTIVITY = '1') and (TX_ACTIVITY = '0') then
                        activity_state <= RX_ACT;
                        state_cycle <= 0;
                     elsif (TX_ACTIVITY = '1') then
                        activity_state <= TX_ACT;
                        state_cycle <= 0;
                     else
                        activity_state <= IDLE;
                     end if;

                  when RX_TX_ACT =>  -- Both RX and TX active
                     green_mode <= BLINK;
                     red_mode   <= BLINK_1;

                     if state_cycle = ptrn_length-1 then
                        activity_state <= IDLE;
                     else
                        activity_state <= RX_TX_ACT;
                     end if;

                  when RX_ACT =>  -- RX is active - green blink
                     green_mode <= BLINK;
                     red_mode   <= OFF;

                     if state_cycle = ptrn_length-1 then
                        activity_state <= IDLE;
                     elsif (TX_ACTIVITY = '1') then
                        activity_state <= RX_TX_ACT;
                        -- state_cycle <= 0; -- If the TX pulse needs to be enlarged
                     else
                        activity_state <= RX_ACT;
                     end if;

                  when TX_ACT =>  -- RX is active - yellow blink
                     green_mode  <= BLINK;
                     red_mode    <= BLINK;

                     if state_cycle = ptrn_length-1 then
                        activity_state <= IDLE;
                     elsif (RX_ACTIVITY = '1') then
                        activity_state <= RX_TX_ACT;
                        -- state_cycle <= 0; -- Uncomment If the RX pulses needs to be enlarged
                     else
                        activity_state <= TX_ACT;
                     end if;
                  end case;

            end if; -- enabled
         end if;  -- present, line up

      end if;
   end process;

   led_stat <= green_mode(led_cycle) & red_mode(led_cycle);

   LED_DRV_P: process(CLK)
   begin
      if (CLK'event and CLK='1') then

         case led_stat is
            when "00" =>  LED_GREEN <= not ON_VAL;    -- Both LEDs off
                          LED_RED   <= not ON_VAL;
            when "01" =>  LED_GREEN <= not ON_VAL;    -- RED
                          LED_RED   <= pwm_on_r;
            when "10" =>  LED_GREEN <= pwm_on_g;        -- GREEN
                          LED_RED   <= not ON_VAL;
            when "11" =>  -- YELLOW - alternate RED and GREEN (60 kHz pwm)
                          if time_cntr(17) = '1' then
                             LED_GREEN <= pwm_on_g;
                             LED_RED   <= not ON_VAL;
                          else
                             LED_RED   <= pwm_on_r;
                             LED_GREEN <= not ON_VAL;
                          end if;
            when others => LED_GREEN <= not ON_VAL;    -- Both LEDs off
                           LED_RED   <= not ON_VAL;
         end case;
       end if;
   end process;

   pwm_on_r <= ON_VAL when (time_cntr(16 downto 16-INTENSITY_R'high) <= INTENSITY_R) else (not ON_VAL);
   pwm_on_g <= ON_VAL when (time_cntr(16 downto 16-INTENSITY_G'high) <= INTENSITY_G) else (not ON_VAL);

end architecture;
