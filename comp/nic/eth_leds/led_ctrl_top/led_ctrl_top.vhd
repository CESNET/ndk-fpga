-- led_ctrl_top.vhd: ETH LED controller
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity ETH_LED_CTRL_TOP is
generic (
    ETH_PORTS      : natural := 2;
    ETH_CHANNELS   : natural := 4;
    LEDS_PER_PORT  : natural := 1;
    SYS_CLK_PERIOD : natural := 5;
    LED_ON_VAL     : std_logic := '1'
);
port (
    ETH_CLK          : in  std_logic_vector(ETH_PORTS-1 downto 0);
    SYS_CLK          : in  std_logic;
    SYS_RESET        : in  std_logic;

    ETH_RX_LINK_UP   : in  std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    ETH_RX_ACTIVITY  : in  std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    ETH_TX_ACTIVITY  : in  std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    ETH_PORT_ENABLED : in  std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    ETH_MODPRS_N     : in  std_logic_vector(ETH_PORTS-1 downto 0);

    ETH_LED_G        : out std_logic_vector(ETH_PORTS*LEDS_PER_PORT-1 downto 0);
    ETH_LED_R        : out std_logic_vector(ETH_PORTS*LEDS_PER_PORT-1 downto 0)
);
end entity;

architecture FULL of ETH_LED_CTRL_TOP is

    constant PWM_STEP  : natural := 16/ETH_CHANNELS;
    constant PWM_START : unsigned(4-1 downto 0) := (others => '1');

    signal s_eth_rx_act_sync : std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    signal s_eth_tx_act_sync : std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    signal s_led_r           : std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    signal s_led_g           : std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    signal s_led_sync        : std_logic_vector(ETH_PORTS*ETH_CHANNELS-1 downto 0);
    signal s_led_mux_sel     : u_array_t(ETH_PORTS-1 downto 0)(log2(ETH_CHANNELS)-1 downto 0);
    signal s_led_pwm         : slv_array_t(ETH_CHANNELS-1 downto 0)(4-1 downto 0);
    signal s_eth_led_g       : std_logic_vector(ETH_PORTS*LEDS_PER_PORT-1 downto 0);
    signal s_eth_led_r       : std_logic_vector(ETH_PORTS*LEDS_PER_PORT-1 downto 0);

begin

    process(all)
    begin
        for i in 0 to ETH_CHANNELS-1 loop
            s_led_pwm(i) <= std_logic_vector(PWM_START - (i*PWM_STEP));
        end loop;
    end process;

    ports_g : for p in 0 to ETH_PORTS-1 generate
        chan_g : for i in 0 to ETH_CHANNELS-1 generate
            rx_act_sync_i: entity work.ASYNC_GENERAL
            generic map (
                DETECT_RISING_EDGE  => false,
                DETECT_FALLING_EDGE => false
            )
            port map (
                ACLK        => ETH_CLK(p),
                ARST        => '0',
                ADATAIN     => ETH_RX_ACTIVITY(p*ETH_CHANNELS+i),
                AREADY      => open,
                BCLK        => SYS_CLK,
                BRST        => SYS_RESET,
                BDATAOUT    => s_eth_rx_act_sync(p*ETH_CHANNELS+i)
            );

            tx_act_sync_i: entity work.ASYNC_GENERAL
            generic map (
                DETECT_RISING_EDGE  => false,
                DETECT_FALLING_EDGE => false
            )
            port map (
                ACLK        => ETH_CLK(p),
                ARST        => '0',
                ADATAIN     => ETH_TX_ACTIVITY(p*ETH_CHANNELS+i),
                AREADY      => open,
                BCLK        => SYS_CLK,
                BRST        => SYS_RESET,
                BDATAOUT    => s_eth_tx_act_sync(p*ETH_CHANNELS+i)
            );

            led_ctrl_i: entity work.LED_CTRL_ADV
            generic map (
                CLK_PERIOD => SYS_CLK_PERIOD,
                ON_VAL     => LED_ON_VAL
            )
            port map (
                CLK         => SYS_CLK,
                PRESENT     => '1',
                ENABLED     => ETH_PORT_ENABLED(p*ETH_CHANNELS+i),
                LINE_UP     => ETH_RX_LINK_UP(p*ETH_CHANNELS+i),
                RX_ACTIVITY => s_eth_rx_act_sync(p*ETH_CHANNELS+i),
                TX_ACTIVITY => s_eth_tx_act_sync(p*ETH_CHANNELS+i),
                MOD_ABS     => ETH_MODPRS_N(p),
                MOD_RX_LOS  => '1',
                INTENSITY_R => s_led_pwm(i),
                INTENSITY_G => s_led_pwm(i),
                LED_RED     => s_led_r(p*ETH_CHANNELS+i),
                LED_GREEN   => s_led_g(p*ETH_CHANNELS+i),
                SYNC        => s_led_sync(p*ETH_CHANNELS+i)
            );
        end generate;

        process(SYS_CLK)
        begin
            if rising_edge(SYS_CLK) then
                if (s_led_sync(p*ETH_CHANNELS) = '1') then
                    s_led_mux_sel(p) <= s_led_mux_sel(p) + 1;
                end if;
                if (SYS_RESET = '1') then
                    s_led_mux_sel(p) <= (others => '0');
                end if;
            end if;
        end process;

        process(all)
        begin
            s_eth_led_r((p+1)*LEDS_PER_PORT-1 downto p*LEDS_PER_PORT) <= (others => not LED_ON_VAL);
            s_eth_led_g((p+1)*LEDS_PER_PORT-1 downto p*LEDS_PER_PORT) <= (others => not LED_ON_VAL);

            if (LEDS_PER_PORT < ETH_CHANNELS) then
                -- Multiplex all ETH channels to all port LEDs
                for i in 0 to LEDS_PER_PORT-1 loop
                    s_eth_led_r(p*LEDS_PER_PORT+i) <= s_led_r(to_integer(s_led_mux_sel(p)));
                    s_eth_led_g(p*LEDS_PER_PORT+i) <= s_led_g(to_integer(s_led_mux_sel(p)));
                end loop;
            end if;

            if (LEDS_PER_PORT >= ETH_CHANNELS) then
                -- One LED per ETH channel
                for i in 0 to ETH_CHANNELS-1 loop
                    s_eth_led_r(p*LEDS_PER_PORT+i) <= s_led_r(p*ETH_CHANNELS+i);
                    s_eth_led_g(p*LEDS_PER_PORT+i) <= s_led_g(p*ETH_CHANNELS+i);
                end loop;
            end if;
        end process;

    end generate;

    process(SYS_CLK)
    begin
        if rising_edge(SYS_CLK) then
            ETH_LED_R <= s_eth_led_r;
            ETH_LED_G <= s_eth_led_g;
        end if;
    end process;

end architecture;
