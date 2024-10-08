-- pulse_short.vhd: creates one short pulse with one clock period duration
-- Copyright (c) 2021 CESNET z.s.p.o.
-- Author: Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------

-- This component allows to shorten arbitrary long pulse on the input
-- :vhdl:portsignal:`TRIGGER <PULSE_SHORT.TRIGGER>` to only one clock period
-- short pulse (driven by the :vhdl:portsignal:`BCLK <PULSE_SHORT.BCLK>`).
-- Outuput pulse can be arbirarily delayed when :vhdl:genconstant:`DELAY_COUNT
-- <PULSE_SHORT.DELAY_COUNT>` constant is set. Optional CDC could be applied on
-- control inputs by setting specific bits in the :vhdl:genconstant:`ASYNC_MASK
-- <PULSE_SHORT.ASYNC_MASK>` generic constant.
entity PULSE_SHORT is

    generic (
        -- Controls for how much clock cycles should the output be delayed.
        -- Maximum value is 1 048 575 because I don't think you need to
        -- delay one pulse even for that long
        DELAY_COUNT : natural := 0;

        -- controls whether specific input should be connected throgh clock
        -- domain crossings:
        -- bit 0 -> RST,
        -- bit 1 -> EN,
        -- bit 2 -> TRIGGER
        ASYNC_MASK : std_logic_vector(2 downto 0) := "000"
        );

    port (
        -- Input clock, usage is optional but needs to be used when some
        -- bit in the ASYNC_MASK generic parameter is set to 1
        ACLK      : in  std_logic := '0';
        BCLK      : in  std_logic;      -- Output clock
        RST       : in  std_logic;      -- Reset signal
        EN        : in  std_logic := '1';  -- Enable signal, usage is optional
        TRIGGER   : in  std_logic;      -- Input triggering pulse
        PULSE_OUT : out std_logic  -- Output pulse with one BCLK period duration
        );

end entity;

-------------------------------------------------------------------------------

architecture FULL of PULSE_SHORT is

    constant DELAY_COUNTER_LENGTH : natural range 1 to 20 := 20;

    -- if component is in idle state
    signal idle : std_logic := '1';

    signal del_cntr       : unsigned(DELAY_COUNTER_LENGTH-1 downto 0);
    signal counter_trigg  : std_logic;
    type del_cntr_state_type is (WT_FOR_CNTR_TRIGGER, CNT_DELAY);
    signal del_cntr_state : del_cntr_state_type := WT_FOR_CNTR_TRIGGER;

    signal rst_sync     : std_logic;
    signal en_sync      : std_logic;
    signal trigger_sync : std_logic;

begin  -- architecture str

    cdc_rst_g : if (ASYNC_MASK(0) = '1') generate

        cdc_rst_i : entity work.ASYNC_RESET
            generic map (TWO_REG => FALSE, OUT_REG => TRUE, REPLICAS => 0)
            port map (CLK        => BCLK, ASYNC_RST => RST, OUT_RST(0) => rst_sync);

    else generate
        rst_sync <= RST;
    end generate;

    cdc_en_g : if (ASYNC_MASK(1) = '1') generate

        cdc_en_i : entity work.ASYNC_OPEN_LOOP
            generic map (IN_REG => FALSE, TWO_REG => TRUE)
            port map (ADATAIN   => EN, BCLK => BCLK, BDATAOUT => en_sync);

    else generate
        en_sync <= EN;
    end generate;

    cdc_trigger_g : if (ASYNC_MASK(2) = '1') generate

        ASYNC_GENERAL_1 : entity work.ASYNC_GENERAL
            generic map (
                TWO_REG             => FALSE,
                DETECT_RISING_EDGE  => TRUE,
                DETECT_FALLING_EDGE => FALSE)
            port map (
                ACLK     => ACLK,
                ARST     => RST,
                ADATAIN  => TRIGGER,
                AREADY   => open,
                BCLK     => BCLK,
                BRST     => '0',
                BDATAOUT => trigger_sync);

    else generate
        trigger_sync <= TRIGGER;
    end generate;

    del_cntr_g : if (DELAY_COUNT = 0) generate

        PULSE_OUT <= counter_trigg;

    elsif (DELAY_COUNT = 1) generate

        -- purpose: delays output pulse by one clock period
        -- type   : sequential
        del_out_pulse_p: process (BCLK) is
        begin  -- process del_out_pulse_p
            if (rising_edge(BCLK)) then  -- rising clock edge

                PULSE_OUT <= counter_trigg;

            end if;
        end process;

    else generate

        -- purpose: counts the delay in which the input pulse should be delayed
        -- type   : sequential
        del_cntr_p : process (BCLK) is
        begin  -- process del_cntr_p
            if (rising_edge(BCLK)) then  -- rising clock edge

                PULSE_OUT <= '0';

                if (rst_sync = '1') then  -- synchronous reset (active high)

                    del_cntr_state <= WT_FOR_CNTR_TRIGGER;

                else
                    case del_cntr_state is

                        -- this state waits for trigger from short_by_trigg_p
                        when WT_FOR_CNTR_TRIGGER =>

                            if (counter_trigg = '1') then

                                del_cntr_state <= CNT_DELAY;
                                del_cntr       <= (others => '0');

                            end if;

                        -- this state counts the delay of the input pulse
                        when CNT_DELAY =>

                            del_cntr <= del_cntr + 1;

                            if (del_cntr = (DELAY_COUNT - 2)) then

                                del_cntr_state <= WT_FOR_CNTR_TRIGGER;
                                PULSE_OUT      <= '1';

                            end if;

                        when others => null;

                    end case;

                end if;
            end if;
        end process;

    end generate;

    -- purpose: two-state state machine which waits for trigger set and then waits for trigger deassert
    -- type   : sequential
    short_by_trigg_p : process (BCLK) is
    begin  -- process short_by_trigg_g
        if (rising_edge(BCLK)) then     -- rising clock edge

            counter_trigg <= '0';

            if (rst_sync = '1') then    -- synchronous reset (active high)

                idle <= '1';

            elsif (en_sync = '1') then

                if (idle = '1') then

                    -- waits for rising edge of the trigger
                    if (trigger_sync = '1') then

                        idle          <= '0';
                        counter_trigg <= '1';

                    end if;

                else

                    -- waits for falling edge of the trigger
                    if (trigger_sync = '0') then
                        idle <= '1';
                    end if;

                end if;

            end if;
        end if;
    end process;

end architecture;
-------------------------------------------------------------------------------
