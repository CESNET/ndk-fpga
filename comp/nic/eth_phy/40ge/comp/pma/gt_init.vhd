-- gt_init.vhd : Transceivers initialization and watchdog state machine
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;


entity gt_init is
    generic (
        TX_TIMER_MAX  : natural :=  3750000; -- ~ 30ms @ 125 MHz CLK
        RX_TIMER_MAX  : natural := 16250000  -- ~130ms @ 125 MHz CLK
    );
    port (
        CLK           : in  std_logic; -- Stable free-running clock
        RESET         : in  std_logic; -- Global reset, async
        TX_INIT_DONE  : in  std_logic; -- GT TX init done
        RX_INIT_DONE  : in  std_logic; -- GT RX init done
        RX_DATA_OK    : in  std_logic; -- Received data ok (from decoder)
        RESET_OUT     : out std_logic; -- Reset TX + RX
        RXRESET_OUT   : out std_logic; -- RX reset
        INIT_DONE     : out std_logic  -- All OK
    );
end gt_init;

architecture behavioral of gt_init is

type t_init_fsm_state is (START, TX_WAIT, RX_WAIT, DONE);
signal state : t_init_fsm_state := START;

signal reset_sync        : std_logic;
signal tx_init_done_sync : std_logic;
signal rx_init_done_sync : std_logic;
signal rx_data_ok_sync   : std_logic;

signal cntr_clr          : std_logic;
signal cntr              : unsigned(26 downto 0) := (others => '0');
signal tx_timer_done     : std_logic;
signal rx_timer_done     : std_logic;

begin

rst_sync_i: entity work.ASYNC_RESET
generic map(
   TWO_REG => false
)
port map(
   CLK        => CLK,
   ASYNC_RST  => RESET,
   OUT_RST(0) => reset_sync
);

txinit_sync_i : entity work.ASYNC_OPEN_LOOP
generic map (
    IN_REG  => false,
    TWO_REG => false
) port map (
    ADATAIN  => TX_INIT_DONE,
    BCLK     => CLK,
    BRST     => '0',
    BDATAOUT => tx_init_done_sync
);

rxinit_sync_i : entity work.ASYNC_OPEN_LOOP
generic map (
    IN_REG  => false,
    TWO_REG => false
) port map (
    ADATAIN  => RX_INIT_DONE,
    BCLK     => CLK,
    BRST     => '0',
    BDATAOUT => rx_init_done_sync
);

rxdataok_sync_i : entity work.ASYNC_OPEN_LOOP
generic map (
    IN_REG  => false,
    TWO_REG => false
) port map (
    ADATAIN  => RX_DATA_OK,
    BCLK     => CLK,
    BRST     => '0',
    BDATAOUT => rx_data_ok_sync
);

-- Timer and timer done logic
timer_p: process(CLK)
begin
    if rising_edge(CLK) then
        if cntr_clr = '1' then
            cntr <= (others => '0');
            tx_timer_done <= '0';
            rx_timer_done <= '0';
        else
            cntr <= cntr + 1;
        end if;
        if cntr = to_unsigned(TX_TIMER_MAX, cntr'length) then
            tx_timer_done <= '1';
        end if;
        if cntr = to_unsigned(RX_TIMER_MAX, cntr'length) then
            rx_timer_done <= '1';
        end if;
    end if;

end process;

init_fsm: process(CLK)
begin
    if rising_edge(CLK) then
        cntr_clr    <= '0';
        RESET_OUT   <= '0';
        RXRESET_OUT <= '0';
        INIT_DONE   <= '0';

        case state is

            when START =>
                cntr_clr    <= '1';
                state       <= TX_WAIT;
            -- Wait for TX start
            when TX_WAIT =>
                if tx_init_done_sync = '1' then
                    cntr_clr  <= '1';
                    state     <= RX_WAIT;
                elsif tx_timer_done = '1' then -- TX timer out: retry the whole startup process
                    cntr_clr  <= '1';
                    RESET_OUT <= '1';
                    state     <= START;
                end if;
            -- Wait for RX init done and data OK
            when RX_WAIT =>
                if (rx_timer_done = '1') then
                    if (rx_init_done_sync = '1') and (rx_data_ok_sync = '1') then
                        state     <= DONE;
                    else -- RX timer expired: reset RX and retry the startup process
                       cntr_clr    <= '1';
                       RXRESET_OUT <= '1';
                       state       <= START;
                    end if;
                end if;
            -- Done, continue monitoring RX and reset RX in case of an error
            when DONE =>
                INIT_DONE   <= '1';
                if (rx_init_done_sync = '0') or (rx_data_ok_sync = '0') then
                    cntr_clr <= '1';
                    RXRESET_OUT <= '1';
                    state <= START;
                end if;
        end case;

        if reset_sync = '1' then
            state <= START;
        end if;
    end if;
end process;

end behavioral;
