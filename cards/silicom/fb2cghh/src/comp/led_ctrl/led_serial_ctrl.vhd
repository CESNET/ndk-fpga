-- led_serial_ctrl.vhd: Serial LED controller for TLC5916 LED Driver
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <benes.david2000@seznam.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

entity LED_SERIAL_CTRL is
    generic (
        -- Number of LED´s
        LED_W          : natural   := 16;
        -- CLK divider ratio - chosen value must be even in order of keeping LED_CLK symmetrical, minimal value is 4
        FREQ_DIV       : natural   := 10;
        -- Invert polarity by switching POLARITY value
        LED_POLARITY   : std_logic := '1';
        -- 16 bit timeout, Forces update of LEDs
        CNT_TIMEOUT    : unsigned(15 downto 0) := (others => '1')
    );
    port (
        CLK            : in  std_logic;
        RST            : in  std_logic;
        -- Input signals
        GREEN_LED      : in  std_logic_vector(LED_W-1 downto 0);
        RED_LED        : in  std_logic_vector(LED_W-1 downto 0);
        -- Serial-data output to the Shift register
        LED_SDI        : out std_logic;
        -- Clock output for data shift on rising edge - Max 25 MHz
        LED_CLK        : out std_logic;
        -- Serial data transfer is complete when LED_LE is high
        LED_LE         : out std_logic
    );
end LED_SERIAL_CTRL;

architecture FULL of LED_SERIAL_CTRL is

    constant CNT_W      : natural := log2(LED_W);
    constant TIMER_W    : natural := log2(FREQ_DIV);

    type t_fsm_led_ctrl is (
                            st_idle,       -- idle state, waiting for LED to change
                            st_red,        -- sending serial data to LED_SDI (red LED)
                            st_green,      -- sending serial data to LED_SDI (green LED)
                            st_eos         -- end of sequence  
                           );       

    -- Control logic (FSM)
    signal state, next_state: t_fsm_led_ctrl := st_idle;

    -- Synchronization
    signal red_led_sync            : std_logic_vector(LED_W-1 downto 0) := (others => '0');
    signal green_led_sync          : std_logic_vector(LED_W-1 downto 0) := (others => '0');

    -- Registers for LED change detection
    signal red_led_d               : std_logic_vector(LED_W-1 downto 0) := (others => '0');
    signal green_led_d             : std_logic_vector(LED_W-1 downto 0) := (others => '0');
    signal red_led_q               : std_logic_vector(LED_W-1 downto 0) := (others => '0');
    signal green_led_q             : std_logic_vector(LED_W-1 downto 0) := (others => '0');

    -- Counter registers 
    signal led_cnt                  : unsigned(CNT_W - 1 downto 0) := (others => '0');
    signal led_cnt_next             : unsigned(CNT_W - 1 downto 0) := (others => '0');

    -- Output registers
    signal led_le_d                 : std_logic; 
    signal led_le_q                 : std_logic;
    signal led_sdi_d                : std_logic; 
    signal led_sdi_q                : std_logic;
    signal sdi_out_d                : std_logic;
    signal sdi_out_q                : std_logic;
    signal le_out_d                 : std_logic;
    signal le_out_q                 : std_logic;

    --Timer related signals
    signal cnt                      : unsigned(TIMER_W - 1 downto 0) := (others => '0');
    signal led_update               : std_logic;
    signal led_en                   : std_logic;   
    
    --Timeout 
    signal timeout_cnt              : unsigned(15 downto 0) := CNT_TIMEOUT;
    signal timeout_event            : std_logic;



begin
    -----------------------------------------------------------------------------
    --                          SYNCHRONIZATION
    -----------------------------------------------------------------------------
    sync_gen: for i in 0 to LED_W -1 generate

        red_sync_i: entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG   => false,
            TWO_REG  => true
        )
        port map(
            --INPUT
            ACLK     => '0',
            ARST     => '0',
            ADATAIN  => RED_LED(i),
            
            --OUTPUT
            BCLK     => CLK,
            BRST     => RST,
            BDATAOUT => red_led_sync(i)
        );
        
        green_sync_i: entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG   => false,
            TWO_REG  => true
        )
        port map(
            --INPUT 
            ACLK     => '0',
            ARST     => '0',
            ADATAIN  => GREEN_LED(i),
            
            --OUTPUT
            BCLK     => CLK,
            BRST     => RST,
            BDATAOUT => green_led_sync(i)
        );

    end generate sync_gen;
    -----------------------------------------------------------------------------
    --                          SEQUENTIAL PART
    -----------------------------------------------------------------------------

    mem_p: process (clk)
    begin 
        if rising_edge(clk) then
            if RST = '1' then
                state             <= st_idle;
                led_cnt           <= (others => '0'); 
                green_led_q       <= (others => '0'); 
                red_led_q         <= (others => '0'); 
                led_sdi_q         <= '0';
                sdi_out_q         <= '0';
                led_le_q          <= '0';
                le_out_q          <= '0';
            else
                state             <= next_state;
                led_cnt           <= led_cnt_next;
                green_led_q       <= green_led_d;
                red_led_q         <= red_led_d;
                led_sdi_q         <= led_sdi_d;
                sdi_out_q         <= sdi_out_d;
                led_le_q          <= led_le_d;
                le_out_q          <= le_out_d;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                         COMBINATIONAL PART
    -----------------------------------------------------------------------------
    sdi_out_d       <= led_sdi_q xor LED_POLARITY;
    le_out_d        <= led_le_q;
    LED_SDI         <= sdi_out_q;
    LED_LE          <= le_out_q;
   
    fsm_p: process(state, led_update, red_led_sync, green_led_sync, red_led_d, green_led_d, 
                   led_cnt, red_led_q, green_led_q, led_le_q, led_sdi_q, timeout_event)
    begin
        next_state   <= state;
        green_led_d  <= green_led_q;
        red_led_d    <= red_led_q;
        led_sdi_d    <= led_sdi_q;
        led_cnt_next <= led_cnt;
        led_le_d     <= '0';
        led_en       <= '0';

        case(state) is
            when st_idle   =>
                if led_update = '1' then 
                    red_led_d    <= red_led_sync;
                    green_led_d  <= green_led_sync;

                    if (red_led_sync /= red_led_q) or (green_led_sync /= green_led_q) or timeout_event = '1' then
                       next_state <= st_red;
                    end if;          
                end if;

            when st_red    =>
                led_sdi_d   <= red_led_q(  to_integer(led_cnt));
                led_en      <= '1';                

                if led_update = '1' then
                    next_state  <= st_green;
                end if;

            when st_green  =>
                led_sdi_d   <= green_led_q(to_integer(led_cnt));
                led_en      <= '1';

                if led_update = '1' then
                    if led_cnt < LED_W - 1 then
                        led_cnt_next    <= led_cnt + 1;
                        next_state      <= st_red;
                    else
                        led_cnt_next    <= (others => '0');
                        next_state      <= st_eos;
                        led_sdi_d       <= '0';
                    end if;

                end if;

            when st_eos    =>
                led_le_d    <= '1';

                if led_update = '1' then 
                    next_state  <= st_idle;
                end if;

            when others    =>
                next_state  <= st_idle;

        end case;
    end process;

    -----------------------------------------------------------------------------
    --                                  TIMER
    -----------------------------------------------------------------------------

    divider_p: process (CLK)
    begin
        if rising_edge(CLK) then
            cnt         <= cnt + 1;
            led_update  <= '0';

            if RST = '1' then
                cnt         <= (others => '0');
                led_update  <= '0';
            elsif (cnt =  FREQ_DIV - 1) then
                cnt         <= (others => '0');
                led_update  <= '1';
            elsif cnt = (FREQ_DIV/2) and led_en = '1' then
                LED_CLK   <= '1';
            elsif cnt = 0 then 
                LED_CLK   <= '0';
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                                  TIMEOUT
    -----------------------------------------------------------------------------

    timeout_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                timeout_event   <= '0';
                timeout_cnt     <= (others => '0');
            elsif state = st_idle then
                timeout_cnt     <= timeout_cnt - 1;

                if timeout_cnt = 0 then 
                    timeout_event   <= '1';
                    timeout_cnt     <= CNT_TIMEOUT;
                end if;
            else 
                timeout_event   <= '0';
                timeout_cnt     <= CNT_TIMEOUT;
            end if;
        end if;
    end process;
    
end architecture;