-- block_lock.vhd : Block synchronization component
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity BLOCK_LOCK is
    generic(
        -- number of correct headers to aquire lock, eg. number of sampled headers
        SH_CNT_MAX          : integer := 64;

        -- number of tolerated wrong headers in sampled header to drop the lock
        -- lock is dropped if this number of wrong headers is reached
        SH_INVALID_CNT_MAX  : integer := 16;

        -- number of clock cycles to wait for slip command to be completed
        SLIP_WAIT_TIME      : integer := 32;

        -- when true, SLIP_CMD is just one clock cycle at log. 1, otherwise
        -- is at log. 1 until SLIP_WAIT_TIME elapsed
        SLIP_PULSE          : boolean := true
    );
    port (
        -- header of recieved frame which is checked
        RX_HEADER_IN        : in std_logic_vector(1 downto 0);
        -- says if header should be counted
        RX_HEADER_VALID     : in std_logic;

        CLK                 : in std_logic;
        RST                 : in std_logic;

        -- set to 1 when lock was aquired
        RX_LOCK_AQUIRED     : out std_logic;
        -- request for slip, stays in logical '1' until signal SLIP_DONE is received
        SLIP_CMD            : out std_logic
    );
end entity;

architecture RTL of BLOCK_LOCK is

    type state is (INIT, RESET_CNT, TEST_SH, LOCK, SLIP);

    -- FSM signals
    signal curr_state           : state := INIT;
    signal next_state           : state;

    -- Counter signals
    -- shared count enable for all counters
    signal sh_cnt_en            : std_logic;

    signal sh_cnt               : unsigned(log2(SH_CNT_MAX) downto 0);
    signal sh_cnt_rst           : std_logic;

    signal sh_invalid_cnt       : unsigned(log2(SH_INVALID_CNT_MAX) downto 0);
    signal sh_invalid_cnt_rst   : std_logic;

    -- Set to logical '1' when RX_HEADER_IN is correct
    signal header_found         : std_logic;

    -- RX_LOCK_AQUIRED register
    signal rx_lock_aquired_r    : std_logic := '0';

    -- Shift register for slip wait time
    signal slip_wait_reg        : std_logic_vector(SLIP_WAIT_TIME - 1 downto 0);

    signal slip_cmd_sig         : std_logic;
    signal slip_cmd_reg         : std_logic;

begin

    -- FSM state process
    fsm_state_p : process(CLK, RST)
    begin
        if (RST = '1') then
            curr_state <= INIT;
        elsif rising_edge(CLK) then
            curr_state <= next_state;
        end if;
    end process;

    -- FSM next state logic
    fsm_next_state_logic_p : process(curr_state, RX_HEADER_VALID, header_found, sh_cnt, sh_invalid_cnt, rx_lock_aquired_r, RST, slip_wait_reg)
    begin
        case curr_state is
            when INIT =>
                next_state <= RESET_CNT;

            when RESET_CNT =>
                next_state <= TEST_SH;

            when TEST_SH =>
                next_state <= TEST_SH;
                if (RX_HEADER_VALID = '1') then
                    if (header_found = '1') then
                        if (sh_cnt = SH_CNT_MAX - 1) then
                            if (sh_invalid_cnt = 0) then
                                next_state <= LOCK;
                            else
                                next_state <= RESET_CNT;
                            end if;
                        end if;
                    else
                        if (sh_invalid_cnt = (SH_INVALID_CNT_MAX - 1) or (rx_lock_aquired_r = '0')) then
                            next_state <= SLIP;
                        elsif (sh_cnt = SH_CNT_MAX - 1) then
                            next_state <= RESET_CNT;
                        end if;
                    end if;
                end if;

            when LOCK =>
                next_state <= RESET_CNT;

            when SLIP =>
                next_state <= SLIP;
                if (slip_wait_reg(slip_wait_reg'high) = '1') then
                    next_state <= RESET_CNT;
                end if;
        end case;

    end process;

    -- FSM output logic
    fsm_output_logic_p : process(curr_state)
    begin
        sh_cnt_rst <= '0';
        sh_invalid_cnt_rst <= '0';
        sh_cnt_en <= '0';
        slip_cmd_sig <= '0';

        case curr_state is
            when INIT =>
                null;

            when RESET_CNT =>
                sh_cnt_rst <= '1';
                sh_invalid_cnt_rst <= '1';

            when TEST_SH =>
                sh_cnt_en <= '1';

            when LOCK =>
                null;

            when SLIP =>
                slip_cmd_sig <= '1';

        end case;

    end process;

    -- assign rx_lock_aquired_r to port
    RX_LOCK_AQUIRED <= rx_lock_aquired_r;

    -- comparison of headers
    header_found <= '1' when (RX_HEADER_IN = "10" or RX_HEADER_IN = "01") else '0';

    -- lock aquired register process
    rx_lock_aquired_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (curr_state = LOCK) then
                rx_lock_aquired_r <= '1';
            elsif (curr_state = INIT or curr_state = SLIP) then
                rx_lock_aquired_r <= '0';
            end if;
        end if;
    end process;

    -- counter counting number of incoming valid (RX_HEADER_VALID = '1') headers
    sh_cnt_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (sh_cnt_rst = '1') then
                sh_cnt <= (others => '0');
            elsif (sh_cnt_en = '1' and RX_HEADER_VALID = '1') then
                sh_cnt <= sh_cnt + 1;
            end if;
        end if;
    end process;

    -- counter of incorrect headers
    sh_invalid_cnt_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (sh_invalid_cnt_rst = '1') then
                sh_invalid_cnt <= (others => '0');
            elsif (sh_cnt_en = '1' and RX_HEADER_VALID = '1' and header_found = '0') then
                sh_invalid_cnt <= sh_invalid_cnt + 1;
            end if;
        end if;
    end process;

    -- shift register to wait for SLIP_WAIT_TIME cycles after slip command was set log. 1
    slip_wait_p : process(CLK, RST)
    begin
        if RST = '1' then
            slip_wait_reg <= (others => '0');
        elsif rising_edge(CLK) then
            if next_state = SLIP and slip_wait_reg = (slip_wait_reg'range => '0') then
                slip_wait_reg(0) <= '1';
            elsif not (slip_wait_reg = (slip_wait_reg'range => '0')) then
                slip_wait_reg <= slip_wait_reg(SLIP_WAIT_TIME - 2 downto 0) & '0';
            end if;
        end if;
    end process;

    -- if pulse on slip is needed, generate rising edge detector on slip_cmd_sig
    pulse_g : if SLIP_PULSE generate

        slip_cmd_p : process(CLK, RST, slip_cmd_sig)
        begin
            if RST = '1' then
                slip_cmd_reg <= '0';
            elsif rising_edge(CLK) then
                slip_cmd_reg <= slip_cmd_sig;
            end if;
        end process;

        SLIP_CMD <= slip_cmd_sig and not slip_cmd_reg;

    end generate;

    non_pulse_g : if not SLIP_PULSE generate
        SLIP_CMD <= slip_cmd_sig;
    end generate;

end architecture;
