-- testbench.vhd: Testbench for block_lock.vhd
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use IEEE.math_real.all;

entity TESTBENCH is
end entity;

architecture behavioral of TESTBENCH is

    constant C_CLK_PER    : time := 10.0 ns;

    signal clk            : std_logic := '0';
    signal rst            : std_logic := '0';

    signal rx_header_in : std_logic_vector(1 downto 0) := "00";
    signal rx_header_valid : std_logic := '0';
    signal rx_lock_aquired : std_logic := '0';
    signal slip_command : std_logic := '0';

    signal tb1 : std_logic := '1';
    signal tb2 : std_logic := '0';
    signal tb3 : std_logic := '0';

begin

    clk_gen: process
    begin
       clk <= '1';
       wait for C_CLK_PER / 2;
       clk <= '0';
       wait for C_CLK_PER / 2;
    end process clk_gen;

    dut : entity work.BLOCK_LOCK
    generic map (
        SH_CNT_MAX => 64,
        SH_INVALID_CNT_MAX => 16,
        SLIP_WAIT_TIME => 32,
        SLIP_PULSE => true
    )
    port map (
        RX_HEADER_IN => rx_header_in,
        RX_HEADER_VALID => rx_header_valid,
        RX_LOCK_AQUIRED => rx_lock_aquired,
        CLK => clk,
        RST => rst,
        SLIP_CMD => slip_command
    );

    tb : process

        procedure send_header(header : std_logic_vector(1 downto 0); h_valid : std_logic) is
        begin
            rx_header_in <= header;
            rx_header_valid <= h_valid;
            wait for C_CLK_PER;
            rx_header_valid <= '0';
        end send_header;

        procedure reset is
        begin
            rst <= '1';
            wait for C_CLK_PER;
            rst <= '0';
            wait for C_CLK_PER;
        end reset;

    begin

        -- lock aquirement test
        reset;

        for i in 1 to 32 loop
            send_header("10", '1');
            send_header("01", '1');
        end loop;

        wait for C_CLK_PER; -- wait for changes
        reset;

        -- slip test
        for i in 1 to 8 loop
            send_header("10", '1');
        end loop;
        send_header("11", '1'); -- expect slip
        wait for C_CLK_PER*33;

        for i in 1 to 34 loop
            send_header("10", '1');
            send_header("01", '1');
        end loop; -- expect lock aquired

        wait for C_CLK_PER; -- wait for changes
        reset;

        -- invalid header tolerance test
        for i in 1 to 32 loop
            send_header("10", '1');
            send_header("01", '1');
        end loop;

        for i in 1 to 15 loop
            send_header("11", '1');
        end loop;
        for i in 1 to 49 loop
            send_header("01", '1');
        end loop;

        wait for C_CLK_PER; -- wait for changes
        reset;

        -- lock drop test
        for i in 1 to 32 loop
            send_header("10", '1');
            send_header("01", '1');
        end loop;

        for i in 1 to 25 loop
            send_header("00", '1');
        end loop;
        wait for C_CLK_PER*33;

        wait for C_CLK_PER;

        -- General test
        for i in 1 to 128 loop
            send_header("10", '1');
            send_header("00", '0');
            send_header("01", '0');
            send_header("01", '1');
        end loop;

        wait;

    end process;

end architecture behavioral;
