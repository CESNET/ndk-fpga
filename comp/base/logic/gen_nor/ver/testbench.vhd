-- testbench.vhd: Testbench
-- Copyright (C) 2019 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;
use work.type_pack.all;
use work.math_pack.all;
use work.dma_bus_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

use work.test_pkg.all;

-- ----------------------------------------------------------------------------
--                                  Entity
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------

architecture full of testbench is

    -- Synchronization
    signal clk   : std_logic;

    -- uut I/O

    signal di : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '1');
    signal do : std_logic;

    -- tb signals and variables

    -- common tb variables

    shared variable l     : line;
    shared variable seed1 : positive := RAND_SEED+415;
    shared variable seed2 : positive := RAND_SEED+80;
    shared variable X     : integer;
    shared variable Y     : integer;

    -- tb functions and procedures

begin

    -- -------------------------------------------------------------------------
    -- UUT
    -- -------------------------------------------------------------------------

    uut : entity work.GEN_NOR
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        DEVICE     => DEVICE
    )
    port map (
        DI => di,
        DO => do
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen: process
    begin
        clk <= '1';
        wait for C_CLK_PER / 2;
        clk <= '0';
        wait for C_CLK_PER / 2;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- test processes
    -- -------------------------------------------------------------------------

    -- input driver
    in_driver_gen_pr : process(clk)
    begin
        if (rising_edge(clk)) then

            -- default values
            di <= random_vector(di'length,seed1);

            randint(seed1,seed2,0,99,X);

            if (X<ZEROES_CH) then
                di <= (others => '0');
            end if;
        end if;
    end process;
    ----

    -- output monitor
    out_monitor_gen_pr : process(clk)
    begin
        if (rising_edge(clk)) then

            if (do/=(nor di)) then
                write(l,string'("ERROR: incorrect result!"));
                writeline(output,l);
                stop(1);
            end if;

        end if;
    end process;
    ----

    -- verification ending
    ver_end_pr : process
    begin
        wait for VER_LENGTH*C_CLK_PER;
        write(l,string'(" : Verification finished Successfully!"));
        writeline(output,l);
        stop(0);
    end process;
    ----

end architecture;
