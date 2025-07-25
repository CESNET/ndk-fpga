--! pulse_extend.vhd: Extend one-cycle pulse to a N-cycle
--! Copyright (C) 2017 CESNET
--! Author(s): Stepan Friedl <friedl@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_misc.all;

entity PULSE_EXTEND is
    generic (
        N   : natural := 4 -- Number of clock cycles to which the input pulse should be extend
    );
    port (
        RST     : in  STD_LOGIC := '0'; -- synchronous reset, optional
        CLK     : in  STD_LOGIC;        -- clock
        I       : in  STD_LOGIC;        -- Pulse input
        O       : out STD_LOGIC         -- Output pulse, N clock cycles long
    );
end entity;

--! -------------------------------------------------------------------------
--!                      Architecture declaration
--! -------------------------------------------------------------------------

architecture BEHAVIORAL of PULSE_EXTEND is

    signal i_dly    : std_logic_vector(N-1 downto 0);
    attribute shreg_extract                : string;

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                i_dly <= (others => '0');
            else
                i_dly(0) <= I;
                for ii in 1 to N-1 loop
                    i_dly(ii) <= i_dly(ii-1);
                end loop;
                O <= OR_REDUCE(i_dly);
            end if;
        end if;
    end process;

end architecture;
