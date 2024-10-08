-- tsu_adder_common.vhd: TSU adder implemented in common logic (no DSPs).
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


architecture BEHAVIORAL of TSU_ADDER is

    signal rtr      : std_logic_vector(95 downto 0);
    signal write_en : std_logic;

    signal sum      : std_logic_vector(95 downto 0);

begin

    -- ========================================================================
    -- Input registers
    -- ========================================================================
    process (CLK)
    begin
        if rising_edge(CLK) then
            write_en <= REG_RTR_WE;
        end if;
    end process;

    rtr <= REG_RTR when write_en = '1' else sum;

    -- ========================================================================
    -- The addition
    -- ========================================================================
    process (CLK)
    begin
        if rising_edge(CLK) then
            sum <= std_logic_vector(unsigned(rtr) + unsigned(INCR_VALUE));
            if (RESET = '1') then
                sum <= (others => '0');
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Output registers
    -- ========================================================================
    process (CLK)
    begin
        if rising_edge(CLK) then
            ADD_RESULT <= sum;
            if (RESET = '1') then
                ADD_RESULT  <= (others => '0');
            end if;
        end if;
    end process;

end architecture;
