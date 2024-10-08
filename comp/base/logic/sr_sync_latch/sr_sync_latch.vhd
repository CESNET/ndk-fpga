-- sr_sync_latch.vhd: Pseudo RS latch which were made synchronous. .
-- Copyright (c) 2021 CESNET z.s.p.o.
-- Author: Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- This component provides synchrnous SR latch behavior with some enhancements:
--
-- 1. The forbidden state when both :vhdl:portsignal:`SET <SR_SYNC_LATCH.SET>` and
-- :vhdl:portsignal:`RESET <SR_SYNC_LATCH.RESET>` are asserted has been removed.
-- In this case, the design
-- behaves in the same way when both signals are deasserted, e.g. it keeps its
-- output unchanged.
--
-- 2. Data being latched could be set to arbitrary length so whole bus data can
-- be latched to the output.
--
-- 3. The design is driven by clock signal so it is not purely combinatorial
-- circuit. This is the advantage when meeting time closure.
entity SR_SYNC_LATCH is

    generic (
        -- Width of the data being latched.
        DATA_WIDTH : positive := 32
        );

    port (
        CLK       : in  std_logic;
        -- When asserted, the data from DATA_IN are latched to the output LATCH_OUT
        SET       : in  std_logic;
        -- When asserted, the data on the output LATCH_OUT are cleared.
        RESET     : in  std_logic;
        -- Input data to being latched, usage of this port is optional.
        DATA_IN   : in  std_logic_vector((DATA_WIDTH - 1) downto 0) := (others => '1');
        LATCH_OUT : out std_logic_vector((DATA_WIDTH - 1) downto 0)
        );

end entity;

architecture FULL of SR_SYNC_LATCH is

    signal latch_out_int : std_logic_vector((DATA_WIDTH - 1) downto 0) := (others => '0');

begin  -- architecture FULL

    -- purpose: latches output according to its input
    -- type : sequential
    latch_output_p : process (CLK) is
    begin  -- process latch_output_p
        if (rising_edge(CLK)) then      -- rising clock edge
            if ((RESET = '1' and SET = '1') or (RESET = '0' and SET = '0')) then

                latch_out_int <= latch_out_int;

            elsif (RESET = '0' and SET = '1') then

                latch_out_int <= DATA_IN;

            elsif (RESET = '1' and SET = '0') then

                latch_out_int <= (others => '0');

            end if;
        end if;
    end process;

    LATCH_OUT <= latch_out_int;

end architecture;
