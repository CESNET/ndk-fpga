-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- This component converts the Timestamp format of the :ref:`TimeStamp Unit <tsu_gen>` (the TS_NS output port) to pure nanosecond format.
-- It does this by multiplying the upper 32 bits (that indicate the number of ``seconds``) of the input by ``10**9`` and adding it to the lower 32 bits (that indicate the number of nanoseconds).
-- Quartus and Vivado both manage to use DSPs for the multiplication, eventhough this description is behavioral.
-- Input and output registers can be enabled.
--
entity TSU_FORMAT_TO_NS is
generic(
    -- Enable input and output registers.
    -- Options:
    --
    -- - "000" for no registers
    -- - "001" for output registers
    -- - "100" for input registers
    -- - "010" for middle registers
    -- -  ...  all other combinations
    -- - "111" for all registers
    --
    REG_BITMAP : std_logic_vector(2 downto 0) := "101"
);
port(
    CLK    : in  std_logic;
    RESET  : in  std_logic;
    -- Input TimeStamps [s + ns] (TS_NS port of the TSU).
    TS_TSU : in  std_logic_vector(64-1 downto 0);
    -- Output TimeStamps [ns].
    TS_NS  : out std_logic_vector(64-1 downto 0)
);
end entity;

architecture FULL of TSU_FORMAT_TO_NS is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    -- Seconds to ns conversion ratio.
    constant CONV_RATIO : natural := 10**9;

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    signal tsu_seconds      : unsigned(64-1 downto 0);
    signal tsu_ns           : unsigned(64-1 downto 0);

    signal tsu_seconds_conv : unsigned(64-1 downto 0);
    signal ns_part1         : unsigned(64-1 downto 0);
    signal ns_part2         : unsigned(64-1 downto 0);

    signal ns_sum           : unsigned(64-1 downto 0);

begin

    -- ========================================================================
    -- Stage 1
    -- ========================================================================

    input_reg_g : if REG_BITMAP(2)='1' generate
        process(CLK)
        begin
            if rising_edge(CLK) then
                tsu_seconds <= resize(unsigned(TS_TSU(63 downto 32)),64);
                tsu_ns      <= resize(unsigned(TS_TSU(31 downto  0)),64);
            end if;
        end process;
    else generate
        tsu_seconds <= resize(unsigned(TS_TSU(63 downto 32)),64);
        tsu_ns      <= resize(unsigned(TS_TSU(31 downto  0)),64);
    end generate;

    -- ========================================================================
    -- Stage 2
    -- ========================================================================

    tsu_seconds_conv <= resize(tsu_seconds*CONV_RATIO,64);
    middle_reg_g : if REG_BITMAP(1)='1' generate
        process(CLK)
        begin
            if rising_edge(CLK) then
                ns_part1 <= tsu_seconds_conv;
                ns_part2 <= tsu_ns;
            end if;
        end process;
    else generate
        ns_part1 <= tsu_seconds_conv;
        ns_part2 <= tsu_ns;
    end generate;

    -- ========================================================================
    -- Stage 3
    -- ========================================================================

    ns_sum <= ns_part1 + ns_part2;
    output_reg_g : if REG_BITMAP(0)='1' generate
        process(CLK)
        begin
            if rising_edge(CLK) then
                TS_NS <= std_logic_vector(ns_sum);
            end if;
        end process;
    else generate
        TS_NS <= std_logic_vector(ns_sum);
    end generate;

end architecture;
