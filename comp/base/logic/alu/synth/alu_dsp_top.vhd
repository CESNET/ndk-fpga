--! alu_dsp_top.vhd
--!
--! \file
--! \brief ALU  implemented with Virtex-7 DSP slice
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
library unisim;
use unisim.vcomponents.all;

--! \brief DSP slice ALU entity
entity ALU_DSP_TOP is
    generic (
        DATA_WIDTH  : integer := 96;
        --! Input pipeline registers (0, 1)
        REG_IN      : integer := 1;
        --! Output pipeline register (0, 1)
        REG_OUT     : integer := 1
    );
    port (
        --! Clock input
        CLK      : in  std_logic;
        --! Reset input
        RESET    : in  std_logic;
        --! Data input
        A        : in  std_logic_vector((DATA_WIDTH - 1) downto 0);
        --! Data input
        B        : in  std_logic_vector((DATA_WIDTH - 1) downto 0);
        --! Clock enable for input pipeline registers
        CE_IN    : in  std_logic;
        --! Clock enable for output pipeline registers
        CE_OUT   : in  std_logic;

        --! control alu
        --! operators (A [operator] B):
        --!     "0000" -> ADD
        --!
        --!     "0001" -> SUB (A - (B + CARRY_IN))
        --!     (WARNING for SUB: when "DATA_WIDTH <= 48" or "DATA_WIDTH mod 48 = 0"
        --!      CARRY_OUT is inverted)
        --!
        --!     "0010" -> NAND
        --!     "0011" -> AND
        --!     "0100" -> OR
        --!     "0101" -> NOR
        --!     "0110" -> XOR
        --!     "0111" -> XNOR
        --! operators and negated data inputs:
        --!     "1000" -> B AND (NOT A)
        --!     "1001" -> (NOT B) ADD A
        --!     "1010" -> B OR (NOT A)
        --!     "1011" -> (NOT B) OR A
        ALUMODE   : in std_logic_vector(3 downto 0);

        --! carry input
        CARRY_IN  : in std_logic;
        --! carry output
        CARRY_OUT : out std_logic;
        --! Data output
        --! Latency = REG_IN + REG_OUT
        P         : out std_logic_vector((DATA_WIDTH - 1) downto 0)
    );
end entity;

--! Vitrex-7 architecture of ALU_DSP
architecture V7_DSP_TOP of ALU_DSP_TOP is

    --! signals
    signal reset_d     : std_logic;
    signal a_d         : std_logic_vector((DATA_WIDTH - 1) downto 0);
    signal b_d         : std_logic_vector((DATA_WIDTH - 1) downto 0);
    signal ce_in_d     : std_logic;
    signal ce_out_d    : std_logic;
    signal alumode_d   : std_logic_vector(3 downto 0);
    signal carry_in_d  : std_logic;
    signal carry_out_d : std_logic;
    signal p_d         : std_logic_vector((DATA_WIDTH - 1) downto 0);

begin

    uut : entity work.ALU_DSP(structural)
    generic map (
        DATA_WIDTH  => DATA_WIDTH,
        REG_IN      => REG_IN,
        REG_OUT     => REG_OUT
    )
    port map (
        CLK         => CLK,
        RESET       => reset_d,
        A           => a_d,
        B           => b_d,
        CE_IN       => ce_in_d,
        CE_OUT      => ce_out_d,
        ALUMODE     => alumode_d,
        CARRY_IN    => carry_in_d,
        CARRY_OUT   => carry_out_d,
        P           => p_d
    );

    -- input registers
    process (CLK)
    begin
        if ((CLK'event) and (CLK = '1')) then
            if (RESET = '1') then
                reset_d    <= '1';
                a_d        <= (others => '0');
                b_d        <= (others => '0');
                ce_in_d    <= '0';
                ce_out_d   <= '0';
                alumode_d  <= (others => '0');
                carry_in_d <= '0';
            else
                reset_d    <= '0';
                a_d        <= A;
                b_d        <= B;
                ce_in_d    <= CE_IN;
                ce_out_d   <= CE_OUT;
                alumode_d  <= ALUMODE;
                carry_in_d <= CARRY_IN;
            end if;
        end if;
    end process;

    -- output registers
    process (CLK)
    begin
        if ((CLK'event) and (CLK = '1')) then
            if (RESET = '1') then
                CARRY_OUT <= '0';
                P         <= (others => '0');
            else
                CARRY_OUT <= carry_out_d;
                P         <= p_d;
            end if;
        end if;
    end process;
end architecture;
