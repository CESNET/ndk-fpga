-- byte_en_decoder.vhd:  this decodes the FBE and LBE signals in order that non continuous rows of
-- ones are filled to be continuous
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- This component decodes Last and First Byte Enable signals for the incoming PCI Express
-- transactions. Non-continuous series of ones are replaced by contiuous. For example:
--
-- Input (Last_BE,First_BE) -> Output (Last_BE,First_BE)
--
-- * (0010, 0101) -> (0011,1111)
-- * (1111, 0101) -> (1111,1111)
-- * (0000,0100) -> (0000,0100)
-- * (0111,0100) -> (0111,1100)
-- * (1000,0001) -> (1111,1111)
-- * (0000,0110) -> (0000,0110)
--
entity PCIE_BYTE_EN_DECODER is
    port (
        FBE_IN   : in  std_logic_vector(3 downto 0);
        LBE_IN   : in  std_logic_vector(3 downto 0);
        FBE_OUT  : out std_logic_vector(3 downto 0);
        LBE_OUT  : out std_logic_vector(3 downto 0));
end entity;

architecture FULL of PCIE_BYTE_EN_DECODER is
begin
    process (all)
    begin
        FBE_OUT <= FBE_IN;
        LBE_OUT <= LBE_IN;

        if (std_match(FBE_IN,"1--1") AND std_match(LBE_IN,"0000")) then
                  FBE_OUT <= "1111";
        elsif (std_match(FBE_IN,"01-1") AND std_match(LBE_IN,"0000")) then
                     FBE_OUT <= "0111";
        elsif (std_match(FBE_IN,"1-10") AND std_match(LBE_IN,"0000")) then
                     FBE_OUT <= "1110";
        elsif (std_match(FBE_IN,"---1") AND std_match(LBE_IN,"1---")) then
                     FBE_OUT <= "1111";           LBE_OUT <= "1111";
        elsif (std_match(FBE_IN,"---1") AND std_match(LBE_IN,"01--")) then
                     FBE_OUT <= "1111";           LBE_OUT <= "0111";
        elsif (std_match(FBE_IN,"---1") AND std_match(LBE_IN,"001-")) then
                     FBE_OUT <= "1111";           LBE_OUT <= "0011";
        elsif (std_match(FBE_IN,"---1") AND std_match(LBE_IN,"0001")) then
                     FBE_OUT <= "1111";
        elsif (std_match(FBE_IN,"--10") AND std_match(LBE_IN,"1---")) then
                     FBE_OUT <= "1110";           LBE_OUT <= "1111";
        elsif (std_match(FBE_IN,"--10") AND std_match(LBE_IN,"01--")) then
                     FBE_OUT <= "1110";           LBE_OUT <= "0111";
        elsif (std_match(FBE_IN,"--10") AND std_match(LBE_IN,"001-")) then
                     FBE_OUT <= "1110";           LBE_OUT <= "0011";
        elsif (std_match(FBE_IN,"--10") AND std_match(LBE_IN,"0001")) then
                     FBE_OUT <= "1110";
        elsif (std_match(FBE_IN,"-100") AND std_match(LBE_IN,"1---")) then
                     FBE_OUT <= "1100";           LBE_OUT <= "1111";
        elsif (std_match(FBE_IN,"-100") AND std_match(LBE_IN,"01--")) then
                     FBE_OUT <= "1100";           LBE_OUT <= "0111";
        elsif (std_match(FBE_IN,"-100") AND std_match(LBE_IN,"001-")) then
                     FBE_OUT <= "1100";           LBE_OUT <= "0011";
        elsif (std_match(FBE_IN,"-100") AND std_match(LBE_IN,"0001")) then
                     FBE_OUT <= "1100";
        elsif (std_match(FBE_IN,"1000") AND std_match(LBE_IN,"1---")) then
                     FBE_OUT <= "1000";           LBE_OUT <= "1111";
        elsif (std_match(FBE_IN,"1000") AND std_match(LBE_IN,"01--")) then
                     FBE_OUT <= "1000";           LBE_OUT <= "0111";
        elsif (std_match(FBE_IN,"1000") AND std_match(LBE_IN,"001-")) then
                     FBE_OUT <= "1000";           LBE_OUT <= "0011";
        end if;
    end process;
end architecture;
