-- am_check_4.vhd : Alignment marker checker for 4-lane PCS
-- Copyright (C) 2011-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- NOTES:
-- Marker encoding
-- 0 0x90, 0x76, 0x47, BIP3, 0x6F, 0x89, 0xB8, BIP7
-- 1 0xF0, 0xC4, 0xE6, BIP3, 0x0F, 0x3B, 0x19, BIP7
-- 2 0xC5, 0x65, 0x9B, BIP3, 0x3A, 0x9A, 0x64, BIP7
-- 3 0xA2, 0x79, 0x3D, BIP3, 0x5D, 0x86, 0xC2, BIP7
--
-- BIP calculation table
-- 0 2, 10, 18, 26, 34, 42, 50, 58
-- 1 3, 11, 19, 27, 35, 43, 51, 59
-- 2 4, 12, 20, 28, 36, 44, 52, 60
-- 3 0, 5, 13, 21, 29, 37, 45, 53, 61
-- 4 1, 6, 14, 22, 30, 38, 46, 54, 62
-- 5 7, 15, 23, 31, 39, 47, 55, 63
-- 6 8, 16, 24, 32, 40, 48, 56, 64
-- 7 9, 17, 25, 33, 41, 49, 57, 65

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity am_check_4 is
    port (
        RESET     : in std_logic; -- Reset current computation and a start new one
        CLK       : in std_logic; --
        EN        : in std_logic;
        D         : in std_logic_vector(65 downto 0);  -- Input data
        MATCH     : out std_logic_vector(3 downto 0);  -- Generated marker
        BIP_MATCH : out std_logic                      -- Bit parity computation OK
    );
end am_check_4;

    architecture behavioral of am_check_4 is

    constant M_0 : std_logic_vector(23 downto 0) := X"47" & X"76" & X"90";
    constant M_1 : std_logic_vector(23 downto 0) := X"E6" & X"C4" & X"F0";
    constant M_2 : std_logic_vector(23 downto 0) := X"9B" & X"65" & X"C5";
    constant M_3 : std_logic_vector(23 downto 0) := X"3D" & X"79" & X"A2";

    signal bip_prev : std_logic_vector( 7 downto 0);
    signal bip      : std_logic_vector( 7 downto 0);
    signal bip_r    : std_logic_vector( 7 downto 0) := X"00";
    signal m_match  : std_logic_vector( 3 downto 0);
    signal sync_hdr : std_logic;

begin

    m_match(0) <= '1' when (D(25 downto 2) = M_0) and (D(57 downto 34) = not M_0) else '0';
    m_match(1) <= '1' when (D(25 downto 2) = M_1) and (D(57 downto 34) = not M_1) else '0';
    m_match(2) <= '1' when (D(25 downto 2) = M_2) and (D(57 downto 34) = not M_2) else '0';
    m_match(3) <= '1' when (D(25 downto 2) = M_3) and (D(57 downto 34) = not M_3) else '0';

    sync_hdr <= '1' when D(1 downto 0) = "01" else '0';

    MATCH(0)  <= m_match(0) and sync_hdr;
    MATCH(1)  <= m_match(1) and sync_hdr;
    MATCH(2)  <= m_match(2) and sync_hdr;
    MATCH(3)  <= m_match(3) and sync_hdr;
    BIP_MATCH <= '1' when (bip_r = D(33 downto 26)) else '0';

    bip_prev <= X"00" when RESET = '1' else bip_r;

    bip(0) <= bip_prev(0) xor D(2) xor D(10) xor D(18) xor D(26) xor D(34) xor D(42) xor D(50) xor D(58);
    bip(1) <= bip_prev(1) xor D(3) xor D(11) xor D(19) xor D(27) xor D(35) xor D(43) xor D(51) xor D(59);
    bip(2) <= bip_prev(2) xor D(4) xor D(12) xor D(20) xor D(28) xor D(36) xor D(44) xor D(52) xor D(60);
    bip(3) <= bip_prev(3) xor D(0) xor D( 5) xor D(13) xor D(21) xor D(29) xor D(37) xor D(45) xor D(53) xor D(61);
    bip(4) <= bip_prev(4) xor D(1) xor D( 6) xor D(14) xor D(22) xor D(30) xor D(38) xor D(46) xor D(54) xor D(62);
    bip(5) <= bip_prev(5) xor D(7) xor D(15) xor D(23) xor D(31) xor D(39) xor D(47) xor D(55) xor D(63);
    bip(6) <= bip_prev(6) xor D(8) xor D(16) xor D(24) xor D(32) xor D(40) xor D(48) xor D(56) xor D(64);
    bip(7) <= bip_prev(7) xor D(9) xor D(17) xor D(25) xor D(33) xor D(41) xor D(49) xor D(57) xor D(65);

    BIP_SEQ: process(clk,reset)
    begin
        if CLK'event and CLK = '1' then
            if EN = '1' then
                bip_r <= bip;
            end if;
        end if;
    end process;
    --

end behavioral;
