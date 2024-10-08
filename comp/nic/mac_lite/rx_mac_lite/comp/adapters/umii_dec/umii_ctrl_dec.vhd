-- umii_ctrl_dec.vhd: Control MII characters decoder
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity UMII_CTRL_DEC is
    generic(
        -- must be power of two, minimum is 64
        MII_DW : natural := 2048
    );
    port(
        -- =====================================================================
        -- INPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
        -- =====================================================================
        MII_RXD       : in  std_logic_vector(MII_DW-1 downto 0);
        MII_RXC       : in  std_logic_vector(MII_DW/8-1 downto 0);
        -- =====================================================================
        -- OUTPUT CONTROL OCCUR INTERFACE
        -- =====================================================================
        IS_LOCFAULT   : out std_logic;
        IS_PREAMBLE   : out std_logic;
        IS_START      : out std_logic;
        IS_TERMINATE  : out std_logic;
        IS_ERROR      : out std_logic;
        -- =====================================================================
        -- OUTPUT CONTROL POSITION INTERFACE
        -- =====================================================================
        POS_LOCFAULT  : out std_logic_vector(MII_DW/64-1 downto 0);
        POS_PREAMBLE  : out std_logic_vector(MII_DW/64-1 downto 0);
        POS_START     : out std_logic_vector(MII_DW/64-1 downto 0);
        POS_TERMINATE : out std_logic_vector(MII_DW/8-1 downto 0);
        POS_ERROR     : out std_logic_vector(MII_DW/8-1 downto 0)
    );
end entity;

architecture FULL of UMII_CTRL_DEC is

    -- Control MII characters are compatible with XGMII+ standard
    constant MII_IDLE        : std_logic_vector := X"07";
    constant MII_SEQUENCE    : std_logic_vector := X"9C";
    constant MII_START       : std_logic_vector := X"FB";
    constant MII_TERMINATE   : std_logic_vector := X"FD";
    constant MII_ERROR       : std_logic_vector := X"FE";
    constant MII_LOCFAULT_D  : std_logic_vector(63 downto 0) := X"00000000010000" & MII_SEQUENCE;
    constant MII_LOCFAULT_C  : std_logic_vector(7 downto 0) := "00000001";
    constant MII_PREAMBLE_D  : std_logic_vector(63 downto 0) := X"D5555555555555" & MII_START;
    constant MII_PREAMBLE_C  : std_logic_vector(7 downto 0) := "00000001";

    constant BYTES_COUNT : natural := MII_DW/8;
    constant BLOCK_COUNT : natural := MII_DW/64;

    signal s_locfault_char_d  : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_locfault_char_c  : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_preamble_char_d  : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_preamble_char_c  : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_start_char_d     : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_terminate_char_d : std_logic_vector(BYTES_COUNT-1 downto 0);
    signal s_error_char_d     : std_logic_vector(BYTES_COUNT-1 downto 0);

    signal s_pos_locfault     : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_pos_preamble     : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_pos_start        : std_logic_vector(BLOCK_COUNT-1 downto 0);
    signal s_pos_terminate    : std_logic_vector(BYTES_COUNT-1 downto 0);
    signal s_pos_error        : std_logic_vector(BYTES_COUNT-1 downto 0);

begin

    -- detect at each eighth byte (block)
    block_detect : for i in 0 to BLOCK_COUNT-1 generate
        -- detect local fault sequence starting at each eighth byte (block)
        s_locfault_char_d(i) <= '1' when (MII_RXD((i+1)*64-1 downto i*64) = MII_LOCFAULT_D) else '0';
        s_locfault_char_c(i) <= '1' when (MII_RXC((i+1)*8-1 downto i*8) = MII_LOCFAULT_C) else '0';
        s_pos_locfault(i) <= s_locfault_char_d(i) and s_locfault_char_c(i);
        POS_LOCFAULT(i)   <= s_pos_locfault(i);

        -- detect start control characters and preamble pattern starting at each eighth byte (block)
        s_preamble_char_d(i) <= '1' when (MII_RXD((i+1)*64-1 downto i*64) = MII_PREAMBLE_D) else '0';
        s_preamble_char_c(i) <= '1' when (MII_RXC((i+1)*8-1 downto i*8) = MII_PREAMBLE_C) else '0';
        s_pos_preamble(i) <= s_preamble_char_d(i) and s_preamble_char_c(i);
        POS_PREAMBLE(i)   <= s_pos_preamble(i);

        -- detect start control characters starting at each eighth byte (block)
        s_start_char_d(i) <= '1' when (MII_RXD((i*64)+8-1 downto i*64) = MII_START) else '0';
        s_pos_start(i) <= s_start_char_d(i) and MII_RXC(i*8);
        POS_START(i)   <= s_pos_start(i);
    end generate;

    -- detect at each byte
    bytes_detect_g : for i in 0 to BYTES_COUNT-1 generate
        -- detect terminate on each byte
        s_terminate_char_d(i) <= '1' when (MII_RXD((i+1)*8-1 downto i*8) = MII_TERMINATE) else '0';
        s_pos_terminate(i) <= s_terminate_char_d(i) and MII_RXC(i);
        POS_TERMINATE(i)   <= s_pos_terminate(i);

        -- detect error on each byte
        s_error_char_d(i) <= '1' when (MII_RXD((i+1)*8-1 downto i*8) = MII_ERROR) else '0';
        s_pos_error(i) <= s_error_char_d(i) and MII_RXC(i);
        POS_ERROR(i)   <= s_pos_error(i);
    end generate;

    -- output control occur
    IS_LOCFAULT  <= or s_pos_locfault;
    IS_PREAMBLE  <= or s_pos_preamble;
    IS_START     <= or s_pos_start;
    IS_TERMINATE <= or s_pos_terminate;
    IS_ERROR     <= or s_pos_error;

end architecture;
