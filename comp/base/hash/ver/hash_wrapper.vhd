-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

entity HASH_WRAPPER is
    generic (
        -- width of the input key, should not exceed 191B.
        -- If not aligned to whole bytes, the rest is
        -- extended by zeros
        KEY_WIDTH     : natural := 296;
        -- width of the generated hash, max 128 bits
        HASH_WIDTH    : natural := 128;
        -- width of the passthrough metadata
        META_WIDTH    : natural := 32;
        -- adds a register to the output
        OUT_REG       : boolean := true;
        -- name of the hash function to be wrapped
        HASH_FUNCTION : string := "SPOOKYHASH"
    );
    port (
        -- main clock
        CLK           : in std_logic;
        -- synchronious reset
        RESET         : in std_logic;

        -- key to be hashed
        IN_KEY        : in std_logic_vector(KEY_WIDTH-1 downto 0);
        -- use seed for better durability of the hash
        IN_SEED       : in std_logic_vector(128-1 downto 0);
        -- passthrough metadata input
        IN_META       : in std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID      : in std_logic;

        -- calculated hash
        OUT_HASH      : out std_logic_vector(HASH_WIDTH-1 downto 0);
        -- passthrough metadata output
        OUT_META      : out std_logic_vector(META_WIDTH-1 downto 0);
        -- hash validity
        OUT_VALID     : out std_logic
    );
end entity;

architecture FULL of HASH_WRAPPER is
begin
    hash_function_g: if HASH_FUNCTION = "SPOOKYHASH" generate
        spookyhash_i: entity work.SPOOKYHASH
        generic map (
            KEY_WIDTH  => KEY_WIDTH,
            HASH_WIDTH => HASH_WIDTH,
            META_WIDTH => META_WIDTH,
            OUT_REG    => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    elsif HASH_FUNCTION = "SIPHASH_2_4" generate
        siphash_i: entity work.SIPHASH
        generic map (
            KEY_WIDTH           => KEY_WIDTH,
            HASH_WIDTH          => HASH_WIDTH,
            META_WIDTH          => META_WIDTH,
            COMPRESSION_ROUDS   => 2,
            FINALIZATION_ROUNDS => 4,
            WORD_WIDTH          => 64,
            OUT_REG             => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    elsif HASH_FUNCTION = "SIPHASH_4_8" generate
        siphash_i: entity work.SIPHASH
        generic map (
            KEY_WIDTH           => KEY_WIDTH,
            HASH_WIDTH          => HASH_WIDTH,
            META_WIDTH          => META_WIDTH,
            COMPRESSION_ROUDS   => 4,
            FINALIZATION_ROUNDS => 8,
            WORD_WIDTH          => 64,
            OUT_REG             => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    elsif HASH_FUNCTION = "HALFSIPHASH_2_4" generate
        siphash_i: entity work.SIPHASH
        generic map (
            KEY_WIDTH           => KEY_WIDTH,
            HASH_WIDTH          => HASH_WIDTH,
            META_WIDTH          => META_WIDTH,
            COMPRESSION_ROUDS   => 2,
            FINALIZATION_ROUNDS => 4,
            WORD_WIDTH          => 32,
            OUT_REG             => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    elsif HASH_FUNCTION = "HALFSIPHASH_4_8" generate
        siphash_i: entity work.SIPHASH
        generic map (
            KEY_WIDTH           => KEY_WIDTH,
            HASH_WIDTH          => HASH_WIDTH,
            META_WIDTH          => META_WIDTH,
            COMPRESSION_ROUDS   => 4,
            FINALIZATION_ROUNDS => 8,
            WORD_WIDTH          => 32,
            OUT_REG             => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    elsif HASH_FUNCTION = "CHASKEY" generate
        chaskey_i: entity work.CHASKEY
        generic map (
            KEY_WIDTH  => KEY_WIDTH,
            HASH_WIDTH => HASH_WIDTH,
            META_WIDTH => META_WIDTH,
            ROUNDS     => 8,
            OUT_REG    => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    elsif HASH_FUNCTION = "CHASKEY_LTS" generate
        chaskey_i: entity work.CHASKEY
        generic map (
            KEY_WIDTH  => KEY_WIDTH,
            HASH_WIDTH => HASH_WIDTH,
            META_WIDTH => META_WIDTH,
            ROUNDS     => 12,
            OUT_REG    => OUT_REG
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => IN_KEY,
            IN_SEED    => IN_SEED,
            IN_META    => IN_META,
            IN_VALID   => IN_VALID,
            OUT_HASH   => OUT_HASH,
            OUT_META   => OUT_META,
            OUT_VALID  => OUT_VALID
        );
    else generate
        assert false
            report "Unknown hash function '" & HASH_FUNCTION & "'."
            severity error;
    end generate;

end architecture;
