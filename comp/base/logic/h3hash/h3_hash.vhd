-- h3_hash.vhd: H3 Class hash function
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.h3_pack.all;

-- Component for computing any hash function from universal H3 class. Universal hash functions
-- have some interesting properties, for reference, check out this paper:
-- https://www.cs.princeton.edu/courses/archive/fall09/cos521/Handouts/universalclasses.pdf.
-- This component has default latency of 0 clock cycles, for larger inputs and outputs
-- one can enable one pipeline stage and output register.
entity H3_HASH is
    generic (
        -- Width of data, which will be hashed, currently supporting
        -- `DATA_WIDTH` <= 256
        DATA_WIDTH  : natural := 256;
        -- Resulting hash width, currently supporting `HASH_WIDTH` <= 64
        HASH_WIDTH  : natural := 64;

        -- Type of hash core, which will be used. Those are precomputed and stored in h3_pack.vhd.
        -- Names are defined like this: H3C_(input_width)x(output_width).
        -- Available values are:
        --
        -- * "H3C_64x16"
        -- * "H3C_64x22"
        -- * "H3C_22x11"
        -- * "H3C_256x64"
        -- * "AUTO" - hash core will be selected automatically
        H3_TYPE     : string := "AUTO";

        -- One pipeline stage will be inserted into H3 hash function,
        -- adding latency of 1 clock cycle.
        PIPELINE    : boolean := true;

        -- Add output register.
        OUT_REG     : boolean := true
    );
    port (
        CLK             : in std_logic;
        RESET           : in std_logic;

        -- Input data
        DATA_IN         : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
        DATA_IN_VLD     : in  std_logic := '1';
        DATA_IN_RDY     : out std_logic;

        -- Output hash
        DATA_OUT        : out std_logic_vector(HASH_WIDTH - 1 downto 0);
        DATA_OUT_VLD    : out std_logic;
        DATA_OUT_RDY    : in  std_logic := '1'
    );
end entity;

architecture behavioral of H3_HASH is

    constant h3_conf : h3_config := h3_get_type(H3_TYPE, DATA_WIDTH, HASH_WIDTH);

    signal core_data_in     : std_logic_vector(h3_conf.key_width - 1 downto 0);
    signal core_data_out    : std_logic_vector(h3_conf.hash_width - 1 downto 0);

begin

    process (all)
    begin
        core_data_in <= (others => '0');
        core_data_in(DATA_WIDTH - 1 downto 0) <= DATA_IN;
    end process;

    core_i : entity work.H3_CORE
    generic map (
        CONFIG      => h3_conf,
        PIPELINE    => PIPELINE,
        OUT_REG     => OUT_REG
    ) port map (
        CLK             => CLK,
        RESET           => RESET,

        DATA_IN         => core_data_in,
        DATA_IN_VLD     => DATA_IN_VLD,
        DATA_IN_RDY     => DATA_IN_RDY,

        DATA_OUT        => core_data_out,
        DATA_OUT_VLD    => DATA_OUT_VLD,
        DATA_OUT_RDY    => DATA_OUT_RDY
    );

    DATA_OUT <= core_data_out(HASH_WIDTH - 1 downto 0);

end architecture;
