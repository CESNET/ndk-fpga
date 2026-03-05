-- barrel_shifter.vhd Barrel shifter with generic data width
-- Copyright (C) 2026 CESNET
-- Author(s): Radek Iša <isa@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                  ENTITY DECLARATION -- Barrel shifter                     --
-- ----------------------------------------------------------------------------
-- Note: please prefr BARREL_SHIFTER_GEN instead
entity BARREL_SHIFTER is
    generic (
        DATA_WIDTH  : integer := 64;
        BLOCKS      : integer := DATA_WIDTH / 8;
        -- set true to shift left, false to shift right
        SHIFT_LEFT  : boolean := true
    );
    port (
        -- Input interface ------------------------------------------------------
        DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);
        SEL         : in  std_logic_vector(log2(BLOCKS)-1 downto 0)
    );
end entity;


architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
    constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
begin

    assert (DATA_WIDTH mod BLOCKS = 0)
        report "DATA_WIDTH must be divisible by BLOCK"
        severity failure;

    shifter_inst : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => BLOCKS,
        BLOCK_SIZE => BLOCK_WIDTH,
        SHIFT_LEFT => SHIFT_LEFT
    )
    port map (
        DATA_IN  => DATA_IN,
        DATA_OUT => DATA_OUT,
        SEL      => SEL
    );
end architecture;


