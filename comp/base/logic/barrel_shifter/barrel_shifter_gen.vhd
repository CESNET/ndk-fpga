-- barrel_shifter_gen.vhd:
-- Copyright (C) 2026 CESNET
-- Author(s): Radek Iša <isa@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

-- Generically adjustable barrel shifter supporting shifts of single bits and whole blocks
-- Supports bite-level rotation when `BLOCK_SIZE == 1`
-- Configurable shift direction
entity BARREL_SHIFTER_GEN is
    generic (
        -- input/output data width in BLOCKs
        BLOCKS      : integer := 256;
        -- size of one block in bits
        BLOCK_SIZE  : integer := 64;
        -- set true to shift left, false to shift right
        SHIFT_LEFT  : boolean := false
    );
    port (
        DATA_IN     : in  std_logic_vector(BLOCKS*BLOCK_SIZE-1 downto 0);
        DATA_OUT    : out std_logic_vector(BLOCKS*BLOCK_SIZE-1 downto 0);
        SEL         : in  std_logic_vector(log2(BLOCKS)-1 downto 0)
    );
end entity;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER_GEN is
    constant DATA_WIDTH : natural := BLOCKS*BLOCK_SIZE;

    signal data_in_tmp   : unsigned(2*DATA_WIDTH-1 downto 0);
    signal data_out_tmp  : unsigned(2*DATA_WIDTH-1 downto 0);
    signal sel_int       : integer range 0 to maximum(BLOCKS, 1)-1; -- Don't change it. It would requires more resources.
begin

    data_in_tmp <= unsigned(DATA_IN & DATA_IN);

    sel_int_gen : if (BLOCKS > 1) generate
        sel_int <= to_integer(unsigned(SEL)) when unsigned(SEL) < BLOCKS else
                   to_integer(unsigned'(log2(BLOCKS)-1 downto 0 => 'X'));
    else generate
        sel_int <= 0;
    end generate;

    shift_sel_gen : if (SHIFT_LEFT) generate
        data_out_tmp <= IEEE.numeric_std.shift_left(data_in_tmp, sel_int*BLOCK_SIZE);
        DATA_OUT     <= std_logic_vector(data_out_tmp(DATA_WIDTH*2-1 downto DATA_WIDTH));
    else generate
        data_out_tmp <= IEEE.numeric_std.shift_right(data_in_tmp, sel_int*BLOCK_SIZE);
        DATA_OUT     <= std_logic_vector(data_out_tmp(DATA_WIDTH-1 downto 0));
    end generate;
end architecture;



