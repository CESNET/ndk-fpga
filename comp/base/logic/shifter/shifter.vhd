-- barrel_shifter_gen.vhd:
-- Copyright (C) 2026 CESNET
-- Author(s): Radek Iša <isa@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;



entity SHIFTER is
    generic (
        BLOCKS      : integer := 64;
        BLOCK_WIDTH : integer := 1;
        MOVE_LEFT   : boolean := true; -- moving left when true, right when false
        ROTATE      : boolean := false -- rotating when true, shifting when false
    );
    port (
        DI      : in std_logic_vector(BLOCKS*BLOCK_WIDTH-1 downto 0);
        SEL     : in std_logic_vector(max(1,log2(BLOCKS))-1 downto 0);
        DO      : out std_logic_vector(BLOCKS*BLOCK_WIDTH-1 downto 0)
    );
end entity;



architecture ARCH of SHIFTER is
    constant DATA_WIDTH : natural := BLOCKS*BLOCK_WIDTH;

    signal data_in_tmp   : unsigned(2*DATA_WIDTH-1 downto 0);
    signal data_out_tmp  : unsigned(2*DATA_WIDTH-1 downto 0);
    signal sel_int       : integer range 0 to maximum(BLOCKS,0)-1; -- Don't change it. It would requires more resources.
begin

    -- Operation ROTATION
    fce_rotate_gen : if (ROTATE) generate
        data_in_tmp <= unsigned(DI & DI);
    else generate
        -- Operation SHIFT
        fce_shift_gen : if (MOVE_LEFT) generate
            data_in_tmp <= unsigned(DI) & (DATA_WIDTH-1 downto 0 => '0');
        else generate
            data_in_tmp <= (DATA_WIDTH-1 downto 0 => '0') & unsigned(DI);
        end generate;
    end generate;

    sel_int_gen : if (BLOCKS > 1) generate
        sel_int <= to_integer(unsigned(SEL)) when unsigned(SEL) < BLOCKS else
                   to_integer(unsigned'(log2(BLOCKS)-1 downto 0 => 'X'));
    else generate
        sel_int <= 0;
    end generate;

    shift_sel_gen : if (MOVE_LEFT) generate
        data_out_tmp <= IEEE.numeric_std.shift_left(data_in_tmp, sel_int*BLOCK_WIDTH);
        DO           <= std_logic_vector(data_out_tmp(DATA_WIDTH*2-1 downto DATA_WIDTH));
    else generate
        data_out_tmp <= IEEE.numeric_std.shift_right(data_in_tmp, sel_int*BLOCK_WIDTH);
        DO           <= std_logic_vector(data_out_tmp(DATA_WIDTH-1 downto 0));
    end generate;
end architecture;
