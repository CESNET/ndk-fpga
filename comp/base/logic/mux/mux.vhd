-- mux.vhd: Generic multiplexer
-- Copyright (C) 2026 CESNET
-- Author(s): Radek Iša <isa@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity GEN_MUX is
    generic (
        DATA_WIDTH  : integer := 64;
        MUX_WIDTH   : integer := 15   -- multiplexer width (number of inputs)
    );
    port (
        DATA_IN     : in  std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
        SEL         : in  std_logic_vector(max(1,log2(MUX_WIDTH))-1 downto 0);
        DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of GEN_MUX is
    signal data_in_tmp    : unsigned(DATA_WIDTH*MUX_WIDTH-1 downto 0);
    signal data_out_tmp   : unsigned(DATA_WIDTH*MUX_WIDTH-1 downto 0);
    signal sel_int        : integer range 0 to MUX_WIDTH-1; -- Don't change it. It would requires more resources.
begin

    assert MUX_WIDTH > 0
        report "NUMBER OF MUX INPUT HAVE TO BE GREATER THAT ZERO. PLEASE MODIFY YOUR CODE."
        severity failure;

    data_in_tmp <= unsigned(DATA_IN);

    sel_int_gen : if (MUX_WIDTH > 1) generate
        sel_int <= to_integer(unsigned(SEL)) when unsigned(SEL) < MUX_WIDTH else
                   to_integer(unsigned'(log2(MUX_WIDTH)-1 downto 0 => 'X'));
    else generate
        sel_int <= 0;
    end generate;

    -- Select item by rottation on start
    data_out_tmp <= IEEE.numeric_std.shift_right(data_in_tmp, sel_int*DATA_WIDTH);
    DATA_OUT     <= std_logic_vector(data_out_tmp(DATA_WIDTH-1 downto 0));

end architecture;

