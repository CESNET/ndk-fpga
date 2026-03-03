--
-- barrel_shifter.vhd Barrel shifter with generic data width
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                  ENTITY DECLARATION -- Barrel shifter                     --
-- ----------------------------------------------------------------------------

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

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture BARREL_SHIFTER_ARCH of BARREL_SHIFTER is
    constant BLOCK_WIDTH : natural := DATA_WIDTH / BLOCKS;
begin

    assert DATA_WIDTH mod BLOCKS = 0
        report "DATA_WIDTH is not multiple of BLOCKS"
        severity Failure;

    multiplexors: for i in 0 to BLOCKS-1 generate
        process (DATA_IN, SEL)
            variable sel_aux : integer;
            variable sel_blk : integer;
        begin
            if (SHIFT_LEFT) then
                sel_aux := conv_integer('0'&SEL);
            else
                sel_aux := conv_integer('0'&(0-SEL));
            end if;

            sel_blk := ((BLOCKS-sel_aux+i) mod BLOCKS);

            DATA_OUT((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH) <= DATA_IN((sel_blk+1)*BLOCK_WIDTH-1 downto sel_blk*BLOCK_WIDTH);
        end process;
    end generate;

end architecture;
