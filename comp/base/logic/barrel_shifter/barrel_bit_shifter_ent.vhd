-- barrel_bit_shifter_ent.vhd: Barrel shifter with generic data width
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

entity BARREL_BIT_SHIFTER is
   generic (
      DATA_WIDTH  : integer := 8;
      -- set true to shift left, false to shift right
      SHIFT_LEFT  : boolean := true
   );
   port (
      -- Input interface ------------------------------------------------------
      DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);
      SEL         : in  std_logic_vector(log2(DATA_WIDTH)-1 downto 0)
   );
end BARREL_BIT_SHIFTER;

