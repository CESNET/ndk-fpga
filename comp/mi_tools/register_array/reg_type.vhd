-- reg_type.vhd: register data type
-- # Copyright (C) 2015 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use ieee.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

package REG_PACK is
   --! data type
	type REG_TYPE is record
      DATA_WIDTH	: integer;
      INTER	      : boolean;
      MI_RD_EN    : boolean;
      MI_WR_EN    : boolean;
      USR_WR_EN   : boolean;
      RST_EN      : boolean;
      BE_EN       : boolean;
	end record;
   --! array data type
   type REG_TYPE_ARRAY
      is array (integer range <>) of REG_TYPE;
end package REG_PACK;

package body REG_PACK is
end package body REG_PACK;
