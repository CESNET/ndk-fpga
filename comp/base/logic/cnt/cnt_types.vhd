--
-- cnt_types.vhd: definition of type for determine counter type
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
library IEEE;
--use IEEE.std_logic_1164.all;
--use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Package declaration
-- ----------------------------------------------------------------------------
Package CNT_TYPES is

   -- counter type
   type TCNT is (up, down);

end  CNT_TYPES;
