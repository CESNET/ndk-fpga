-- fl_fifo_pkg.vhd: Package with function
-- Copyright (C) 2003 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
-- ------------------------------------------------------------------
--                   Package Interface
-- ------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;

package fl_fifo_pkg is

   function get_juice_width(data_width:integer;use_brams:boolean)return integer;

end fl_fifo_pkg;

-- ------------------------------------------------------------------
--                   Package Body
-- ------------------------------------------------------------------
package body fl_fifo_pkg is

   function min(L, R: integer) return integer is
   begin
      if L < R then
         return L;
      else
         return R;
      end if;
   end;

   -- ----------------------------------------------------------------------
   function get_juice_width(data_width:integer;use_brams:boolean)return
   integer is
   begin
      if use_brams = true then
         return min(data_width/16, 4);
      else
         return 4;
      end if;
   end;

end fl_fifo_pkg;
