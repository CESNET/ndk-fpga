--! mux_lvl_func.vhd
--!
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

package mux_lvl_func is
   function num_muxs(mux_width, lvl : Integer) return integer;
   function mod_muxs(mux_width, lvl : Integer) return integer;
   function gen_pipe_in(reg_in, lvl : Integer) return integer;
   function gen_pipe_out(lvl, lvl_max, reg_out, reg_lvl : Integer) return integer;
   function gen_in_cascade(lvl : Integer) return boolean;
   function gen_pipe_sel(reg_lvl, reg_in, lvl : Integer) return integer;
   function func_new_data_width(data_width : Integer) return integer;
end package;

--! \brief Body of package with functions
package body mux_lvl_func is

   -- number of multiplexers for lvl
   function func_new_data_width(data_width : Integer) return integer is
      variable width_mod : integer;
   begin
      width_mod := data_width mod 48;
      if (width_mod = 0) then
         return data_width;
      else
         return (data_width + (48 - width_mod));
      end if;
   end function;

   function num_muxs(mux_width, lvl : Integer) return integer is
      variable num_inputs     : integer;
      variable first_lvl      : integer;
      variable lvl_mod        : integer;
      variable others_lvl     : integer;
   begin
      first_lvl   := mux_width/2;
      lvl_mod     := mux_width mod 2;
      num_inputs  := first_lvl + lvl_mod;

      if (lvl = 0) then
         return first_lvl;
      end if;

      for I in 1 to lvl loop
         others_lvl := num_inputs/2;
         lvl_mod    := num_inputs mod 2;
         num_inputs := others_lvl + lvl_mod;
      end loop;

      return others_lvl;
   end function;

   -- number of multiplexers for lvl
   function mod_muxs(mux_width, lvl : Integer) return integer is
      variable num_inputs     : integer;
      variable first_lvl      : integer;
      variable lvl_mod        : integer;
      variable others_lvl     : integer;
   begin
      first_lvl   := mux_width/2;
      lvl_mod     := mux_width mod 2;
      num_inputs  := first_lvl + lvl_mod;

      if (lvl = 0) then
         return first_lvl;
      end if;

      for I in 1 to lvl loop
         others_lvl := num_inputs/2;
         lvl_mod    := num_inputs mod 2;
         num_inputs := others_lvl + lvl_mod;
      end loop;

      return lvl_mod;
   end function;

      -- number of multiplexers for lvl
   function gen_pipe_in(reg_in, lvl : Integer) return integer is
   begin
      if (lvl = 0 and reg_in = 1) then
         return 1;
      end if;
      return 0;
   end function;

   function gen_pipe_sel(reg_lvl, reg_in, lvl : Integer) return integer is
   begin
      if (lvl = 0) then
         return reg_in;
      else
         return reg_lvl;
      end if;
   end function;

   function gen_pipe_out(lvl, lvl_max, reg_out, reg_lvl : Integer) return integer is
   begin
      if (lvl = lvl_max) then
         return reg_out;
      else
         return reg_lvl;
      end if;
   end function;

   function gen_in_cascade(lvl : Integer) return boolean is
   begin
      if (lvl = 0) then
         return false;
      else
         return true;
      end if;
   end function;

end mux_lvl_func;

