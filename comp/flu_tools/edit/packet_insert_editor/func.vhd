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

package editor_func is
   function func_num_regs(input_pipe : boolean) return integer;
end package;

--! \brief Body of package with functions
package body editor_func is

   function func_num_regs(input_pipe : boolean) return integer is
   begin
      if (input_pipe = true) then
         return 4;
      else
         return 3;
      end if;
   end function;

end editor_func;

