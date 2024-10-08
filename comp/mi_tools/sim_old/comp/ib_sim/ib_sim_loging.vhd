--
-- ib_sim_loging.vhd: Simulation component for internal bus
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.ib_pkg.all;
use work.ib_sim_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
-- Log transactions on Internal Bus Link
entity IB_SIM_LOGING is
   generic (
      FILE_NAME         : string -- Log File Path
      );
   port(
      -- Common interface
      IB_RESET          : in  std_logic;
      IB_CLK            : in  std_logic;

      -- Repeater behaviour
      IB_IN             : inout t_internal_bus_link64;
      IB_OUT            : inout t_internal_bus_link64
      );
end entity IB_SIM_LOGING;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SIM_LOGING_ARCH of IB_SIM_LOGING is

begin

-- Repeater
IB_OUT.DATA      <= IB_IN.DATA;
IB_OUT.SOP_N     <= IB_IN.SOP_N;
IB_OUT.EOP_N     <= IB_IN.EOP_N;
IB_OUT.SRC_RDY_N <= IB_IN.SRC_RDY_N;
IB_IN.DST_RDY_N  <= IB_OUT.DST_RDY_N;


main : process
-- ----------------------------------------------------------------
--                        Process Body
-- ----------------------------------------------------------------
variable address1      : std_logic_vector(31 downto 0);
variable address2      : std_logic_vector(31 downto 0);
variable length        : std_logic_vector(11 downto 0);
variable trans_type    : std_logic_vector( 2 downto 0);
variable trans_flag    : std_logic;
variable tag           : std_logic_vector(15 downto 0);
variable data          : std_logic_vector(63 downto 0);
file     log_file      : text;
variable out_line      : line;

--FSM States
type t_fsm_states is (ST_HEAD1, ST_HEAD2, ST_DATA);
variable state : t_fsm_states;

constant str_divider : string :=
"----------------------------------------------------------------------------------------";
constant str_info : string :=
"Transactions on Internal Bus";
constant str_null : string :="";

constant str_tag : string :=
"; TAG: ";
constant str_length   : string :=
"; LENGTH: ";
constant str_src_addr : string :=
"; SRC. ADDR: ";
constant str_dst_addr : string :=
"; DST. ADDR: ";
constant str_type0 : string :=
"TYPE: Local2Local Write(no ACK)";
constant str_type1 : string :=
"TYPE: Local2Local Write(ACK)";
constant str_type2 : string :=
"TYPE: Local2Local Read";
constant str_type3 : string :=
"TYPE: Read Completition";
constant str_type4 : string :=
"TYPE: Write Completition";
constant str_type5 : string :=
"TYPE: Local2Global Write";
constant str_type6 : string :=
"TYPE: Global2Local Read";

begin

-- Wait when reset
wait until (IB_RESET = '0');
state := ST_HEAD1;


-- Insert Title
if (FILE_NAME /= "") then
   file_open(log_file, FILE_NAME, WRITE_MODE);
   write(out_line, str_info);
   writeline(log_file, out_line);
   write(out_line, str_null);
   writeline(log_file, out_line);
   file_close(log_file);
end if;

-- Do main loop
while true loop

wait until (IB_CLK'event and IB_CLK='1' and IB_IN.SRC_RDY_N='0' and IB_OUT.DST_RDY_N='0');

-- HEAD 1 ---------------------------------------------------------
if (state = ST_HEAD1 and IB_IN.SOP_N='0') then
   address1   := IB_IN.DATA(63 downto 32);
   trans_type := IB_IN.DATA(14 downto 12);
   trans_flag := IB_IN.DATA(15);
   length     := IB_IN.DATA(11 downto 0);
   tag        := IB_IN.DATA(31 downto 16);

   -- Write divider
   if (FILE_NAME /= "") then
      file_open(log_file, FILE_NAME, APPEND_MODE);
      write(out_line, str_divider);
      writeline(log_file, out_line);
   end if;

   if (trans_type = C_IB_L2LW_TRANSACTION and FILE_NAME /= "") then
      state := ST_HEAD2;
   elsif (trans_type = C_IB_L2LR_TRANSACTION and FILE_NAME /= "") then
      state := ST_HEAD2;
   elsif (trans_type = C_IB_WR_COMPL_TRANSACTION and FILE_NAME /= "") then
      state := ST_HEAD2;
   elsif (trans_type = C_IB_RD_COMPL_TRANSACTION and FILE_NAME /= "") then
      state := ST_HEAD2;
   elsif (trans_type = C_IB_L2GW_TRANSACTION and FILE_NAME /= "") then
      state := ST_HEAD2;
   elsif (trans_type = C_IB_G2LR_TRANSACTION and FILE_NAME /= "") then
      state := ST_HEAD2;
   else
      assert FILE_NAME = "" report "Unknown Transaction Type" severity ERROR;
   end if;
   file_close(log_file);




-- HEAD 2 ---------------------------------------------------------
elsif (state = ST_HEAD2) then


   if (FILE_NAME /= "") then
      file_open(log_file, FILE_NAME, APPEND_MODE);
   end if;

   if (trans_type = C_IB_L2LW_TRANSACTION and FILE_NAME /= "") then
      address2 := IB_IN.DATA(31 downto 0);
      if (trans_flag = '0') then
        write(out_line, str_type0);
      else
        write(out_line, str_type1);
      end if;
      write(out_line, str_length);
      hwrite(out_line, length);
      write(out_line, str_dst_addr);
      hwrite(out_line, address1);
      write(out_line, str_src_addr);
      hwrite(out_line, address2);
      writeline(log_file, out_line);
      state := ST_DATA;
   elsif (trans_type = C_IB_L2LR_TRANSACTION and FILE_NAME /= "") then
      address2 := IB_IN.DATA(31 downto 0);
      write(out_line, str_type2);
      write(out_line, str_length);
      hwrite(out_line, length);
      write(out_line, str_tag);
      hwrite(out_line, tag);
      write(out_line, str_src_addr);
      hwrite(out_line, address1);
      write(out_line, str_dst_addr);
      hwrite(out_line, address2);
      writeline(log_file, out_line);
      write(out_line, str_null);
      writeline(log_file, out_line);
      state := ST_HEAD1;

   elsif (trans_type = C_IB_RD_COMPL_TRANSACTION and FILE_NAME /= "") then
      address2 := IB_IN.DATA(31 downto 0);
      write(out_line, str_type3);
      state := ST_DATA;
      write(out_line, str_length);
      hwrite(out_line, length);
      write(out_line, str_tag);
      hwrite(out_line, tag);
      write(out_line, str_dst_addr);
      hwrite(out_line, address1);
      write(out_line, str_src_addr);
      hwrite(out_line, address2);
      writeline(log_file, out_line);

   elsif (trans_type = C_IB_WR_COMPL_TRANSACTION and FILE_NAME /= "") then
      address2 := IB_IN.DATA(31 downto 0);
      write(out_line, str_type4);
      state := ST_HEAD1;
      write(out_line, str_length);
      hwrite(out_line, length);
      write(out_line, str_tag);
      hwrite(out_line, tag);
      write(out_line, str_dst_addr);
      hwrite(out_line, address1);
      write(out_line, str_src_addr);
      hwrite(out_line, address2);
      writeline(log_file, out_line);
      write(out_line, str_null);
      writeline(log_file, out_line);

   elsif (trans_type = C_IB_L2GW_TRANSACTION and FILE_NAME /= "") then
      address2 := IB_IN.DATA(63 downto 32);
      write(out_line, str_type5);
      write(out_line, str_length);
      hwrite(out_line, length);
      write(out_line, str_tag);
      hwrite(out_line, tag);
      write(out_line, str_dst_addr);
      hwrite(out_line, address2 & address1);
      address1 := IB_IN.DATA(31 downto 0);
      write(out_line, str_src_addr);
      hwrite(out_line, address1);
      writeline(log_file, out_line);
      state := ST_DATA;

   elsif (trans_type = C_IB_G2LR_TRANSACTION and FILE_NAME /= "") then
      address2 := IB_IN.DATA(63 downto 32);
      write(out_line, str_type6);
      write(out_line, str_length);
      hwrite(out_line, length);
      write(out_line, str_tag);
      hwrite(out_line, tag);
      write(out_line, str_src_addr);
      hwrite(out_line, address2 & address1);
      address1 := IB_IN.DATA(31 downto 0);
      write(out_line, str_dst_addr);
      hwrite(out_line, address1);
      writeline(log_file, out_line);
      write(out_line, str_null);
      writeline(log_file, out_line);
      state := ST_HEAD1;
   end if;
   file_close(log_file);

-- DATA -----------------------------------------------------------
elsif (IB_IN.SRC_RDY_N='0') then
   data := IB_IN.DATA;

   if (FILE_NAME /= "") then
      file_open(log_file, FILE_NAME, APPEND_MODE);
      hwrite(out_line, data);
      writeline(log_file, out_line);
      file_close(log_file);
   end if;

   if (IB_IN.EOP_N='0') then
      if (FILE_NAME /= "") then
         file_open(log_file, FILE_NAME, APPEND_MODE);
         write(out_line, str_null);
         writeline(log_file, out_line);
         file_close(log_file);
      end if;
      state := ST_HEAD1;
   end if;


end if;

end loop;

end process;



end architecture IB_SIM_LOGING_ARCH;

