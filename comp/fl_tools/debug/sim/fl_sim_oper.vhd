-- fl_sim_oper.vhd: Support package for fl_sim
-- Copyright (C) 2006 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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

package fl_sim_oper is
-- types declaration
-- t_file_name type
   type t_file_name is record
      LEN   : integer;
      ARR   : string(1 to 256);
   end record;

-- t_fl_ctrl type
   type t_fl_ctrl is record
     file_name: t_file_name;
     device: std_logic;
   end record;


-- functions and procedures declaration
-- read variable length string from input file
procedure read_string(file in_file: TEXT;  --input file
                      out_string: out string;  --output string
                      load_count: inout integer); --number of read characters
-- convert character to upper case
function to_upper(c:character) return character;
-- convert hexa character to std_logic_vector
procedure convert_character(data:inout std_logic_vector; -- output 4-bit number
                            c:character);  -- input hexa value in character
-- load 32bit number from input string
procedure load_32(data:inout std_logic_vector; -- 32bit number
                  s:string;  -- input string
                  i:inout integer; -- current position in string
                  size:integer;  -- size of string
                  count: inout std_logic_vector); -- count of valid bytes in 32-bit number
-- convert file name in string to t_fl_ctrl
function fl_send32(file_name:string) return t_fl_ctrl;

end fl_sim_oper;

package body fl_sim_oper is

-- convert file name in string to t_file_name
function conv_file_name(file_name : string) return t_file_name is
variable result : t_file_name;
begin
   result.len := file_name'length;
   result.arr(1 to result.len) := file_name;
   return result;
end;

-- read variable length string from input file
procedure read_string(file in_file: TEXT;out_string: out string;load_count: inout integer) is
variable l:line;
variable c:character;
variable not_eof: boolean;
begin
  load_count:=0;
  readline(in_file, l);
  -- read characters from line up to length of string or end of line
     for i in out_string'range loop
        read(l, c, not_eof);
        out_string(i) := c;
        if not not_eof then -- end of line
           exit;
        end if;
        load_count:=load_count+1;
     end loop;

end read_string;

-- convert character to upper case
function to_upper(c:character) return character is
variable output:character;
begin
  case c is
    when 'a' => output := 'A';
    when 'b' => output := 'B';
    when 'c' => output := 'C';
    when 'd' => output := 'D';
    when 'e' => output := 'E';
    when 'f' => output := 'F';
    when others => output := c;
  end case;
  return output;
end;

-- convert hexa character to std_logic_vector
procedure convert_character(data:inout std_logic_vector;c:character) is
variable c_decoded:std_logic_vector(3 downto 0);
variable lbound:integer;
begin
  case to_upper(c) is
    when '0'=> c_decoded :="0000";
    when '1'=> c_decoded :="0001";
    when '2'=> c_decoded :="0010";
    when '3'=> c_decoded :="0011";
    when '4'=> c_decoded :="0100";
    when '5'=> c_decoded :="0101";
    when '6'=> c_decoded :="0110";
    when '7'=> c_decoded :="0111";
    when '8'=> c_decoded :="1000";
    when '9'=> c_decoded :="1001";
    when 'A'=> c_decoded :="1010";
    when 'B'=> c_decoded :="1011";
    when 'C'=> c_decoded :="1100";
    when 'D'=> c_decoded :="1101";
    when 'E'=> c_decoded :="1110";
    when 'F'=> c_decoded :="1111";
    when others => c_decoded :="ZZZZ";
  end case;
  lbound:=data'left - 4;
  data:=data(lbound downto 0)&c_decoded;
end convert_character;

-- load 32bit number from input string
procedure load_32(data:inout std_logic_vector;s:string;i:inout integer;size:integer;count: inout std_logic_vector) is
variable j:integer;
begin
  for j in 0 to 31 loop
    data(j):='0';
  end loop;
  count:="00";
  convert_character(data,s(i));
  i:=i+1;
  convert_character(data,s(i));
  i:=i+1;
  if (i<size) then
      count:=count+'1';
      convert_character(data,s(i));
      i:=i+1;
      convert_character(data,s(i));
      i:=i+1;
  end if;
  if (i<size) then
      count:=count+'1';
      convert_character(data,s(i));
      i:=i+1;
      convert_character(data,s(i));
      i:=i+1;
  end if;
  if (i<size) then
      count:=count+'1';
      convert_character(data,s(i));
      i:=i+1;
      convert_character(data,s(i));
      i:=i+1;
  end if;
end load_32;

-- convert file name in string to t_fl_ctrl
function fl_send32(file_name:string) return t_fl_ctrl is
variable result:t_fl_ctrl;
begin
  result.file_name:=conv_file_name(file_name);
  result.device:='0';
  return result;
end fl_send32;

end fl_sim_oper;
