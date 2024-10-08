-- flu_bfm_pkg.vhd: Support package for flu_bfm
-- Copyright (C) 2014 CESNET
-- Author(s): Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;
use work.flu_bfm_rdy_pkg.all;

-- ----------------------------------------------------------------------------
--                    FrameLinkUnaligned Bus BFM Package
-- ----------------------------------------------------------------------------
PACKAGE flu_bfm_pkg IS
   TYPE StartDriveType  IS (SOP, NOP);
   TYPE EndDriveType    IS (EOP, NOP);
   CONSTANT DataTypeLength : integer := 65535;
   TYPE Item IS RECORD
      Data         : std_logic_vector(7 downto 0);
      Space        : integer;
      StartControl :StartDriveType;
      EndControl   :EndDriveType;
   END RECORD;

   TYPE DataType IS ARRAY (0 TO DataTypeLength) of Item;

   -- Operation parameters
   TYPE CmdTypeItem IS RECORD
      RDYDriver      : RDYSignalDriver;
      Length         : integer;                       -- Length
      Data           : DataType;                      -- Data
   END RECORD;

   TYPE CmdType IS ARRAY (0 to 15) of CmdTypeItem;

   -- Command REQ/ACK record
   TYPE fluCmdTypeItem IS
      RECORD
         Req      : std_logic;
         ReqAck   : std_logic;
         Ack      : std_logic;
      END RECORD;

   ----------------------------------------------------------------------------
   -- SIGNAL FOR SETTINGS BFM REQUESTS
   ----------------------------------------------------------------------------
   signal fluCmd_0 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_1 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_2 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_3 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_4 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_5 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_6 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_7 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_8 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_9 : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_A : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_B : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_C : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_D : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_E : fluCmdTypeItem := ('0','Z','Z');
   signal fluCmd_F : fluCmdTypeItem := ('0','Z','Z');

   ----------------------------------------------------------------------------
   -- BFM FUNCTIONS
   ----------------------------------------------------------------------------

   -- Function is called by IB BFM model to obtain command parameters
   PROCEDURE ReadCommand (VARIABLE Cmd : OUT CmdTypeItem; CONSTANT FLUBFMID : IN integer);

   ----------------------------------------------------------------------------
   -- Function is called by IB BFM model to return results
   PROCEDURE WriteCommand (VARIABLE Cmd  : IN CmdTypeItem; CONSTANT FLUBFMID : IN integer);

   -- convert character to upper case
   function to_upper(c:character) return character;

   -- convert hexa character to std_logic_vector
   procedure convert_character(data:inout std_logic_vector; -- output 4-bit number
                              c:character);  -- input hexa value in character

   -- converts a three-digit number from string into integer
   function to_integer(s: string) return integer;

   -- converts integer to string(1 to 3)
   function int2str(int: integer) return string;

   -- load 32bit number from input string
   procedure load_32(data:inout std_logic_vector; -- 32bit number
                     s:string;  -- input string
                     i:inout integer; -- current position in string
                     size:integer;  -- size of string
                     count: inout integer); -- count of valid bytes in 32-bit number

   -- read variable length string from input file
   procedure read_string(file in_file: TEXT;  --input file
                         out_string: out string;  --output string
                         load_count: inout integer); --number of read characters

   PROCEDURE SendWriteFile (
      CONSTANT FileName : IN string;               -- Filename from where are data writen
      CONSTANT RDYDriver: IN RDYSignalDriver;
      SIGNAL fluCmd : INOUT fluCmdTypeItem;
      CONSTANT FLUBFMID  : IN integer
   );
END flu_bfm_pkg;

-- ----------------------------------------------------------------------------
--                 FrameLinkUnaligned Bus BFM Package BODY
-- ----------------------------------------------------------------------------
PACKAGE BODY flu_bfm_pkg IS

   -----------------------------------------------------------------------------
   -- Command shared variable
   SHARED  VARIABLE Command : CmdType;

   -----------------------------------------------------------------------------
   -- Functions is called by IB BFM model to obtain command parameters
   PROCEDURE ReadCommand (VARIABLE Cmd : OUT CmdTypeItem; CONSTANT FLUBFMID : IN integer) IS
   BEGIN
      Cmd := Command(FLUBFMID);
   END;

   -----------------------------------------------------------------------------
   -- Functions is called by IB BFM model to return results
   PROCEDURE WriteCommand (VARIABLE Cmd  : IN CmdTypeItem; CONSTANT FLUBFMID : IN integer) IS
   BEGIN
      Command(FLUBFMID) := Cmd;
   END;

   -- read variable length string from input file
   procedure read_string(file in_file: TEXT;out_string: out string; load_count: inout integer) is
      variable l:line;
      variable c:character;
      variable not_eol: boolean;
   begin
      load_count:=0;
      readline(in_file, l);
      -- read characters from line up to length of string or end of line
      for i in out_string'range loop
         read(l, c, not_eol);
         out_string(i) := c;
         if not not_eol then -- end of line
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

   -- converts a three-digit number from string into integer
   function to_integer(s: string) return integer is
      variable int100: integer;
      variable int10: integer;
      variable int1: integer;
      variable int: integer;
      variable slv : std_logic_vector(3 downto 0);
   begin
      convert_character(slv, s(1));
      int100 := conv_integer(slv);
      convert_character(slv, s(2));
      int10 := conv_integer(slv);
      convert_character(slv, s(3));
      int1 := conv_integer(slv);

      int := int100*100 + int10*10 + int1;
      return int;
   end to_integer;

   -- converts integer to string(1 to 3)
   function int2str(int: integer) return string is
      variable str : string(1 to 3);
   begin
      if int < 10 then
         str := '0' & '0' & integer'image(int);
      elsif int < 100 then
         str := '0' & integer'image(int);
      else
         str := integer'image(int);
      end if;
      return str;
   end int2str;

   -- load 32bit number from input string
   procedure load_32(data:inout std_logic_vector;s:string;i:inout integer;size:integer;count: inout integer) is
      variable j:integer;
   begin
      data(31 downto 0) := (others => '0');
      count := 0;
      convert_character(data,s(i+1));
      i:=i+1;
      convert_character(data,s(i-1));
      i:=i+1;
      if (i<size) then
         count:=count + 1;
         convert_character(data,s(i+1));
         i:=i+1;
         convert_character(data,s(i-1));
         i:=i+1;
      end if;
      if (i<size) then
         count:=count + 1;
         convert_character(data,s(i+1));
         i:=i+1;
         convert_character(data,s(i-1));
         i:=i+1;
      end if;
      if (i<size) then
         count:=count + 1;
         convert_character(data,s(i+1));
         i:=i+1;
         convert_character(data,s(i-1));
         i:=i+1;
      end if;
   end load_32;

   PROCEDURE SendWriteFile (
      CONSTANT FileName : IN string;                   -- Filename from where are data writen
      CONSTANT RDYDriver: IN RDYSignalDriver;
      SIGNAL fluCmd     : INOUT fluCmdTypeItem;
      CONSTANT FLUBFMID  : IN integer
   ) IS
      file     input_file  : TEXT;
      variable file_status : file_open_status;
      variable s           : string(1 to 2048);
      variable number       : string(1 to 3);
      variable size        : integer;
      variable index       : integer;
      variable count       : integer;
      variable i           : integer;
      variable j           : integer;
      variable data        : std_logic_vector(31 downto 0);

   BEGIN
      for i in 0 to DataTypeLength loop
         Command(FLUBFMID).Data(i).StartControl := NOP;
         Command(FLUBFMID).Data(i).EndControl := NOP;
      end loop;
      Command(FLUBFMID).Data(0).StartControl := SOP;

      index := 0;
      file_open(file_status, input_file, FileName, READ_MODE);
      assert (file_status = OPEN_OK) report "File with data was not found!" severity ERROR;

      while (not endfile(input_file)) loop
         read_string(input_file, s, size);
         i := 1;
         if (s(i) = '$') then
            -- Read space between packets
            number := s(2) & s(3) & s(4);
            Command(FLUBFMID).Data(index).Space := to_integer(number);

            if (not(index-1 <= 0)) then
               Command(FLUBFMID).Data(index - 1).EndControl := EOP;
            else
               Command(FLUBFMID).Data(index).EndControl := NOP;
            end if;
            Command(FLUBFMID).Data(index).StartControl := SOP;

         elsif (s(i) = '-') then

         else
            while (i<=size) loop
               load_32(data, s, i, size, count);
	            for j in count downto 0 loop
	               Command(FLUBFMID).Data(index).Data := data((j + 1) * 8 - 1 downto j * 8);
	               index := index + 1;
	            end loop;
            end loop;
         end if;
      end loop;
      Command(FLUBFMID).Data(index - 1).EndControl := EOP;
      file_close(input_file);
      Command(FLUBFMID).Length := index - 1;
      Command(FLUBFMID).RDYDriver := RDYDriver;

      -- Req toggles each time we want the BFM to do a new check.
      fluCmd.Req <= '1';
      WAIT ON fluCmd.ReqAck;
      fluCmd.Req <= '0';
      WAIT UNTIL fluCmd.Ack = '1';

   END SendWriteFile;
END flu_bfm_pkg;
