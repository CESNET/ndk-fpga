-- fl_bfm_pkg.vhd: Support package for bfm_sim
-- Copyright (C) 2007 CESNET
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;
use work.fl_bfm_rdy_pkg.all;

-- ----------------------------------------------------------------------------
--                        FrameLink Bus BFM Package
-- ----------------------------------------------------------------------------
PACKAGE fl_bfm_pkg IS
  TYPE StartDriveType  IS (SOP, SOF, NOP);
  TYPE EndDriveType    IS (EOP, EOF, NOP);
  CONSTANT DataTypeLength : integer := 65535;
  TYPE Item IS RECORD
    Data         : std_logic_vector(7 downto 0);
    StartControl :StartDriveType;
    EndControl   :EndDriveType;
  END RECORD;

  TYPE DataType IS ARRAY (0 TO DataTypeLength) of Item;

  -- Operation parameters
  TYPE CmdTypeItem IS RECORD
    RDYDriver      : RDYSignalDriver;
    Length         : integer;                       -- Length
    Data           : DataType;                      -- Data
    --Enable         : boolean;
    --FileName       : FileNameType;
  END RECORD;

  TYPE CmdType IS ARRAY (0 to 15) of CmdTypeItem;

  -- Command REQ/ACK record
  TYPE flCmdTypeItem IS
    RECORD
      Req      : std_logic;
      ReqAck   : std_logic;
      Ack      : std_logic;
    END RECORD;

  ----------------------------------------------------------------------------
  -- SIGNAL FOR SETTINGS BFM REQUESTS
  ----------------------------------------------------------------------------
 signal flCmd_0 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_1 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_2 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_3 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_4 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_5 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_6 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_7 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_8 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_9 : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_A : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_B : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_C : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_D : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_E : flCmdTypeItem := ('0','Z','Z');
 signal flCmd_F : flCmdTypeItem := ('0','Z','Z');

  ----------------------------------------------------------------------------
  -- BFM FUNCTIONS
  ----------------------------------------------------------------------------

  ----------------------------------------------------------------------------
  -- Functions is called by IB BFM model to obtain command parameters
  PROCEDURE ReadCommand (VARIABLE Cmd : OUT CmdTypeItem; CONSTANT FLBFMID : IN integer);

  ----------------------------------------------------------------------------
  -- Functions is called by IB BFM model to return results
  PROCEDURE WriteCommand (VARIABLE Cmd  : IN CmdTypeItem; CONSTANT FLBFMID : IN integer);

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
                    count: inout integer); -- count of valid bytes in 32-bit number

  -- read variable length string from input file
  procedure read_string(file in_file: TEXT;  --input file
                        out_string: out string;  --output string
                        load_count: inout integer); --number of read characters

  procedure SendPreparedData(
    CONSTANT RDYDriver  : IN RDYSignalDriver;
    SIGNAL   flCmd      : INOUT flCmdTypeItem;
    CONSTANT FLBFMID    : IN integer;
    CONSTANT Cmd        : IN CmdType
    );

  PROCEDURE SendWriteFile (
    CONSTANT FileName : IN string;                        -- Filename from where are data writen
    CONSTANT RDYDriver: IN RDYSignalDriver;
    SIGNAL flCmd : INOUT flCmdTypeItem;
    CONSTANT FLBFMID  : IN integer
    );
END fl_bfm_pkg;


-- ----------------------------------------------------------------------------
--                      FrameLink Bus BFM Package BODY
-- ----------------------------------------------------------------------------
PACKAGE BODY fl_bfm_pkg IS

  -----------------------------------------------------------------------------
  -- Command shared variable
  SHARED  VARIABLE Command : CmdType;

  -----------------------------------------------------------------------------
  -- Functions is called by IB BFM model to obtain command parameters
  PROCEDURE ReadCommand (VARIABLE Cmd : OUT CmdTypeItem; CONSTANT FLBFMID : IN integer) IS
  BEGIN
    Cmd := Command(FLBFMID);
  END;

  -----------------------------------------------------------------------------
  -- Functions is called by IB BFM model to return results
  PROCEDURE WriteCommand (VARIABLE Cmd  : IN CmdTypeItem; CONSTANT FLBFMID : IN integer) IS
  BEGIN
    Command(FLBFMID) := Cmd;
  END;

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
  procedure load_32(data:inout std_logic_vector;s:string;i:inout integer;size:integer;count: inout integer) is
  variable j:integer;
  begin
    data(31 downto 0) := (others => '0');
    count := 0;
    convert_character(data,s(i));
    i:=i+1;
    convert_character(data,s(i));
    i:=i+1;
    if (i<size) then
      count:=count + 1;
      convert_character(data,s(i));
      i:=i+1;
      convert_character(data,s(i));
      i:=i+1;
    end if;
    if (i<size) then
      count:=count + 1;
      convert_character(data,s(i));
      i:=i+1;
      convert_character(data,s(i));
      i:=i+1;
    end if;
    if (i<size) then
      count:=count + 1;
      convert_character(data,s(i));
      i:=i+1;
      convert_character(data,s(i));
      i:=i+1;
    end if;
  end load_32;

  -- Send data prepared in the Cmd parameter
  procedure SendPreparedData(
    CONSTANT RDYDriver  : IN RDYSignalDriver;
    SIGNAL   flCmd      : INOUT flCmdTypeItem;
    CONSTANT FLBFMID    : IN integer;
    CONSTANT Cmd        : IN CmdType
    ) IS
  begin
    Command(FLBFMID) := Cmd(FLBFMID);
    flCmd.Req <= '1';
    WAIT ON flCmd.ReqAck;
    flCmd.Req <= '0';
    WAIT ON flCmd.Ack;
  end SendPreparedData;


  PROCEDURE SendWriteFile (
    CONSTANT FileName : IN string;                        -- Filename from where are data writen
    CONSTANT RDYDriver: IN RDYSignalDriver;
    SIGNAL flCmd : INOUT flCmdTypeItem;
    CONSTANT FLBFMID  : IN integer
    ) IS
    file     input_file  : TEXT;
    variable file_status : file_open_status;
    variable s           : string(1 to 2048);
    variable size        : integer;
    variable index       : integer;
    variable count       : integer;
    variable i           : integer;
    variable data        : std_logic_vector(31 downto 0);

  BEGIN
    for i in 0 to DataTypeLength loop
      Command(FLBFMID).Data(i).StartControl := NOP;
      Command(FLBFMID).Data(i).EndControl := NOP;
    end loop;
    Command(FLBFMID).Data(0).StartControl := SOF;

    index := 0;
    file_open(file_status, input_file, FileName, READ_MODE);
    assert (file_status = OPEN_OK) report "File with data was not found!" severity ERROR;

    while (not endfile(input_file)) loop
       read_string(input_file, s, size);
       i := 1;
       if (s(i) = '#') then
          assert (not(index - 1 <= 0)) report "# found on file start" severity ERROR;
          Command(FLBFMID).Data(index - 1).EndControl := EOF;
	  Command(FLBFMID).Data(index).StartControl := SOF;
          --i := i + 1;
       elsif (s(i) = '$') then
          assert (not(index - 1 <= 0)) report "$ found on file start" severity ERROR;
          Command(FLBFMID).Data(index - 1).EndControl := EOP;
	  Command(FLBFMID).Data(index).StartControl := SOP;
          --i := i + 1;
       elsif (s(i) = '-') then

       else
         while (i<=size) loop
           load_32(data, s, i, size, count);
	   for j in 0 to count loop
	      Command(FLBFMID).Data(index).Data := data((j + 1) * 8 - 1 downto j * 8);
	      index := index + 1;
	   end loop;
         end loop;
       end if;
    end loop;
    file_close(input_file);
    Command(FLBFMID).Length := index - 1;
    Command(FLBFMID).RDYDriver := RDYDriver;

    -- Req toggles each time we want the BFM to do a new check.
    flCmd.Req <= '1';
    WAIT ON flCmd.ReqAck;
    flCmd.Req <= '0';
    WAIT UNTIL flCmd.Ack = '1';

  END SendWriteFile;

END fl_bfm_pkg;
