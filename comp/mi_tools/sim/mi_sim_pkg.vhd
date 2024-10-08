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

-- ----------------------------------------------------------------------------
--                        MI SIM Package
-- ----------------------------------------------------------------------------
package mi_sim_pkg is
   constant MAX_LINE_LENGHT : integer := 256;
   type TTransactionDirection is (READ, WRITE);

   type TTransaction is record
      DATA : std_logic_vector(31 downto 0);
      ADDR : std_logic_vector(31 downto 0);
      BE   : std_logic_vector(3 downto 0);
      DIRECTION : TTransactionDirection;
   end record;

   type TTransactionsArray is array (0 to 15) of TTransaction;


   type TCommandStatus is record
      BUSY : std_logic;
      REQ_ACK : std_logic;
      REQ  : std_logic;
   end record;

   type TCommandStatusArray is array (0 to 15) of TCommandStatus;

   signal status : TCommandStatusArray := (others => ('Z', 'Z', '0'));

   -- internaly used to synchronize model
   procedure WriteTransaction(variable trans : in TTransaction; constant mi_sim_id : in integer);
   procedure ReadTransaction(variable trans : out TTransaction; constant mi_sim_id : in integer);
   -- internaly used to read line from file and convert it to string
   procedure ReadStringLine(file inputFile : TEXT; variable outString : out string; variable stringLenght : inout integer);
   -- internaly used to convert line string to addr and data
   procedure ParseLine(variable stringLine : in string(1 to MAX_LINE_LENGHT); variable lineLenght : in integer;
                       variable addr : out std_logic_vector(31 downto 0);
                       variable data : out std_logic_vector(31 downto 0));
   procedure ParseLineForContWrite(variable stringLine : in string(1 to MAX_LINE_LENGHT); variable lineLenght : in integer;
                                   variable data : out std_logic_vector(31 downto 0));
   function HexaCharToStdLogic(ch :  character) return std_logic_vector;
   function to_upper(c:character) return character;

   -- std_logic_vector to hexa string. copied from http://www.stefanvhdl.com/vhdl/vhdl/txt_util.vhd
   function hstr(slv: std_logic_vector) return string;

   -- write data on address addr with byte enables be. status_cnt have to be status(x) and mi_sim_id have to be x
   procedure WriteData(variable addr : in std_logic_vector(31 downto 0);
                       variable data : in std_logic_vector(31 downto 0);
                       variable be : in std_logic_vector(3 downto 0);
                       signal status_cnt : inout TCommandStatus;
                       constant mi_sim_id : in integer);
   -- read data from address addr with byte enables be. status_cnt have to be status(x) and mi_sim_id have to be x
   procedure ReadData(variable addr : in std_logic_vector(31 downto 0);
                      variable data : out std_logic_vector(31 downto 0);
                      variable be : in std_logic_vector(3 downto 0);
                      signal status_cnt : inout TCommandStatus;
                      constant mi_sim_id : in integer);
   procedure WriteFileToMem(constant path : in string;
                       signal status_cnt : inout TCommandStatus;
                       constant mi_sim_id : in integer);
   -- Write data to file continuoslly from address start_address
   procedure WriteFileToMemCont(constant path : in string;
                                       variable start_address : in std_logic_vector(31 downto 0);
                                       signal status_cnt : inout TCommandStatus;
                                       constant mi_sim_id : in integer);
   procedure ReadMemToFileCont(constant path : in string;
                               variable start_address : in std_logic_vector(31 downto 0);
                               constant words_to_read : in integer;
                               signal status_cnt : inout TCommandStatus;
                               constant mi_sim_id : in integer);

end mi_sim_pkg;


-- ----------------------------------------------------------------------------
--                      MI SIM PKG BODY
-- ----------------------------------------------------------------------------
package body mi_sim_pkg is
   shared variable transactions : TTransactionsArray;


   procedure ReadTransaction(variable trans : out TTransaction; constant mi_sim_id : in integer) is
   begin
      trans := transactions(mi_sim_id);
   end procedure;

   procedure WriteTransaction(variable trans : in TTransaction; constant mi_sim_id : in integer) is
   begin
      transactions(mi_sim_id) := trans;
   end procedure;

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

   -- copied from http://www.stefanvhdl.com/vhdl/vhdl/txt_util.vhd
   function hstr(slv: std_logic_vector) return string is
       variable hexlen: integer;
       variable longslv : std_logic_vector(67 downto 0) := (others => '0');
       variable hex : string(1 to 16);
       variable fourbit : std_logic_vector(3 downto 0);
     begin
       hexlen := (slv'left+1)/4;
       if (slv'left+1) mod 4 /= 0 then
         hexlen := hexlen + 1;
       end if;
       longslv(slv'left downto 0) := slv;
       for i in (hexlen -1) downto 0 loop
         fourbit := longslv(((i*4)+3) downto (i*4));
         case fourbit is
           when "0000" => hex(hexlen -I) := '0';
           when "0001" => hex(hexlen -I) := '1';
           when "0010" => hex(hexlen -I) := '2';
           when "0011" => hex(hexlen -I) := '3';
           when "0100" => hex(hexlen -I) := '4';
           when "0101" => hex(hexlen -I) := '5';
           when "0110" => hex(hexlen -I) := '6';
           when "0111" => hex(hexlen -I) := '7';
           when "1000" => hex(hexlen -I) := '8';
           when "1001" => hex(hexlen -I) := '9';
           when "1010" => hex(hexlen -I) := 'A';
           when "1011" => hex(hexlen -I) := 'B';
           when "1100" => hex(hexlen -I) := 'C';
           when "1101" => hex(hexlen -I) := 'D';
           when "1110" => hex(hexlen -I) := 'E';
           when "1111" => hex(hexlen -I) := 'F';
           when "ZZZZ" => hex(hexlen -I) := 'z';
           when "UUUU" => hex(hexlen -I) := 'u';
           when "XXXX" => hex(hexlen -I) := 'x';
           when others => hex(hexlen -I) := '?';
         end case;
       end loop;
       return hex(1 to hexlen);
     end hstr;

   function HexaCharToStdLogic(ch :character) return std_logic_vector is
   begin
      case to_upper(ch) is
         when '0' => return X"0";
         when '1' => return X"1";
         when '2' => return X"2";
         when '3' => return X"3";
         when '4' => return X"4";
         when '5' => return X"5";
         when '6' => return X"6";
         when '7' => return X"7";
         when '8' => return X"8";
         when '9' => return X"9";
         when 'A' => return X"A";
         when 'B' => return X"B";
         when 'C' => return X"C";
         when 'D' => return X"D";
         when 'E' => return X"E";
         when 'F' => return X"F";
         when others => return "ZZZZ";
      end case;
   end function;

   -- Modified version from fl_bfm_pkg.vhd
   procedure ReadStringLine(file inputFile : TEXT;
                            variable outString : out string;
                            variable stringLenght : inout integer) is
      variable fileLine : line;
      variable char : character;
      variable notEof : boolean;
   begin
      stringLenght := 0;
      readline(inputFile, fileLine);
      for i in outString'range loop
         read(fileLine, char, notEof);
         if (not notEof) then
            exit;
         end if;
         outString(i) := char;
         stringLenght :=  stringLenght + 1;
      end loop;
   end procedure;

   procedure ParseLine(variable stringLine : in string(1 to MAX_LINE_LENGHT); variable lineLenght : in integer;
                       variable addr : out std_logic_vector(31 downto 0);
                       variable data : out std_logic_vector(31 downto 0)) is
      variable i : integer;
   begin
      for i in 1 to 8 loop
         addr((32-((i-1)*4)-1) downto (32-((i-1)*4)-4)) := HexaCharToStdLogic(stringLine(i));
      end loop;

      for i in 10 to 17 loop
         data((32-(i-10)*4-1) downto (32-(i-10)*4-4)) := HexaCharToStdLogic(stringLine(i));
      end loop;
   end procedure;


   procedure ParseLineForContWrite(variable stringLine : in string(1 to MAX_LINE_LENGHT); variable lineLenght : in integer;
                                   variable data : out std_logic_vector(31 downto 0)) is
      variable i : integer;
   begin
      for i in 1 to 8 loop
         data((32-((i-1)*4)-1) downto (32-((i-1)*4)-4)) := HexaCharToStdLogic(stringLine(i));
      end loop;
   end procedure;



   procedure WriteData(variable addr : in std_logic_vector(31 downto 0);
                       variable data : in std_logic_vector(31 downto 0);
                       variable be : in std_logic_vector(3 downto 0);
                       signal status_cnt : inout TCommandStatus;
                       constant mi_sim_id : in integer) is
      variable transaction : TTransaction;
   begin
      transaction.ADDR := addr;
      transaction.DATA := data;
      transaction.BE := be;
      transaction.DIRECTION := WRITE;

      transactions(mi_sim_id) := transaction;
      status_cnt.REQ <= '1';
      wait on status_cnt.REQ_ACK;
      status_cnt.REQ <= '0';
      wait until status_cnt.BUSY = '0';

   end procedure;


   procedure ReadData(variable addr : in std_logic_vector(31 downto 0);
                      variable data : out std_logic_vector(31 downto 0);
                      variable be : in std_logic_vector(3 downto 0);
                      signal status_cnt : inout TCommandStatus;
                      constant mi_sim_id : in integer) is
      variable transaction : TTransaction;
   begin
      transaction.ADDR := addr;
      transaction.BE := be;
      transaction.DIRECTION := READ;
      transactions(mi_sim_id) := transaction;
      status_cnt.REQ <= '1';
      wait on status_cnt.REQ_ACK;
      status_cnt.REQ <= '0';
      wait until status_cnt.BUSY = '0';
      data := transactions(mi_sim_id).DATA;
   end procedure;

   procedure WriteFileToMem(constant path : in string;
                       signal status_cnt : inout TCommandStatus;
                       constant mi_sim_id : in integer) is
      file inputFile : TEXT;
      variable fileStatus : file_open_status;
      variable fileLine : string(1 to MAX_LINE_LENGHT);
      variable fileLineLenght : integer;
      variable addr : std_logic_vector(31 downto 0);
      variable be : std_logic_vector(3 downto 0);
      variable data : std_logic_vector(31 downto 0);
   begin
      file_open(fileStatus, inputFile, path, READ_MODE);
      assert (fileStatus = OPEN_OK) report "Error when opening file: " & path severity error;
      be := "1111";

      while (not endfile(inputFile)) loop
         ReadStringLine(inputFile, fileLine, fileLineLenght);
         if (fileLine(1) /= '#' and fileLineLenght > 1) then
            ParseLine(fileLine, fileLineLenght, addr, data);
            WriteData(addr, data, be, status_cnt, mi_sim_id);
         end if;
      end loop;

      file_close(inputFile);
   end procedure;


   procedure WriteFileToMemCont(constant path : in string;
                                       variable start_address : in std_logic_vector(31 downto 0);
                                       signal status_cnt : inout TCommandStatus;
                                       constant mi_sim_id : in integer) is
      file inputFile : TEXT;
      variable fileStatus : file_open_status;
      variable fileLine : string(1 to MAX_LINE_LENGHT);
      variable fileLineLenght : integer;
      variable addr : std_logic_vector(31 downto 0);
      variable be : std_logic_vector(3 downto 0);
      variable data : std_logic_vector(31 downto 0);
   begin
      file_open(fileStatus, inputFile, path, READ_MODE);
      assert (fileStatus = OPEN_OK) report "Error when opening file: " & path severity error;
      be := "1111";
      addr := start_address;

      while (not endfile(inputFile)) loop
         ReadStringLine(inputFile, fileLine, fileLineLenght);
         if (fileLine(1) /= '#' and fileLineLenght > 1) then
            ParseLineForContWrite(fileLine, fileLineLenght, data);
            WriteData(addr, data, be, status_cnt, mi_sim_id);
            addr := addr + 4;
         end if;
      end loop;
      file_close(inputFile);
   end procedure;


   procedure ReadMemToFileCont(constant path : in string;
                               variable start_address : in std_logic_vector(31 downto 0);
                               constant words_to_read : in integer;
                               signal status_cnt : inout TCommandStatus;
                               constant mi_sim_id : in integer) is
      file outputFile : TEXT;
      variable fileStatus : file_open_status;
      variable fileLine : line;
      variable i : integer;
      variable addr : std_logic_vector(31 downto 0);
      variable be : std_logic_vector(3 downto 0);
      variable data : std_logic_vector(31 downto 0);
   begin
      i := 0;
      file_open(fileStatus, outputFile, path,  WRITE_MODE);
      assert (fileStatus = OPEN_OK) report "Error when opening file for write: " & path severity error;
      addr := start_address;
      be := "1111";

      while (i < words_to_read) loop
         ReadData(addr, data, be, status_cnt, mi_sim_id);
         write(fileLine, hstr(data));
         writeline(outputFile, fileLine);
         addr := addr + 4;
         i := i + 1;
      end loop;

      file_close(outputFile);

   end procedure;






end mi_sim_pkg;
