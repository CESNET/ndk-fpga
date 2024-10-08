-- storage_init_pkg.vhd: Storage Init PKG
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        STORAGE INIT Declaration
-- ----------------------------------------------------------------------------
package ib_sim_oper is

   -- t_ib_oper type
   type t_ib_oper is (LOCAL_READ, LOCAL_READ_FILE, LOCAL_WRITE, LOCAL_WRITE_FILE, LOCAL_WRITE_FILE32,
                      READ_COMPLETITION, WRITE_COMPLETITION);

   -- t_file_name type
   type t_file_name is record
      LEN   : integer;
      ARR   : string(1 to 256);
   end record;

   -- t_ib_params type
   type t_ib_params is record
      DST_ADDR       : std_logic_vector(31 downto 0);
      SRC_ADDR       : std_logic_vector(31 downto 0);
      LENGTH         : integer;
      TAG            : integer;
      TRANS_FLAG     : std_logic;
      DATA           : std_logic_vector(63 downto 0);
      FILE_NAME      : t_file_name;
   end record;

   -- t_ib_ctrl type
   type t_ib_ctrl is record
      OPER           : t_ib_oper;
      PARAMS         : t_ib_params;
      READ_WAIT      : boolean;
   end record;

   -- t_ib_status type
   type t_ib_status is record
      DO    : std_logic_vector(63 downto 0);
      DV    : std_logic;
   end record;



-- function declaration ---------------------------------------
   -- Send Local Read Transaction
                          -- Address from where are data readed
   function ib_local_read(src_addr    : in std_logic_vector(31 downto 0);
                          -- Destination address of completition transaction
                          dst_addr    : in std_logic_vector(31 downto 0);
                          -- Number of bytes to be readed
                          length      : in integer;
                          -- Transaction Tag
                          tag         : in integer;
                          -- Wait for completition transaction
                          read_wait   : in boolean:=false)
                     return t_ib_ctrl;

   -- Send Local Read Transaction (Readed data is saved to file)
                               -- Address from where are data readed
   function ib_local_read_file(src_addr    : in std_logic_vector(31 downto 0);
                               -- Destination address of completition transaction
                               dst_addr    : in std_logic_vector(31 downto 0);
                               -- Number of bytes to be readed
                               length      : in integer;
                               -- Transaction Tag
                               tag         : in integer;
                               -- Filename where are readed data saved (64 bit hexa values)
                               file_name   : in string)
                     return t_ib_ctrl;

   -- Send Local Write Transaction (up to 64 bits of data)
                           -- Destination addres of write transaction
   function ib_local_write(dst_addr   : in std_logic_vector(31 downto 0);
                           -- From where are write transaction generated
                           src_addr   : in std_logic_vector(31 downto 0);
                           -- Length of writen data
                           length     : in integer;
                           -- Transaction Tag
                           tag        : in integer;
                           -- 0 - No ACK/ 1 - Write completition ACK
                           trans_flag : in std_logic;
                           -- Data to be writen
                           data       : in std_logic_vector(63 downto 0))
                     return t_ib_ctrl;

   -- Send Local Write Transaction (Write data from file)
                                -- Destination address of write transaction
   function ib_local_write_file(dst_addr   : in std_logic_vector(31 downto 0);
                                -- From where are write transaction generated
                                src_addr   : in std_logic_vector(31 downto 0);
                                -- Length of writen data (when 0 all data from file is writen)
                                length     : in integer;
                                -- Transaction Tag
                                tag        : in integer;
                                -- 0 - No ACK/ 1 - Write completition ACK
                                trans_flag : in std_logic;
                                -- Filename from where are data writen (64 bit hexa values)
                                file_name  : in string)
                     return t_ib_ctrl;

   -- Send Local Write Transaction (Write 32 bit data from file)
                                  -- Destination address of write transaction
   function ib_local_write_file32(dst_addr   : in std_logic_vector(31 downto 0);
                                  -- From where are write transaction generated
                                  src_addr   : in std_logic_vector(31 downto 0);
                                  -- Length of writen data (when 0 all data from file is writen)
                                  length     : in integer;
                                  -- Transaction Tag
                                  tag        : in integer;
                                  -- 0 - No ACK/ 1 - Write completition ACK
                                  trans_flag : in std_logic;
                                  -- Filename from where are data writen (64 bit hexa values)
                                  file_name  : in string)
                     return t_ib_ctrl;


   -- Send Read Completition Transaction without Last Fragment Flag (Write data from file)
                                 -- Destination address of read completition
   function ib_read_completition_nolast(dst_addr    : in std_logic_vector(31 downto 0);
                                 -- Src address of completition transaction
                                 src_addr    : in std_logic_vector(31 downto 0);
                                 -- Transaction Length (when 0 all data from file is writen)
                                 length      : in integer;
                                 -- Transaction Tag
                                 tag         : in integer;
                                 -- Filename from where are data writen
                                 file_name   : in string)
                     return t_ib_ctrl;

   -- Send Read Completition Transaction with Last Frament Flag (Write data from file)
                                 -- Destination address of read completition
   function ib_read_completition(dst_addr    : in std_logic_vector(31 downto 0);
                                 -- Src address of completition transaction
                                 src_addr    : in std_logic_vector(31 downto 0);
                                 -- Transaction Length (when 0 all data from file is writen)
                                 length      : in integer;
                                 -- Transaction Tag
                                 tag         : in integer;
                                 -- Filename from where are data writen
                                 file_name   : in string)
                     return t_ib_ctrl;

   -- Send Write Completition Transaction
                                  -- Destination address of write completition
   function ib_write_completition(dst_addr    : in std_logic_vector(31 downto 0);
                                  -- Src address of completition transaction
                                  src_addr    : in std_logic_vector(31 downto 0);
                                  -- Transaction Length
                                  length      : in integer;
                                  -- Transaction Tag
                                  tag         : in integer)
                     return t_ib_ctrl;

-- AUX Functions ----------------------------------------------------------------------------------------
   -- Count Number of lines in file
   function file_line_count(file_name : in string) return integer;


end ib_sim_oper;


-- ----------------------------------------------------------------------------
--                      INTERNAL BUS OPERATIONS
-- ----------------------------------------------------------------------------
package body ib_sim_oper is


-- ----------------------------------------------------------------
-- function conv_file_name converts string type into the t_file_name
-- type
--
-- Parameters:
--    file_name : filename in string format
--
function conv_file_name(file_name : string) return t_file_name is
variable result : t_file_name;
begin
   result.len := file_name'length;
   result.arr(1 to result.len) := file_name;
   return result;
end;

-- ----------------------------------------------------------------
-- function conv_fn_file_name converts t_file_name type into the string
-- type
--
-- Parameters:
--    file_name : filename in t_file_name format
--
function conv_fn_string(file_name : t_file_name) return string is
begin
   return file_name.arr(1 to file_name.len);
end;

-- ----------------------------------------------------------------
-- Count Number of lines in file
function file_line_count(file_name : in string) return integer is
   file     in_file      : text;
   variable in_line      : line;
   variable readFlag     : boolean;
   variable data         : std_logic_vector(63 downto 0);
   variable i            : integer;
   begin
   i:=0;
   file_open(in_file, file_name, READ_MODE);
   while not (endfile(in_file)) loop
      readline(in_file, in_line);
      i:=i+1;
   end loop;
   file_close(in_file);
   return i;
end;


-- ---------------------------------------------------------------------------
   -- Send Local Read Transaction
                          -- Address from where are data readed
   function ib_local_read(src_addr    : in std_logic_vector(31 downto 0);
                          -- Destination address of completition transaction
                          dst_addr    : in std_logic_vector(31 downto 0);
                          -- Number of bytes to be readed
                          length      : in integer;
                          -- Transaction Tag
                          tag         : in integer;
                          -- Wait for completition transaction
                          read_wait   : in boolean:=false)
                     return t_ib_ctrl is

    variable result: t_ib_ctrl;
      begin
      result.OPER              :=LOCAL_READ;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TRANS_FLAG :='0';
      result.READ_WAIT         :=read_wait;
      return result;
    end;

-- ---------------------------------------------------------------------------
   -- Send Local Read Transaction (Readed data is saved to file)
                               -- Address from where are data readed
   function ib_local_read_file(src_addr    : in std_logic_vector(31 downto 0);
                               -- Destination address of completition transaction
                               dst_addr    : in std_logic_vector(31 downto 0);
                               -- Number of bytes to be readed
                               length      : in integer;
                               -- Transaction Tag
                               tag         : in integer;
                               -- Filename where are readed data saved (64 bit hexa values)
                               file_name   : in string)
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=LOCAL_READ_FILE;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TRANS_FLAG :='0';
      result.READ_WAIT         :=true;
      result.PARAMS.FILE_NAME  :=conv_file_name(file_name);
      return result;
   end;

   -- ---------------------------------------------------------------------------
   -- Send Local Write Transaction (up to 64 bits of data)
                           -- Destination addres of write transaction
   function ib_local_write(dst_addr   : in std_logic_vector(31 downto 0);
                           -- From where are write transaction generated
                           src_addr   : in std_logic_vector(31 downto 0);
                           -- Length of writen data
                           length     : in integer;
                           -- Transaction Tag
                           tag        : in integer;
                           -- 0 - No ACK/ 1 - Write completition ACK
                           trans_flag : in std_logic;
                           -- Data to be writen
                           data       : in std_logic_vector(63 downto 0))
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=LOCAL_WRITE;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.TRANS_FLAG :=trans_flag;
      result.PARAMS.DATA       :=data;
      return result;
    end;

-- ---------------------------------------------------------------------------
   -- Send Local Write Transaction (Write data from file)
                                -- Destination address of write transaction
   function ib_local_write_file(dst_addr   : in std_logic_vector(31 downto 0);
                                -- From where are write transaction generated
                                src_addr   : in std_logic_vector(31 downto 0);
                                -- Length of writen data
                                length     : in integer;
                                -- Transaction Tag
                                tag        : in integer;
                                -- 0 - No ACK/ 1 - Write completition ACK
                                trans_flag : in std_logic;
                                -- Filename from where are data writen (64 bit hexa values)
                                file_name  : in string)
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=LOCAL_WRITE_FILE;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.TRANS_FLAG :=trans_flag;
      result.PARAMS.FILE_NAME  :=conv_file_name(file_name);
      return result;
    end;


-- Send Local Write Transaction (Write 32 bit data from file)
                                  -- Destination address of write transaction
   function ib_local_write_file32(dst_addr   : in std_logic_vector(31 downto 0);
                                  -- From where are write transaction generated
                                  src_addr   : in std_logic_vector(31 downto 0);
                                  -- Length of writen data (when 0 all data from file is writen)
                                  length     : in integer;
                                  -- Transaction Tag
                                  tag        : in integer;
                                  -- 0 - No ACK/ 1 - Write completition ACK
                                  trans_flag : in std_logic;
                                  -- Filename from where are data writen (64 bit hexa values)
                                  file_name  : in string)
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=LOCAL_WRITE_FILE32;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.TRANS_FLAG :=trans_flag;
      result.PARAMS.FILE_NAME  :=conv_file_name(file_name);
      return result;
    end;


-- ---------------------------------------------------------------------------
   -- Send Read Completition Transaction with Last Fragment Flag (Write data from file)
                                 -- Destination address of read completition
   function ib_read_completition(dst_addr    : in std_logic_vector(31 downto 0);
                                 -- Src address of completition transaction
                                 src_addr    : in std_logic_vector(31 downto 0);
                                 -- Transaction Length
                                 length      : in integer;
                                 -- Transaction Tag
                                 tag         : in integer;
                                 -- Filename from where are data writen
                                 file_name   : in string)
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=READ_COMPLETITION;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TAG        :=tag;
      -- Used to pass the Last Fragment Flag value
      result.PARAMS.TRANS_FLAG :='1';
      result.PARAMS.FILE_NAME  :=conv_file_name(file_name);
      return result;
   end;

-- ---------------------------------------------------------------------------
   -- Send Read Completition Transaction without Last Fragment Flag (Write data from file)
                                 -- Destination address of read completition
   function ib_read_completition_nolast(dst_addr    : in std_logic_vector(31 downto 0);
                                 -- Src address of completition transaction
                                 src_addr    : in std_logic_vector(31 downto 0);
                                 -- Transaction Length
                                 length      : in integer;
                                 -- Transaction Tag
                                 tag         : in integer;
                                 -- Filename from where are data writen
                                 file_name   : in string)
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=READ_COMPLETITION;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.TRANS_FLAG :='0'; -- Used to pass Last Fragment Flag value
      result.PARAMS.FILE_NAME  :=conv_file_name(file_name);
      return result;
   end;


-- ---------------------------------------------------------------------------
   -- Send Write Completition Transaction
                                  -- Destination address of write completition
   function ib_write_completition(dst_addr    : in std_logic_vector(31 downto 0);
                                  -- Src address of completition transaction
                                  src_addr    : in std_logic_vector(31 downto 0);
                                  -- Transaction Length
                                  length      : in integer;
                                  -- Transaction Tag
                                  tag         : in integer)
                     return t_ib_ctrl is
   variable result: t_ib_ctrl;
      begin
      result.OPER              :=WRITE_COMPLETITION;
      result.PARAMS.SRC_ADDR   :=src_addr;
      result.PARAMS.DST_ADDR   :=dst_addr;
      result.PARAMS.LENGTH     :=length;
      result.PARAMS.TAG        :=tag;
      result.PARAMS.TRANS_FLAG :='1';
      return result;
   end;


end ib_sim_oper;

