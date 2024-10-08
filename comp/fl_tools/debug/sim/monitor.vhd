--
-- Monitor.vhd: FrameLink monitoring unit fl_logging based
-- subcomponent
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
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.fl_pkg.all;
use work.fl_sim_oper.all;
use work.fl_bfm_rdy_pkg.all;
-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity MONITOR is
   generic(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH  : integer;
      FILE_NAME         : string;  -- Log File Path
      FRAME_PARTS       : integer;
      RDY_DRIVER        : RDYSignalDriver
   );
   port(
      -- Common interface
      FL_RESET          : in  std_logic;
      FL_CLK            : in  std_logic;

      -- RX Frame link Interface
      RX_DATA        : in std_logic_vector(RX_TX_DATA_WIDTH-1 downto 0);
      RX_REM         : in std_logic_vector(log2(RX_TX_DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic
     );
end entity MONITOR;

architecture MONITOR_ARCH of MONITOR is

-- inside FL BUS width
constant TX_DATA_WIDTH32 : integer   := 32;

-- end of packet character
constant sharp: character :='#';

-- end of part of packet character
constant dolar: character :='$';

-- FL FIFO constants
--constant DATA_WIDTH  : integer   := 32;
constant USE_BRAMS   : boolean   := true;
constant ITEMS       : integer   := 512000;
constant BLOCK_SIZE  : integer   := 15;
constant STATUS_WIDTH: integer   := 4;

-- inside FL buses
signal INBUS_DATA        : std_logic_vector(RX_TX_DATA_WIDTH-1 downto 0);
signal INBUS_REM         : std_logic_vector(log2(RX_TX_DATA_WIDTH/8)-1 downto 0);
signal INBUS_SOF_N       : std_logic;
signal INBUS_EOF_N       : std_logic;
signal INBUS_SOP_N       : std_logic;
signal INBUS_EOP_N       : std_logic;
signal INBUS_SRC_RDY_N   : std_logic;
signal INBUS_DST_RDY_N   : std_logic;

signal DATA        : std_logic_vector(RX_TX_DATA_WIDTH-1 downto 0);
signal DREM        : std_logic_vector(log2(RX_TX_DATA_WIDTH/8)-1 downto 0);
signal SOF_N       : std_logic;
signal EOF_N       : std_logic;
signal SOP_N       : std_logic;
signal EOP_N       : std_logic;
signal SRC_RDY_N   : std_logic;
signal DST_RDY_N   : std_logic;

signal AUX_FL_BUS: t_fl32;

-- FL FIFO control signals
signal LSTBLK        : std_logic;
signal EMPTY         : std_logic;
signal FULL          : std_logic;
signal STATUS        : std_logic_vector(STATUS_WIDTH-1 downto 0);
signal FRAME_RDY     : std_logic;

-- RDY signal
signal RDY_N : std_logic;
signal FIFO_RDY_N : std_logic;

begin

-- Repeater
  DATA<=RX_DATA;
  DREM<=RX_REM;
  SOF_N<=RX_SOF_N;
  EOF_N<=RX_EOF_N;
  SOP_N<=RX_SOP_N;
  EOP_N<=RX_EOP_N;
  SRC_RDY_N<=RX_SRC_RDY_N;
  RX_DST_RDY_N<=DST_RDY_N or FIFO_RDY_N;

RDY_N<= RX_SRC_RDY_N or DST_RDY_N or FIFO_RDY_N;

input_fifo:if (RX_TX_DATA_WIDTH > 8) generate
FL_FIFO_LOG: entity work.FL_FIFO
  generic map(
      -- Data width
      -- Should be multiple of 16: only 16,32,64,128 supported
      DATA_WIDTH=>RX_TX_DATA_WIDTH,
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS=>USE_BRAMS,
      -- number of items in the FIFO
      ITEMS=>ITEMS,
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE=>BLOCK_SIZE,
      -- Width of STATUS signal available
      STATUS_WIDTH=>STATUS_WIDTH,
      PARTS    => FRAME_PARTS
   )
   port map(
      CLK=>FL_CLK,
      RESET=>FL_RESET,

      -- write interface
      RX_DATA=>RX_DATA,
      RX_REM=>RX_REM,
      RX_SRC_RDY_N=>RDY_N,  -- RX_SRC_RDY_N
      RX_DST_RDY_N=>FIFO_RDY_N,
      RX_SOP_N=>RX_SOP_N,
      RX_EOP_N=>RX_EOP_N,
      RX_SOF_N=>RX_SOF_N,
      RX_EOF_N=>RX_EOF_N,

      -- read interface
      TX_DATA=>INBUS_DATA,
      TX_REM=>INBUS_REM,
      TX_SRC_RDY_N=>INBUS_SRC_RDY_N,
      TX_DST_RDY_N=>INBUS_DST_RDY_N,
      TX_SOP_N=>INBUS_SOP_N,
      TX_EOP_N=>INBUS_EOP_N,
      TX_SOF_N=>INBUS_SOF_N,
      TX_EOF_N=>INBUS_EOF_N,

      -- FIFO state signals
      LSTBLK=>LSTBLK,
      FULL=>FULL,
      EMPTY=>EMPTY,
      STATUS=>STATUS,
      FRAME_RDY=>FRAME_RDY
   );
end generate;

input_fifo8:if (RX_TX_DATA_WIDTH = 8) generate
FL_FIFO_LOG8: entity work.FL_FIFO8
  generic map(
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS=>USE_BRAMS,
      -- number of items in the FIFO
      ITEMS=>ITEMS,
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE=>BLOCK_SIZE,
      -- Width of STATUS signal available
      STATUS_WIDTH=>STATUS_WIDTH,
      PARTS    => FRAME_PARTS
   )
   port map(
      CLK=>FL_CLK,
      RESET=>FL_RESET,

      -- write interface
      RX_DATA=>RX_DATA,
      RX_SRC_RDY_N=>RDY_N,  -- RX_SRC_RDY_N
      RX_DST_RDY_N=>open,
      RX_SOP_N=>RX_SOP_N,
      RX_EOP_N=>RX_EOP_N,
      RX_SOF_N=>RX_SOF_N,
      RX_EOF_N=>RX_EOF_N,

      -- read interface
      TX_DATA=>INBUS_DATA,
      TX_SRC_RDY_N=>INBUS_SRC_RDY_N,
      TX_DST_RDY_N=>INBUS_DST_RDY_N,
      TX_SOP_N=>INBUS_SOP_N,
      TX_EOP_N=>INBUS_EOP_N,
      TX_SOF_N=>INBUS_SOF_N,
      TX_EOF_N=>INBUS_EOF_N,

      -- FIFO state signals
      LSTBLK=>LSTBLK,
      FULL=>FULL,
      EMPTY=>EMPTY,
      STATUS=>STATUS,
      FRAME_RDY=>FRAME_RDY
   );
   INBUS_REM <= (others => '0');
end generate;

-- FL TRANSFORMER
FL_TRASFORMER_U: entity work.FL_TRANSFORMER
   generic map (
      RX_DATA_WIDTH=>RX_TX_DATA_WIDTH,
      TX_DATA_WIDTH=>TX_DATA_WIDTH32
   )
   port map (
      CLK => FL_CLK,
      RESET=> FL_RESET,

      RX_DATA=>INBUS_DATA,
      RX_REM=>INBUS_REM,
      RX_SOF_N=>INBUS_SOF_N,
      RX_EOF_N=>INBUS_EOF_N,
      RX_SOP_N=>INBUS_SOP_N,
      RX_EOP_N=>INBUS_EOP_N,
      RX_SRC_RDY_N=>INBUS_SRC_RDY_N,
      RX_DST_RDY_N=>INBUS_DST_RDY_N,        -- open

      TX_DATA=>AUX_FL_BUS.DATA,
      TX_REM=>AUX_FL_BUS.DREM,
      TX_SOF_N=>AUX_FL_BUS.SOF_N,
      TX_EOF_N=>AUX_FL_BUS.EOF_N,
      TX_SOP_N=>AUX_FL_BUS.SOP_N,
      TX_EOP_N=>AUX_FL_BUS.EOP_N,
      TX_SRC_RDY_N=>AUX_FL_BUS.SRC_RDY_N,
      TX_DST_RDY_N=>AUX_FL_BUS.DST_RDY_N
   );

-- Logging process
main_process:process

-- variables
file output_file: TEXT;
variable file_status: file_open_status;
variable out_line   : line;
variable buff1: std_logic_vector(7 downto 0);
variable buff2: std_logic_vector(15 downto 0);
variable buff3: std_logic_vector(23 downto 0);


begin
   AUX_FL_BUS.DST_RDY_N<='1';
   wait until (FL_RESET='0');
   AUX_FL_BUS.DST_RDY_N<='0';
   -- Open output file for write
   assert (FILE_NAME/="") report "MONITOR: Empty file name!" severity failure;
   if (FILE_NAME/="") then
      file_open(file_status,output_file,FILE_NAME,write_mode);
      assert (file_status = OPEN_OK) report "MONITOR: File couldn't be created!" severity failure;
      if (file_status = OPEN_OK) then
         file_close(output_file);
         while (FL_RESET='0') loop
            wait until (FL_CLK'event and FL_CLK='1' and AUX_FL_BUS.SRC_RDY_N='0' and AUX_FL_BUS.DST_RDY_N='0');
            file_open(output_file,FILE_NAME,append_mode);
            -- FL DATA will be writen
            if (AUX_FL_BUS.DREM="00" and AUX_FL_BUS.EOP_N = '0') then
               buff1:=AUX_FL_BUS.DATA(7 downto 0);
               hwrite(out_line,buff1);
            else if (AUX_FL_BUS.DREM="01" and AUX_FL_BUS.EOP_N = '0') then
               buff2:=AUX_FL_BUS.DATA(15 downto 0);
               hwrite(out_line,buff2);
            else if (AUX_FL_BUS.DREM="10" and AUX_FL_BUS.EOP_N = '0') then
               buff3:=AUX_FL_BUS.DATA(23 downto 0);
               hwrite(out_line,buff3);
            else
               hwrite(out_line,AUX_FL_BUS.DATA);
            end if;
            end if;
            end if;
            writeline(output_file,out_line);
            -- End of part of packet and end of packet occured -> we will write '#' to the output file
            if (AUX_FL_BUS.EOP_N='0' and AUX_FL_BUS.EOF_N='0') then
               write(out_line,sharp);
               writeline(output_file,out_line);
            end if;
            -- End of part of packet occured -> we will write '$' to the output file
            if (AUX_FL_BUS.EOP_N='0' and AUX_FL_BUS.EOF_N='1') then
               write(out_line,dolar);
               writeline(output_file,out_line);
            end if;
            file_close(output_file);
         end loop;
      end if;
   end if;
   AUX_FL_BUS.DST_RDY_N<='1';
end process;

DRIVE_DST_RDY_N: PROCESS
  BEGIN
    LOOP
      IF (RDY_DRIVER = EVER) then
         DriveRdyNAll(FL_CLK, DST_RDY_N);
      elsif (RDY_DRIVER = ONOFF) then
         DriveRdyN50_50(FL_CLK, DST_RDY_N);
      elsif (RDY_DRIVER = RND) then
         DriveRdyNRnd(FL_CLK, DST_RDY_N);
      end if;
    END LOOP;
  END PROCESS;

end architecture MONITOR_ARCH;
