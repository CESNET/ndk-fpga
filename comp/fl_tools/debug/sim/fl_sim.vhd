--
-- fl_sim.vhd: Simulation component for Frame link
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
use work.fl_pkg.all;
use work.fl_sim_oper.all;
-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_SIM is
   generic(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      DATA_WIDTH  : integer;
      RX_LOG_FILE : string:="";
      TX_LOG_FILE : string:="";
      FRAME_PARTS : integer
   );
   port(
      -- Common interface
      FL_RESET          : in  std_logic;
      FL_CLK            : in  std_logic;

      -- Frame link Interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic;

      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;

      -- FL SIM interface
      CTRL              : in  t_fl_ctrl;
      STROBE            : in  std_logic;
      BUSY              : out std_logic
     );
end entity FL_SIM;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_SIM_ARCH of FL_SIM is

constant STATUS_WIDTH: integer   := 4;

-- Signals
signal AUX_FL_BUS: t_fl32;
signal AUX_FL_BUS2: t_fl32;
signal AUX_FL_BUS3: t_fl32;

signal INBUS1_DATA        : std_logic_vector(DATA_WIDTH-1 downto 0);
signal INBUS1_REM         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal INBUS1_SOF_N       : std_logic;
signal INBUS1_EOF_N       : std_logic;
signal INBUS1_SOP_N       : std_logic;
signal INBUS1_EOP_N       : std_logic;
signal INBUS1_SRC_RDY_N   : std_logic;
signal INBUS1_DST_RDY_N   : std_logic;

signal INBUS2_DATA        : std_logic_vector(DATA_WIDTH-1 downto 0);
signal INBUS2_REM         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal INBUS2_SOF_N       : std_logic;
signal INBUS2_EOF_N       : std_logic;
signal INBUS2_SOP_N       : std_logic;
signal INBUS2_EOP_N       : std_logic;
signal INBUS2_SRC_RDY_N   : std_logic;
signal INBUS2_DST_RDY_N   : std_logic;

signal INBUS3_DATA        : std_logic_vector(DATA_WIDTH-1 downto 0);
signal INBUS3_REM         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal INBUS3_SOF_N       : std_logic;
signal INBUS3_EOF_N       : std_logic;
signal INBUS3_SOP_N       : std_logic;
signal INBUS3_EOP_N       : std_logic;
signal INBUS3_SRC_RDY_N   : std_logic;
signal INBUS3_DST_RDY_N   : std_logic;

-- FL FIFO control signals
signal LSTBLK        : std_logic;
signal EMPTY         : std_logic;
signal FULL          : std_logic;
signal STATUS        : std_logic_vector(STATUS_WIDTH-1 downto 0);
signal FRAME_RDY     : std_logic;
-- FL FIFO constants
--constant DATA_WIDTH  : integer   := 32;
constant USE_BRAMS   : boolean   := true;
constant ITEMS       : integer   := 32768;
constant BLOCK_SIZE  : integer   := 15;
-- Inside bus width
constant RX_DATA_WIDTH32 : integer   := 32;
begin

-- FL_SIM_LOGGING RX
FL_SIM_LOGGING_RX_U: entity work.FL_SIM_LOGGING
   generic map(
      -- FrameLink data bus width
      -- only 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH=>DATA_WIDTH,
      FILE_NAME=>RX_LOG_FILE,
      FRAME_PARTS => FRAME_PARTS
   )
   port map(
      -- Common interface
      FL_RESET=>FL_RESET,
      FL_CLK=>FL_CLK,

      -- RX Frame link Interface
      RX_DATA=>RX_DATA,
      RX_REM=>RX_REM,
      RX_SOF_N=>RX_SOF_N,
      RX_EOF_N=>RX_EOF_N,
      RX_SOP_N=>RX_SOP_N,
      RX_EOP_N=>RX_EOP_N,
      RX_SRC_RDY_N=>RX_SRC_RDY_N,
      RX_DST_RDY_N=>RX_DST_RDY_N,

     -- TX Frame link Interface
      TX_DATA=>INBUS3_DATA,
      TX_REM=>INBUS3_REM,
      TX_SOF_N=>INBUS3_SOF_N,
      TX_EOF_N=>INBUS3_EOF_N,
      TX_SOP_N=>INBUS3_SOP_N,
      TX_EOP_N=>INBUS3_EOP_N,
      TX_SRC_RDY_N=>INBUS3_SRC_RDY_N,
      TX_DST_RDY_N=>INBUS3_DST_RDY_N
     );

-- FL_SIM_LOGGING TX
FL_SIM_LOGGING_TX_U: entity work.FL_SIM_LOGGING
   generic map(
      -- FrameLink data bus width
      -- only 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH=>DATA_WIDTH,
      FILE_NAME=>TX_LOG_FILE,
      FRAME_PARTS=>FRAME_PARTS
   )
   port map(
      -- Common interface
      FL_RESET=>FL_RESET,
      FL_CLK=>FL_CLK,

      -- RX Frame link Interface
      RX_DATA=>INBUS2_DATA,
      RX_REM=>INBUS2_REM,
      RX_SOF_N=>INBUS2_SOF_N,
      RX_EOF_N=>INBUS2_EOF_N,
      RX_SOP_N=>INBUS2_SOP_N,
      RX_EOP_N=>INBUS2_EOP_N,
      RX_SRC_RDY_N=>INBUS2_SRC_RDY_N,
      RX_DST_RDY_N=>INBUS2_DST_RDY_N,

     -- TX Frame link Interface
      TX_DATA=>TX_DATA,
      TX_REM=>TX_REM,
      TX_SOF_N=>TX_SOF_N,
      TX_EOF_N=>TX_EOF_N,
      TX_SOP_N=>TX_SOP_N,
      TX_EOP_N=>TX_EOP_N,
      TX_SRC_RDY_N=>TX_SRC_RDY_N,
      TX_DST_RDY_N=>TX_DST_RDY_N
     );

-- FL FIFO
   FL_FIFO_32: entity work.FL_FIFO_FL32
   generic map
   (
      USE_BRAMS   => USE_BRAMS,
      ITEMS       => ITEMS,
      BLOCK_SIZE  => BLOCK_SIZE,
      STATUS_WIDTH=> STATUS_WIDTH,
      PARTS => FRAME_PARTS
   )
   port map
   (
      CLK            => FL_CLK,
      RESET          => FL_RESET,

      -- write interface
      RX.DATA        => AUX_FL_BUS2.DATA,
      RX.DREM         => AUX_FL_BUS2.DREM,
      RX.SRC_RDY_N   => AUX_FL_BUS2.SRC_RDY_N,
      RX.DST_RDY_N   => AUX_FL_BUS2.DST_RDY_N,
      RX.SOP_N       => AUX_FL_BUS2.SOP_N,
      RX.EOP_N       => AUX_FL_BUS2.EOP_N,
      RX.SOF_N       => AUX_FL_BUS2.SOF_N,
      RX.EOF_N       => AUX_FL_BUS2.EOF_N,

      -- read interface
      TX.DATA        => AUX_FL_BUS3.DATA,
      TX.DREM         => AUX_FL_BUS3.DREM,
      TX.SRC_RDY_N   => AUX_FL_BUS3.SRC_RDY_N,
      TX.DST_RDY_N   => AUX_FL_BUS3.DST_RDY_N,
      TX.SOP_N       => AUX_FL_BUS3.SOP_N,
      TX.EOP_N       => AUX_FL_BUS3.EOP_N,
      TX.SOF_N       => AUX_FL_BUS3.SOF_N,
      TX.EOF_N       => AUX_FL_BUS3.EOF_N,

      -- FIFO state signals
   LSTBLK      => LSTBLK,
   FULL        => FULL,
   EMPTY       => EMPTY,
   STATUS      => STATUS,
   FRAME_RDY   => FRAME_RDY
   );

-- FL TRANSFORMER
FL_TRASFORMER_U: entity work.FL_TRANSFORMER
   generic map (
      RX_DATA_WIDTH=>RX_DATA_WIDTH32,
      TX_DATA_WIDTH=>DATA_WIDTH
   )
   port map (
      CLK => FL_CLK,
      RESET=> FL_RESET,

      RX_DATA=>AUX_FL_BUS3.DATA,
      RX_REM=>AUX_FL_BUS3.DREM,
      RX_SOF_N=>AUX_FL_BUS3.SOF_N,
      RX_EOF_N=>AUX_FL_BUS3.EOF_N,
      RX_SOP_N=>AUX_FL_BUS3.SOP_N,
      RX_EOP_N=>AUX_FL_BUS3.EOP_N,
      RX_SRC_RDY_N=>AUX_FL_BUS3.SRC_RDY_N,
      RX_DST_RDY_N=>AUX_FL_BUS3.DST_RDY_N,

      TX_DATA=>INBUS1_DATA,
      TX_REM=>INBUS1_REM,
      TX_SOF_N=>INBUS1_SOF_N,
      TX_EOF_N=>INBUS1_EOF_N,
      TX_SOP_N=>INBUS1_SOP_N,
      TX_EOP_N=>INBUS1_EOP_N,
      TX_SRC_RDY_N=>INBUS1_SRC_RDY_N,
      TX_DST_RDY_N=>INBUS1_DST_RDY_N
   );

-- FL bus multiplexors
  INBUS2_DATA<=INBUS1_DATA when (CTRL.device='0') else INBUS3_DATA;
  INBUS2_REM<=INBUS1_REM when (CTRL.device='0') else INBUS3_REM;
  INBUS2_SOF_N<=INBUS1_SOF_N when (CTRL.device='0') else INBUS3_SOF_N;
  INBUS2_EOF_N<=INBUS1_EOF_N when (CTRL.device='0') else INBUS3_EOF_N;
  INBUS2_SOP_N<=INBUS1_SOP_N when (CTRL.device='0') else INBUS3_SOP_N;
  INBUS2_EOP_N<=INBUS1_EOP_N when (CTRL.device='0') else INBUS3_EOP_N;
  INBUS2_SRC_RDY_N<=INBUS1_SRC_RDY_N when (CTRL.device='0') else INBUS3_SRC_RDY_N;
  INBUS3_DST_RDY_N<=INBUS2_DST_RDY_N when (CTRL.device/='0' or RX_LOG_FILE="") else '1';
  INBUS1_DST_RDY_N<=INBUS2_DST_RDY_N when (CTRL.device='0') else '1';


-- reseting fl_sim when reset is required
reset_service:
  AUX_FL_BUS2.EOF_N<='1' when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.EOF_N;
  AUX_FL_BUS2.EOP_N<='1' when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.EOP_N;
  AUX_FL_BUS2.SOF_N<='1' when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.SOF_N;
  AUX_FL_BUS2.SOP_N<='1' when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.SOP_N;
  AUX_FL_BUS2.DATA<=X"00000000" when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.DATA;
  AUX_FL_BUS2.DREM<="11" when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.DREM;
  AUX_FL_BUS2.SRC_RDY_N<='1' when (FL_RESET = '1' or STROBE='1' or not(CTRL.DEVICE='0' or CTRL.DEVICE='1')) else AUX_FL_BUS.SRC_RDY_N;
  AUX_FL_BUS.DST_RDY_N<=AUX_FL_BUS2.DST_RDY_N;

main:process
file input_file:TEXT;
variable file_status: file_open_status;
variable s:string(1 to 2048);
variable c:character;
variable size,i:integer;
variable is_first:std_logic;
variable data:std_logic_vector(31 downto 0);
variable count:std_logic_vector(1 downto 0);
begin
BUSY<= '0';
-- Wait when reset
wait until (FL_RESET = '0');
-- Do main loop
while true loop
BUSY <= '0';
wait until ((STROBE = '1')and (CTRL.DEVICE='0'));
BUSY <= '1';
-- Open input file for read
file_open(file_status,input_file,CTRL.file_name.arr(1 to CTRL.file_name.len),read_mode);
if (file_status = OPEN_OK) then
  AUX_FL_BUS.SRC_RDY_N<='0';
  is_first:='1';
  --Do read loop until end of file
  while ((not endfile(input_file))and(FL_RESET='0')) loop
  read_string(input_file,s,size);
  i:=1;
  if (is_first='1') then
     wait until (FL_CLK'event and FL_CLK='1');
     is_first:='0';
     AUX_FL_BUS.SOF_N<='0';
     AUX_FL_BUS.SOP_N<='0';
  else if (s(i)='#') then -- end of frame
         --wait until (AUX_FL_BUS.DST_RDY_N='0');
         AUX_FL_BUS.EOF_N<='0';
         AUX_FL_BUS.EOP_N<='0';
         --AUX_FL_BUS.SOF_N<='1';
         AUX_FL_BUS.DATA<=data;
         AUX_FL_BUS.DREM<=count;
         wait until (FL_CLK'event and FL_CLK='1' and AUX_FL_BUS.DST_RDY_N='0');
         AUX_FL_BUS.EOF_N<='1';
         AUX_FL_BUS.EOP_N<='1';
         AUX_FL_BUS.SOF_N<='0';
         AUX_FL_BUS.SOP_N<='0';
         if not endfile(input_file) then
           read_string(input_file,s,size);
           i:=1;
         end if;
       else if (s(i)='$') then -- end of packet in frame
         --wait until (AUX_FL_BUS.DST_RDY_N='0');
         AUX_FL_BUS.EOP_N<='0';
         AUX_FL_BUS.EOF_N<='1';
         AUX_FL_BUS.DATA<=data;
         AUX_FL_BUS.DREM<=count;
         wait until (FL_CLK'event and FL_CLK='1' and AUX_FL_BUS.DST_RDY_N='0');
         AUX_FL_BUS.SOF_N<='1';
         AUX_FL_BUS.EOP_N<='1';
         AUX_FL_BUS.SOP_N<='0';
         if not endfile(input_file) then
           read_string(input_file,s,size);
           i:=1;
         end if;
      else  -- packet continue on the next line
        -- wait until (AUX_FL_BUS.DST_RDY_N='0');
         AUX_FL_BUS.EOF_N<='1';
         AUX_FL_BUS.EOP_N<='1';
         AUX_FL_BUS.DATA<=data;
         AUX_FL_BUS.DREM<=count;
         wait until (FL_CLK'event and FL_CLK='1' and AUX_FL_BUS.DST_RDY_N='0');
         AUX_FL_BUS.SOF_N<='1';
         AUX_FL_BUS.SOP_N<='1';
       end if;
    end if;
  end if;
  -- read values from string
  while (i<=size)and(s(i)/='#')and(s(i)/='$')and(FL_RESET='0') loop
    count:="00";
    load_32(data,s,i,size,count);  --read 8-32bits from string
    if (i+1)<size then
      -- 32bits were read, write them to FL BUS
     -- wait until (AUX_FL_BUS.DST_RDY_N='0');
      AUX_FL_BUS.EOF_N<='1';
      AUX_FL_BUS.EOP_N<='1';
      AUX_FL_BUS.DATA<=data;
      AUX_FL_BUS.DREM<=count;
      wait until (FL_CLK'event and FL_CLK='1' and AUX_FL_BUS.DST_RDY_N='0');
      AUX_FL_BUS.SOF_N<='1';
      AUX_FL_BUS.SOP_N<='1';
    end if;
  end loop;
  end loop;
  file_close(input_file);
end if; -- No other data will be writen
AUX_FL_BUS.SRC_RDY_N<='1';
AUX_FL_BUS.EOF_N<='1';
AUX_FL_BUS.EOP_N<='1';
AUX_FL_BUS.SOF_N<='1';
AUX_FL_BUS.SOP_N<='1';
AUX_FL_BUS.DATA<=X"00000000";
AUX_FL_BUS.DREM<="11";
BUSY <= '0';
end loop;
end process;
end architecture FL_SIM_ARCH;
