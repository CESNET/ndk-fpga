-- flu2fl_ent.vhd: Top level entity for FLU to FL converter
-- Copyright (C) 2012 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity flu2fl is
   generic(
      -- data width of input FLU and output FL interfaces
      DATA_WIDTH       : integer := 256;
      -- sop_pos width of input FLU
      SOP_POS_WIDTH    : integer := 2;
      -- use input pipe
      IN_PIPE_EN       : boolean := false;
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      IN_PIPE_TYPE     : string  := "SHREG";
      -- use output register of input pipe, only for IN_PIPE_TYPE = "SHREG"!
      IN_PIPE_OUTREG   : boolean := false;
      -- use output pipe
      OUT_PIPE_EN      : boolean := false;
      -- type of pipe implementation, same as IN_PIPE_TYPE
      OUT_PIPE_TYPE    : string  := "SHREG";
      -- use output register of input pipe, only for OUT_PIPE_TYPE = "SHREG"!
      OUT_PIPE_OUTREG  : boolean := false
   );
   port(
      -- common interface
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface (FLU)
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- output interface (FL)
      TX_SOF_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_DREM        : out std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0)
     );
end entity;
