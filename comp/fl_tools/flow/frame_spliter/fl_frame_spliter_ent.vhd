--
-- fl_frame_spliter_ent.vhd: Dividing frame link into two parts
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
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
use work.fl_pkg.all;
use work.fl_sim_oper.all;
-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity Frame_spliter is
   generic(
      -- FrameLink data bus width
      -- only 16, 32, 64 and 128 bit fl bus supported
      FL_WIDTH_IN  : integer := 32;
      FL_WIDTH_OUT1 : integer := 32;
      FL_WIDTH_OUT2 : integer := 32;
      Split_Pos   : integer := 1
   );
   port(
      -- Common interface
      FL_RESET            : in  std_logic;
      FL_CLK              : in  std_logic;

      -- Frame link Interface
      RX_DATA             : in std_logic_vector(FL_WIDTH_IN-1 downto 0);
      RX_REM              : in std_logic_vector(log2(FL_WIDTH_IN/8)-1 downto 0);
      RX_SOF_N            : in std_logic;
      RX_EOF_N            : in std_logic;
      RX_SOP_N            : in std_logic;
      RX_EOP_N            : in std_logic;
      RX_SRC_RDY_N        : in std_logic;
      RX_DST_RDY_N        : out  std_logic;

      TX_DATA_OUT1        : out std_logic_vector(FL_WIDTH_OUT1-1 downto 0);
      TX_REM_OUT1         : out std_logic_vector(log2(FL_WIDTH_OUT1/8)-1 downto 0);
      TX_SOF_N_OUT1       : out std_logic;
      TX_EOF_N_OUT1       : out std_logic;
      TX_SOP_N_OUT1       : out std_logic;
      TX_EOP_N_OUT1       : out std_logic;
      TX_SRC_RDY_N_OUT1   : out std_logic;
      TX_DST_RDY_N_OUT1   : in  std_logic;

      TX_DATA_OUT2        : out std_logic_vector(FL_WIDTH_OUT2-1 downto 0);
      TX_REM_OUT2         : out std_logic_vector(log2(FL_WIDTH_OUT2/8)-1 downto 0);
      TX_SOF_N_OUT2       : out std_logic;
      TX_EOF_N_OUT2       : out std_logic;
      TX_SOP_N_OUT2       : out std_logic;
      TX_EOP_N_OUT2       : out std_logic;
      TX_SRC_RDY_N_OUT2   : out std_logic;
      TX_DST_RDY_N_OUT2   : in  std_logic
     );
end entity;

