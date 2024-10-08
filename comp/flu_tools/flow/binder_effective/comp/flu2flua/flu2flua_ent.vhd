--
-- flu2flua_ent.vhd: Component for conversion of FLU to Aligned FLU
-- Copyright (C) 2014 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU2FLUA is
   generic(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH    : integer:= 256;
      SOP_POS_WIDTH : integer:= 2;

      -- Pipeline Config ------------------------
      -- Use input pipe
      IN_PIPE_EN           : boolean := false;
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      IN_PIPE_TYPE         : string := "SHREG";
      -- Use output register of input pipe
      IN_PIPE_OUTREG       : boolean := false;
      -- Use output pipe
      OUT_PIPE_EN          : boolean := false;
      -- same as IN_PIPE_TYPE
      OUT_PIPE_TYPE        : string := "SHREG";
      -- Use output register of input pipe
      OUT_PIPE_OUTREG      : boolean := false;
      -- Select PIPE compnent implementation
      -- Use "REG" for Intel devices
      -- Use "SHREG" for Xilinx devices
      PIPE_TYPE            : string := "REG";
      -- Base ID - if ID not enabled, ID output is not connected
      -- DISTRIBUTED_TO output will be disabled too
      ENABLE_DEBUG         : integer := 1;
      ID_WIDTH             : integer := 1;
      ID0_VAL              : integer := 0;
      ID1_VAL              : integer := 1;

      -- Align input flow
      ALIGN                : boolean := true;

      --! Enable/Disable header (which can be assigned to input FLU frame)
      --!   0 - Disable Header function
      --!   1 - Enable Header function
      HDR_ENABLE     : integer := 1;
      --! Widht of the header
      HDR_WIDTH      : integer := 128;
      --! Header FIFO configuration
      HDR_FIFO_ITEMS    : integer := 32
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Header input interface
      RX_HDR_DATA    : in std_logic_vector(HDR_WIDTH-1 downto 0);
      RX_HDR_SRC_RDY : in std_logic;
      RX_HDR_DST_RDY : out std_logic;

      -- Distributed to output (active when SOP = 1)
      DISTRIBUTED_TO : out std_logic;

      -- Frame Link Unaligned output lane 0
      TX_DATA0      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS0   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS0   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP0       : out std_logic;
      TX_EOP0       : out std_logic;
      TX_SRC_RDY0   : out std_logic;
      TX_DST_RDY0   : in std_logic;
      ID0           : out std_logic_vector(ID_WIDTH-1 downto 0);
      TX_HDR_DATA0  : out std_logic_vector(HDR_WIDTH-1 downto 0);

      -- Frame Link Unaligned output lane 1
      TX_DATA1      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS1   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS1   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP1       : out std_logic;
      TX_EOP1       : out std_logic;
      TX_SRC_RDY1   : out std_logic;
      TX_DST_RDY1   : in std_logic;
      ID1           : out std_logic_vector(ID_WIDTH-1 downto 0);
      TX_HDR_DATA1  : out std_logic_vector(HDR_WIDTH-1 downto 0)
   );
end entity;
