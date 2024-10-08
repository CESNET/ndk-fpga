--
-- align_ent.vhd: FLU align component
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
entity FLUA_BINDER is
   generic(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH     : integer:= 256;
      SOP_POS_WIDTH  : integer:= 2;

      --! ID WIDTH
      ID_WIDTH       : integer := 1;
      ENABLE_ID      : integer := 1;

      -- Pipeline Config ------------------------
      -- Use output pipe
      OUT_PIPE_EN          : boolean := false;
      -- Use output register of input pipe
      OUT_PIPE_OUTREG      : boolean := false;

      --! Enable/Disable header (which can be assigned to input FLU frame)
      --!   0 - Disable Header function
      --!   1 - Enable Header function
      HDR_ENABLE     : integer := 1;
      --! Widht of the header
      HDR_WIDTH      : integer := 128;

      --! Enable/disable the reservation of 128 bit gap
      --! NOTICE: If you enable this functionality, you should be sure
      --! that the minimal length of the frame (in bytes) + 128/8 is
      --! bigger or equal to DATA_WIDTH/8. Because this functionality
      --! is tightly bounded with usage in network module and the
      --! FSM needs to be optimized for that usage.
      --!   0 - Disable insertion of the 128 bit gap between FLU frames
      --!   1 - Enable insertion of the 128 bit gap between FLU frames
      RESERVE_GAP_EN : boolean := true
   );
   port(
       -- -------------------------------------------------
       -- \name Common interface
       -- -------------------------------------------------
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- --------------------------------------------------
      -- \name Frame Link Unaligned input interface
      -- --------------------------------------------------
      -- RX Lane 0
      RX_HDR_DATA0  : in std_logic_vector(HDR_WIDTH-1 downto 0);
      RX_DATA0      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS0   : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS0   : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP0       : in std_logic;
      RX_EOP0       : in std_logic;
      RX_SRC_RDY0   : in std_logic;
      RX_DST_RDY0   : out std_logic;
      ID0           : in std_logic_vector(ID_WIDTH-1 downto 0);

      -- RX Lane 1
      RX_HDR_DATA1  : in std_logic_vector(HDR_WIDTH-1 downto  0);
      RX_DATA1      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS1   : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS1   : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP1       : in std_logic;
      RX_EOP1       : in std_logic;
      RX_SRC_RDY1   : in std_logic;
      RX_DST_RDY1   : out std_logic;
      ID1           : in std_logic_vector(ID_WIDTH-1 downto 0);

      -- --------------------------------------------------
      -- \name Frame Link Unaligned output interface
      -- --------------------------------------------------
      TX_HDR_DATA    : out std_logic_vector(HDR_WIDTH-1 downto 0);
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic;
      ID             : out std_logic_vector(ID_WIDTH-1 downto 0)
   );
end entity;
