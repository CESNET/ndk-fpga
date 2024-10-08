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
entity RR_SELECT is
   generic(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH     : integer:= 512;
      SOP_POS_WIDTH  : integer:= 3;
      --! Number of input input interfaces
      INPUTS         : integer := 2;

      --! ID information width. If not enabled, ID output is not
      --! connected.
      ENABLE_ID      : integer := 1;
      ID_WIDTH       : integer := 1;

      -- Pipeline Config ------------------------
      -- Use input pipe
      OUT_PIPE_EN    : boolean := false;

      --! Enable/Disable header (which can be assigned to input FLU frame)
      --!   0 - Disable Header function
      --!   1 - Enable Header function
      HDR_ENABLE     : integer := 1;
      --! Widht of the header
      HDR_WIDTH      : integer := 128;

      --! Enable DSP multiplexing
      ENABLE_DSP     : boolean := false
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
      RX_DATA       : in std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(INPUTS*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(INPUTS*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic_vector(INPUTS-1 downto 0);
      RX_EOP        : in std_logic_vector(INPUTS-1 downto 0);
      RX_SRC_RDY    : in std_logic_vector(INPUTS-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUTS-1 downto 0);
      ID_IN         : in std_logic_vector(INPUTS*ID_WIDTH-1 downto 0);
      RX_HDR        : in std_logic_vector(INPUTS*HDR_WIDTH-1 downto 0);

      -- --------------------------------------------------
      -- \name Frame Link Unaligned output interface
      -- --------------------------------------------------
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic;
      ID_OUT         : out std_logic_vector(ID_WIDTH-1 downto 0);
      TX_HDR         : out std_logic_vector(HDR_WIDTH-1 downto 0)
   );
end entity;
