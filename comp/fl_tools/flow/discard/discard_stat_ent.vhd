-- discard_stat_ent.vhd: FrameLink Discard entity with statistics via MI32.
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl_discard_stat is
   generic(
      -- FrameLink data width
      DATA_WIDTH  : integer := 64;
      -- Number of channels, up to 64
      CHANNELS    : integer := 4;
      -- Width of the STATUS signal for each channel, up to 16 bits
      STATUS_WIDTH  : integer := 10;
      -- Width of counters, 16 to 64 bits
      CNT_WIDTH   : integer := 64;
      -- Enable various conters
      COUNT_DROP  : boolean := true;
      COUNT_PASS  : boolean := true;
      COUNT_DROP_LEN:boolean:= true;
      COUNT_PASS_LEN:boolean:= true;
      -- Generate output register on output FrameLink
      -- (It's possible because on output FrameLink is not used st_rdy_n signal)
      OUTPUT_REG    : boolean := true
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Write interface
         -- RX_DATA must carry frame length in the lowest 16 bits of the
         -- first frame word.
      RX_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_DREM     : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N: in  std_logic;
      RX_DST_RDY_N: out std_logic_vector(CHANNELS-1 downto 0);
      RX_SOP_N    : in  std_logic;
      RX_EOP_N    : in  std_logic;
      RX_SOF_N    : in  std_logic;
      RX_EOF_N    : in  std_logic;

      -- Must be valid with SOF
      RX_CHAN     : in  std_logic_vector(log2(CHANNELS) - 1 downto 0);

      -- Read interfaces
      TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_DREM     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic;
      -- TX_DST_RDY_N: in  std_logic;
      TX_SOP_N    : out std_logic;
      TX_EOP_N    : out std_logic;
      TX_SOF_N    : out std_logic;
      TX_EOF_N    : out std_logic;

      -- Is valid during the whole frame
      TX_CHAN     : out std_logic_vector(log2(CHANNELS) - 1 downto 0);

      -- STATUS interface displays number of full bytes
      STATUS      : in  std_logic_vector(CHANNELS*STATUS_WIDTH - 1 downto 0);

      -- MI32 interface
      MI_DWR      : in  std_logic_vector(31 downto 0);
      MI_ADDR     : in  std_logic_vector(31 downto 0);
      MI_BE       : in  std_logic_vector(3 downto 0);
      MI_RD       : in  std_logic;
      MI_WR       : in  std_logic;
      MI_DRDY     : out std_logic;
      MI_ARDY     : out std_logic;
      MI_DRD      : out std_logic_vector(31 downto 0)
   );
end entity fl_discard_stat;
