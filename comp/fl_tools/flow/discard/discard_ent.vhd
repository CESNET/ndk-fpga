-- discard_ent.vhd: FrameLink Discard entity.
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
entity fl_discard is
   generic (
      -- FrameLink data width
      DATA_WIDTH  : integer := 64;
      -- Number of channels
      CHANNELS    : integer := 2;
      -- Width of the STATUS signal for each channel, up to 16 bits
      -- Target buffer size is considered to be 2^(STATUS_WIDTH-1) words.
      -- For 4 KiB buffers
      STATUS_WIDTH  : integer := 10;
      -- Generate output register on output FrameLink signals
      -- (It's possible because on output FrameLink is not used dst_rdy_n signal)
      OUTPUT_REG    : boolean := true
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- ===================
      -- Write interface
      -- ===================

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

      -- ===================
      -- Read interfaces
      -- ===================

      TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_DREM     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic;
      --TX_DST_RDY_N: in  std_logic;
      TX_SOP_N    : out std_logic;
      TX_EOP_N    : out std_logic;
      TX_SOF_N    : out std_logic;
      TX_EOF_N    : out std_logic;

      -- Is valid during the whole frame
      TX_CHAN     : out std_logic_vector(log2(CHANNELS) - 1 downto 0);

      -- STATUS interface displays number of non-free WORDS
      STATUS      : in  std_logic_vector(CHANNELS*STATUS_WIDTH - 1 downto 0);

      -- ===================
      -- Statistic interface
      -- ===================

      -- Frame passed (1-cycle pulse)
      STAT_PASS   : out std_logic;
      -- Frame dropped (1-cycle pulse
      STAT_DROP   : out std_logic;
         -- Channel number (active with PASS od DROP)
      STAT_CHAN   : out std_logic_vector(log2(CHANNELS) - 1 downto 0);
         -- Frame length (active with PASS od DROP)
      STAT_LEN    : out std_logic_vector(15 downto 0);
         -- Free space (active with PASS od DROP)
      STAT_FREE   : out std_logic_vector(15 downto 0);
         -- Cannot process frames, because counters are being cleared
      STAT_CLEARING:in  std_logic
   );
end entity fl_discard;
