--
-- pipe.vhd: Deeper (up to 4 items stored) version of basic pipe (up to 2 items stored)
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--               ENTITY DECLARATION -- Internal Bus Pipeline                 --
-- ----------------------------------------------------------------------------

entity PIPE_DEEPER is
   generic(
      DATA_WIDTH      : integer := 64;
      USE_OUTREG      : boolean := false;
      -- wires only (to disable pipe easily)
      FAKE_PIPE       : boolean := false;
      RESET_BY_INIT   : boolean := false;

      -- VIVADO can convert SRL shitf register to filip-flop register. It cost more resources.
      -- If you realy want shift register use SRL.
      -- VIVADO, SRL
      OPT             : string  := "SRL"
   );
   port(
      -- ================
      -- Common interface
      -- ================

      CLK            : in std_logic;
      -- NOTE: also starts debug counters
      RESET          : in std_logic;

      -- ================
      -- Input interface
      -- ================

      IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SRC_RDY     : in  std_logic;
      IN_DST_RDY     : out std_logic;

      -- ================
      -- Output interface
      -- ================

      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SRC_RDY    : out std_logic;
      OUT_DST_RDY    : in  std_logic;

      -- ==================
      -- Debuging interface
      -- ==================

      -- blocks data words on pipe's input interface
      DEBUG_BLOCK        : in  std_logic := '0';
      -- drops data words on pipe's input interface (higher priority than BLOCK)
      DEBUG_DROP         : in  std_logic := '0';
      -- source ready on pipe's input
      DEBUG_SRC_RDY      : out std_logic;
      -- destination ready on pipe's input
      DEBUG_DST_RDY      : out std_logic
   );
end entity PIPE_DEEPER;



