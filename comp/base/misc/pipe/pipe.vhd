--
-- pipe.vhd: Internal Bus Pipeline
-- Copyright (C) 2013 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--            Lukas Kekely <kekely@cesnet.cz>
--            Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--               ENTITY DECLARATION -- Internal Bus Pipeline                 --
-- ----------------------------------------------------------------------------

entity PIPE is
   generic(
      DATA_WIDTH    : integer := 64;
      -- wires only (to disable pipe easily)
      FAKE_PIPE     : boolean := false;
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register, optimization of
      --              mapping shreg on Xilinx FPGA can be set using OPT generic
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      PIPE_TYPE     : string  := "SHREG";
      -- YOU CAN SELECT SHREG OPTIMALIZATION:
      --    "SRL"    - shreg implemented in SRL16E (better, but Xilinx only)
      --    "REG"    - shreg implemented in flip-flops (registers)
      --    "VIVADO" - vivado selects implementation of shreg
      -- Only for PIPE_TYPE = "SHREG"!
      OPT           : string  := "SRL";
      -- Only for PIPE_TYPE = "SHREG"!
      USE_OUTREG    : boolean := false;
      -- Only for PIPE_TYPE = "SHREG"!
      RESET_BY_INIT : boolean := false;

      DEVICE        : string  := "7SERIES"
   );
   port(
      -- =================
      -- Common interface
      -- =================

      CLK           : in std_logic;
      -- NOTE: also starts debug counters
      RESET         : in std_logic;

      -- =================
      -- Input interface
      -- =================

      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SRC_RDY    : in  std_logic;
      IN_DST_RDY    : out std_logic;

      -- =================
      -- Output interface
      -- =================

      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SRC_RDY   : out std_logic;
      OUT_DST_RDY   : in  std_logic;

      -- ===================
      -- Debuging interface
      -- ===================

      -- blocks data words on pipe's input interface
      DEBUG_BLOCK   : in  std_logic := '0';
      -- drops data words on pipe's input interface (higher priority than BLOCK)
      DEBUG_DROP    : in  std_logic := '0';
      -- source ready on pipe's input
      DEBUG_SRC_RDY : out std_logic;
      -- destination ready on pipe's input
      DEBUG_DST_RDY : out std_logic
   );
end entity PIPE;



