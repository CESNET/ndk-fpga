-- mi_pipe.vhd: MI Pipe - wrapper to generic pipe
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

-- Wrapper over generic Pipe (comp/base/misc/pipe) for MI interface.
entity MI_PIPE is
   generic(
      DATA_WIDTH  : integer := 32;
      ADDR_WIDTH  : integer := 32;
      META_WIDTH  : integer := 2;
      -- Type of the PIPEs implementation:
      --
      -- "SHREG"
      --    Pipe implemented as shift register, optimization of mapping shreg on Xilinx FPGA can be
      --    set using OPT generic
      -- "REG"
      --    Two-stage pipe created from two registers + 1 MUX, better on wide buses and on
      --    Intel/Altera devices
      PIPE_TYPE   : string  := "SHREG";
      USE_OUTREG  : boolean := false; -- Only for PIPE_TYPE = "SHREG"!
      FAKE_PIPE   : boolean := false; -- wires only (to disable pipe easily)

      DEVICE      : string := "7SERIES"
   );
   port(
      -- ===========================================================================================
      -- Common interface
      -- ===========================================================================================
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- ===========================================================================================
      -- Input MI interface
      -- ===========================================================================================
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
      IN_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;

      -- ===========================================================================================
      -- Output MI interface
      -- ===========================================================================================
      OUT_DWR     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_MWR     : out std_logic_vector(META_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      OUT_BE      : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic;
      OUT_WR      : out std_logic;
      OUT_ARDY    : in  std_logic;
      OUT_DRD     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic
   );
end entity MI_PIPE;

