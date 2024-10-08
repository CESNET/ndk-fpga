-- fifo_n1.vhd: FIFO_N1 - m x n bit with multiple write ports
--                  - synchronous read/write
-- Copyright (C) 2017 CESNET
-- Author(s): Vaclav Hummel vaclav.hummel@cesnet.cz
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                        Description
-- ----------------------------------------------------------------------------
-- Multiple write ports, single read port FIFO. Uses SDP distmem. WE may be
-- set at any bit - the component always finds set WE bit at any position. LSB
-- WE item is first in and first out.

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FIFO_N1 is
   generic (
      -- Number of independent write ports
      WRITE_PORTS    : integer := 1;
      -- Set data width here
      DATA_WIDTH     : integer := 23;
      -- Set number of items per ONE memory
      -- Total size equals to WRITE_PORTS*ITEMS
      ITEMS          : integer := 32;

      ALMOST_FULL_OFFSET      : integer := 16;
      ALMOST_EMPTY_OFFSET     : integer := 16;

      DI_PIPE        : boolean := false;
      DO_PIPE        : boolean := false;

      DEVICE : string := "7SERIES"
   );
   port(
      -- Global clock signal
      CLK      : in  std_logic;
      -- Global reset signal
      RESET    : in  std_logic;

      -- ===============
      -- Write interface
      -- ===============

      -- Data input
      DATA_IN  : in  slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
      -- Write request
      WE       : in  std_logic_vector(WRITE_PORTS-1 downto 0);
      -- FIFO is full
      FULL     : out std_logic;
      -- FIFO is almost full (see ALMOST_FULL_OFFSET)
      AFULL    : out std_logic;

      -- ===============
      -- Read interface
      -- ===============

      -- Data output
      DATA_OUT       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      -- Read request
      RE             : in  std_logic;
      -- FIFO is empty
      EMPTY          : out std_logic;
      -- FIFO is almost empty (see ALMOST_EMPTY_OFFSET)
      AEMPTY         : out std_logic
   );
end entity;
