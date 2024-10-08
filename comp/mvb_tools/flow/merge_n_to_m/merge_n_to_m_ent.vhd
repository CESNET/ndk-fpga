-- merge_n_to_m_ent.vhd : Entity of merger from n inputs to m outputs
--!
--! \file
--! \brief Entity of merger from n inputs to m outputs
-- SPDX-License-Identifier: BSD-3-Clause
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET z. s. p. o.
--!
--!


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- **OBSOLETE!!!** Use at your own risk. This component is used by **SHAKEDOWN**.
-- Merges N item MVB into M item MVB, on RX interface, there must be at most
-- M items marked as valid, otherwise, they will be lost!.
-- This component can be used as combinational logic.
entity merge_n_to_m is
generic (
   -- Number of inputs (at most M active!!!)
   INPUTS               : integer := 32;
   -- Number of outputs
   OUTPUTS              : integer := 4;
   -- Data width (LSB of each item is valid bit!!!)
   DATA_WIDTH           : integer := 32;
   -- Pipe enable
   OUTPUT_REG           : boolean := true
);
port (
   -- Common clock
   CLK               : in  std_logic;
   -- Common reset
   RESET             : in  std_logic;

   -- Input MVB N item interface
   INPUT_DATA        : in  std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);
   INPUT_SRC_RDY     : in  std_logic := '1';
   INPUT_DST_RDY     : out std_logic;

   -- Output MVB M item interface
   OUTPUT_DATA       : out std_logic_vector(OUTPUTS*DATA_WIDTH-1 downto 0);
   OUTPUT_SRC_RDY    : out std_logic;
   OUTPUT_DST_RDY    : in  std_logic := '1'

);
end entity merge_n_to_m;
