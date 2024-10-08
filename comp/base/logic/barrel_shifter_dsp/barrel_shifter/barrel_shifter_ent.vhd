-- barrel_shifter_ent.vhd: entity of barrel shifter with DSP
-- Copyright (C) 2015 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                  ENTITY DECLARATION -- Barrel shifter DSP                 --
-- ----------------------------------------------------------------------------

-- -------------------------------------------
-- Architectures:
--    1. shift_arch  (barrel_shifter_top.vhd) - leading zeros
--    2. rotate_arch (barrel_shifter_rotate_top.vhd) - support rotation
-- --------------------------------------------

entity BARREL_SHIFTER_DSP is
   generic (
      -- every 24 bits => one DSP
      DATA_WIDTH  : integer := 24;
      -- set true to shift left, false to shift right
      SHIFT_LEFT  : boolean := true;
      -- input registers (0 -> false, 1 -> true)
      REG_IN      : integer := 0;
      -- output registers (0 -> false, 1 -> true)
      REG_OUT     : integer := 0;

      -- connect input/output registers with DPS or normal logic
      -- dsp use fewer resources
      REGS_WITH_DSP  : boolean := true;

      -- number of maximum shift bit,
      MAX_SHIFT   : integer := 16;

      -- choice shift with binary numbers or exponentially format (2^N)
      -- binary use more resources as exponentially
      -- BINARY -> 1, signal SHIFT_BINARY
      -- EXP    -> 0, signal SHIFT_EXP
      SEL_FORMAT_SHIFT : integer := 0
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;
      -- Input interface
      DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);

      -- SHIFT
      -- format 2^N
      -- only one bit can by '1'
      SHIFT_EXP      : in  std_logic_vector(MAX_SHIFT-1 downto 0);
      -- binary numbers
      SHIFT_BINARY   : in  std_logic_vector(log2(MAX_SHIFT) - 1 downto 0);

      -- clock enbale for input registers
      CE_IN          : in std_logic;
      -- clock enbale for output registers
      CE_OUT         : in std_logic
   );
end BARREL_SHIFTER_DSP;
