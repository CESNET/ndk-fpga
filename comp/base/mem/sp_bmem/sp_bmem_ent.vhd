--
-- sp_bmem_ent.vhd: Single port generic memory composed from Block Rams - entity
-- declaration
-- Copyright (C) 2005 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity SP_BMEM is
   -- Capacity of 1, 2, 4 Block rams is 16384 bits
   -- Capacity of 9, 18, 36 Block rams is 18432 bits
   generic(
      DATA_WIDTH  : integer := 32;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer := 1024;
      -- What operation will be performed first when both WE and RE are
      -- active? Only for behavioral simulation purpose.
      -- WRITE_FIRST(default) | READ_FIRST | NO_CHANGE
      WRITE_MODE  : string := "WRITE_FIRST";
      -- Output directly from BlockRams or throw register
      OUTPUT_REG  : boolean := true
   );

   port(
      -- ================
      -- Common interface
      -- ================

      -- Reset only if output_reg
      RESET  : in    std_logic;

      -- ================
      -- Interface A
      -- ================

      -- Clock A
      CLK   : in    std_logic;
      -- Pipe Enable
      PIPE_EN : in  std_logic;
      -- Read Enable
      RE    : in    std_logic;
      -- Write Enable
      WE    : in    std_logic;
      -- Address A
      ADDR  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0);
      -- Data A In
      DI    : in    std_logic_vector(DATA_WIDTH-1 downto 0);
      -- Data A Valid
      DO_DV : out   std_logic;
      -- Data A Out
      DO    : out   std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity SP_BMEM;

