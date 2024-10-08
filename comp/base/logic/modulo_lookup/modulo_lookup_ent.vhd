--!
--! \file modulo_lookup_ent.vhd
--! \brief Modulo look-up table entity
--! \author Jan Kučera <xkuce73@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! Package with log2 function.
use work.math_pack.all;

--! \brief Modulo look-up table entity
entity MODULO_LOOKUP is
   generic (
      --! Modulo data width
      MODULO_WIDTH  : integer := 4;
      --! Operand data width
      OPERAND_WIDTH : integer := 9;
      --! Output directly from BlockRams or through register
      OUTPUT_REG    : boolean := false;
      --! Memory type - auto, block, distributed
      MEM_TYPE      : string  := "block"
   );
   port (
      --! Common interface
      CLK     : in std_logic;
      RESET   : in std_logic;

      --! Input interface
      MODULO  : in std_logic_vector(MODULO_WIDTH-1 downto 0);
      OPERAND : in std_logic_vector(OPERAND_WIDTH-1 downto 0);
      IN_VLD  : in std_logic;

      --! Output interface: RESULT = OPERAND mod (MODULO + 1)
      RESULT  : out std_logic_vector(MODULO_WIDTH-1 downto 0);
      OUT_VLD : out std_logic
   );
end entity;
