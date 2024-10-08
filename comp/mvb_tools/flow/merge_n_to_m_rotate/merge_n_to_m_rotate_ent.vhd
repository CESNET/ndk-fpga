-- merge_n_to_m_ent_rotate.vhd : Entity of merger from n inputs to m outputs and rotate
--!
--! \file
--! \brief Entity of merger from n inputs to m outputs and rotate
-- SPDX-License-Identifier: BSD-3-Clause
--! \author Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET z. s. p. o.
--!
--!


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;


-- -----------------------------------------------------------------------------
--                            Entity declaration
-- -----------------------------------------------------------------------------

entity merge_n_to_m_rotate is
generic (
   --! \brief Number of inputs (at most M active!!!)
   INPUTS               : integer := 32;
   --! \brief Number of outputs
   OUTPUTS              : integer := 4;
   --! \brief Data width (LSB of each item is valid bit!!!)
   DATA_WIDTH           : integer := 32;
   --! \brief Pipe
   OUTPUT_REG           : boolean := true;
   --! set true to shift left, false to shift right
   SHIFT_LEFT           : boolean := true
);
port (
   --! \name Clock & reset interface
   -- --------------------------------------------------------------------------
   --! \brief Common clock
   CLK               : in  std_logic;
   --! \brief Common reset
   RESET             : in  std_logic;

   --! \name Input data
   -- --------------------------------------------------------------------------
   INPUT_DATA           : in  std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);

   --! \name Desired output rotation
   -- --------------------------------------------------------------------------
   SEL                  : in  std_logic_vector(log2(OUTPUTS)-1 downto 0);

   --! \name Ouput data
   -- --------------------------------------------------------------------------
   OUTPUT_DATA          : out std_logic_vector(OUTPUTS*DATA_WIDTH-1 downto 0)

);
end entity merge_n_to_m_rotate;
