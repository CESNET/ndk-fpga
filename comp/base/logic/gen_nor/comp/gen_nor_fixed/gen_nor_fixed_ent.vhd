-- gen_nor_ent.vhd : Entity of gen nor
--!
--! \file
--! \brief Entity of gen nor
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

--! -----------------------------------------------------------------------------
--!                            Entity declaration
--! -----------------------------------------------------------------------------

entity GEN_NOR_FIXED is
   generic(
      --! \brief Width of input signal, number of bits to NOR.
      --! \details Must be greater than 0.
      DATA_WIDTH    : integer := 288;  -- or width (number of inputs)
      DEVICE        : string := "none" --! "VIRTEX6", "7SERIES", "ULTRASCALE", "none" (behavioral)
   );
   port(
      --! Input data, vector of bits to OR.
      DI  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Output data, result of OR.
      DO  : out std_logic
   );
end entity;
