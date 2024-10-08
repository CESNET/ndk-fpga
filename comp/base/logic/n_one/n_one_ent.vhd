-- n_one_ent.vhd : Entity of n one detector
--!
--! \file
--! \brief Entity of n one detector
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
use work.math_pack.all;

--! -----------------------------------------------------------------------------
--!                            Entity declaration
--! -----------------------------------------------------------------------------

entity n_one is
generic (
   --! \brief Data width of input vector
   DATA_WIDTH           : integer := 16
);
port (

   --! \name Clock & reset interface
   --! --------------------------------------------------------------------------
   --! \brief Common clock
   CLK               : in  std_logic;
   --! \brief Common reset
   RESET             : in  std_logic;

   --! \name Input vector
   --! --------------------------------------------------------------------------
   D                 : in  std_logic_vector(DATA_WIDTH-1 downto 0);

   --! \name N one number
   --! -------------------------------------------------------------------------
   N                 : in  std_logic_vector(max(log2(DATA_WIDTH),1)-1 downto 0);

   --! \name Output address
   --! --------------------------------------------------------------------------
   A                 : out std_logic_vector(max(log2(DATA_WIDTH),1)-1 downto 0);
   --! \brief Valid bit
   VLD               : out std_logic

);
end entity n_one;
