-- first_one.vhd
--!
--! \file
--! \brief Generic fist one detector.
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--! \brief Generic first one detector entity.
entity FIRST_ONE is
   generic(
      --! \brief Width of input/output signal. Output address is one-hot encoded
      --! \details Must be greater than 0.
      DATA_WIDTH    : integer
   );
   port(
      --! Input data vector
      DI  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Output data vector - one-hot encoded
      DO  : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity;

--! \brief Implementation of generic first one detector.
architecture full of FIRST_ONE is
begin

   --! First one detector without priority
   --! Other implementations possible...
   DO <= (DI) and ((not DI) + 1);

end architecture;

