-- gen_enc_ent.vhd : Entity of n one detector
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
use ieee.numeric_std.all;
use work.math_pack.all;

--! -----------------------------------------------------------------------------
--!                            Entity declaration
--! -----------------------------------------------------------------------------

entity gen_enc is
generic (
   --! \brief Data width of input vector
   ITEMS           : integer := 4096;
   DEVICE          : string := "none" --! "VIRTEX6", "7SERIES", "ULTRASCALE", "none" (behavioral)

);
port (
   --! \name Input vector
   --! --------------------------------------------------------------------------
   DI                 : in  std_logic_vector(ITEMS-1 downto 0);
   --! \name Output address
   --! --------------------------------------------------------------------------
   ADDR                 : out std_logic_vector(max(log2(ITEMS),1)-1 downto 0)

);
end entity gen_enc;
