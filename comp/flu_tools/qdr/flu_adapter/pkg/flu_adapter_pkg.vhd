-- sdm_pkg.vhd
--!
--! \file
--! \brief FLU_ADAPTER package
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

--! \brief Package with constants for FLU_ADAPTER
package flu_adapter_pkg is

   --! \name State constants
   --! disabled
   constant STORAGE_DISABLE             : std_logic_vector(3 downto 0) := X"0";
   --! fifo
   constant STORAGE_FIFO                : std_logic_vector(3 downto 0) := X"1";
   --! capture
   constant STORAGE_CAPTURE             : std_logic_vector(3 downto 0) := X"2";
   --! replay
   constant STORAGE_REPLAY              : std_logic_vector(3 downto 0) := X"3";
   --! replay_repeated
   constant STORAGE_REPLAY_REPEATED     : std_logic_vector(3 downto 0) := X"4";
   --! clear
   constant STORAGE_CLEAR               : std_logic_vector(3 downto 0) := X"5";

end flu_adapter_pkg;

package body flu_adapter_pkg is

end flu_adapter_pkg;
