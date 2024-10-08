-- mi_test_pkg.vhd: Test Package containing MI bus control for VHDL verification
-- Copyright (C) 2018 CESNET
-- Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields
use std.env.stop;
use STD.textio.all;
use work.mi_test_pkg.all;

   -- ----------------------------------------------------------------------------
   --                        package declarations
   -- ----------------------------------------------------------------------------

package mi_test_pkg is

   -- MI bus interface
   type mi_i_t is record
      mi_addr : std_logic_vector(32-1 downto 0);
      mi_ardy : std_logic;
      mi_be   : std_logic_vector(4-1 downto 0);
      mi_drd  : std_logic_vector(32-1 downto 0);
      mi_drdy : std_logic;
      mi_dwr  : std_logic_vector(32-1 downto 0);
      mi_wr   : std_logic;
      mi_rd   : std_logic;
   end record;
   ----

   -- functions and procedures
   procedure write_mi_data(mi_i : mi_i_t; addr : std_logic_vector; data : std_logic_vector);
   procedure read_mi_data(mi_i : mi_i_t; addr : std_logic_vector; data : out std_logic_vector);
   ----

end mi_test_pkg;

   -- ----------------------------------------------------------------------------
   --                            package body
   -- ----------------------------------------------------------------------------

package body mi_test_pkg is

end mi_test_pkg;

