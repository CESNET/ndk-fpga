-- combo_const.vhd : Package with constants for Intel FPGA cards
-- Copyright (C) 2017 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                            Package declaration
-- ----------------------------------------------------------------------------

package combo_const is

    -- NDK version numbers
    constant NDK_MAJOR         : std_logic_vector(7 downto 0) := X"01";
    constant NDK_MINOR         : std_logic_vector(7 downto 0) := X"00";

    -- PCIe BARs base addresses
    constant BAR0_BASE_ADDR    : std_logic_vector := X"00000000";
    constant BAR1_BASE_ADDR    : std_logic_vector := X"00000000";
    constant BAR2_BASE_ADDR    : std_logic_vector := X"04000000";
    constant BAR3_BASE_ADDR    : std_logic_vector := X"04000000";
    constant BAR4_BASE_ADDR    : std_logic_vector := X"80000000";
    constant BAR5_BASE_ADDR    : std_logic_vector := X"80000000";
    constant EXP_ROM_BASE_ADDR : std_logic_vector := X"80000000";

end package combo_const;

-- ----------------------------------------------------------------------------
--                               Package body
-- ----------------------------------------------------------------------------

package body combo_const is
end package body combo_const;
