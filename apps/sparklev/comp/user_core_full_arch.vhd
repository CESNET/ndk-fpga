-- user_core_full_arch.vhd: End-user application core full architecture
-- Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
--
-- SPDX-License-Identifier: CERN-OHL-P-2.0

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture FULL of USER_CORE is
    signal sync_mi_dwr  : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_addr : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    signal sync_mi_be   : std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    signal sync_mi_rd   : std_logic;
    signal sync_mi_wr   : std_logic;
    signal sync_mi_drd  : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_ardy : std_logic;
    signal sync_mi_drdy : std_logic;
begin

end architecture;
