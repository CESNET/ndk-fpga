-- sdp_bram_xilinx_empty.vhd: sdp_bram_xilinx wrapper
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

architecture EMPTY of SDP_BRAM_XILINX2 is

begin

    RD_DATA <= (others => '0');

end architecture;
