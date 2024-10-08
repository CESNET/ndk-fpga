-- fifo_bram_xilinx_empty.vhd: FIFO implemented in Xilinx BRAMs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

architecture EMPTY of FIFO_BRAM_XILINX is

begin

    AFULL  <= '1';
    FULL   <= '1';
    DO     <= (others => '0');
    AEMPTY <= '1';
    EMPTY  <= '1';

end architecture;
