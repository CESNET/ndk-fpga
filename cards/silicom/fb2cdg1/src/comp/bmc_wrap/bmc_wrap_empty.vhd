-- bmc_wrap_empty.vhd : Wrapper of Silicom BMC
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of BMC_WRAP is

begin

    QSPI_D0                  <= 'Z';
    QSPI_D1                  <= 'Z';
    QSPI_D2                  <= 'Z';
    QSPI_D3                  <= 'Z';
    SPI_INGRESS_SCLK         <= 'Z';
    SPI_INGRESS_CSN          <= 'Z';
    SPI_INGRESS_MOSI         <= 'Z';
    SPI_EGRESS_MISO          <= 'Z';
    FPGA_MAX_HB              <= '0';
    FPGA_MAX_FPGA_SEU_1V2    <= '0';
    FPGA_MAX_THRM_SHTD_N_1V2 <= '1';

end architecture;
