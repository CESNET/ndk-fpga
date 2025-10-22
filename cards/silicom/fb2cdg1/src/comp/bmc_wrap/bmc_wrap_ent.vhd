-- bmc_wrap_ent.vhd : Wrapper of Silicom BMC
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity BMC_WRAP is
    generic(
        DEVICE : string := "AGILEX"
    );
    port(
        CLK                      : in    std_logic;
        RESET                    : in    std_logic;

        MI_DWR                   : in    std_logic_vector(32-1 downto 0);
        MI_ADDR                  : in    std_logic_vector(32-1 downto 0);
        MI_RD                    : in    std_logic;
        MI_WR                    : in    std_logic;
        MI_BE                    : in    std_logic_vector((32/8)-1 downto 0);
        MI_DRD                   : out   std_logic_vector(32-1 downto 0);
        MI_ARDY                  : out   std_logic;
        MI_DRDY                  : out   std_logic;

        QSPI_CSN_1V2             : out    std_logic;
        QSPI_D0                  : inout  std_logic;
        QSPI_D1                  : inout  std_logic;
        QSPI_D2                  : inout  std_logic;
        QSPI_D3                  : inout  std_logic;
        QSPI_CLK                 : out    std_logic;

        SPI_INGRESS_SCLK         : out    std_logic;
        SPI_INGRESS_CSN          : out    std_logic;
        SPI_INGRESS_MISO         : in     std_logic;
        SPI_INGRESS_MOSI         : out    std_logic;

        SPI_EGRESS_MOSI          : in     std_logic;
        SPI_EGRESS_CSN           : in     std_logic;
        SPI_EGRESS_SCLK          : in     std_logic;
        SPI_EGRESS_MISO          : out    std_logic;

        MAX_FPGA_HB_1V2          : in     std_logic;
        FPGA_MAX_HB              : out    std_logic;
        FPGA_MAX_FPGA_SEU_1V2    : out    std_logic;
        FPGA_MAX_THRM_SHTD_N_1V2 : out    std_logic
    );
end entity;
