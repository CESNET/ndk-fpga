-- bmc_wrap_ent.vhd : Wrapper of Bittware BMC
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
        CLK                : in    std_logic;
        RESET              : in    std_logic;

        MI_DWR             : in    std_logic_vector(32-1 downto 0);
        MI_ADDR            : in    std_logic_vector(32-1 downto 0);
        MI_RD              : in    std_logic;
        MI_WR              : in    std_logic;
        MI_BE              : in    std_logic_vector((32/8)-1 downto 0);
        MI_DRD             : out   std_logic_vector(32-1 downto 0);
        MI_ARDY            : out   std_logic;
        MI_DRDY            : out   std_logic;

        QSFPDD0_RST_N      : in    std_logic;
        QSFPDD0_LPMODE     : in    std_logic;
        QSFPDD0_INT_N      : out   std_logic;
        QSFPDD0_PRESENT_N  : out   std_logic;

        BMC_IF_PRESENT_N   : out   std_logic;
        FPGA_EG_SPI_SCK    : out   std_logic;
        FPGA_EG_SPI_MISO   : in    std_logic;
        FPGA_EG_SPI_MOSI   : out   std_logic;
        FPGA_EG_SPI_PCS0   : out   std_logic;
        BMC_TO_FPGA_IRQ    : in    std_logic;
        FPGA_IG_SPI_SCK    : in    std_logic;
        FPGA_IG_SPI_MISO   : inout std_logic;
        FPGA_IG_SPI_MOSI   : in    std_logic;
        FPGA_IG_SPI_PCS0   : in    std_logic;
        FPGA_TO_BMC_IRQ    : out   std_logic
    );
end entity;
