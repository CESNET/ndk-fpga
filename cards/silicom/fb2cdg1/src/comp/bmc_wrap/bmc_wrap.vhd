-- bmc_wrap.vhd : Wrapper of Silicom BMC
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;

architecture FULL of BMC_WRAP is

    signal qspi_data_out : std_logic_vector(4 - 1 downto 0);
    signal qspi_data_oe  : std_logic_vector(4 - 1 downto 0);

begin

    -- BMC controller
    QSPI_D0 <= qspi_data_out(0) when qspi_data_oe(0) = '1' else 'Z';
    QSPI_D1 <= qspi_data_out(1) when qspi_data_oe(1) = '1' else 'Z';
    QSPI_D2 <= qspi_data_out(2) when qspi_data_oe(2) = '1' else 'Z';
    QSPI_D3 <= qspi_data_out(3) when qspi_data_oe(3) = '1' else 'Z';

    pmci_i : entity work.PMCI_FB2CDG1
    generic map(
        DEVICE        => DEVICE,
        G_SWB_RD_TYPE => 1 -- Thunderfjord
    ) port map(
        CLK                      => CLK,
        RESET                    => RESET,

        MI_DWR                   => MI_DWR,
        MI_ADDR                  => MI_ADDR,
        MI_RD                    => MI_RD,
        MI_WR                    => MI_WR,
        MI_BE                    => MI_BE,
        MI_DRD                   => MI_DRD,
        MI_ARDY                  => MI_ARDY,
        MI_DRDY                  => MI_DRDY,

        FLASH_CTRLR_ATOM_PORTS_DCLK     => QSPI_CLK,
        FLASH_CTRLR_ATOM_PORTS_NCS      => QSPI_CSN_1V2,
        FLASH_CTRLR_ATOM_PORTS_OE       => open,
        FLASH_CTRLR_ATOM_PORTS_DATAOUT  => qspi_data_out,
        FLASH_CTRLR_ATOM_PORTS_DATAOE   => qspi_data_oe,
        FLASH_CTRLR_ATOM_PORTS_DATAIN   => QSPI_D3 & QSPI_D2 & QSPI_D1 & QSPI_D0,

        M10_GPIO_FPGA_USR_100M          => '0',
        M10_GPIO_FPGA_M10_HB            => MAX_FPGA_HB_1V2,
        M10_GPIO_PMCI_NIOS_HB           => FPGA_MAX_HB,
        M10_GPIO_M10_SEU_ERROR          => '0',
        M10_GPIO_FPGA_THERM_SHDN        => FPGA_MAX_THRM_SHTD_N_1V2,
        M10_GPIO_FPGA_SEU_ERROR         => FPGA_MAX_FPGA_SEU_1V2,

        SPI_INGRESS_SCLK                => SPI_INGRESS_SCLK,
        SPI_INGRESS_CSN                 => SPI_INGRESS_CSN,
        SPI_INGRESS_MISO                => SPI_INGRESS_MISO,
        SPI_INGRESS_MOSI                => SPI_INGRESS_MOSI,

        SPI_EGRESS_MOSI                 => SPI_EGRESS_MOSI,
        SPI_EGRESS_CSN                  => SPI_EGRESS_CSN,
        SPI_EGRESS_SCLK                 => SPI_EGRESS_SCLK,
        SPI_EGRESS_MISO                 => SPI_EGRESS_MISO
    );

end architecture;
