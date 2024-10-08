-- mi_test_space.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity MI_TEST_SPACE is
    generic (
        -- Supported devices: AGILEX, STRATIX10, ULTRASCALE, 7SERIES
        DEVICE  : string := "ULTRASCALE"
    );
    port(
        CLK     : in  std_logic;
        RESET   : in  std_logic;
        MI_DWR  : in  std_logic_vector(32-1 downto 0);
        MI_ADDR : in  std_logic_vector(32-1 downto 0);
        MI_BE   : in  std_logic_vector(4-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(32-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
    );
end entity;

architecture FULL of MI_TEST_SPACE is

    constant BRAM_ADDR_WIDTH : natural := 6;
    constant BRAM_ITEMS      : natural := 2**BRAM_ADDR_WIDTH;

    type byte_array_t is array(4-1 downto 0) of std_logic_vector(8-1 downto 0);
    type ram_intel_t is array(BRAM_ITEMS-1 downto 0) of byte_array_t;
    type ram_xilinx_t is array(BRAM_ITEMS-1 downto 0) of std_logic_vector(32-1 downto 0);

    signal bram_intel   : ram_intel_t := (others => (others => (others => '0')));
    signal bram_xilinx  : ram_xilinx_t := (others => (others => '0'));
    signal bram_addr    : unsigned(BRAM_ADDR_WIDTH-1 downto 0);
    signal rd_data      : byte_array_t;

    attribute ram_style : string; -- for Vivado
    attribute ram_style of bram_xilinx : signal is "block";
    attribute ramstyle  : string; -- for Quartus
    attribute ramstyle  of bram_intel : signal is "M20K";

begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "MI_TEST_SPACE: unsupported device!" severity failure;

    MI_ARDY   <= MI_RD or MI_WR;
    bram_addr <= unsigned(MI_ADDR(BRAM_ADDR_WIDTH+2-1 downto 2));

    be_bram_intel_g : if DEVICE = "STRATIX10" OR DEVICE = "AGILEX" generate
        bram_intel_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (MI_WR = '1') then
                    if (MI_BE(0) = '1') then
                        bram_intel(to_integer(bram_addr))(0) <= MI_DWR(8-1 downto 0);
                    end if;
                    if (MI_BE(1) = '1') then
                        bram_intel(to_integer(bram_addr))(1) <= MI_DWR(16-1 downto 8);
                    end if;
                    if (MI_BE(2) = '1') then
                        bram_intel(to_integer(bram_addr))(2) <= MI_DWR(24-1 downto 16);
                    end if;
                    if (MI_BE(3) = '1') then
                        bram_intel(to_integer(bram_addr))(3) <= MI_DWR(32-1 downto 24);
                    end if;
                end if;
                rd_data <= bram_intel(to_integer(bram_addr));
            end if;
        end process;

        MI_DRD(8-1 downto 0) <= rd_data(0);
        MI_DRD(16-1 downto 8) <= rd_data(1);
        MI_DRD(24-1 downto 16) <= rd_data(2);
        MI_DRD(32-1 downto 24) <= rd_data(3);
    end generate;

    be_bram_xilinx_g : if DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES" generate
        bram_xilinx_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (MI_WR = '1') then
                    if (MI_BE(0) = '1') then
                        bram_xilinx(to_integer(bram_addr))(8-1 downto 0) <= MI_DWR(8-1 downto 0);
                    end if;
                    if (MI_BE(1) = '1') then
                        bram_xilinx(to_integer(bram_addr))(16-1 downto 8) <= MI_DWR(16-1 downto 8);
                    end if;
                    if (MI_BE(2) = '1') then
                        bram_xilinx(to_integer(bram_addr))(24-1 downto 16) <= MI_DWR(24-1 downto 16);
                    end if;
                    if (MI_BE(3) = '1') then
                        bram_xilinx(to_integer(bram_addr))(32-1 downto 24) <= MI_DWR(32-1 downto 24);
                    end if;
                end if;
                MI_DRD <= bram_xilinx(to_integer(bram_addr));
            end if;
        end process;
    end generate;

    drdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                MI_DRDY <= '0';
            else
                MI_DRDY <= MI_RD;
            end if;
        end if;
    end process;

end architecture;
