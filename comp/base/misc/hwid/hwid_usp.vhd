-- hwid_usp.vhd : component for acquisition hardware identification
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

library unisim;
use unisim.vcomponents.all;

architecture arch of HWID is

   signal dna_shift_reg     : std_logic_vector(96 downto 0) := '1' & (95 downto 0 => '0');
   signal dna_read_inited   : std_logic := '0';
   signal dna_read_enable   : std_logic := '1';
   signal dna_shift_enable  : std_logic;
   signal dna_bit           : std_logic;

begin

    XILINX_DNA      <= dna_shift_reg(96 downto 1);
    XILINX_DNA_VLD  <= dna_shift_reg(0);

    usp_g: if DEVICE = "ULTRASCALE" generate
        dna_shift_enable <= not dna_shift_reg(0) and not dna_read_enable;

        dna_port_i : DNA_PORTE2
        generic map(
            SIM_DNA_VALUE => X"0123456789ABCDEF01234567"
        )
        port map (
            CLK     => CLK,
            DIN     => '0',
            SHIFT   => dna_shift_enable,
            READ    => dna_read_enable,
            DOUT    => dna_bit
        );

        dna_read_p: process(CLK)
        begin
            if (CLK'event and CLK = '1') then
                if (dna_read_inited = '0') then
                    dna_read_inited     <= '1';
                    dna_read_enable     <= '1';
                else
                    dna_read_enable     <= '0';
                    if (dna_shift_enable = '1') then
                        dna_shift_reg   <= dna_bit & dna_shift_reg(96 downto 1);
                    end if;
                end if;
            end if;
        end process;
    end generate;

end architecture;
