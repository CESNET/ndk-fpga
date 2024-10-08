-- fp_ptr_ctrl.vhd: Pointer Control Unit
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This unit handles pointer for the given channel and generates overflow signal
entity FP_PTR_CTRL is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        RX_SRC_RDY      : in  std_logic;
        RX_PTR_INC      : in  u_array_t(MFB_REGIONS downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);

        TX_CH_PTR       : out unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
        TX_CH_OVERFLOW  : out std_logic
    );
end entity;

architecture FULL of FP_PTR_CTRL is
    signal ptr_reg : unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
    signal ptr_inc : u_array_t(MFB_REGIONS downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);

begin
    ptr_inc(0)  <= RX_PTR_INC(0);
    ptr_inc_sum_g: for i in 0 to MFB_REGIONS - 1 generate
        ptr_inc(i+1) <= ptr_inc(i) + RX_PTR_INC(i+1);
    end generate;

    ptr_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                ptr_reg <= (others => '0');
            elsif RX_SRC_RDY = '1' then
                ptr_reg <= '0' & ptr_reg(ptr_reg'high -1 downto 0) + ptr_inc(MFB_REGIONS);
            else
                ptr_reg(ptr_reg'high) <='0';
            end if;
         end if;
    end process;

    TX_CH_PTR       <= ptr_reg(ptr_reg'high -1 downto 0);
    TX_CH_OVERFLOW  <= std_logic(ptr_reg(ptr_reg'high));

end architecture;
