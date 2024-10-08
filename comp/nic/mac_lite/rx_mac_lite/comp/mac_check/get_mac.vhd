-- get_mac.vhd: Get destination MAC address
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_GET_MAC is
    generic(
        -- must be power of 2
        REGION_SIZE : natural := 8;
        -- must be power of 2, BLOCK_SIZE*ITEM_WIDTH >= 48!
        BLOCK_SIZE  : natural := 8;
        -- must be power of 2, BLOCK_SIZE*ITEM_WIDTH >= 48!
        ITEM_WIDTH  : natural := 8
    );
    port(
        -- ===============
        -- CLOCK AND RESET
        -- ===============

        CLK         : in  std_logic;
        RESET       : in  std_logic;

        -- ====================
        -- INPUT DATA INTERFACE
        -- ====================

        RX_DATA     : in  std_logic_vector(REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_SOF_POS  : in  std_logic_vector(max(1,log2(REGION_SIZE))-1 downto 0);
        RX_SOF      : in  std_logic;
        RX_SRC_RDY  : in  std_logic;

        -- ====================
        -- OUTPUT MAC INTERFACE
        -- ====================

        -- destination MAC address
        MAC_DST     : out std_logic_vector(48-1 downto 0);
        -- valid of extracted MAC address, latency is 1 cycle
        MAC_DST_VLD : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_GET_MAC is

    signal s_data_array : slv_array_t(REGION_SIZE-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);

    signal s_ext_mac_dst : std_logic_vector(48-1 downto 0);

begin

    assert ((BLOCK_SIZE*ITEM_WIDTH) > 47)
        report "RX_MAC_LITE_GET_MAC: BLOCK_SIZE*ITEM_WIDTH >= 48!!!"
        severity failure;

    data_arr_off_g: if (REGION_SIZE = 1) generate
        -- destination MAC address is on first 48b of data bus
        s_ext_mac_dst <= RX_DATA(47 downto 0);
    end generate;

    data_arr_on_g: if (REGION_SIZE > 1) generate
        s_data_array <= slv_array_downto_deser(RX_DATA,REGION_SIZE,BLOCK_SIZE*ITEM_WIDTH);
        -- multiplexor for extract destination MAC address
        s_ext_mac_dst <= s_data_array(to_integer(unsigned(RX_SOF_POS)))(47 downto 0);
    end generate;

    -- output register of extracted MAC address
    mac_dst_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            MAC_DST <= s_ext_mac_dst;
        end if;
    end process;

    -- output register of MAC address valid flag
    mac_dst_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                MAC_DST_VLD <= '0';
            else
                MAC_DST_VLD <= RX_SOF and RX_SRC_RDY;
            end if;
        end if;
    end process;

end architecture;
