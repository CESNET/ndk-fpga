-- fp_mux_ctrl.vhd: Unit for setting the correct SEL signal for Channel MUXes
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component is a part of Channel Cell
entity FP_MUX_CTRL is
    generic(
        MFB_REGIONS         : natural := 4;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        MUX_WIDTH           : natural := 2
    );
    port(
        -- RX_VLD format: [BS][VLD]
        RX_VLD_ARR      : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- Select for each MUX
        TX_SEL_ARR      : out slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1,log2(MUX_WIDTH))-1 downto 0)
    );
end entity;

architecture FULL of FP_MUX_CTRL is
begin
    -- Check if there is a valid bit for the block - If yes, pass index of BS to the array
    mux_sel_p: process(all)
        variable sel_arr_v : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1,log2(MUX_WIDTH))-1 downto 0);
    begin
        sel_arr_v  := (others => (others => '0'));
        bs_sel_l: for i in 0 to MFB_REGIONS loop
            input_sel_l: for j in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 loop
                if RX_VLD_ARR(i)(j) = '1' then
                    sel_arr_v(j)   := std_logic_vector(to_unsigned(i, max(1, log2(MUX_WIDTH))));
                end if;
            end loop;
        end loop;

        TX_SEL_ARR  <= sel_arr_v;
    end process;

end architecture;
