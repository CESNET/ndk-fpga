-- h3_core.vhd - H3 Class generic hash function
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.h3_pack.all;

entity H3_CORE is
    generic (
        CONFIG      : h3_config := H3C_256x64;
        PIPELINE    : boolean := false;
        OUT_REG     : boolean := false
    );
    port (
        CLK             : in std_logic;
        RESET           : in std_logic;

        -- Input data
        DATA_IN         : in  std_logic_vector(CONFIG.key_width - 1 downto 0);
        DATA_IN_VLD     : in  std_logic := '1';
        DATA_IN_RDY     : out std_logic;

        DATA_OUT        : out std_logic_vector(CONFIG.hash_width - 1 downto 0);
        DATA_OUT_VLD    : out std_logic;
        DATA_OUT_RDY    : in  std_logic := '1'
    );
end entity;

architecture behavioral of H3_CORE is

    constant MATRIX_DESER   : slv_array_t(CONFIG.key_width - 1 downto 0)(CONFIG.hash_width - 1 downto 0) := slv_array_deser(CONFIG.matrix, CONFIG.key_width);

    signal anded_mtx        : slv_array_t(CONFIG.key_width - 1 downto 0)(CONFIG.hash_width - 1 downto 0);
    signal anded_mtx_reg    : slv_array_t(CONFIG.key_width - 1 downto 0)(CONFIG.hash_width - 1 downto 0);
    signal anded_mtx_vld    : std_logic;

    signal do_int : std_logic_vector(CONFIG.hash_width - 1 downto 0);

begin

    and_g : for i in 0 to CONFIG.key_width - 1 generate
        anded_mtx(i) <= MATRIX_DESER(i) when DATA_IN(i) = '1' else (others => '0');
    end generate;

    and_reg_g : if PIPELINE generate

        process (CLK)
        begin
            if rising_edge(CLK) then
                if DATA_OUT_RDY = '1' then
                    anded_mtx_reg <= anded_mtx;
                end if;
            end if;
        end process;

        process (CLK)
        begin
            if rising_edge(CLK) then
                if RESET = '1' then
                    anded_mtx_vld <= '0';
                else
                    if DATA_OUT_RDY = '1' then
                        anded_mtx_vld <= DATA_IN_VLD;
                    end if;
                end if;
            end if;
        end process;

    else generate

        anded_mtx_reg <= anded_mtx;
        anded_mtx_vld <= DATA_IN_VLD;

    end generate;

    process (all)
        variable xor_sum : std_logic_vector(CONFIG.hash_width - 1 downto 0);
    begin
        xor_sum := (others => '0');
        for i in 0 to CONFIG.key_width - 1 loop
            xor_sum := xor_sum xor anded_mtx_reg(i);
        end loop;

        do_int <= xor_sum;
    end process;

    out_reg_g : if OUT_REG generate
    begin
        process (CLK)
        begin
            if rising_edge(CLK) then
                if DATA_OUT_RDY = '1' then
                    DATA_OUT <= do_int;
                end if;
            end if;
        end process;

        process (CLK)
        begin
            if rising_edge(CLK) then
                if RESET = '1' then
                    DATA_OUT_VLD <= '0';
                else
                    if DATA_OUT_RDY = '1' then
                        DATA_OUT_VLD <= anded_mtx_vld;
                    end if;
                end if;
            end if;
        end process;

    else generate
        DATA_OUT        <= do_int;
        DATA_OUT_VLD    <= anded_mtx_vld;
    end generate;

    DATA_IN_RDY <= DATA_OUT_RDY;

end architecture;
