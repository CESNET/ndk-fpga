-- ab_init_pack.vhd: Package with functions for initialization of
--                     ADDR_BASE,
--                     PORT_MAPPING and
--                     ADDR_MASK
--                   in mi_splitter_plus_gen.vhd and mi_splitter_plus_gen_wrapper.vhd
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;
use work.basics_test_pkg.all;

package ab_init_pack is

    function init_addr_base_downto(ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t;
    function init_addr_base_to(ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t;

    function init_port_mapping_downto(ADDR_BASES : integer; PORTS : integer) return i_array_t;
    function init_addr_mask_downto(ADDR_BASE : slv_array_t; ADDR_WIDTH : integer) return std_logic_vector;

end package;

package body ab_init_pack is

    function init_addr_base_downto(ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t is
        variable v  : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '1');
        variable s1 : integer := 8;
        variable s2 : integer := 5;
        variable x  : integer := 0;
        variable addr_base_arr_dto : slv_array_t(ITEMS_X-1 downto 0)(DATA_WIDTH-1 downto 0);
    begin

        pb_init_l : for i in ITEMS_X-1 downto 0 loop
            randint(s1, s2, 0, max(0, 2**DATA_WIDTH-1), x);
            v := std_logic_vector(unsigned(v) - x);
            addr_base_arr_dto(i) := v;
        end loop pb_init_l;

        addr_base_arr_dto(0) := (others => '0');
        return addr_base_arr_dto;

    end function;

    function init_addr_base_to(ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t is
        variable v  : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '1');
        variable s1 : integer := 4;
        variable s2 : integer := 7;
        variable x  : integer := 2;
        variable addr_base_arr_to : slv_array_t(0 to ITEMS_X-1)(DATA_WIDTH-1 downto 0);
    begin

        pb_init_l : for i in ITEMS_X-1 downto 0 loop
            randint(s1, s2, 0, max(0, 2**DATA_WIDTH-1), x);
            v := std_logic_vector(unsigned(v) - x);
            addr_base_arr_to(i) := v;
        end loop pb_init_l;

        addr_base_arr_to(0) := (others => '0');
        return addr_base_arr_to;

    end function;

    function init_port_mapping_downto(ADDR_BASES : integer; PORTS : integer) return i_array_t is
        variable mapping : i_array_t(ADDR_BASES-1 downto 0);
        variable p : integer;
    begin
        p := 0;
        for i in 0 to ADDR_BASES-1 loop
            mapping(i) := p;
            if (p<PORTS-1) then
                p := p+1;
            end if;
        end loop;
        return mapping;
    end function;

    function init_addr_mask_downto(ADDR_BASE : slv_array_t; ADDR_WIDTH : integer) return std_logic_vector is
        variable mask          : std_logic_vector(ADDR_WIDTH-1 downto 0) := (others => '0');
        variable first_one_ind : natural := ADDR_WIDTH-1;
        variable last_one_ind  : natural := 0;
    begin
        -- OR all Address Bases
        for i in 0 to ADDR_BASE'length-1 loop
            mask := mask or ADDR_BASE(i);
        end loop;

        -- Find postion of the first '1'
        for i in ADDR_WIDTH-1 downto 0 loop
            first_one_ind := first_one_ind;
            if mask(i) = '1' then
                first_one_ind := i;
                exit;
            end if;
        end loop;

        -- Find postion of the last '1'
        for i in 0 to ADDR_WIDTH-1 loop
            last_one_ind := last_one_ind;
            if mask(i) = '1' then
                last_one_ind := i;
                exit;
            end if;
        end loop;

        --  Fill the mask with '0's and then ...
        mask := (others => '0');
        -- ... overwrite '0's by '1's from the position of the first '1' to the last '1'
        mask(first_one_ind downto last_one_ind) := (others => '1');
        return mask;
    end function;

end package body;
