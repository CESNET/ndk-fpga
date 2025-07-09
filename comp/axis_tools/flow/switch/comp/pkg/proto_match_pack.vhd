-- proto_match_pack.vhd: Protocols Match Parameters Package
-- Copyright (C) 2024 CESNET
-- Author: Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- -----------------------------------------------------------------------------
--                        Protocol Match Package
-- -----------------------------------------------------------------------------
package proto_match_pack is

    -- Array of natural values.
    type natural_array_t is array (natural range <>) of natural;

    -- Match-action table configuration record.
    type mat_config_t is record
        match_num_fields  : natural;
        match_items       : natural;
        match_protocols   : natural_array_t;
        match_range_highs : natural_array_t;
        match_range_lows  : natural_array_t;
    end record mat_config_t;

    -- Switch configuration.
    type config_array_t is array (natural range <>) of mat_config_t;

    -- config_array_get_max selectors.
    constant MAT_CONFIG_ITEMS       : natural := 0;
    constant MAT_CONFIG_MATCH_WIDTH : natural := 1; -- calculated from ranges

    -- Get data vector width in bits.
    function mat_match_width(mat_config : mat_config_t) return natural;

    -- Get data vector field offsets.
    function mat_match_data_bases(mat_config : mat_config_t) return natural_array_t;

    -- Get max value from the given configuration object based on selector.
    function config_array_get_max(config_array : config_array_t; selector : natural) return natural;

    -- Empty configuration object.
    constant CONFIG_NONE : config_array_t := (
        0 => (
            match_num_fields  => 0,
            match_items       => 0,
            match_protocols   => (0 => 0),
            match_range_highs => (0 => 0),
            match_range_lows  => (0 => 0)
        )
    );

end package;

-- -----------------------------------------------------------------------------
--                        Protocol Match Package body
-- -----------------------------------------------------------------------------
package body proto_match_pack is

    function mat_match_width(mat_config : mat_config_t) return natural is
        variable match_data_width : natural := 0;
        variable field_data_width : natural := 0;
    begin
        for i in 0 to mat_config.match_num_fields-1 loop
            field_data_width := mat_config.match_range_highs(i) - mat_config.match_range_lows(i) + 1;
            match_data_width := match_data_width + field_data_width;
        end loop;
        return match_data_width;
    end function mat_match_width;

    function mat_match_data_bases(mat_config : mat_config_t) return natural_array_t is
        variable match_data_bases : natural_array_t(mat_config.match_num_fields+1-1 downto 0) := (others => 0);
    begin
        for i in 0 to mat_config.match_num_fields-1 loop
            match_data_bases(i+1) := mat_config.match_range_highs(i) - mat_config.match_range_lows(i) + 1 + match_data_bases(i);
        end loop;
        return match_data_bases;
    end function mat_match_data_bases;

    function config_array_get_max(config_array : config_array_t; selector : natural) return natural is
        variable max_value : natural := 0;
        variable tmp_value : natural := 0;
    begin
        for i in config_array'range loop
            case selector is
                when MAT_CONFIG_ITEMS       =>
                    tmp_value := config_array(i).match_items;
                when MAT_CONFIG_MATCH_WIDTH =>
                    tmp_value := mat_match_width(config_array(i));
                when others                 =>
                    tmp_value := 0;
            end case;
            max_value := max(max_value, tmp_value);
        end loop;
        return max_value;
    end function config_array_get_max;

end package body;
