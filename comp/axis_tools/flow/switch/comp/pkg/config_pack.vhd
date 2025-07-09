-- config_pack.vhd: Switch Configuration Package
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author: Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

use work.proto_hdr_pack.all;
use work.proto_match_pack.all;

-- -----------------------------------------------------------------------------
--                        Switch Configuration Package
-- -----------------------------------------------------------------------------
package config_pack is

    -- Protocol identifiers.
    constant MATCH_PROTOCOL_MAC     : natural := 0;
    constant MATCH_PROTOCOL_VLAN_Q  : natural := 1;
    constant MATCH_PROTOCOL_VLAN_AD : natural := 2;

    constant CONFIG_NUM_PORTS   : natural := 4;
    constant CONFIG_NUM_ACTIONS : natural := CONFIG_NUM_PORTS;
    constant CONFIG_VOQ_ITEMS   : natural := 150;
    constant CONFIG_OP_ITEMS    : natural := 150;

    -- TODO: this is not a very pleasant way to configure the switch.
    constant MAX_FIELDS         : natural := 2;

    constant MAT_CONFIG_DST_MAC : mat_config_t (
        match_protocols(MAX_FIELDS-1 downto 0),
        match_range_highs(MAX_FIELDS-1 downto 0),
        match_range_lows(MAX_FIELDS-1 downto 0)
    ) := (
        match_num_fields   => 1,
        match_items        => 64,
        match_protocols    => (0 => MATCH_PROTOCOL_MAC, others => 0),
        match_range_highs  => (0 => MAC_DST_R'high    , others => 0),
        match_range_lows   => (0 => MAC_DST_R'low     , others => 0)
    );

    constant MAT_CONFIG_VID : mat_config_t (
        match_protocols(MAX_FIELDS-1 downto 0),
        match_range_highs(MAX_FIELDS-1 downto 0),
        match_range_lows(MAX_FIELDS-1 downto 0)
    ) := (
        match_num_fields   => 1,
        match_items        => 64,
        match_protocols    => (0 => MATCH_PROTOCOL_VLAN_Q, others => 0),
        match_range_highs  => (0 => VLAN_TCI_VID_R'high  , others => 0),
        match_range_lows   => (0 => VLAN_TCI_VID_R'low   , others => 0)
    );

    -- TODO: add corresponding software support
--    constant MAT_CONFIG_SRC_DST_MAC : mat_config_t (
--        match_protocols(MAX_FIELDS-1 downto 0),
--        match_range_highs(MAX_FIELDS-1 downto 0),
--        match_range_lows(MAX_FIELDS-1 downto 0)
--    ) := (
--        match_num_fields   => 2,
--        match_items        => 64,
--        match_protocols    => (others => MATCH_PROTOCOL_MAC),
--        match_range_highs  => (0 => MAC_DST_R'high, 1 => MAC_SRC_R'high),
--        match_range_lows   => (0 => MAC_DST_R'low,  1 => MAC_SRC_R'low)
--    );

    -- lower index also means higher priority
    constant CONFIG : config_array_t := (
        0 => MAT_CONFIG_DST_MAC,
        1 => MAT_CONFIG_VID --,
--        2 => MAT_CONFIG_SRC_DST_MAC
    );

end package;

-- -----------------------------------------------------------------------------
--                        Protocol Match Package body
-- -----------------------------------------------------------------------------
package body config_pack is
end package body;
