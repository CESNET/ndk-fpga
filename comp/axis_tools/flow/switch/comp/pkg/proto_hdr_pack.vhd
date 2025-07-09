-- proto_hdr_pack.vhd: Protocols Header Package
-- Copyright (C) 2024 CESNET
-- Author: Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

-- -----------------------------------------------------------------------------
--                        Protocol Header Package
-- -----------------------------------------------------------------------------
package proto_hdr_pack is

    constant MAC_ADDR_W      : natural := 48;
    constant MAC_ETHERTYPE_W : natural := 16;
    constant MAC_HDR_W       : natural := MAC_ADDR_W*2 + MAC_ETHERTYPE_W;

    subtype MAC_DST_R       is natural range  MAC_ADDR_W    -1 downto 0;
    subtype MAC_SRC_R       is natural range (MAC_ADDR_W*2) -1 downto MAC_ADDR_W;
    subtype MAC_ETHERTYPE_R is natural range  MAC_HDR_W     -1 downto MAC_ADDR_W*2;

    constant VLAN_TPID_W     : natural := 16;
    constant VLAN_TCI_W      : natural := 16;
    constant VLAN_HDR_W      : natural := VLAN_TPID_W + VLAN_TCI_W;

    subtype VLAN_TPID_R     is natural range VLAN_TPID_W -1 downto 0;
    subtype VLAN_TCI_R      is natural range VLAN_HDR_W  -1 downto VLAN_TPID_W;

    constant VLAN_TCI_PCP_W  : natural := 3;
    constant VLAN_TCI_DEI_W  : natural := 1;
    constant VLAN_TCI_VID_W  : natural := 12;

    subtype VLAN_TCI_PCP_R  is natural range VLAN_TPID_W +  VLAN_TCI_PCP_W                 -1 downto VLAN_TPID_W + 0;
    subtype VLAN_TCI_DEI_R  is natural range VLAN_TPID_W + (VLAN_TCI_PCP_W+VLAN_TCI_DEI_W) -1 downto VLAN_TPID_W + VLAN_TCI_PCP_W;
    subtype VLAN_TCI_VID_R  is natural range VLAN_TPID_W +  VLAN_TCI_W                     -1 downto VLAN_TPID_W + VLAN_TCI_PCP_W+VLAN_TCI_DEI_W;

end package;

-- -----------------------------------------------------------------------------
--                        Protocol Header Package body
-- -----------------------------------------------------------------------------
package body proto_hdr_pack is

end package body;
