-- eth_hdr_pack.vhd: Ethernet Header Package
-- Copyright (C) 2021 CESNET
-- Author: Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

-- -----------------------------------------------------------------------------
--                        Ethernet Header Package
-- -----------------------------------------------------------------------------

-- **RX Ethernet HDR items description:**
--
-- ============== ============ =================================================
-- Item bit range Item name    Item description
-- ============== ============ =================================================
-- 0  to 15       LENGTH       Length of Ethernet frame in bytes
-- 16 to 23       PORT         Source port/channel number in global format for the entire card; Examples: card with 2 ports each with 4 channels; third channel of the second port = 6; second channel of the first port = 1)
-- 24 to 24       ERROR        Flag of global error, masked OR of all error bits
-- 25 to 25       ERRORFRAME   Flag of frame error
-- 26 to 26       ERRORMINTU   Flag of length below MINTU
-- 27 to 27       ERRORMAXTU   Flag of length over MAXTU
-- 28 to 28       ERRORCRC     Flag of CRC error
-- 29 to 29       ERRORMAC     Flag of MAC error
-- 30 to 30       BROADCAST    Flag of Broadcast MAC
-- 31 to 31       MULTICAST    Flag of Multicast MAC
-- 32 to 32       HITMACVLD    Flag of hit MAC address in TCAM memory
-- 33 to 36       HITMAC       Index of hit MAC address in TCAM memory
-- 37 to 37       TIMESTAMPVLD Flag of valid timestamp
-- 38 to 101      TIMESTAMP    Timestamp of frame (see TSU module docs for format description)
-- ============== ============ =================================================
--
-- **TX Ethernet HDR items description:**
--
-- ============== ========== ===================================================
-- Item bit range Item name  Item description
-- ============== ========== ===================================================
-- 0  to 15       LENGTH     Length of Ethernet frame in bytes
-- 16 to 23       PORT       Destination port/channel number in global format for the entire card; Examples: card with 2 ports each with 4 channels; third channel of the second port = 6; second channel of the first port = 1)
-- 24 to 24       DISCARD    DRAFT ONLY: Discard frame before transmit to network
-- ============== ========== ===================================================
package eth_hdr_pack is

    constant ETH_RX_HDR_LENGTH_W       : natural := 16;
    constant ETH_RX_HDR_PORT_W         : natural := 8;
    constant ETH_RX_HDR_ERROR_W        : natural := 1;
    constant ETH_RX_HDR_ERRORFRAME_W   : natural := 1;
    constant ETH_RX_HDR_ERRORMINTU_W   : natural := 1;
    constant ETH_RX_HDR_ERRORMAXTU_W   : natural := 1;
    constant ETH_RX_HDR_ERRORCRC_W     : natural := 1;
    constant ETH_RX_HDR_ERRORMAC_W     : natural := 1;
    constant ETH_RX_HDR_BROADCAST_W    : natural := 1;
    constant ETH_RX_HDR_MULTICAST_W    : natural := 1;
    constant ETH_RX_HDR_HITMACVLD_W    : natural := 1;
    constant ETH_RX_HDR_HITMAC_W       : natural := 4;
    constant ETH_RX_HDR_TIMESTAMPVLD_W : natural := 1;
    constant ETH_RX_HDR_TIMESTAMP_W    : natural := 64;

    constant ETH_TX_HDR_LENGTH_W       : natural := 16;
    constant ETH_TX_HDR_PORT_W         : natural := 8;
    constant ETH_TX_HDR_DISCARD_W      : natural := 1;

    constant ETH_RX_HDR_LENGTH_O       : natural := 0;
    constant ETH_RX_HDR_PORT_O         : natural := ETH_RX_HDR_LENGTH_O       + ETH_RX_HDR_LENGTH_W;
    constant ETH_RX_HDR_ERROR_O        : natural := ETH_RX_HDR_PORT_O         + ETH_RX_HDR_PORT_W;
    constant ETH_RX_HDR_ERRORFRAME_O   : natural := ETH_RX_HDR_ERROR_O        + ETH_RX_HDR_ERROR_W;
    constant ETH_RX_HDR_ERRORMINTU_O   : natural := ETH_RX_HDR_ERRORFRAME_O   + ETH_RX_HDR_ERRORFRAME_W;
    constant ETH_RX_HDR_ERRORMAXTU_O   : natural := ETH_RX_HDR_ERRORMINTU_O   + ETH_RX_HDR_ERRORMINTU_W;
    constant ETH_RX_HDR_ERRORCRC_O     : natural := ETH_RX_HDR_ERRORMAXTU_O   + ETH_RX_HDR_ERRORMAXTU_W;
    constant ETH_RX_HDR_ERRORMAC_O     : natural := ETH_RX_HDR_ERRORCRC_O     + ETH_RX_HDR_ERRORCRC_W;
    constant ETH_RX_HDR_BROADCAST_O    : natural := ETH_RX_HDR_ERRORMAC_O     + ETH_RX_HDR_ERRORMAC_W;
    constant ETH_RX_HDR_MULTICAST_O    : natural := ETH_RX_HDR_BROADCAST_O    + ETH_RX_HDR_BROADCAST_W;
    constant ETH_RX_HDR_HITMACVLD_O    : natural := ETH_RX_HDR_MULTICAST_O    + ETH_RX_HDR_MULTICAST_W;
    constant ETH_RX_HDR_HITMAC_O       : natural := ETH_RX_HDR_HITMACVLD_O    + ETH_RX_HDR_HITMACVLD_W;
    constant ETH_RX_HDR_TIMESTAMPVLD_O : natural := ETH_RX_HDR_HITMAC_O       + ETH_RX_HDR_HITMAC_W;
    constant ETH_RX_HDR_TIMESTAMP_O    : natural := ETH_RX_HDR_TIMESTAMPVLD_O + ETH_RX_HDR_TIMESTAMPVLD_W;

    constant ETH_TX_HDR_LENGTH_O       : natural := 0;
    constant ETH_TX_HDR_PORT_O         : natural := ETH_TX_HDR_LENGTH_O + ETH_TX_HDR_LENGTH_W;
    constant ETH_TX_HDR_DISCARD_O      : natural := ETH_TX_HDR_PORT_O   + ETH_TX_HDR_PORT_W;

    subtype ETH_RX_HDR_LENGTH          is natural range ETH_RX_HDR_LENGTH_O       + ETH_RX_HDR_LENGTH_W       -1 downto ETH_RX_HDR_LENGTH_O;
    subtype ETH_RX_HDR_PORT            is natural range ETH_RX_HDR_PORT_O         + ETH_RX_HDR_PORT_W         -1 downto ETH_RX_HDR_PORT_O;
    subtype ETH_RX_HDR_ERROR           is natural range ETH_RX_HDR_ERROR_O        + ETH_RX_HDR_ERROR_W        -1 downto ETH_RX_HDR_ERROR_O;
    subtype ETH_RX_HDR_ERRORFRAME      is natural range ETH_RX_HDR_ERRORFRAME_O   + ETH_RX_HDR_ERRORFRAME_W   -1 downto ETH_RX_HDR_ERRORFRAME_O;
    subtype ETH_RX_HDR_ERRORMINTU      is natural range ETH_RX_HDR_ERRORMINTU_O   + ETH_RX_HDR_ERRORMINTU_W   -1 downto ETH_RX_HDR_ERRORMINTU_O;
    subtype ETH_RX_HDR_ERRORMAXTU      is natural range ETH_RX_HDR_ERRORMAXTU_O   + ETH_RX_HDR_ERRORMAXTU_W   -1 downto ETH_RX_HDR_ERRORMAXTU_O;
    subtype ETH_RX_HDR_ERRORCRC        is natural range ETH_RX_HDR_ERRORCRC_O     + ETH_RX_HDR_ERRORCRC_W     -1 downto ETH_RX_HDR_ERRORCRC_O;
    subtype ETH_RX_HDR_ERRORMAC        is natural range ETH_RX_HDR_ERRORMAC_O     + ETH_RX_HDR_ERRORMAC_W     -1 downto ETH_RX_HDR_ERRORMAC_O;
    subtype ETH_RX_HDR_BROADCAST       is natural range ETH_RX_HDR_BROADCAST_O    + ETH_RX_HDR_BROADCAST_W    -1 downto ETH_RX_HDR_BROADCAST_O;
    subtype ETH_RX_HDR_MULTICAST       is natural range ETH_RX_HDR_MULTICAST_O    + ETH_RX_HDR_MULTICAST_W    -1 downto ETH_RX_HDR_MULTICAST_O;
    subtype ETH_RX_HDR_HITMACVLD       is natural range ETH_RX_HDR_HITMACVLD_O    + ETH_RX_HDR_HITMACVLD_W    -1 downto ETH_RX_HDR_HITMACVLD_O;
    subtype ETH_RX_HDR_HITMAC          is natural range ETH_RX_HDR_HITMAC_O       + ETH_RX_HDR_HITMAC_W       -1 downto ETH_RX_HDR_HITMAC_O;
    subtype ETH_RX_HDR_TIMESTAMPVLD    is natural range ETH_RX_HDR_TIMESTAMPVLD_O + ETH_RX_HDR_TIMESTAMPVLD_W -1 downto ETH_RX_HDR_TIMESTAMPVLD_O;
    subtype ETH_RX_HDR_TIMESTAMP       is natural range ETH_RX_HDR_TIMESTAMP_O    + ETH_RX_HDR_TIMESTAMP_W    -1 downto ETH_RX_HDR_TIMESTAMP_O;

    subtype ETH_TX_HDR_LENGTH          is natural range ETH_TX_HDR_LENGTH_O    + ETH_TX_HDR_LENGTH_W -1 downto ETH_TX_HDR_LENGTH_O;
    subtype ETH_TX_HDR_PORT            is natural range ETH_TX_HDR_PORT_O      + ETH_TX_HDR_PORT_W   -1 downto ETH_TX_HDR_PORT_O;
    subtype ETH_TX_HDR_DISCARD         is natural range ETH_TX_HDR_DISCARD_O   + ETH_TX_HDR_DISCARD_W-1 downto ETH_TX_HDR_DISCARD_O;

    constant ETH_RX_HDR_WIDTH          : natural := ETH_RX_HDR_TIMESTAMP_O + ETH_RX_HDR_TIMESTAMP_W;
    constant ETH_TX_HDR_WIDTH          : natural := ETH_TX_HDR_DISCARD_O   + ETH_TX_HDR_DISCARD_W;

end package;

-- -----------------------------------------------------------------------------
--                        Ethernet Header Package body
-- -----------------------------------------------------------------------------

package body eth_hdr_pack is

end package body;
