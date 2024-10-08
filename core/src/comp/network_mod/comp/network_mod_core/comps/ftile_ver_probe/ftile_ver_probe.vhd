-- ftile_ver_probe.vhd: A probe for verification purposes
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.type_pack.all;

entity NETWORK_MOD_CORE_FTILE_VER_PROBE is
generic (
    CHANNELS        : natural;

    DATA_WIDTH      : natural;
    INFRAME_WIDTH   : natural;
    EOP_EMPTY_WIDTH : natural;
    FCS_ERROR_WIDTH : natural;
    ERROR_WIDTH     : natural;
    STATUS_WIDTH    : natural
);
port (
    -- INPUT
    IN_MAC_DATA      : in  slv_array_t      (CHANNELS-1 downto 0)(DATA_WIDTH     -1 downto 0);
    IN_MAC_INFRAME   : in  slv_array_t      (CHANNELS-1 downto 0)(INFRAME_WIDTH  -1 downto 0);
    IN_MAC_EOP_EMPTY : in  slv_array_t      (CHANNELS-1 downto 0)(EOP_EMPTY_WIDTH-1 downto 0);
    IN_MAC_FCS_ERROR : in  slv_array_t      (CHANNELS-1 downto 0)(FCS_ERROR_WIDTH-1 downto 0);
    IN_MAC_ERROR     : in  slv_array_t      (CHANNELS-1 downto 0)(ERROR_WIDTH    -1 downto 0);
    IN_MAC_STATUS    : in  slv_array_t      (CHANNELS-1 downto 0)(STATUS_WIDTH   -1 downto 0);
    IN_MAC_VALID     : in  std_logic_vector (CHANNELS-1 downto 0);
    
    -- OUTPUT
    OUT_MAC_DATA      : out  slv_array_t      (CHANNELS-1 downto 0)(DATA_WIDTH     -1 downto 0);
    OUT_MAC_INFRAME   : out  slv_array_t      (CHANNELS-1 downto 0)(INFRAME_WIDTH  -1 downto 0);
    OUT_MAC_EOP_EMPTY : out  slv_array_t      (CHANNELS-1 downto 0)(EOP_EMPTY_WIDTH-1 downto 0);
    OUT_MAC_FCS_ERROR : out  slv_array_t      (CHANNELS-1 downto 0)(FCS_ERROR_WIDTH-1 downto 0);
    OUT_MAC_ERROR     : out  slv_array_t      (CHANNELS-1 downto 0)(ERROR_WIDTH    -1 downto 0);
    OUT_MAC_STATUS    : out  slv_array_t      (CHANNELS-1 downto 0)(STATUS_WIDTH   -1 downto 0);
    OUT_MAC_VALID     : out  std_logic_vector (CHANNELS-1 downto 0)
);
end entity;

architecture FULL of NETWORK_MOD_CORE_FTILE_VER_PROBE is

    -- Signals for verification purposes
    signal mac_data      : std_logic_vector (CHANNELS*DATA_WIDTH     -1 downto 0);
    signal mac_inframe   : std_logic_vector (CHANNELS*INFRAME_WIDTH  -1 downto 0);
    signal mac_eop_empty : std_logic_vector (CHANNELS*EOP_EMPTY_WIDTH-1 downto 0);
    signal mac_fcs_error : std_logic_vector (CHANNELS*FCS_ERROR_WIDTH-1 downto 0);
    signal mac_error     : std_logic_vector (CHANNELS*ERROR_WIDTH    -1 downto 0);
    signal mac_status    : std_logic_vector (CHANNELS*STATUS_WIDTH   -1 downto 0);
    signal mac_valid     : std_logic_vector (CHANNELS                -1 downto 0);

begin

    -- Input serialization
    mac_data      <= slv_array_ser(IN_MAC_DATA     , CHANNELS, DATA_WIDTH     );
    mac_inframe   <= slv_array_ser(IN_MAC_INFRAME  , CHANNELS, INFRAME_WIDTH  );
    mac_eop_empty <= slv_array_ser(IN_MAC_EOP_EMPTY, CHANNELS, EOP_EMPTY_WIDTH);
    mac_fcs_error <= slv_array_ser(IN_MAC_FCS_ERROR, CHANNELS, FCS_ERROR_WIDTH);
    mac_error     <= slv_array_ser(IN_MAC_ERROR    , CHANNELS, ERROR_WIDTH    );
    mac_status    <= slv_array_ser(IN_MAC_STATUS   , CHANNELS, STATUS_WIDTH   );
    mac_valid     <= IN_MAC_VALID;

    -- Output deserialization
    OUT_MAC_DATA      <= slv_array_deser(mac_data     , CHANNELS, DATA_WIDTH     );
    OUT_MAC_INFRAME   <= slv_array_deser(mac_inframe  , CHANNELS, INFRAME_WIDTH  );
    OUT_MAC_EOP_EMPTY <= slv_array_deser(mac_eop_empty, CHANNELS, EOP_EMPTY_WIDTH);
    OUT_MAC_FCS_ERROR <= slv_array_deser(mac_fcs_error, CHANNELS, FCS_ERROR_WIDTH);
    OUT_MAC_ERROR     <= slv_array_deser(mac_error    , CHANNELS, ERROR_WIDTH    );
    OUT_MAC_STATUS    <= slv_array_deser(mac_status   , CHANNELS, STATUS_WIDTH   );
    OUT_MAC_VALID     <= mac_valid;

end architecture;
