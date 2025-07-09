-- switch_fabric.vhd: AXIS_SWITCH_FABRIC component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

entity AXIS_SWITCH_FABRIC is
    generic (
        -- Number of input/output ports.
        NUM_PORTS       : natural := 2;
        -- Maximum capacity width in bits.
        STATUS_WIDTH    : integer := 4+1;
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH : natural := 512;
        -- AXI-Stream user data width in bits.
        AXI_TUSER_WIDTH : natural := 0;
        -- Target device.
        DEVICE          : string  := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- =========================================================================
        -- RX AXI INTERFACE
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER    : in  std_logic_vector(NUM_PORTS*AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST    : in  std_logic_vector(NUM_PORTS-1 downto 0);
        RX_AXI_TVALID   : in  std_logic_vector(NUM_PORTS-1 downto 0);
        RX_AXI_TREADY   : out std_logic_vector(NUM_PORTS-1 downto 0);

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(NUM_PORTS*AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER    : out std_logic_vector(NUM_PORTS*AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        TX_AXI_TLAST    : out std_logic_vector(NUM_PORTS-1 downto 0);
        TX_AXI_TVALID   : out std_logic_vector(NUM_PORTS-1 downto 0);
        TX_AXI_TREADY   : in  std_logic_vector(NUM_PORTS-1 downto 0);

        -- =========================================================================
        -- PORT-MATCHING CONTROL INTERFACE
        -- =========================================================================
        DEST_REQ_VEC    : in  std_logic_vector(NUM_PORTS*NUM_PORTS-1 downto 0);
        DEST_REQ_SIZES  : in  std_logic_vector(NUM_PORTS*NUM_PORTS*STATUS_WIDTH-1 downto 0) := (others => '0');
        IP_CONN_VLD     : out std_logic_vector(NUM_PORTS-1 downto 0);
        IP_CONN_SEL     : out std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0);
        OP_CONN_VLD     : out std_logic_vector(NUM_PORTS-1 downto 0);
        OP_CONN_SEL     : out std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0)
    );
end entity;

architecture FULL of AXIS_SWITCH_FABRIC is
begin

    islip_i : entity work.ISLIP
    generic map (
        NUM_PORTS => NUM_PORTS,
        NUM_ITEMS => 2**(STATUS_WIDTH-1),
        DEVICE    => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,
        DEST_REQ_VEC   => DEST_REQ_VEC,
        DEST_REQ_SIZES => DEST_REQ_SIZES,
        IP_CONN_VLD    => IP_CONN_VLD,
        IP_CONN_SEL    => IP_CONN_SEL,
        OP_CONN_VLD    => OP_CONN_VLD,
        OP_CONN_SEL    => OP_CONN_SEL
    );

    axis_crossbar_i : entity work.AXIS_CROSSBAR
    generic map (
        AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
        AXI_TUSER_WIDTH => AXI_TUSER_WIDTH,
        NUM_PORTS       => NUM_PORTS
    )
    port map (
        RX_AXI_TDATA  => RX_AXI_TDATA,
        RX_AXI_TKEEP  => RX_AXI_TKEEP,
        RX_AXI_TUSER  => RX_AXI_TUSER,
        RX_AXI_TLAST  => RX_AXI_TLAST,
        RX_AXI_TVALID => RX_AXI_TVALID,
        RX_AXI_TREADY => RX_AXI_TREADY,
        TX_AXI_TDATA  => TX_AXI_TDATA,
        TX_AXI_TKEEP  => TX_AXI_TKEEP,
        TX_AXI_TUSER  => TX_AXI_TUSER,
        TX_AXI_TLAST  => TX_AXI_TLAST,
        TX_AXI_TVALID => TX_AXI_TVALID,
        TX_AXI_TREADY => TX_AXI_TREADY,
        OP_CONN_VLD   => OP_CONN_VLD,
        OP_CONN_SEL   => OP_CONN_SEL
    );

end architecture;
