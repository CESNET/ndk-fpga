-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The AXIS_DISCARD component filters (drops) AXI-Stream packets based on a
-- per-packet discard control signal. When RX_AXI_DISCARD is asserted at
-- Start-of-Packet, the entire packet is consumed from the RX interface
-- without being forwarded to the TX interface. When RX_AXI_DISCARD is
-- deasserted at SOP, the packet passes through unchanged.
--
-- The discard decision is sampled only at the first word of each packet
-- (SOP) and remains active for the entire packet duration. Discarded
-- packets are consumed immediately regardless of TX backpressure,
-- ensuring that discarded packets never block the pipeline.
--
-- Guaranteed throughput: 1 word per clock cycle.
--
entity AXIS_DISCARD is
    generic (
        -- AXI-Stream data bus width in bits; must be a multiple of 8.
        AXI_TDATA_WIDTH  : natural := 512;
        -- AXI-Stream user signal width in bits. Set to 0 to disable TUSER.
        AXI_TUSER_WIDTH  : natural := 64;
        -- Target device.
        DEVICE           : string  := "AGILEX"
    );
    port (
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- =====================================================================
        -- RX AXI-Stream Interface
        -- =====================================================================
        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER     : in  std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- =====================================================================
        -- Discard control (sampled only at the first word of each packet)
        -- When '1' at SOP, the entire packet is dropped.
        -- =====================================================================
        RX_AXI_DISCARD   : in  std_logic;

        -- =====================================================================
        -- TX AXI-Stream Interface
        -- =====================================================================
        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER     : out std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
    );
end entity;

architecture FULL of AXIS_DISCARD is

    -- Active discard flag: combinatorial at SOP, registered during packet
    signal discard      : std_logic;
    signal discard_reg  : std_logic;

    -- Packet tracking
    signal in_pkt       : std_logic;
    signal rx_transfer  : std_logic;

begin

    -- =====================================================================
    -- Discard Flag Muxing
    -- At SOP (in_pkt=0): use combinatorial RX_AXI_DISCARD input
    -- During packet (in_pkt=1): use registered value captured at SOP
    -- =====================================================================
    discard <= RX_AXI_DISCARD when in_pkt = '0' else discard_reg;

    -- =====================================================================
    -- AXI-Stream Handshake
    --
    -- When discarding: RX_AXI_TREADY = '1' (consume immediately, bypass
    --                  TX backpressure) and TX_AXI_TVALID = '0' (suppress
    --                  output).
    -- When not discarding: Normal pass-through with backpressure
    --                      propagation from TX to RX.
    -- =====================================================================
    RX_AXI_TREADY <= '1' when discard = '1' else TX_AXI_TREADY;
    TX_AXI_TVALID <= RX_AXI_TVALID and not discard;

    -- Transfer occurs when both VALID and READY are asserted
    rx_transfer <= RX_AXI_TVALID and RX_AXI_TREADY;

    -- =====================================================================
    -- Data Pass-Through (combinatorial, no pipeline)
    -- Output data is only visible when TX_AXI_TVALID is asserted (i.e.,
    -- when not discarding), so discarded data never appears on TX.
    -- =====================================================================
    TX_AXI_TDATA <= RX_AXI_TDATA;
    TX_AXI_TKEEP <= RX_AXI_TKEEP;
    TX_AXI_TLAST <= RX_AXI_TLAST;

    -- TUSER pass-through (conditional generate for zero-width case)
    tuser_g : if AXI_TUSER_WIDTH > 0 generate
        TX_AXI_TUSER <= RX_AXI_TUSER;
    else generate
        TX_AXI_TUSER <= (others => '0');
    end generate;

    -- =====================================================================
    -- Packet Tracking and Discard Flag Registration
    --
    -- Tracks whether we are currently inside a packet and captures the
    -- discard flag at SOP for the duration of the packet.
    -- =====================================================================
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                in_pkt      <= '0';
                discard_reg <= '0';
            elsif (rx_transfer = '1') then
                if (RX_AXI_TLAST = '1') then
                    -- EOP: no longer inside a packet
                    in_pkt <= '0';
                elsif (in_pkt = '0') then
                    -- SOP accept: entering a multi-word packet, capture discard
                    in_pkt      <= '1';
                    discard_reg <= RX_AXI_DISCARD;
                end if;
                -- Middle of packet (in_pkt=1, TLAST=0): hold registered values
            end if;
        end if;
    end process;

end architecture;
