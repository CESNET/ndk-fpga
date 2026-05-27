-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): David Vodak <vodak@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component counts the length of each AXI-Stream packet in bytes.
-- The packet length is output on the TX_PACKET_LEN port and is valid
-- together with the TX_AXI_TLAST signal.
--
-- The component has a 1-cycle latency (registered output).
--
entity AXIS_PACKET_LEN is
    generic (
        -- AXI-Stream data bus width in bits; must be a multiple of 8.
        AXI_TDATA_WIDTH : natural := 512;
        -- Maximum packet length (MTU) in bytes. Used to size the byte counter.
        PKT_MTU         : natural := 9216;
        -- Target device.
        DEVICE          : string  := "AGILEX"
    );
    port (
        CLK           : in  std_logic;
        RESET         : in  std_logic;

        -- RX AXI-Stream Interface
        RX_AXI_TDATA  : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP  : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST  : in  std_logic;
        RX_AXI_TVALID : in  std_logic;
        RX_AXI_TREADY : out std_logic;

        -- TX AXI-Stream Interface
        TX_AXI_TDATA  : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP  : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST  : out std_logic;
        TX_AXI_TVALID : out std_logic;
        TX_AXI_TREADY : in  std_logic;

        -- Packet length in bytes, valid with TX_AXI_TLAST.
        TX_PACKET_LEN : out std_logic_vector(log2(PKT_MTU+1)-1 downto 0)
    );
end entity;

architecture FULL of AXIS_PACKET_LEN is

    constant WORD_BYTES : natural := AXI_TDATA_WIDTH/8;
    constant PKT_LEN_W  : natural := log2(PKT_MTU+1);
    constant POPCOUNT_W : natural := log2(WORD_BYTES+1);

    signal rx_word_valid : std_logic;
    signal rx_eop        : std_logic;
    signal rx_in_packet  : std_logic;

    signal popcount      : unsigned(POPCOUNT_W-1 downto 0);
    signal byte_cnt      : unsigned(PKT_LEN_W-1 downto 0);
    signal byte_cnt_next : unsigned(PKT_LEN_W-1 downto 0);

    signal pkt_len_reg   : std_logic_vector(PKT_LEN_W-1 downto 0);

    signal tx_tdata_reg  : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_tkeep_reg  : std_logic_vector(WORD_BYTES-1 downto 0);
    signal tx_tlast_reg  : std_logic;
    signal tx_tvalid_reg : std_logic;

begin

    -- =========================================================================
    --  Input control
    -- =========================================================================

    rx_word_valid <= RX_AXI_TVALID and RX_AXI_TREADY;
    rx_eop        <= RX_AXI_TLAST and rx_word_valid;

    -- Detect whether we are inside a packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or rx_eop = '1') then
                rx_in_packet <= '0';
            elsif (rx_word_valid = '1') then
                rx_in_packet <= '1';
            end if;
        end if;
    end process;

    -- =========================================================================
    --  Byte counter
    -- =========================================================================

    popcount <= to_unsigned(count_ones(RX_AXI_TKEEP), POPCOUNT_W);

    byte_cnt_next <= byte_cnt + popcount;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_word_valid = '1') then
                if (RX_AXI_TLAST = '1') then
                    byte_cnt <= (others => '0');
                else
                    byte_cnt <= byte_cnt_next;
                end if;
            end if;
            if (RESET = '1') then
                byte_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- =========================================================================
    --  Packet length capture
    -- =========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_eop = '1') then
                pkt_len_reg <= std_logic_vector(byte_cnt_next);
            end if;
        end if;
    end process;

    -- =========================================================================
    --  Output register
    -- =========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                tx_tdata_reg  <= RX_AXI_TDATA;
                tx_tkeep_reg  <= RX_AXI_TKEEP;
                tx_tlast_reg  <= RX_AXI_TLAST;
                tx_tvalid_reg <= RX_AXI_TVALID;
            end if;
            if (RESET = '1') then
                tx_tvalid_reg <= '0';
            end if;
        end if;
    end process;

    RX_AXI_TREADY <= TX_AXI_TREADY;

    TX_AXI_TDATA  <= tx_tdata_reg;
    TX_AXI_TKEEP  <= tx_tkeep_reg;
    TX_AXI_TLAST  <= tx_tlast_reg;
    TX_AXI_TVALID <= tx_tvalid_reg;
    TX_PACKET_LEN <= pkt_len_reg;

end architecture;
