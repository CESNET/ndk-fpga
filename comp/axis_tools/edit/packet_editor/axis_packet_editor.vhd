-- axis_packet_editor.vhd: AXIS_PACKET_EDITOR component
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): David Vodak <vodak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- AXIS_PACKET_EDITOR rewrites selected bytes inside AXI-Stream packets.
-- One edit instruction is sampled at the first word of each packet and held
-- for the whole packet. The instruction contains:
--   * RX_AXI_EDIT_DATA   - replacement bytes
--   * RX_AXI_EDIT_OFFSET - packet byte offset of edit_data(7:0)
--   * RX_AXI_EDIT_MASK   - per-byte enable for EDIT_BYTES
--   * RX_AXI_EDIT_ENABLE - global instruction enable
-- Throughput is 1 word per cycle, no internal buffering is used.
entity AXIS_PACKET_EDITOR is
    generic (
        -- AXI-Stream data bus width in bits; must be a multiple of 8.
        AXI_TDATA_WIDTH  : natural := 512;
        -- Maximum packet length (MTU) in bytes. Used for offset width.
        PKT_MTU          : natural := 9216;
        -- Number of editable bytes carried in one instruction.
        EDIT_BYTES       : natural := 16;
        -- Target device technology.
        DEVICE           : string  := "AGILEX"
    );
    port (
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- AXI-Stream RX interface
        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- Edit instruction sampled at packet start (SOP)
        RX_AXI_EDIT_DATA   : in  std_logic_vector(EDIT_BYTES*8-1 downto 0);
        RX_AXI_EDIT_OFFSET : in  std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        RX_AXI_EDIT_MASK   : in  std_logic_vector(EDIT_BYTES-1 downto 0);
        RX_AXI_EDIT_ENABLE : in  std_logic;

        -- AXI-Stream TX interface
        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
    );
end entity;

architecture FULL of AXIS_PACKET_EDITOR is

    constant WORD_BYTES     : natural := AXI_TDATA_WIDTH/8;
    constant EDIT_OFFSET_W  : natural := log2(PKT_MTU+1);

    -- Input stage and packet tracking
    signal rx_valid_word    : std_logic;
    signal rx_sop           : std_logic;
    signal rx_in_packet     : std_logic;
    signal pkt_byte_cnt     : unsigned(EDIT_OFFSET_W-1 downto 0);

    -- Edit instruction captured at SOP
    signal cfg_edit_data    : std_logic_vector(EDIT_BYTES*8-1 downto 0);
    signal cfg_edit_offset  : unsigned(EDIT_OFFSET_W-1 downto 0);
    signal cfg_edit_mask    : std_logic_vector(EDIT_BYTES-1 downto 0);
    signal cfg_edit_enable  : std_logic;

    -- Active edit configuration (live on SOP, registered otherwise)
    signal cur_edit_data    : std_logic_vector(EDIT_BYTES*8-1 downto 0);
    signal cur_edit_offset  : unsigned(EDIT_OFFSET_W-1 downto 0);
    signal cur_edit_mask    : std_logic_vector(EDIT_BYTES-1 downto 0);
    signal cur_edit_enable  : std_logic;

    -- Edited AXI word
    signal edit_tdata       : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal edit_tkeep       : std_logic_vector(WORD_BYTES-1 downto 0);
    signal edit_tlast       : std_logic;
    signal edit_tvalid      : std_logic;

    -- Output registers
    signal tx_tdata_reg     : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_tkeep_reg     : std_logic_vector(WORD_BYTES-1 downto 0);
    signal tx_tlast_reg     : std_logic;
    signal tx_tvalid_reg    : std_logic;

begin

    -- Static parameter checks.
    assert (AXI_TDATA_WIDTH mod 8 = 0)
        report "AXIS_PACKET_EDITOR: AXI_TDATA_WIDTH must be a multiple of 8."
        severity failure;

    assert (EDIT_BYTES > 0)
        report "AXIS_PACKET_EDITOR: EDIT_BYTES must be greater than 0."
        severity failure;

    ---------------------------------------------------------------------------
    -- Input stage
    ---------------------------------------------------------------------------

    RX_AXI_TREADY <= TX_AXI_TREADY;
    rx_valid_word <= RX_AXI_TVALID and TX_AXI_TREADY;

    -- Track whether input is currently inside a packet.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                rx_in_packet <= '0';
            elsif (rx_valid_word = '1') then
                rx_in_packet <= not RX_AXI_TLAST;
            end if;
        end if;
    end process;

    rx_sop <= rx_valid_word and not rx_in_packet;

    -- Byte offset of the current AXI word in packet.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_valid_word = '1') then
                if (RX_AXI_TLAST = '1') then
                    pkt_byte_cnt <= (others => '0');
                else
                    pkt_byte_cnt <= pkt_byte_cnt + to_unsigned(WORD_BYTES, EDIT_OFFSET_W);
                end if;
            end if;
            if (RESET = '1') then
                pkt_byte_cnt <= (others => '0');
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------
    -- Edit instruction capture
    ---------------------------------------------------------------------------

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_sop = '1') then
                cfg_edit_data   <= RX_AXI_EDIT_DATA;
                cfg_edit_offset <= unsigned(RX_AXI_EDIT_OFFSET);
                cfg_edit_mask   <= RX_AXI_EDIT_MASK;
                cfg_edit_enable <= RX_AXI_EDIT_ENABLE;
            elsif (rx_valid_word = '1' and RX_AXI_TLAST = '1') then
                -- Safety guard: never carry edit enable to the next packet.
                cfg_edit_enable <= '0';
            end if;
            if (RESET = '1') then
                cfg_edit_enable <= '0';
            end if;
        end if;
    end process;

    -- First beat uses live SOP instruction, other beats use captured instruction.
    cur_edit_data   <= RX_AXI_EDIT_DATA                when (rx_sop = '1') else cfg_edit_data;
    cur_edit_offset <= unsigned(RX_AXI_EDIT_OFFSET)    when (rx_sop = '1') else cfg_edit_offset;
    cur_edit_mask   <= RX_AXI_EDIT_MASK                when (rx_sop = '1') else cfg_edit_mask;
    cur_edit_enable <= RX_AXI_EDIT_ENABLE              when (rx_sop = '1') else cfg_edit_enable;

    ---------------------------------------------------------------------------
    -- Byte editor stage
    ---------------------------------------------------------------------------

    process (all)
        variable v_tdata          : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        variable v_word_base      : integer;
        variable v_edit_base      : integer;
        variable v_lane_idx       : integer;
    begin
        v_tdata     := RX_AXI_TDATA;
        v_word_base := to_integer(pkt_byte_cnt);
        v_edit_base := to_integer(cur_edit_offset);

        if (cur_edit_enable = '1') then
            for i in 0 to EDIT_BYTES-1 loop
                v_lane_idx := v_edit_base + i - v_word_base;
                if (cur_edit_mask(i) = '1') then
                    if (v_lane_idx >= 0 and v_lane_idx < WORD_BYTES) then
                        if (RX_AXI_TKEEP(v_lane_idx) = '1') then
                            v_tdata(8*(v_lane_idx+1)-1 downto 8*v_lane_idx) := cur_edit_data(8*(i+1)-1 downto 8*i);
                        end if;
                    end if;
                end if;
            end loop;
        end if;

        edit_tdata <= v_tdata;
    end process;

    edit_tkeep  <= RX_AXI_TKEEP;
    edit_tlast  <= RX_AXI_TLAST;
    edit_tvalid <= RX_AXI_TVALID;

    ---------------------------------------------------------------------------
    -- Output register stage
    ---------------------------------------------------------------------------

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                tx_tdata_reg  <= edit_tdata;
                tx_tkeep_reg  <= edit_tkeep;
                tx_tlast_reg  <= edit_tlast;
                tx_tvalid_reg <= edit_tvalid;
            end if;
            if (RESET = '1') then
                tx_tdata_reg  <= (others => '0');
                tx_tkeep_reg  <= (others => '0');
                tx_tlast_reg  <= '0';
                tx_tvalid_reg <= '0';
            end if;
        end if;
    end process;

    TX_AXI_TDATA  <= tx_tdata_reg;
    TX_AXI_TKEEP  <= tx_tkeep_reg;
    TX_AXI_TLAST  <= tx_tlast_reg;
    TX_AXI_TVALID <= tx_tvalid_reg;

end architecture;
