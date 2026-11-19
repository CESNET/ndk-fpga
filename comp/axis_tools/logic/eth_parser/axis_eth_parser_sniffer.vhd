-- axis_eth_parser_sniffer.vhd: AXI-Stream Ethernet Parser Sniffer
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The AXIS_ETH_PARSER_SNIFFER component extracts a contiguous block of bytes
-- from an AXI-Stream data flow at a specified offset. The component keeps the
-- last EXTRACT_BYTES-1 bytes of the stream. It reads all extracted bytes in the
-- AXI word that contains the last extracted byte. START_VALID must come no later
-- than this AXI word. Metadata (protocol type and offset) is passed through the
-- component to maintain context for downstream parser stages.
-- The AXI-Stream data passes through with one cycle latency.
--
entity AXIS_ETH_PARSER_SNIFFER is
    generic (
        -- Width of the AXI-Stream data bus in bits (must be power of two, e.g., 256, 512)
        AXI_TDATA_WIDTH    : natural := 512;
        -- Number of bytes to extract from the header, at least 2
        EXTRACT_BYTES      : natural := 32;
        -- Maximum packet size in bytes (determines offset field width)
        PKT_MTU            : natural := 2**14;
        -- Width of metadata field (protocol + offset information)
        META_WIDTH         : natural := 32;
        -- Target device family for implementation (e.g., "AGILEX", "ULTRASCALE")
        DEVICE             : string  := "AGILEX"
    );
    port (
        -- System clock
        CLK                   : in  std_logic;
        -- Active-high synchronous reset
        RESET                 : in  std_logic;

        -- RX AXI-Stream Interface
        RX_AXI_TDATA          : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP          : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST          : in  std_logic;
        RX_AXI_TVALID         : in  std_logic;
        RX_AXI_TREADY         : out std_logic;

        -- TX AXI-Stream Interface
        TX_AXI_TDATA          : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP          : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST          : out std_logic;
        TX_AXI_TVALID         : out std_logic;
        TX_AXI_TREADY         : in  std_logic;

        -- Start metadata (protocol and offset for extraction)
        START_META            : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- Start byte offset within the frame
        START_OFFSET          : in  std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        -- Start extraction enable
        START_ENABLE          : in  std_logic;
        -- Start extraction valid
        START_VALID           : in  std_logic;

        -- Extracted metadata (passed through from START_META)
        EXTRACTED_META        : out std_logic_vector(META_WIDTH-1 downto 0);
        -- Extracted header data (EXTRACT_BYTES bytes)
        EXTRACTED_DATA        : out std_logic_vector(EXTRACT_BYTES*8-1 downto 0);
        -- Extracted data valid
        EXTRACTED_VALID       : out std_logic;
        -- All EXTRACT_BYTES bytes are inside the packet. Valid with EXTRACTED_VALID.
        EXTRACTED_COMPLETE    : out std_logic
    );
end entity;

architecture FULL of AXIS_ETH_PARSER_SNIFFER is

    -- Number of bytes per AXI word
    constant WORD_BYTES      : natural := AXI_TDATA_WIDTH/8;
    -- Width of the offset field in bits (derived from PKT_MTU)
    constant OFFSET_WIDTH    : natural := log2(PKT_MTU+1);
    -- Bits required for byte offset within an AXI word
    constant OFF_BYTES_W     : natural := log2(WORD_BYTES);
    -- Width of the offset of the last extracted byte, which can be above PKT_MTU
    constant END_OFF_W       : natural := max(log2(PKT_MTU+EXTRACT_BYTES), OFF_BYTES_W+1);
    -- Bits required for word offset within the frame
    constant END_WORDS_W     : natural := END_OFF_W - OFF_BYTES_W;

    -- AXI word tracking
    signal valid_word           : std_logic;
    signal end_word             : std_logic;
    signal word_cnt             : unsigned(END_WORDS_W-1 downto 0);

    -- AXI register stage signals
    signal tx_axi_tdata_reg     : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_axi_tkeep_reg     : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal tx_axi_tlast_reg     : std_logic;
    signal tx_axi_tvalid_reg    : std_logic;

    -- Offset of the last extracted byte and metadata latching
    signal end_off_reg          : unsigned(END_OFF_W-1 downto 0);
    signal start_valid_reg      : std_logic;
    signal start_enable_reg     : std_logic;
    signal end_off              : unsigned(END_OFF_W-1 downto 0);
    signal end_off_word         : unsigned(END_WORDS_W-1 downto 0);
    signal end_off_byte         : unsigned(OFF_BYTES_W-1 downto 0);
    signal soff_vld             : std_logic;
    signal skip_vld_done        : std_logic;
    signal enable_flag          : std_logic;

    -- The last EXTRACT_BYTES-1 bytes of the stream before the current AXI word. Byte 0 is the oldest.
    signal history              : std_logic_vector((EXTRACT_BYTES-1)*8-1 downto 0);
    -- history followed by the current AXI word
    signal window               : std_logic_vector((EXTRACT_BYTES-1+WORD_BYTES)*8-1 downto 0);

    -- Extraction
    signal extraction_complete  : std_logic;
    signal last_byte_vld        : std_logic;

    -- Metadata registers
    signal start_meta_reg       : std_logic_vector(META_WIDTH-1 downto 0);
    signal extracted_meta_reg   : std_logic_vector(META_WIDTH-1 downto 0);

    -- Extracted data registers
    signal extracted_data_reg   : std_logic_vector(EXTRACT_BYTES*8-1 downto 0);
    signal extracted_data_next  : std_logic_vector(EXTRACT_BYTES*8-1 downto 0);
    signal extracted_done_reg   : std_logic;
    signal extracted_vld        : std_logic;
    signal extracted_vld_reg    : std_logic;
    signal extracted_cmpl_reg   : std_logic;

begin

    assert (EXTRACT_BYTES >= 2)
        report "AXIS_ETH_PARSER_SNIFFER: Use EXTRACT_BYTES of 2 or more."
        severity failure;

    -- AXI word valid and last word detection
    valid_word <= RX_AXI_TVALID and TX_AXI_TREADY;
    end_word   <= RX_AXI_TLAST and valid_word;

    -- Word counter tracks position within packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                word_cnt <= (others => '0');
            elsif (valid_word = '1') then
                word_cnt <= word_cnt + 1;
            end if;
        end if;
    end process;

    -- AXI register stage provides one cycle latency for data path
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                tx_axi_tdata_reg  <= (others => '0');
                tx_axi_tkeep_reg  <= (others => '0');
                tx_axi_tlast_reg  <= '0';
                tx_axi_tvalid_reg <= '0';
            elsif (TX_AXI_TREADY = '1') then
                tx_axi_tdata_reg  <= RX_AXI_TDATA;
                tx_axi_tkeep_reg  <= RX_AXI_TKEEP;
                tx_axi_tlast_reg  <= RX_AXI_TLAST;
                tx_axi_tvalid_reg <= RX_AXI_TVALID;
            end if;
        end if;
    end process;

    TX_AXI_TDATA  <= tx_axi_tdata_reg;
    TX_AXI_TKEEP  <= tx_axi_tkeep_reg;
    TX_AXI_TLAST  <= tx_axi_tlast_reg;
    TX_AXI_TVALID <= tx_axi_tvalid_reg;
    RX_AXI_TREADY <= TX_AXI_TREADY;

    -- Latch the offset of the last extracted byte and metadata when extraction begins
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (START_VALID = '1') then
                end_off_reg      <= resize(unsigned(START_OFFSET), END_OFF_W) + (EXTRACT_BYTES-1);
                start_valid_reg  <= '1';
                start_meta_reg   <= START_META;
                start_enable_reg <= START_ENABLE;
            end if;
            if ((RESET = '1') or (end_word = '1')) then
                start_valid_reg <= '0';
            end if;
        end if;
    end process;

    -- Current offset of the last extracted byte (combinational or registered)
    end_off      <= resize(unsigned(START_OFFSET), END_OFF_W) + (EXTRACT_BYTES-1) when (START_VALID = '1') else end_off_reg;
    soff_vld     <= start_valid_reg or START_VALID;
    end_off_word <= end_off(END_OFF_W-1 downto OFF_BYTES_W);
    end_off_byte <= end_off(OFF_BYTES_W-1 downto 0);

    enable_flag <= START_ENABLE when (START_VALID = '1') else start_enable_reg;

    -- The window contains all extracted bytes in the AXI word with the last extracted byte
    window <= RX_AXI_TDATA & history;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (valid_word = '1') then
                history <= window(window'high downto WORD_BYTES*8);
            end if;
        end if;
    end process;

    -- The last extracted byte is byte end_off_byte of the current AXI word.
    -- The extracted bytes start at byte end_off_byte of window.
    process (all)
    begin
        extracted_data_next <= (others => '0');
        for i in 0 to WORD_BYTES-1 loop
            if (end_off_byte = i) then
                extracted_data_next <= window((i+EXTRACT_BYTES)*8-1 downto i*8);
            end if;
        end loop;
    end process;

    extraction_complete <= '1' when (soff_vld = '1' and valid_word = '1' and end_off_word = word_cnt) else '0';

    -- Store extracted data bytes
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (extraction_complete = '1') then
                extracted_data_reg <= extracted_data_next;
            end if;
        end if;
    end process;

    -- Track when extraction is done
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                extracted_done_reg <= '0';
            elsif (extraction_complete = '1') then
                extracted_done_reg <= '1';
            end if;
        end if;
    end process;

    -- Generate valid pulse when extraction completes or packet ends
    extracted_vld <= (extraction_complete and not extracted_done_reg) or
                     (end_word and not extraction_complete and not extracted_done_reg);

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                extracted_vld_reg <= '0';
            elsif (enable_flag = '1') then
                extracted_vld_reg <= extracted_vld;
            else
                -- Nothing is extracted, so the valid pulse does not wait for the word at START_OFFSET.
                -- That word can be after the end of the packet.
                extracted_vld_reg <= soff_vld and valid_word and not skip_vld_done;
            end if;
        end if;
    end process;

    -- The valid pulse without extraction is sent only once per packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                skip_vld_done <= '0';
            elsif (soff_vld = '1' and valid_word = '1') then
                skip_vld_done <= '1';
            end if;
        end if;
    end process;

    -- In the last AXI word, the last extracted byte is valid only when RX_AXI_TKEEP marks it
    last_byte_vld <= RX_AXI_TKEEP(to_integer(end_off_byte)) when (RX_AXI_TLAST = '1') else '1';

    process (CLK)
    begin
        if rising_edge(CLK) then
            extracted_cmpl_reg <= extraction_complete and last_byte_vld;
        end if;
    end process;

    -- Store metadata for output
    process (CLK)
    begin
        if rising_edge(CLK) then
            extracted_meta_reg <= START_META when (START_VALID = '1') else start_meta_reg;
        end if;
    end process;

    -- Drive extracted data outputs
    EXTRACTED_META     <= extracted_meta_reg;
    EXTRACTED_DATA     <= extracted_data_reg;
    EXTRACTED_VALID    <= extracted_vld_reg;
    EXTRACTED_COMPLETE <= extracted_cmpl_reg;

end architecture;
