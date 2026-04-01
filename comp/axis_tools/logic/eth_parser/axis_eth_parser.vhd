-- axis_eth_parser.vhd: AXI-Stream Ethernet Header Parser
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
use work.axis_eth_parser_types.all;

-- The AXIS_ETH_PARSER component parses Ethernet frames and extracts headers
-- from multiple protocol layers (Ethernet, VLAN, IPv4, TCP, UDP). The parser
-- uses a multi-stage pipeline architecture where each stage processes one
-- protocol header and passes the remaining data to the next stage. Extracted
-- headers are stored in separate FIFOs and presented on the HEADERS output
-- interface. The original frame data passes through unchanged to the TX
-- interface. Backpressure is applied to the RX interface when the internal
-- packet counter approaches FIFO capacity to prevent data loss.
--
entity AXIS_ETH_PARSER is
    generic (
        -- Width of the AXI-Stream data bus in bits (e.g., 256, 512)
        AXI_TDATA_WIDTH : natural := 512;
        -- Maximum packet size in bytes (determines offset field width)
        -- Maximum supported value is 2**14.
        PKT_MTU         : natural := 2**14;
        -- Depth of internal FIFOs (number of packets that can be buffered)
        FIFO_DEPTH      : natural := 64;
        -- Target device family for FIFO implementation (e.g., "AGILEX", "ULTRASCALE")
        DEVICE          : string  := "AGILEX"
    );
    port (
        -- System clock
        CLK           : in  std_logic;
        -- Active-high synchronous reset
        RESET         : in  std_logic;

        -- RX AXI-Stream Interface
        RX_AXI_TDATA  : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP  : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST  : in  std_logic;
        RX_AXI_TVALID : in  std_logic;
        RX_AXI_TREADY : out std_logic;

        -- TX AXI-Stream Interface
        TX_AXI_TDATA  : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP  : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST  : out std_logic;
        TX_AXI_TVALID : out std_logic;
        TX_AXI_TREADY : in  std_logic;

        -- Headers Output Interface
        HEADERS       : out extracted_headers_t;
        HEADERS_VLD   : out std_logic;
        HEADERS_READY : in  std_logic
    );
end entity;

architecture FULL of AXIS_ETH_PARSER is

    -- Number of parsing stages (Ethernet, VLAN, IPv4, TCP, UDP)
    constant NUM_STAGES        : natural := 5;
    -- Protocol sequence for each stage in the parsing pipeline
    constant PROTOCOL_SEQUENCE : integer_vector(0 to NUM_STAGES-1) := (PROTO_ETH, PROTO_VLAN, PROTO_IPV4, PROTO_TCP, PROTO_UDP);
    -- Number of bytes per AXI word
    constant WORD_BYTES        : natural := AXI_TDATA_WIDTH/8;
    -- Number of bits required for byte offset within an AXI word
    constant OFF_BYTES_W       : natural := log2(WORD_BYTES);
    -- Width of the offset field in bits (derived from PKT_MTU)
    constant OFFSET_WIDTH      : natural := log2(PKT_MTU+1);
    -- Number of bits required for word offset
    constant OFF_WORDS_W       : natural := OFFSET_WIDTH - OFF_BYTES_W;
    -- Number of bits required for packet counter
    constant PACKET_CNT_W      : natural := log2(FIFO_DEPTH);
    -- Width of FIFO data entry (extracted data + offset + valid flag)
    constant FIFO_DATA_WIDTH   : natural := get_max_extract_bytes*8 + OFFSET_WIDTH + 1;

    -- Registered indicator that current beat is not the first beat of a packet
    signal rx_axi_nonfirst_reg      : std_logic;
    -- Combinatorial indicator of the first beat of a packet
    signal rx_axi_first             : std_logic;

    -- AXI chain signals between pipeline stages (index 0 = RX input, index NUM_STAGES = TX output)
    signal axi_tdata                : slv_array_t(NUM_STAGES+1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal axi_tkeep                : slv_array_t(NUM_STAGES+1 downto 0)(WORD_BYTES-1 downto 0);
    signal axi_tlast                : std_logic_vector(NUM_STAGES+1 downto 0);
    signal axi_tvalid               : std_logic_vector(NUM_STAGES+1 downto 0);
    signal axi_tready               : std_logic_vector(NUM_STAGES+1 downto 0);

    -- Protocol chain signals - protocol identification passed between stages
    signal stage_in_protocol        : slv_array_t(NUM_STAGES downto 0)(PROTOCOL_WIDTH-1 downto 0);
    signal stage_in_offset          : slv_array_t(NUM_STAGES downto 0)(OFFSET_WIDTH-1 downto 0);
    signal stage_in_vld             : std_logic_vector(NUM_STAGES downto 0);
    signal stage_out_protocol       : slv_array_t(NUM_STAGES downto 0)(PROTOCOL_WIDTH-1 downto 0);
    signal stage_out_offset         : slv_array_t(NUM_STAGES downto 0)(OFFSET_WIDTH-1 downto 0);
    signal stage_out_vld            : std_logic_vector(NUM_STAGES downto 0);

    -- Extracted header data from each parser stage
    signal stage_extracted_data     : slv_array_t(NUM_STAGES-1 downto 0)(get_max_extract_bytes*8-1 downto 0);
    signal stage_extracted_data_vld : std_logic_vector(NUM_STAGES-1 downto 0);
    signal stage_extracted_data_ok  : std_logic_vector(NUM_STAGES-1 downto 0);
    signal stage_extracted_offset   : slv_array_t(NUM_STAGES-1 downto 0)(OFFSET_WIDTH-1 downto 0);

    -- FIFO signals for storing extracted headers
    signal fifo_wr_data             : slv_array_t(NUM_STAGES-1 downto 0)(FIFO_DATA_WIDTH-1 downto 0);
    signal fifo_rd_data             : slv_array_t(NUM_STAGES-1 downto 0)(FIFO_DATA_WIDTH-1 downto 0);
    signal fifo_wr_en               : std_logic_vector(NUM_STAGES-1 downto 0);
    signal fifo_rd_en               : std_logic_vector(NUM_STAGES-1 downto 0);
    signal fifo_empty               : std_logic_vector(NUM_STAGES-1 downto 0);
    signal fifo_full                : std_logic_vector(NUM_STAGES-1 downto 0);
    signal fifo_data                : slv_array_t(NUM_STAGES-1 downto 0)(get_max_extract_bytes*8-1 downto 0);
    signal fifo_offset              : slv_array_t(NUM_STAGES-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal fifo_ok                  : std_logic_vector(NUM_STAGES-1 downto 0);

    -- Control signals for header output flow control
    signal all_fifo_ready           : std_logic;
    signal headers_accepted         : std_logic;
    signal packets_in_flight        : unsigned(PACKET_CNT_W-1 downto 0);
    signal backpressure             : std_logic;
    signal headers_from_fifos       : extracted_headers_t;

    -- Debug counters (synthesis disabled)
    signal dbg_rx_pkt_cnt           : unsigned(63 downto 0);
    signal dbg_hdr_cnt              : unsigned(63 downto 0);

begin

    -- Initialize first parser stage with Ethernet protocol and zero offset
    stage_in_protocol(0) <= std_logic_vector(to_unsigned(PROTOCOL_SEQUENCE(0), PROTOCOL_WIDTH));
    stage_in_offset(0)   <= (others => '0');
    stage_in_vld(0)      <= '1';

    -- Connect RX AXI-Stream to first pipeline stage with backpressure control
    axi_tdata(0)  <= RX_AXI_TDATA;
    axi_tkeep(0)  <= RX_AXI_TKEEP;
    axi_tlast(0)  <= RX_AXI_TLAST;
    axi_tvalid(0) <= RX_AXI_TVALID and not backpressure;
    RX_AXI_TREADY <= axi_tready(0) and not backpressure;

    -- Connect last pipeline stage to TX AXI-Stream
    TX_AXI_TDATA           <=  axi_tdata(NUM_STAGES);
    TX_AXI_TKEEP           <=  axi_tkeep(NUM_STAGES);
    TX_AXI_TLAST           <=  axi_tlast(NUM_STAGES);
    TX_AXI_TVALID          <=  axi_tvalid(NUM_STAGES);
    axi_tready(NUM_STAGES) <= TX_AXI_TREADY;

    -- Generate parser pipeline stages with associated FIFOs
    gen_stages : for i in 0 to NUM_STAGES-1 generate
        constant CURRENT_PROTO : natural := PROTOCOL_SEQUENCE(i);
    begin
        -- Parser unit extracts header data for the current protocol stage
        stage_i : entity work.AXIS_ETH_PARSER_UNIT
        generic map (
            AXI_TDATA_WIDTH      => AXI_TDATA_WIDTH,
            EXTRACT_DATA_WIDTH   => get_max_extract_bytes * 8,
            PROTOCOL             => CURRENT_PROTO,
            PKT_MTU              => PKT_MTU,
            DEVICE               => DEVICE
        )
        port map (
            CLK                   => CLK,
            RESET                 => RESET,
            RX_AXI_TDATA          => axi_tdata(i),
            RX_AXI_TKEEP          => axi_tkeep(i),
            RX_AXI_TLAST          => axi_tlast(i),
            RX_AXI_TVALID         => axi_tvalid(i),
            RX_AXI_TREADY         => axi_tready(i),
            TX_AXI_TDATA          => axi_tdata(i+1),
            TX_AXI_TKEEP          => axi_tkeep(i+1),
            TX_AXI_TLAST          => axi_tlast(i+1),
            TX_AXI_TVALID         => axi_tvalid(i+1),
            TX_AXI_TREADY         => axi_tready(i+1),
            IN_PROTOCOL           => stage_in_protocol(i),
            IN_OFFSET             => stage_in_offset(i),
            IN_VLD                => stage_in_vld(i),
            NEXT_PROTOCOL         => stage_out_protocol(i),
            NEXT_OFFSET           => stage_out_offset(i),
            NEXT_VLD              => stage_out_vld(i),
            EXTRACTED_DATA        => stage_extracted_data(i),
            EXTRACTED_DATA_VLD    => stage_extracted_data_vld(i),
            EXTRACTED_DATA_OFFSET => stage_extracted_offset(i),
            EXTRACTED_DATA_OK     => stage_extracted_data_ok(i)
        );

        -- Connect stage outputs to next stage inputs in the parsing pipeline
        stage_in_protocol(i+1) <= stage_out_protocol(i);
        stage_in_offset(i+1)   <= stage_out_offset(i);
        stage_in_vld(i+1)      <= stage_out_vld(i);

        -- Write extracted header data to FIFO with offset and valid flag
        fifo_wr_en(i)   <= stage_extracted_data_vld(i);
        fifo_wr_data(i) <= stage_extracted_data(i) &
                           stage_extracted_offset(i) &
                           stage_extracted_data_ok(i);

        -- FIFO stores extracted headers for asynchronous readout
        fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH => FIFO_DATA_WIDTH,
            ITEMS      => FIFO_DEPTH,
            DEVICE     => DEVICE
        )
        port map (
            CLK    => CLK,
            RESET  => RESET,
            DI     => fifo_wr_data(i),
            DO     => fifo_rd_data(i),
            WR     => fifo_wr_en(i),
            RD     => fifo_rd_en(i),
            EMPTY  => fifo_empty(i),
            FULL   => fifo_full(i),
            AFULL  => open,
            STATUS => open,
            AEMPTY => open
        );

        -- Extract data, offset and valid flag from FIFO output word
        fifo_data(i)   <= fifo_rd_data(i)(FIFO_DATA_WIDTH-1 downto OFFSET_WIDTH+1);
        fifo_offset(i) <= fifo_rd_data(i)(OFFSET_WIDTH downto 1);
        fifo_ok(i)     <= fifo_rd_data(i)(0);

        -- Assertion detects attempts to write to a full FIFO (indicates design error)
        assert_fifo_not_full : process (CLK)
        begin
            if rising_edge(CLK) then
                assert not (fifo_wr_en(i) = '1' and fifo_full(i) = '1')
                    report "FIFO " & integer'image(i) & " overflow - writing to full FIFO"
                    severity error;
            end if;
        end process;
    end generate;

    -- Generate read enable for all FIFOs when headers can be accepted
    all_fifo_ready   <= '1' when (fifo_empty = (fifo_empty'range => '0')) else '0';
    headers_accepted <= all_fifo_ready and HEADERS_READY;

    gen_fifo_read : for i in 0 to NUM_STAGES-1 generate
        fifo_rd_en(i) <= headers_accepted;
    end generate;

    -- Assemble header fields from FIFO data into extracted_headers_t record
    process (fifo_data, fifo_offset, fifo_ok)
        variable hdrs : extracted_headers_t;
    begin
        hdrs := init_extracted_headers;
        for i in 0 to NUM_STAGES-1 loop
            if (i < PROTOCOL_SEQUENCE'length) then
                case PROTOCOL_SEQUENCE(i) is
                    when PROTO_ETH =>
                        hdrs.eth.dst_mac   := fifo_data(i)(8*(0+1)-1 downto 8*0) &
                                              fifo_data(i)(8*(1+1)-1 downto 8*1) &
                                              fifo_data(i)(8*(2+1)-1 downto 8*2) &
                                              fifo_data(i)(8*(3+1)-1 downto 8*3) &
                                              fifo_data(i)(8*(4+1)-1 downto 8*4) &
                                              fifo_data(i)(8*(5+1)-1 downto 8*5);
                        hdrs.eth.src_mac   := fifo_data(i)(8*(6+1)-1 downto 8*6) &
                                              fifo_data(i)(8*(7+1)-1 downto 8*7) &
                                              fifo_data(i)(8*(8+1)-1 downto 8*8) &
                                              fifo_data(i)(8*(9+1)-1 downto 8*9) &
                                              fifo_data(i)(8*(10+1)-1 downto 8*10) &
                                              fifo_data(i)(8*(11+1)-1 downto 8*11);
                        hdrs.eth.ethertype := fifo_data(i)(8*(12+1)-1 downto 8*12) &
                                              fifo_data(i)(8*(13+1)-1 downto 8*13);
                        hdrs.eth_vld       := fifo_ok(i);
                        hdrs.eth_offset    := resize(unsigned(fifo_offset(i)), MAX_OFFSET_WIDTH);
                    when PROTO_VLAN =>
                        hdrs.vlan.tci       := fifo_data(i)(8*(0+1)-1 downto 8*0) &
                                               fifo_data(i)(8*(1+1)-1 downto 8*1);
                        hdrs.vlan.ethertype := fifo_data(i)(8*(2+1)-1 downto 8*2) &
                                               fifo_data(i)(8*(3+1)-1 downto 8*3);
                        hdrs.vlan_vld       := fifo_ok(i);
                        hdrs.vlan_offset    := resize(unsigned(fifo_offset(i)), MAX_OFFSET_WIDTH);
                    when PROTO_IPV4 =>
                        hdrs.ipv4.version         := fifo_data(i)(8*(0+1)-1 downto 8*0+4);
                        hdrs.ipv4.ihl             := fifo_data(i)(8*0+3 downto 8*0);
                        hdrs.ipv4.tos             := fifo_data(i)(8*(1+1)-1 downto 8*1);
                        hdrs.ipv4.total_length    := fifo_data(i)(8*(2+1)-1 downto 8*2) &
                                                     fifo_data(i)(8*(3+1)-1 downto 8*3);
                        hdrs.ipv4.identification  := fifo_data(i)(8*(4+1)-1 downto 8*4) &
                                                     fifo_data(i)(8*(5+1)-1 downto 8*5);
                        hdrs.ipv4.flags           := fifo_data(i)(8*(6+1)-1 downto 8*6+5);
                        hdrs.ipv4.fragment_offset := fifo_data(i)(8*(7+1)-4 downto 8*7) &
                                                     fifo_data(i)(8*(6+1)-1 downto 8*6);
                        hdrs.ipv4.ttl             := fifo_data(i)(8*(8+1)-1 downto 8*8);
                        hdrs.ipv4.protocol        := fifo_data(i)(8*(9+1)-1 downto 8*9);
                        hdrs.ipv4.header_checksum := fifo_data(i)(8*(10+1)-1 downto 8*10) &
                                                     fifo_data(i)(8*(11+1)-1 downto 8*11);
                        hdrs.ipv4.src_ip          := fifo_data(i)(8*(12+1)-1 downto 8*12) &
                                                     fifo_data(i)(8*(13+1)-1 downto 8*13) &
                                                     fifo_data(i)(8*(14+1)-1 downto 8*14) &
                                                     fifo_data(i)(8*(15+1)-1 downto 8*15);
                        hdrs.ipv4.dst_ip          := fifo_data(i)(8*(16+1)-1 downto 8*16) &
                                                     fifo_data(i)(8*(17+1)-1 downto 8*17) &
                                                     fifo_data(i)(8*(18+1)-1 downto 8*18) &
                                                     fifo_data(i)(8*(19+1)-1 downto 8*19);
                        hdrs.ipv4_vld             := fifo_ok(i);
                        hdrs.ipv4_offset          := resize(unsigned(fifo_offset(i)), MAX_OFFSET_WIDTH);
                    when PROTO_TCP =>
                        hdrs.tcp.src_port    := fifo_data(i)(8*(0+1)-1 downto 8*0) &
                                                fifo_data(i)(8*(1+1)-1 downto 8*1);
                        hdrs.tcp.dst_port    := fifo_data(i)(8*(2+1)-1 downto 8*2) &
                                                fifo_data(i)(8*(3+1)-1 downto 8*3);
                        hdrs.tcp.seq_num     := fifo_data(i)(8*(4+1)-1 downto 8*4) &
                                                fifo_data(i)(8*(5+1)-1 downto 8*5) &
                                                fifo_data(i)(8*(6+1)-1 downto 8*6) &
                                                fifo_data(i)(8*(7+1)-1 downto 8*7);
                        hdrs.tcp.ack_num     := fifo_data(i)(8*(8+1)-1 downto 8*8) &
                                                fifo_data(i)(8*(9+1)-1 downto 8*9) &
                                                fifo_data(i)(8*(10+1)-1 downto 8*10) &
                                                fifo_data(i)(8*(11+1)-1 downto 8*11);
                        hdrs.tcp.data_offset := fifo_data(i)(8*(12+1)-1 downto 8*12+4);
                        hdrs.tcp.reserved    := fifo_data(i)(8*12+3 downto 8*12+1);
                        hdrs.tcp.flags       := fifo_data(i)(8*12+7) &
                                                fifo_data(i)(8*(13+1)-1 downto 8*13);
                        hdrs.tcp.window      := fifo_data(i)(8*(14+1)-1 downto 8*14) &
                                                fifo_data(i)(8*(15+1)-1 downto 8*15);
                        hdrs.tcp.checksum    := fifo_data(i)(8*(16+1)-1 downto 8*16) &
                                                fifo_data(i)(8*(17+1)-1 downto 8*17);
                        hdrs.tcp.urgent_ptr  := fifo_data(i)(8*(18+1)-1 downto 8*18) &
                                                fifo_data(i)(8*(19+1)-1 downto 8*19);
                        hdrs.tcp_vld         := fifo_ok(i);
                        hdrs.tcp_offset      := resize(unsigned(fifo_offset(i)), MAX_OFFSET_WIDTH);
                    when PROTO_UDP =>
                        hdrs.udp.src_port := fifo_data(i)(8*(0+1)-1 downto 8*0) &
                                             fifo_data(i)(8*(1+1)-1 downto 8*1);
                        hdrs.udp.dst_port := fifo_data(i)(8*(2+1)-1 downto 8*2) &
                                             fifo_data(i)(8*(3+1)-1 downto 8*3);
                        hdrs.udp.length   := fifo_data(i)(8*(4+1)-1 downto 8*4) &
                                             fifo_data(i)(8*(5+1)-1 downto 8*5);
                        hdrs.udp.checksum := fifo_data(i)(8*(6+1)-1 downto 8*6) &
                                             fifo_data(i)(8*(7+1)-1 downto 8*7);
                        hdrs.udp_vld      := fifo_ok(i);
                        hdrs.udp_offset   := resize(unsigned(fifo_offset(i)), MAX_OFFSET_WIDTH);
                    when others => null;
                end case;
            end if;
        end loop;
        headers_from_fifos <= hdrs;
    end process;

    -- Headers valid when all FIFOs contain data
    HEADERS_VLD <= all_fifo_ready;

    -- Detect first beat of each packet for packet counter
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((RESET = '1') or (RX_AXI_TLAST = '1' and RX_AXI_TVALID = '1' and RX_AXI_TREADY = '1')) then
                rx_axi_nonfirst_reg <= '0';
            elsif (RX_AXI_TVALID = '1' and RX_AXI_TREADY = '1') then
                rx_axi_nonfirst_reg <= '1';
            end if;
        end if;
    end process;

    rx_axi_first <= RX_AXI_TVALID and RX_AXI_TREADY and not rx_axi_nonfirst_reg;

    -- Track number of packets currently being processed (in flight)
    -- Counter increments on first beat of new packet, decrements when headers are accepted
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                packets_in_flight <= (others => '0');
            elsif (rx_axi_first = '1' and headers_accepted = '0') then
                packets_in_flight <= packets_in_flight + 1;
            elsif (rx_axi_first = '0' and headers_accepted = '1') then
                packets_in_flight <= packets_in_flight - 1;
            end if;
        end if;
    end process;

    -- Generate backpressure when packet counter approaches FIFO capacity
    -- Reserve 2 entries to account for pipeline latency
    backpressure <= '1' when packets_in_flight >= FIFO_DEPTH - 2 else '0';

    -- Output assembled headers
    HEADERS <= headers_from_fifos;

    -- Debug counters for packet and header statistics (synthesis disabled)
    -- pragma synthesis_off
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rx_pkt_cnt <= (others => '0');
            elsif (rx_axi_first = '1') then
                dbg_rx_pkt_cnt <= dbg_rx_pkt_cnt + 1;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_hdr_cnt <= (others => '0');
            elsif (HEADERS_VLD = '1' and HEADERS_READY = '1') then
                dbg_hdr_cnt <= dbg_hdr_cnt + 1;
            end if;
        end if;
    end process;
    -- pragma synthesis_on

end architecture;
