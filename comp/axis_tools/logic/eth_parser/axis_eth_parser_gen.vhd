-- axis_eth_parser_gen.vhd: AXI-Stream Ethernet Header Parser with a configurable protocol set
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

-- The AXIS_ETH_PARSER_GEN component reads protocol headers from Ethernet frames.
-- The frames pass unchanged from the RX to the TX interface.
--
-- The parser is a chain of stages. PROTOCOLS sets the protocol of each stage.
-- A stage reads the header only when the previous headers announce its protocol.
-- Otherwise the stage passes the announced protocol and its offset to the next stage.
-- The order in PROTOCOLS must therefore follow the order of headers in a frame.
-- The first stage must be PROTO_ETH.
--
-- For each frame, the parser outputs one item on the HDR_* interface.
-- Item i contains the header that stage i read.
-- The package axis_eth_parser_types provides functions that decode HDR_DATA.
-- The parser reads only the first get_extract_bytes(PROTOCOLS(i)) bytes of a header.
-- A header is reported as not found when the frame ends before all bytes that the stage reads.
--
-- A register stage between two parser stages shortens the critical path and adds
-- one clock cycle of latency. STAGE_REG_AUTO and STAGE_REG select these register stages.
--
entity AXIS_ETH_PARSER_GEN is
    generic (
        -- Width of the AXI-Stream data bus in bits, a power of two (e.g., 256, 512)
        AXI_TDATA_WIDTH : natural       := 512;
        -- Protocols of the parser stages in pipeline order (see PROTO_* in axis_eth_parser_types)
        PROTOCOLS       : proto_array_t := (PROTO_ETH, PROTO_VLAN, PROTO_IPV4, PROTO_TCP, PROTO_UDP);
        -- Bit i set: a register stage after parser stage i. Bits above the number of stages are not used.
        STAGE_REG       : std_logic_vector(MAX_STAGES-1 downto 0) := (others => '0');
        -- True: get_stage_reg_auto(PROTOCOLS) selects the register stages and STAGE_REG is not used
        STAGE_REG_AUTO  : boolean       := true;
        -- Maximum packet size in bytes (determines offset field width)
        PKT_MTU         : natural       := 2**14;
        -- Depth of internal FIFOs (number of packets that can be buffered), at least 3
        FIFO_DEPTH      : natural       := 64;
        -- Target device family for FIFO implementation (e.g., "AGILEX", "ULTRASCALE")
        DEVICE          : string        := "AGILEX"
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

        -- Headers Output Interface, one item per frame
        -- Header bytes read by stage i, byte 0 of the header is in bits 7:0. Valid when HDR_FOUND(i) is set.
        HDR_DATA      : out slv_array_t(PROTOCOLS'length-1 downto 0)(get_max_extract_bytes(PROTOCOLS)*8-1 downto 0);
        -- Byte offset of the header of stage i in the frame. Valid when HDR_FOUND(i) is set.
        HDR_OFFSET    : out slv_array_t(PROTOCOLS'length-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
        -- Bit i is set when stage i found its header and the frame contains all bytes that stage i reads
        HDR_FOUND     : out std_logic_vector(PROTOCOLS'length-1 downto 0);
        HDR_VLD       : out std_logic;
        HDR_READY     : in  std_logic
    );
end entity;

architecture FULL of AXIS_ETH_PARSER_GEN is

    -- Protocol list with indexes from 0 to NUM_STAGES-1
    constant PROTOS            : proto_array_t(0 to PROTOCOLS'length-1) := PROTOCOLS;
    constant NUM_STAGES        : natural := PROTOS'length;
    constant MAX_EXTRACT_BYTES : natural := get_max_extract_bytes(PROTOS);
    constant OFFSET_WIDTH      : natural := log2(PKT_MTU+1);
    constant PACKET_CNT_W      : natural := log2(FIFO_DEPTH);
    constant META_WIDTH        : natural := OFFSET_WIDTH + PROTOCOL_WIDTH;

    function get_stage_reg return std_logic_vector is
    begin
        if (STAGE_REG_AUTO) then
            return get_stage_reg_auto(PROTOS);
        end if;
        return STAGE_REG;
    end function;

    constant STAGE_REG_EN      : std_logic_vector(MAX_STAGES-1 downto 0) := get_stage_reg;

    -- The check is in the declarative part, so it runs before the stages are elaborated
    function cfg_check return boolean is
        variable reachable : boolean;
    begin
        assert (NUM_STAGES <= MAX_STAGES)
            report "AXIS_ETH_PARSER_GEN: Use at most " & integer'image(MAX_STAGES) & " items in PROTOCOLS."
            severity failure;
        assert (2**log2(AXI_TDATA_WIDTH/8) = AXI_TDATA_WIDTH/8)
            report "AXIS_ETH_PARSER_GEN: Use AXI_TDATA_WIDTH that is 8 times a power of two."
            severity failure;
        assert (FIFO_DEPTH >= 3)
            report "AXIS_ETH_PARSER_GEN: Use FIFO_DEPTH of 3 or more."
            severity failure;
        assert (PROTOS(0) = PROTO_ETH)
            report "AXIS_ETH_PARSER_GEN: Use PROTO_ETH as the first item of PROTOCOLS."
            severity failure;
        for i in 0 to NUM_STAGES-1 loop
            assert (PROTOS(i) < 2**PROTOCOL_WIDTH)
                report "AXIS_ETH_PARSER_GEN: Increase PROTOCOL_WIDTH, so it can store PROTOCOLS(" & integer'image(i) & ")."
                severity failure;
        end loop;
        for i in 1 to NUM_STAGES-1 loop
            reachable := false;
            for j in 0 to i-1 loop
                reachable := reachable or proto_can_follow(PROTOS(j), PROTOS(i));
            end loop;
            assert reachable
                report "AXIS_ETH_PARSER_GEN: Put a protocol that can contain PROTOCOLS(" & integer'image(i) & ") before it."
                severity failure;
        end loop;
        return true;
    end function;

    constant CFG_CHECKED : boolean := cfg_check;

    signal rx_axi_nonfirst_reg : std_logic;
    signal rx_axi_first        : std_logic;

    -- AXI chain signals between pipeline stages (index 0 = RX input, index NUM_STAGES = TX output)
    signal axi_tdata           : slv_array_t(NUM_STAGES downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal axi_tkeep           : slv_array_t(NUM_STAGES downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal axi_tlast           : std_logic_vector(NUM_STAGES downto 0);
    signal axi_tvalid          : std_logic_vector(NUM_STAGES downto 0);
    signal axi_tready          : std_logic_vector(NUM_STAGES downto 0);

    -- Protocol chain signals, index i is the input of stage i
    signal chain_proto         : slv_array_t(NUM_STAGES downto 0)(PROTOCOL_WIDTH-1 downto 0);
    signal chain_offset        : slv_array_t(NUM_STAGES downto 0)(OFFSET_WIDTH-1 downto 0);
    signal chain_vld           : std_logic_vector(NUM_STAGES downto 0);

    -- AXI and protocol chain signals at the output of stage i, before the optional register stage
    signal stage_tdata         : slv_array_t(NUM_STAGES-1 downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal stage_tkeep         : slv_array_t(NUM_STAGES-1 downto 0)(AXI_TDATA_WIDTH/8-1 downto 0);
    signal stage_tlast         : std_logic_vector(NUM_STAGES-1 downto 0);
    signal stage_tvalid        : std_logic_vector(NUM_STAGES-1 downto 0);
    signal stage_next_proto    : slv_array_t(NUM_STAGES-1 downto 0)(PROTOCOL_WIDTH-1 downto 0);
    signal stage_next_offset   : slv_array_t(NUM_STAGES-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal stage_next_vld      : std_logic_vector(NUM_STAGES-1 downto 0);

    -- Header output of each stage
    signal stage_data          : slv_array_t(NUM_STAGES-1 downto 0)(MAX_EXTRACT_BYTES*8-1 downto 0);
    signal stage_offset        : slv_array_t(NUM_STAGES-1 downto 0)(OFFSET_WIDTH-1 downto 0);
    signal stage_found         : std_logic_vector(NUM_STAGES-1 downto 0);

    -- FIFO status for header output flow control
    signal fifo_empty          : std_logic_vector(NUM_STAGES-1 downto 0);
    signal fifo_full           : std_logic_vector(NUM_STAGES-1 downto 0);
    signal all_fifo_ready      : std_logic;
    signal headers_accepted    : std_logic;
    signal pkt_cnt             : unsigned(PACKET_CNT_W-1 downto 0);
    signal backpressure        : std_logic;

begin

    -- The first stage always starts with Ethernet at offset 0
    chain_proto(0)  <= std_logic_vector(to_unsigned(PROTO_ETH, PROTOCOL_WIDTH));
    chain_offset(0) <= (others => '0');
    chain_vld(0)    <= '1';

    -- Connect RX AXI-Stream to the first stage. RX_AXI_TREADY is low while backpressure is set.
    axi_tdata(0)  <= RX_AXI_TDATA;
    axi_tkeep(0)  <= RX_AXI_TKEEP;
    axi_tlast(0)  <= RX_AXI_TLAST;
    axi_tvalid(0) <= RX_AXI_TVALID and not backpressure;
    RX_AXI_TREADY <= axi_tready(0) and not backpressure;

    -- Connect last pipeline stage to TX AXI-Stream
    TX_AXI_TDATA           <= axi_tdata(NUM_STAGES);
    TX_AXI_TKEEP           <= axi_tkeep(NUM_STAGES);
    TX_AXI_TLAST           <= axi_tlast(NUM_STAGES);
    TX_AXI_TVALID          <= axi_tvalid(NUM_STAGES);
    axi_tready(NUM_STAGES) <= TX_AXI_TREADY;

    stages_g : for i in 0 to NUM_STAGES-1 generate
        constant STAGE_PROTO : natural := PROTOS(i);
        constant STAGE_BYTES : natural := get_extract_bytes(STAGE_PROTO);
        constant FIFO_WIDTH  : natural := STAGE_BYTES*8 + OFFSET_WIDTH + 1;

        signal in_enable     : std_logic;
        signal ext_meta      : std_logic_vector(META_WIDTH-1 downto 0);
        signal ext_data      : std_logic_vector(STAGE_BYTES*8-1 downto 0);
        signal ext_data_max  : std_logic_vector(MAX_EXTRACT_BYTES*8-1 downto 0);
        signal ext_valid     : std_logic;
        signal ext_complete  : std_logic;
        signal ext_proto     : std_logic_vector(PROTOCOL_WIDTH-1 downto 0);
        signal ext_offset    : std_logic_vector(OFFSET_WIDTH-1 downto 0);
        signal ext_match     : std_logic;
        signal fifo_wr_data  : std_logic_vector(FIFO_WIDTH-1 downto 0);
        signal fifo_rd_data  : std_logic_vector(FIFO_WIDTH-1 downto 0);
    begin

        in_enable <= '1' when (to_integer(unsigned(chain_proto(i))) = STAGE_PROTO) else '0';

        sniffer_i : entity work.AXIS_ETH_PARSER_SNIFFER
        generic map (
            AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
            EXTRACT_BYTES   => STAGE_BYTES,
            PKT_MTU         => PKT_MTU,
            META_WIDTH      => META_WIDTH,
            DEVICE          => DEVICE
        )
        port map (
            CLK                => CLK,
            RESET              => RESET,

            RX_AXI_TDATA       => axi_tdata(i),
            RX_AXI_TKEEP       => axi_tkeep(i),
            RX_AXI_TLAST       => axi_tlast(i),
            RX_AXI_TVALID      => axi_tvalid(i),
            RX_AXI_TREADY      => axi_tready(i),

            TX_AXI_TDATA       => stage_tdata(i),
            TX_AXI_TKEEP       => stage_tkeep(i),
            TX_AXI_TLAST       => stage_tlast(i),
            TX_AXI_TVALID      => stage_tvalid(i),
            TX_AXI_TREADY      => axi_tready(i+1),

            START_META         => chain_offset(i) & chain_proto(i),
            START_OFFSET       => chain_offset(i),
            START_ENABLE       => in_enable,
            START_VALID        => chain_vld(i),

            EXTRACTED_META     => ext_meta,
            EXTRACTED_DATA     => ext_data,
            EXTRACTED_VALID    => ext_valid,
            EXTRACTED_COMPLETE => ext_complete
        );

        ext_proto  <= ext_meta(PROTOCOL_WIDTH-1 downto 0);
        ext_offset <= ext_meta(META_WIDTH-1 downto PROTOCOL_WIDTH);
        ext_match  <= '1' when (to_integer(unsigned(ext_proto)) = STAGE_PROTO) else '0';

        -- get_next_proto and get_hdr_len contain code for every protocol.
        -- All of this code must index inside the data.
        ext_data_max <= std_logic_vector(resize(unsigned(ext_data), MAX_EXTRACT_BYTES*8));

        -- A stage that does not read the announced protocol passes it to the next stage unchanged
        process (all)
            variable next_proto  : natural;
            variable next_offset : natural;
        begin
            stage_next_proto(i)  <= ext_proto;
            stage_next_offset(i) <= ext_offset;
            if (ext_match = '1') then
                next_proto  := get_next_proto(STAGE_PROTO, ext_data_max);
                next_offset := to_integer(unsigned(ext_offset)) + get_hdr_len(STAGE_PROTO, ext_data_max);
                -- The next protocol is unknown when the packet ends inside the header
                if (ext_complete = '0') then
                    next_proto := PROTO_NONE;
                end if;
                -- A header after PKT_MTU cannot be in the packet
                if (next_offset > PKT_MTU) then
                    next_proto  := PROTO_NONE;
                    next_offset := to_integer(unsigned(ext_offset));
                end if;
                stage_next_proto(i)  <= std_logic_vector(to_unsigned(next_proto, PROTOCOL_WIDTH));
                stage_next_offset(i) <= std_logic_vector(to_unsigned(next_offset, OFFSET_WIDTH));
            end if;
        end process;

        stage_next_vld(i) <= ext_valid;

        reg_g : if STAGE_REG_EN(i) = '1' generate
            signal next_vld_wait : std_logic;
        begin
            -- The AXI register moves together with the registers in the sniffers
            process (CLK)
            begin
                if rising_edge(CLK) then
                    if (RESET = '1') then
                        axi_tvalid(i+1) <= '0';
                    elsif (axi_tready(i+1) = '1') then
                        axi_tdata(i+1)  <= stage_tdata(i);
                        axi_tkeep(i+1)  <= stage_tkeep(i);
                        axi_tlast(i+1)  <= stage_tlast(i);
                        axi_tvalid(i+1) <= stage_tvalid(i);
                    end if;
                end if;
            end process;

            -- The valid pulse must reach the next stage together with the AXI word that it belongs to.
            -- When the AXI register does not load, the pulse waits in next_vld_wait.
            process (CLK)
            begin
                if rising_edge(CLK) then
                    if (stage_next_vld(i) = '1') then
                        chain_proto(i+1)  <= stage_next_proto(i);
                        chain_offset(i+1) <= stage_next_offset(i);
                    end if;

                    chain_vld(i+1) <= '0';
                    if (axi_tready(i+1) = '1') then
                        chain_vld(i+1) <= stage_next_vld(i) or next_vld_wait;
                        next_vld_wait  <= '0';
                    elsif (stage_next_vld(i) = '1') then
                        next_vld_wait  <= '1';
                    end if;

                    if (RESET = '1') then
                        chain_vld(i+1) <= '0';
                        next_vld_wait  <= '0';
                    end if;
                end if;
            end process;
        else generate
            axi_tdata(i+1)    <= stage_tdata(i);
            axi_tkeep(i+1)    <= stage_tkeep(i);
            axi_tlast(i+1)    <= stage_tlast(i);
            axi_tvalid(i+1)   <= stage_tvalid(i);
            chain_proto(i+1)  <= stage_next_proto(i);
            chain_offset(i+1) <= stage_next_offset(i);
            chain_vld(i+1)    <= stage_next_vld(i);
        end generate;

        -- The FIFO keeps the header of each packet until all stages have one
        fifo_wr_data <= ext_data & ext_offset & (ext_match and ext_complete);

        fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH => FIFO_WIDTH,
            ITEMS      => FIFO_DEPTH,
            DEVICE     => DEVICE
        )
        port map (
            CLK    => CLK,
            RESET  => RESET,
            DI     => fifo_wr_data,
            WR     => ext_valid,
            FULL   => fifo_full(i),
            AFULL  => open,
            STATUS => open,
            DO     => fifo_rd_data,
            RD     => headers_accepted,
            EMPTY  => fifo_empty(i),
            AEMPTY => open
        );

        stage_data(i)   <= std_logic_vector(resize(unsigned(fifo_rd_data(FIFO_WIDTH-1 downto OFFSET_WIDTH+1)), MAX_EXTRACT_BYTES*8));
        stage_offset(i) <= fifo_rd_data(OFFSET_WIDTH downto 1);
        stage_found(i)  <= fifo_rd_data(0);

        -- pragma synthesis_off
        process (CLK)
        begin
            if rising_edge(CLK) then
                assert not (ext_valid = '1' and fifo_full(i) = '1')
                    report "FIFO " & integer'image(i) & " overflow - writing to full FIFO"
                    severity error;
            end if;
        end process;
        -- pragma synthesis_on
    end generate;

    -- Headers are valid when all FIFOs contain data
    all_fifo_ready   <= '1' when (fifo_empty = (fifo_empty'range => '0')) else '0';
    headers_accepted <= all_fifo_ready and HDR_READY;

    HDR_DATA   <= stage_data;
    HDR_OFFSET <= stage_offset;
    HDR_FOUND  <= stage_found;
    HDR_VLD    <= all_fifo_ready;

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

    -- Number of packets that entered the parser and whose headers were not accepted yet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                pkt_cnt <= (others => '0');
            elsif (rx_axi_first = '1' and headers_accepted = '0') then
                pkt_cnt <= pkt_cnt + 1;
            elsif (rx_axi_first = '0' and headers_accepted = '1') then
                pkt_cnt <= pkt_cnt - 1;
            end if;
        end if;
    end process;

    -- Stop the RX interface when pkt_cnt approaches FIFO_DEPTH
    -- Two FIFO items are reserved because of the pipeline latency
    backpressure <= '1' when pkt_cnt >= FIFO_DEPTH - 2 else '0';

end architecture;
