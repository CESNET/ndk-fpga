-- axis_eth_parser_tb.vhd: Test wrapper of AXIS_ETH_PARSER_GEN and AXIS_ETH_PARSER
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

package axis_eth_parser_tb_pkg is

    function count_items (s : string) return natural;
    function str_to_protocols (s : string) return proto_array_t;
    -- Bytes in network order (first byte in the MSBs) in the layout of HDR_DATA (first byte in bits 7:0)
    function be_to_data (be : std_logic_vector; width : natural) return std_logic_vector;

end package;

package body axis_eth_parser_tb_pkg is

    function count_items (s : string) return natural is
        variable cnt : natural := 1;
    begin
        for i in s'range loop
            if (s(i) = '-') then
                cnt := cnt + 1;
            end if;
        end loop;
        return cnt;
    end function;

    function item_to_proto (s : string) return natural is
    begin
        if (s = "eth") then
            return PROTO_ETH;
        elsif (s = "vlan") then
            return PROTO_VLAN;
        elsif (s = "ipv4") then
            return PROTO_IPV4;
        elsif (s = "tcp") then
            return PROTO_TCP;
        elsif (s = "udp") then
            return PROTO_UDP;
        elsif (s = "ipv6") then
            return PROTO_IPV6;
        elsif (s = "ipv6ext") then
            return PROTO_IPV6EXT;
        elsif (s = "mpls") then
            return PROTO_MPLS;
        end if;
        report "AXIS_ETH_PARSER_TB: Unknown protocol '" & s & "' in PROTOCOLS_STR."
            severity failure;
        return PROTO_NONE;
    end function;

    function str_to_protocols (s : string) return proto_array_t is
        variable r     : proto_array_t(0 to count_items(s)-1);
        variable idx   : natural := 0;
        variable start : natural := s'low;
    begin
        for i in s'range loop
            if (s(i) = '-') then
                r(idx) := item_to_proto(s(start to i-1));
                idx    := idx + 1;
                start  := i + 1;
            end if;
        end loop;
        r(idx) := item_to_proto(s(start to s'high));
        return r;
    end function;

    function be_to_data (be : std_logic_vector; width : natural) return std_logic_vector is
        constant BYTES : natural := be'length/8;
        alias    b     : std_logic_vector(be'length-1 downto 0) is be;
        variable r     : std_logic_vector(width-1 downto 0) := (others => '0');
    begin
        for i in 0 to BYTES-1 loop
            r(i*8+7 downto i*8) := b((BYTES-i)*8-1 downto (BYTES-i-1)*8);
        end loop;
        return r;
    end function;

end package body;

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.axis_eth_parser_types.all;
use work.axis_eth_parser_tb_pkg.all;

-- DUT_ENTITY selects the tested entity: "AXIS_ETH_PARSER_GEN" or "AXIS_ETH_PARSER".
-- The protocol list is a string of lowercase protocol names separated by '-',
-- for example "eth-vlan-ipv4-tcp-udp". AXIS_ETH_PARSER requires this list.
-- The HEADERS record of AXIS_ETH_PARSER is converted back to header bytes,
-- so both entities have the same HDR_* outputs. The HDR_* arrays are serialized,
-- item i is in bits (i+1)*W-1 downto i*W. CFG_PROTOCOLS and CFG_PKT_MTU are
-- constant outputs, the test reads the configuration from them.
-- STAGE_REG_MASK bit i is bit i of the STAGE_REG generic of AXIS_ETH_PARSER_GEN.
--
entity AXIS_ETH_PARSER_TB is
    generic (
        DUT_ENTITY      : string  := "AXIS_ETH_PARSER_GEN";
        AXI_TDATA_WIDTH : natural := 512;
        PROTOCOLS_STR   : string  := "eth-vlan-vlan-mpls-mpls-ipv4-ipv6-ipv6ext-ipv6ext-tcp-udp";
        STAGE_REG_AUTO  : boolean := true;
        STAGE_REG_MASK  : natural := 0;
        PKT_MTU         : natural := 2**14;
        FIFO_DEPTH      : natural := 64;
        DEVICE          : string  := "AGILEX"
    );
    port (
        CLK           : in  std_logic;
        RESET         : in  std_logic;

        RX_AXI_TDATA  : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP  : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST  : in  std_logic;
        RX_AXI_TVALID : in  std_logic;
        RX_AXI_TREADY : out std_logic;

        TX_AXI_TDATA  : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP  : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST  : out std_logic;
        TX_AXI_TVALID : out std_logic;
        TX_AXI_TREADY : in  std_logic;

        HDR_DATA      : out std_logic_vector(count_items(PROTOCOLS_STR)*get_max_extract_bytes(str_to_protocols(PROTOCOLS_STR))*8-1 downto 0);
        HDR_OFFSET    : out std_logic_vector(count_items(PROTOCOLS_STR)*log2(PKT_MTU+1)-1 downto 0);
        HDR_FOUND     : out std_logic_vector(count_items(PROTOCOLS_STR)-1 downto 0);
        HDR_VLD       : out std_logic;
        HDR_READY     : in  std_logic;

        CFG_PROTOCOLS : out std_logic_vector(count_items(PROTOCOLS_STR)*8-1 downto 0);
        CFG_PKT_MTU   : out std_logic_vector(31 downto 0)
    );
end entity;

architecture FULL of AXIS_ETH_PARSER_TB is

    constant PROTOCOLS    : proto_array_t := str_to_protocols(PROTOCOLS_STR);
    constant DATA_WIDTH   : natural       := get_max_extract_bytes(PROTOCOLS)*8;
    constant OFFSET_WIDTH : natural       := log2(PKT_MTU+1);
    constant STAGE_REG    : std_logic_vector(MAX_STAGES-1 downto 0) := std_logic_vector(to_unsigned(STAGE_REG_MASK, MAX_STAGES));

    signal hdr_data_arr   : slv_array_t(PROTOCOLS'length-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal hdr_offset_arr : slv_array_t(PROTOCOLS'length-1 downto 0)(OFFSET_WIDTH-1 downto 0);

begin

    gen_g : if DUT_ENTITY = "AXIS_ETH_PARSER_GEN" generate
        dut_i : entity work.AXIS_ETH_PARSER_GEN
        generic map (
            AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
            PROTOCOLS       => PROTOCOLS,
            STAGE_REG       => STAGE_REG,
            STAGE_REG_AUTO  => STAGE_REG_AUTO,
            PKT_MTU         => PKT_MTU,
            FIFO_DEPTH      => FIFO_DEPTH,
            DEVICE          => DEVICE
        )
        port map (
            CLK           => CLK,
            RESET         => RESET,

            RX_AXI_TDATA  => RX_AXI_TDATA,
            RX_AXI_TKEEP  => RX_AXI_TKEEP,
            RX_AXI_TLAST  => RX_AXI_TLAST,
            RX_AXI_TVALID => RX_AXI_TVALID,
            RX_AXI_TREADY => RX_AXI_TREADY,

            TX_AXI_TDATA  => TX_AXI_TDATA,
            TX_AXI_TKEEP  => TX_AXI_TKEEP,
            TX_AXI_TLAST  => TX_AXI_TLAST,
            TX_AXI_TVALID => TX_AXI_TVALID,
            TX_AXI_TREADY => TX_AXI_TREADY,

            HDR_DATA      => hdr_data_arr,
            HDR_OFFSET    => hdr_offset_arr,
            HDR_FOUND     => HDR_FOUND,
            HDR_VLD       => HDR_VLD,
            HDR_READY     => HDR_READY
        );
    end generate;

    wrapper_g : if DUT_ENTITY = "AXIS_ETH_PARSER" generate
        signal headers : extracted_headers_t;
    begin
        assert (PROTOCOLS_STR = "eth-vlan-ipv4-tcp-udp")
            report "AXIS_ETH_PARSER_TB: Use PROTOCOLS_STR eth-vlan-ipv4-tcp-udp to test AXIS_ETH_PARSER."
            severity failure;

        dut_i : entity work.AXIS_ETH_PARSER
        generic map (
            AXI_TDATA_WIDTH => AXI_TDATA_WIDTH,
            PKT_MTU         => PKT_MTU,
            FIFO_DEPTH      => FIFO_DEPTH,
            DEVICE          => DEVICE
        )
        port map (
            CLK           => CLK,
            RESET         => RESET,

            RX_AXI_TDATA  => RX_AXI_TDATA,
            RX_AXI_TKEEP  => RX_AXI_TKEEP,
            RX_AXI_TLAST  => RX_AXI_TLAST,
            RX_AXI_TVALID => RX_AXI_TVALID,
            RX_AXI_TREADY => RX_AXI_TREADY,

            TX_AXI_TDATA  => TX_AXI_TDATA,
            TX_AXI_TKEEP  => TX_AXI_TKEEP,
            TX_AXI_TLAST  => TX_AXI_TLAST,
            TX_AXI_TVALID => TX_AXI_TVALID,
            TX_AXI_TREADY => TX_AXI_TREADY,

            HEADERS       => headers,
            HEADERS_VLD   => HDR_VLD,
            HEADERS_READY => HDR_READY
        );

        hdr_data_arr(0) <= be_to_data(headers.eth.dst_mac & headers.eth.src_mac & headers.eth.ethertype, DATA_WIDTH);
        hdr_data_arr(1) <= be_to_data(headers.vlan.tci & headers.vlan.ethertype, DATA_WIDTH);
        hdr_data_arr(2) <= be_to_data(headers.ipv4.version & headers.ipv4.ihl & headers.ipv4.tos &
                                      headers.ipv4.total_length & headers.ipv4.identification &
                                      headers.ipv4.flags & headers.ipv4.fragment_offset &
                                      headers.ipv4.ttl & headers.ipv4.protocol & headers.ipv4.header_checksum &
                                      headers.ipv4.src_ip & headers.ipv4.dst_ip, DATA_WIDTH);
        hdr_data_arr(3) <= be_to_data(headers.tcp.src_port & headers.tcp.dst_port & headers.tcp.seq_num &
                                      headers.tcp.ack_num & headers.tcp.data_offset & headers.tcp.reserved &
                                      headers.tcp.flags & headers.tcp.window & headers.tcp.checksum &
                                      headers.tcp.urgent_ptr, DATA_WIDTH);
        hdr_data_arr(4) <= be_to_data(headers.udp.src_port & headers.udp.dst_port & headers.udp.length &
                                      headers.udp.checksum, DATA_WIDTH);

        hdr_offset_arr(0) <= std_logic_vector(headers.eth_offset(OFFSET_WIDTH-1 downto 0));
        hdr_offset_arr(1) <= std_logic_vector(headers.vlan_offset(OFFSET_WIDTH-1 downto 0));
        hdr_offset_arr(2) <= std_logic_vector(headers.ipv4_offset(OFFSET_WIDTH-1 downto 0));
        hdr_offset_arr(3) <= std_logic_vector(headers.tcp_offset(OFFSET_WIDTH-1 downto 0));
        hdr_offset_arr(4) <= std_logic_vector(headers.udp_offset(OFFSET_WIDTH-1 downto 0));

        HDR_FOUND <= headers.udp_vld & headers.tcp_vld & headers.ipv4_vld & headers.vlan_vld & headers.eth_vld;
    end generate;

    HDR_DATA   <= slv_array_ser(hdr_data_arr);
    HDR_OFFSET <= slv_array_ser(hdr_offset_arr);

    cfg_g : for i in 0 to PROTOCOLS'length-1 generate
        CFG_PROTOCOLS((i+1)*8-1 downto i*8) <= std_logic_vector(to_unsigned(PROTOCOLS(i), 8));
    end generate;

    CFG_PKT_MTU <= std_logic_vector(to_unsigned(PKT_MTU, 32));

end architecture;
