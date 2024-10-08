-- mi_splitter_plus_gen_wrapper.vhd: Wrapper of mi_splitter_plus_gen where the PORTBASE is a 'downto' array
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause

-- The whole sense is to make ADDR_BASE a 'to' array for the verification because
-- Systemverilog can not transfer the PORTBASE as a 'downto' array from the
-- verification to the MI_SPLITTER_PLUS_GEN (which has ADDR_BASE as 'downto')
-- so this wrapper is the step between verification and MI_SPLITTER_PLUS_GEN
-- and converts ADDR_BASE to a 'downto' array

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.ab_init_pack.all;

entity MI_SPLITTER_PLUS_GEN_WRAPPER is
    generic(
        -- Width of MI address
        ADDR_WIDTH    : integer := 32;
        -- Width of MI data
        DATA_WIDTH    : integer := 32;
        -- Width of MI meta
        META_WIDTH    : integer := 32;
        -- Number of output ports
        PORTS         : integer := 8;
        -- Output pipeline
        PIPE_OUT      : b_array_t(PORTS-1 downto 0) := (others => true);
        -- Number of considered address bases (might be higher or equal to PORTS)
        ADDR_BASES    : integer := PORTS;
        -- Bases of address spaces (base of port0 is 0x00000000)
        ADDR_BASE     : slv_array_t(0 to ADDR_BASES-1)(ADDR_WIDTH-1 downto 0) := init_addr_base_downto(ADDR_BASES, ADDR_WIDTH);
        -- Bits of address that are needed to determine output port
        ADDR_MASK     : std_logic_vector(ADDR_WIDTH-1 downto 0) := init_addr_mask_downto(ADDR_BASE, ADDR_WIDTH);
        -- Bases to ports mapping
        -- constains target port index for each address base
        -- multiple address bases might target the same port
        PORT_MAPPING  : i_array_t(0 to ADDR_BASES-1) := init_port_mapping_downto(ADDR_BASES, PORTS);
        -- Target FPGA
        DEVICE        : string  := "STRATIX10"
    );
    port(
        -- Common interface -----------------------------------------------------
        CLK         : in std_logic;
        RESET       : in std_logic;

        -- Input MI interface ---------------------------------------------------
        RX_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0);
        RX_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        RX_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
        RX_RD       : in  std_logic;
        RX_WR       : in  std_logic;
        RX_ARDY     : out std_logic;
        RX_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_DRDY     : out std_logic;

        -- Output MI interfaces -------------------------------------------------
        TX_DWR     : out slv_array_t(PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_MWR     : out slv_array_t(PORTS-1 downto 0)(META_WIDTH-1 downto 0);
        TX_ADDR    : out slv_array_t(PORTS-1 downto 0)(ADDR_WIDTH-1 downto 0);
        TX_BE      : out slv_array_t(PORTS-1 downto 0)(DATA_WIDTH/8-1 downto 0);
        TX_RD      : out std_logic_vector(PORTS-1 downto 0);
        TX_WR      : out std_logic_vector(PORTS-1 downto 0);
        TX_ARDY    : in  std_logic_vector(PORTS-1 downto 0);
        TX_DRD     : in  slv_array_t(PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_DRDY    : in  std_logic_vector(PORTS-1 downto 0)
    );
end entity;

architecture FULL of MI_SPLITTER_PLUS_GEN_WRAPPER is

    function make_to_downto_addr_base return slv_array_t is
        variable addr_base_downto : slv_array_t(ADDR_BASES-1 downto 0)(ADDR_WIDTH-1 downto 0);
    begin
        for i in ADDR_BASES-1 downto 0 loop
            addr_base_downto(i) := ADDR_BASE(i);
        end loop;
        return addr_base_downto;
    end function;

    function make_to_downto_port_mapping return i_array_t is
        variable port_mapping_downto : i_array_t(ADDR_BASES-1 downto 0);
    begin
        for i in ADDR_BASES-1 downto 0 loop
            port_mapping_downto(i) := PORT_MAPPING(i);
        end loop;
        return port_mapping_downto;
    end function;

begin
    mi_splitter_plus_gen_i: entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH   => ADDR_WIDTH,
            DATA_WIDTH   => DATA_WIDTH,
            META_WIDTH   => META_WIDTH,
            PORTS        => PORTS,
            ADDR_MASK    => ADDR_MASK,
            ADDR_BASES   => ADDR_BASES,
            ADDR_BASE    => make_to_downto_addr_base,
            PORT_MAPPING => make_to_downto_port_mapping,
            PIPE_OUT     => PIPE_OUT,
            DEVICE       => DEVICE
        )
        port map(
            CLK       => CLK,
            RESET     => RESET,

            RX_DWR    => RX_DWR,
            RX_MWR    => RX_MWR,
            RX_ADDR   => RX_ADDR,
            RX_BE     => RX_BE,
            RX_WR     => RX_WR,
            RX_RD     => RX_RD,
            RX_ARDY   => RX_ARDY,
            RX_DRD    => RX_DRD,
            RX_DRDY   => RX_DRDY,

            TX_DWR   => TX_DWR,
            TX_MWR   => TX_MWR,
            TX_ADDR  => TX_ADDR,
            TX_BE    => TX_BE,
            TX_WR    => TX_WR,
            TX_RD    => TX_RD,
            TX_ARDY  => TX_ARDY,
            TX_DRD   => TX_DRD,
            TX_DRDY  => TX_DRDY
        );

end architecture;
