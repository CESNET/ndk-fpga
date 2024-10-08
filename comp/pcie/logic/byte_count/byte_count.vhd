-- byte_count.vhd: PCIE byte count calculator
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component calculates the correct number of bytes contained in the payload of the incoming
-- PCIe transaction. The size is calculated using `DW_COUNT`, `FIRST_BE` and `LAST_BE` signals
-- provided by each transaction.
entity PCIE_BYTE_COUNT is
    generic (
        -- Optional output register
        OUTPUT_REG : boolean := False
    );
    port (
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- DWord count from TLP header
        IN_DW_COUNT    : in  std_logic_vector(11-1 downto 0);
        -- First Byte Enable from TLP header
        IN_FIRST_BE    : in  std_logic_vector(4-1 downto 0);
        -- Last Byte Enable from TLP header
        IN_LAST_BE     : in  std_logic_vector(4-1 downto 0);

        -- First Invalid Bytes of TLP
        OUT_FIRST_IB   : out std_logic_vector(2-1 downto 0);
        -- Last Invalid Bytes of TLP
        OUT_LAST_IB    : out std_logic_vector(2-1 downto 0);
        -- Byte Count of TLP
        OUT_BYTE_COUNT : out std_logic_vector(13-1 downto 0)
    );
end entity;

architecture FULL of PCIE_BYTE_COUNT is

    signal tlp_first_ib       : unsigned(2-1 downto 0);
    signal tlp_last_ib        : unsigned(2-1 downto 0);
    signal tlp_byte_count_raw : unsigned(13-1 downto 0);
    signal tlp_byte_count     : unsigned(13-1 downto 0);

begin

    -- computation of invalid bytes
    process (IN_FIRST_BE, IN_LAST_BE)
    begin
        if (std_match(IN_FIRST_BE,"1--1") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(0,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"01-1") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(1,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1-10") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(1,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"0011") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"0110") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1100") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"0001") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"0010") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"0100") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1000") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"0000") AND std_match(IN_LAST_BE,"0000")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"---1") AND std_match(IN_LAST_BE,"1---")) then
            tlp_first_ib <= to_unsigned(0,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"---1") AND std_match(IN_LAST_BE,"01--")) then
            tlp_first_ib <= to_unsigned(0,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(1,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"---1") AND std_match(IN_LAST_BE,"001-")) then
            tlp_first_ib <= to_unsigned(0,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(2,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"---1") AND std_match(IN_LAST_BE,"0001")) then
            tlp_first_ib <= to_unsigned(0,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(3,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"--10") AND std_match(IN_LAST_BE,"1---")) then
            tlp_first_ib <= to_unsigned(1,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"--10") AND std_match(IN_LAST_BE,"01--")) then
            tlp_first_ib <= to_unsigned(1,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(1,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"--10") AND std_match(IN_LAST_BE,"001-")) then
            tlp_first_ib <= to_unsigned(1,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(2,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"--10") AND std_match(IN_LAST_BE,"0001")) then
            tlp_first_ib <= to_unsigned(1,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(3,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"-100") AND std_match(IN_LAST_BE,"1---")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"-100") AND std_match(IN_LAST_BE,"01--")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(1,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"-100") AND std_match(IN_LAST_BE,"001-")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(2,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"-100") AND std_match(IN_LAST_BE,"0001")) then
            tlp_first_ib <= to_unsigned(2,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(3,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1000") AND std_match(IN_LAST_BE,"1---")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1000") AND std_match(IN_LAST_BE,"01--")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(1,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1000") AND std_match(IN_LAST_BE,"001-")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(2,tlp_last_ib'length);
        elsif (std_match(IN_FIRST_BE,"1000") AND std_match(IN_LAST_BE,"0001")) then
            tlp_first_ib <= to_unsigned(3,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(3,tlp_last_ib'length);
        else
            tlp_first_ib <= to_unsigned(0,tlp_first_ib'length);
            tlp_last_ib  <= to_unsigned(0,tlp_last_ib'length);
        end if;
    end process;

    -- computation of request byte count
    tlp_byte_count_raw <= unsigned(IN_DW_COUNT) & "00";
    tlp_byte_count     <= tlp_byte_count_raw - tlp_first_ib - tlp_last_ib;

    OUT_FIRST_IB   <= std_logic_vector(tlp_first_ib);
    OUT_LAST_IB    <= std_logic_vector(tlp_last_ib);
    OUT_BYTE_COUNT <= std_logic_vector(tlp_byte_count);

    out_reg_g: if OUTPUT_REG generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                OUT_FIRST_IB   <= std_logic_vector(tlp_first_ib);
                OUT_LAST_IB    <= std_logic_vector(tlp_last_ib);
                OUT_BYTE_COUNT <= std_logic_vector(tlp_byte_count);
            end if;
        end process;
    else generate
        OUT_FIRST_IB   <= std_logic_vector(tlp_first_ib);
        OUT_LAST_IB    <= std_logic_vector(tlp_last_ib);
        OUT_BYTE_COUNT <= std_logic_vector(tlp_byte_count);
    end generate;

end architecture;
