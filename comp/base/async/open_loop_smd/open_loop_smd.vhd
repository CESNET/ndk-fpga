-- open_loop_smd.vhd: Grey code CDC synchronizer.
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;

    -- README:
    -- This component is cross domain crossing synchronizer only for sequential
    -- Grey code. It is usually used for synchronization pointers in ASFIFOs.

entity ASYNC_OPEN_LOOP_SMD is
    Generic (
        -- Data width of grey code data signal in bits
        DATA_WIDTH : natural := 8;
        -- Use asynchronous reset in flop-flops
        ASYNC_RST  : boolean := False
    );
    Port (
        -- Clock domain A (source)
        ACLK     : in  std_logic;
        ARST     : in  std_logic;
        ADATAIN  : in  std_logic_vector(DATA_WIDTH-1 downto 0);

        -- Clock domain B (target)
        BCLK     : in  std_logic;
        BRST     : in  std_logic;
        BDATAOUT : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end ASYNC_OPEN_LOOP_SMD;

architecture FULL of ASYNC_OPEN_LOOP_SMD is

    -- Signal declarations
    signal input_reg : std_logic_vector(DATA_WIDTH-1 downto 0) := (others=>'0');
    signal sync1_reg : std_logic_vector(DATA_WIDTH-1 downto 0) := (others=>'0');
    signal sync2_reg : std_logic_vector(DATA_WIDTH-1 downto 0) := (others=>'0');
    signal sync3_reg : std_logic_vector(DATA_WIDTH-1 downto 0) := (others=>'0');

    signal arst_async : std_logic := '0';
    signal brst_async : std_logic := '0';
    signal arst_sync  : std_logic := '0';
    signal brst_sync  : std_logic := '0';

    -- Xilinx attributes
    attribute shreg_extract                : string;
    attribute shreg_extract of sync1_reg   : signal is "no";
    attribute shreg_extract of sync2_reg   : signal is "no";
    attribute shreg_extract of sync3_reg   : signal is "no";
    attribute async_reg                    : string;
    attribute async_reg of sync1_reg       : signal is "true";
    attribute async_reg of sync2_reg       : signal is "true";
    attribute async_reg of sync3_reg       : signal is "true";

    -- Intel attributes
    attribute ALTERA_ATTRIBUTE              : string;
    attribute ALTERA_ATTRIBUTE of sync1_reg : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON; -name SYNCHRONIZER_IDENTIFICATION FORCED";
    attribute ALTERA_ATTRIBUTE of sync2_reg : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";
    attribute ALTERA_ATTRIBUTE of sync3_reg : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";

begin

    reset_g: if ASYNC_RST generate
        arst_async <= ARST;
        brst_async <= BRST;
        arst_sync  <= '0';
        brst_sync  <= '0';
    else generate
        arst_async <= '0';
        brst_async <= '0';
        arst_sync  <= ARST;
        brst_sync  <= BRST;
    end generate;

    -- input register of clock domain A
    process (ACLK, arst_async)
    begin
        if (arst_async = '1') then
            input_reg <= (others=>'0');
        elsif (rising_edge(ACLK)) then
            if (arst_sync = '1') then
                input_reg <= (others=>'0');
            else
                input_reg <= ADATAIN;
            end if;
        end if;
    end process;

    -- three synchronization registers of clock domain B
    process (BCLK, brst_async)
    begin
        if (brst_async = '1') then
            sync1_reg <= (others=>'0');
            sync2_reg <= (others=>'0');
            sync3_reg <= (others=>'0');
        elsif (rising_edge(BCLK)) then
            if (brst_sync = '1') then
                sync1_reg <= (others=>'0');
                sync2_reg <= (others=>'0');
                sync3_reg <= (others=>'0');
            else
                sync1_reg <= input_reg;
                sync2_reg <= sync1_reg;
                sync3_reg <= sync2_reg;
            end if;
        end if;
    end process;

    BDATAOUT <= sync3_reg;

end architecture;
