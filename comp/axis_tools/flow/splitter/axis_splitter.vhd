-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Component AXIS_SPLITTER is used to split one input AXI Stream interface into
-- N output AXI Stream interfaces. The target output stream for each transaction
-- is determined by the RX_AXIS_SEL signal, which is valid with the first word
-- of the transaction.
--
entity AXIS_SPLITTER is
generic (
    -- width of AXI-Stream data signal in bits
    TDATA_WIDTH   : natural := 512;
    -- width of AXI-Stream user signal in bits
    TUSER_WIDTH   : natural := 64;
    -- number of TX AXI-Stream interfaces
    TX_STREAMS    : natural := 32;
    -- target device: AGILEX, STRATIX10, ULTRASCALE,...
    DEVICE        : string  := "AGILEX";
    -- adds register to the output
    OUT_REG       : boolean := true
);
port (
    -- =========================================================================
    -- Clock and reset signals
    -- =========================================================================
    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- =========================================================================
    -- RX AXI-Stream interfaces (CLK)
    -- =========================================================================
    -- The signal RX_AXIS_SEL determines which output stream the transaction
    -- must be sent to. The signal is valid with the first word of the transaction.
    RX_AXIS_SEL    : in  std_logic_vector(log2(TX_STREAMS)-1 downto 0);
    RX_AXIS_TDATA  : in  std_logic_vector(TDATA_WIDTH-1 downto 0);
    RX_AXIS_TUSER  : in  std_logic_vector(TUSER_WIDTH-1 downto 0);
    RX_AXIS_TKEEP  : in  std_logic_vector(TDATA_WIDTH/8-1 downto 0);
    RX_AXIS_TLAST  : in  std_logic;
    RX_AXIS_TVALID : in  std_logic;
    RX_AXIS_TREADY : out std_logic;

    -- =========================================================================
    -- TX AXI-Stream interface (CLK)
    -- =========================================================================
    TX_AXIS_TDATA  : out slv_array_t(TX_STREAMS-1 downto 0)(TDATA_WIDTH-1 downto 0);
    TX_AXIS_TUSER  : out slv_array_t(TX_STREAMS-1 downto 0)(TUSER_WIDTH-1 downto 0);
    TX_AXIS_TKEEP  : out slv_array_t(TX_STREAMS-1 downto 0)(TDATA_WIDTH/8-1 downto 0);
    TX_AXIS_TLAST  : out std_logic_vector(TX_STREAMS-1 downto 0);
    TX_AXIS_TVALID : out std_logic_vector(TX_STREAMS-1 downto 0);
    TX_AXIS_TREADY : in  std_logic_vector(TX_STREAMS-1 downto 0)
);
end entity;

architecture FULL of AXIS_SPLITTER is
    signal data      : std_logic_vector(TDATA_WIDTH-1 downto 0);
    signal user      : std_logic_vector(TUSER_WIDTH-1 downto 0);
    signal keep      : std_logic_vector(TDATA_WIDTH/8-1 downto 0);
    signal last      : std_logic;
    signal valid     : std_logic_vector(TX_STREAMS-1 downto 0);
    signal ready     : std_logic;

begin
    -- =========================================================================
    -- Input
    -- =========================================================================
    RX_AXIS_TREADY <= ready;

    -- =========================================================================
    -- Splitter logic
    -- =========================================================================
    data  <= RX_AXIS_TDATA;
    user  <= RX_AXIS_TUSER;
    keep  <= RX_AXIS_TKEEP;
    last  <= RX_AXIS_TLAST;
    ready <= TX_AXIS_TREADY(to_integer(unsigned(RX_AXIS_SEL)));

    set_valid: process(RX_AXIS_SEL, RX_AXIS_TVALID)
    begin
        valid <= (others => '0');
        valid(to_integer(unsigned(RX_AXIS_SEL))) <= RX_AXIS_TVALID;
    end process;

    -- =========================================================================
    -- Output
    -- =========================================================================
    register_g: if OUT_REG generate
        reg_g: for g in 0 to TX_STREAMS-1 generate
            process(CLK)
            begin
                if rising_edge(CLK) then
                    if TX_AXIS_TREADY(g) = '1' then
                        TX_AXIS_TDATA(g)  <= data;
                        TX_AXIS_TUSER(g)  <= user;
                        TX_AXIS_TKEEP(g)  <= keep;
                        TX_AXIS_TLAST(g)  <= last;
                        TX_AXIS_TVALID(g) <= valid(g);
                    end if;

                    if RESET = '1' then
                        TX_AXIS_TVALID(g) <= '0';
                    end if;
                end if;
            end process;
        end generate;
    else generate
        signal_splitter_g: for g in 0 to TX_STREAMS-1 generate
            TX_AXIS_TDATA(g)  <= data;
            TX_AXIS_TUSER(g)  <= user;
            TX_AXIS_TKEEP(g)  <= keep;
            TX_AXIS_TLAST(g)  <= last;
            TX_AXIS_TVALID(g) <= valid(g);
        end generate;
    end generate;
end architecture;
