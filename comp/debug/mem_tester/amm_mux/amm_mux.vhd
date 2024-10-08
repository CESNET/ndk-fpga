-- mem_tester.vhd: Component for testing DDR4 memory
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity AMM_MUX is
generic (
    -- Main --
    MUX_WIDTH               : integer := 2;
    MUX_LATENCY             : integer := 0;
    SLAVE_INPUT_REG         : boolean := false;
    MASTER_OUTPUT_REG       : boolean := false;
    MASTER_INPUT_LATENCY    : integer := 0;     -- = SLAVE_OUTPUT_LATENCY

    -- Avalon bus --
    AMM_DATA_WIDTH          : integer := 512;
    AMM_ADDR_WIDTH          : integer := 26;
    AMM_BURST_COUNT_WIDTH   : integer := 7
);
port(
    -- Main signals --
    AMM_CLK                     : in  std_logic;
    AMM_RST                     : in  std_logic;
    MUX_SEL                     : in  std_logic_vector(log2(MUX_WIDTH) - 1 downto 0);

    -- Master Avalon interface --
    MASTER_AMM_READY            : in  std_logic;
    MASTER_AMM_READ             : out std_logic;
    MASTER_AMM_WRITE            : out std_logic;
    MASTER_AMM_READ_DATA_VALID  : in  std_logic;
    MASTER_AMM_ADDRESS          : out std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    MASTER_AMM_READ_DATA        : in  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    MASTER_AMM_WRITE_DATA       : out std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    MASTER_AMM_BURST_COUNT      : out std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);

    -- Slave Avalon interfaces --
    SLAVE_AMM_READY             : out std_logic_vector(MUX_WIDTH - 1 downto 0);
    SLAVE_AMM_READ              : in  std_logic_vector(MUX_WIDTH - 1 downto 0);
    SLAVE_AMM_WRITE             : in  std_logic_vector(MUX_WIDTH - 1 downto 0);
    SLAVE_AMM_READ_DATA_VALID   : out std_logic_vector(MUX_WIDTH - 1 downto 0);
    SLAVE_AMM_ADDRESS           : in  slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_ADDR_WIDTH - 1 downto 0);
    SLAVE_AMM_READ_DATA         : out slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    SLAVE_AMM_WRITE_DATA        : in  slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    SLAVE_AMM_BURST_COUNT       : in  slv_array_t(MUX_WIDTH - 1 downto 0)(AMM_BURST_COUNT_WIDTH - 1 downto 0)
);
end entity;

architecture FULL of AMM_MUX is

    -- Constants --
    constant OUT_WIDTH  : integer
        := AMM_ADDR_WIDTH + AMM_DATA_WIDTH + AMM_BURST_COUNT_WIDTH + 2;
    constant IN_WIDTH   : integer
        := AMM_DATA_WIDTH + 1;

    -- Signals --
    signal master_out   : std_logic_vector(OUT_WIDTH - 1 downto 0);
    signal master_in    : std_logic_vector(IN_WIDTH - 1 downto 0);
    signal slave_out    : slv_array_t(MUX_WIDTH - 1 downto 0)(IN_WIDTH - 1 downto 0);
    signal slave_in     : slv_array_t(MUX_WIDTH - 1 downto 0)(OUT_WIDTH - 1 downto 0);

    signal slave_selected           : std_logic_vector(MUX_WIDTH - 1 downto 0);
    signal slave_amm_ready_intern   : std_logic;

    -- Index 0 is not original, not delayed signal
    signal master_in_delayed        : slv_array_t(MASTER_INPUT_LATENCY downto 0)(IN_WIDTH - 1 downto 0);
begin
    ----------------
    -- Components --
    ----------------

    mux_out_i : entity work.GEN_MUX_PIPED
    generic map (
        DATA_WIDTH              => OUT_WIDTH,
        MUX_WIDTH               => MUX_WIDTH,
        MUX_LATENCY             => MUX_LATENCY,
        INPUT_REG               => SLAVE_INPUT_REG,
        OUTPUT_REG              => MASTER_OUTPUT_REG
    )
    port map (
        CLK                     => AMM_CLK,
        RESET                   => AMM_RST,
        RX_SEL                  => MUX_SEL,
        -- in
        RX_DATA                 => slv_array_ser(slave_in),
        -- out
        TX_DATA                 => master_out,
        TX_DST_RDY              => MASTER_AMM_READY
    );

    ------------------------
    -- Interconnect logic --
    ------------------------

    (MASTER_AMM_READ, MASTER_AMM_WRITE,
    MASTER_AMM_ADDRESS, MASTER_AMM_WRITE_DATA,
    MASTER_AMM_BURST_COUNT) <= master_out;


    master_in(0)                                      <= MASTER_AMM_READ_DATA_VALID;
    master_in(AMM_DATA_WIDTH downto 1)                <= MASTER_AMM_READ_DATA;


    interconnect_g : for i in 0 to MUX_WIDTH - 1 generate
        slave_selected(i)   <= '1' when (std_logic_vector(to_unsigned(i, MUX_SEL'length)) = MUX_SEL) else
                               '0';
        SLAVE_AMM_READY(i)  <= MASTER_AMM_READY and slave_selected(i);

        SLAVE_AMM_READ_DATA_VALID(i)    <= slave_out(i)(0) and slave_selected(i);
        SLAVE_AMM_READ_DATA(i)          <= slave_out(i)(AMM_DATA_WIDTH downto 1);

        slave_in(i) <= SLAVE_AMM_READ(i) & SLAVE_AMM_WRITE(i) &
                    SLAVE_AMM_ADDRESS(i) & SLAVE_AMM_WRITE_DATA(i) &
                    SLAVE_AMM_BURST_COUNT(i);

        master_in_delayed(0)<= master_in;
        slave_out(i)        <= master_in_delayed(MASTER_INPUT_LATENCY);
    end generate;

    master_in_delayed_g : for i in 0 to MASTER_INPUT_LATENCY - 1 generate
        master_in_delayed_p : process(AMM_CLK)
        begin
            if (rising_edge(AMM_CLK)) then
                master_in_delayed(i + 1) <= master_in_delayed(i);
            end if;
        end process;
    end generate;

end architecture;
