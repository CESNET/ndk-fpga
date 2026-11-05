-- axis_slr_crossing.vhd: AXI-Stream pipeline for a path between two super logic regions
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

-- The AXIS_SLR_CROSSING component registers an AXI-Stream bus on a path between two
-- super logic regions (SLRs) of an FPGA. All signals including TREADY have registers
-- on both sides of the path. The component uses SLR_CROSSING.
-- RX_AXIS_TREADY is low two clock cycles after a cycle with TX_AXIS_TVALID high and
-- TX_AXIS_TREADY low. Words that the component accepts in these two cycles wait in a
-- shift register. RX_AXIS_TVALID must be low in the first clock cycle after RESET.
-- With FAKE_CROSSING, all signals are only wires.
--
entity AXIS_SLR_CROSSING is
    generic (
        -- Width of TDATA in bits
        TDATA_WIDTH   : natural := 512;
        -- Width of TUSER in bits
        TUSER_WIDTH   : natural := 16;
        -- Adds a register to the TX interface
        USE_OUTREG    : boolean := true;
        -- True: the component contains only wires, for devices without SLRs
        FAKE_CROSSING : boolean := false;
        -- Target device family
        DEVICE        : string  := "ULTRASCALE"
    );
    port (
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        RX_AXIS_TDATA  : in  std_logic_vector(TDATA_WIDTH-1 downto 0);
        RX_AXIS_TUSER  : in  std_logic_vector(TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXIS_TKEEP  : in  std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        RX_AXIS_TLAST  : in  std_logic;
        RX_AXIS_TVALID : in  std_logic;
        RX_AXIS_TREADY : out std_logic;

        TX_AXIS_TDATA  : out std_logic_vector(TDATA_WIDTH-1 downto 0);
        TX_AXIS_TUSER  : out std_logic_vector(TUSER_WIDTH-1 downto 0);
        TX_AXIS_TKEEP  : out std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        TX_AXIS_TLAST  : out std_logic;
        TX_AXIS_TVALID : out std_logic;
        TX_AXIS_TREADY : in  std_logic
    );
end entity;

architecture FULL of AXIS_SLR_CROSSING is

    constant CROSSING_WIDTH : natural := TDATA_WIDTH + TUSER_WIDTH + TDATA_WIDTH/8 + 1;

    signal crossing_in  : std_logic_vector(CROSSING_WIDTH-1 downto 0);
    signal crossing_out : std_logic_vector(CROSSING_WIDTH-1 downto 0);

begin

    crossing_in <= RX_AXIS_TDATA & RX_AXIS_TUSER & RX_AXIS_TKEEP & RX_AXIS_TLAST;

    slr_crossing_i : entity work.SLR_CROSSING
    generic map (
        DATA_WIDTH    => CROSSING_WIDTH,
        USE_OUTREG    => USE_OUTREG,
        FAKE_CROSSING => FAKE_CROSSING,
        DEVICE        => DEVICE
    )
    port map (
        CLK         => CLK,

        IN_RESET    => RESET,
        IN_DATA     => crossing_in,
        IN_SRC_RDY  => RX_AXIS_TVALID,
        IN_DST_RDY  => RX_AXIS_TREADY,

        OUT_RESET   => RESET,
        OUT_DATA    => crossing_out,
        OUT_SRC_RDY => TX_AXIS_TVALID,
        OUT_DST_RDY => TX_AXIS_TREADY
    );

    TX_AXIS_TLAST <= crossing_out(0);
    TX_AXIS_TKEEP <= crossing_out(TDATA_WIDTH/8 downto 1);
    TX_AXIS_TUSER <= crossing_out(TDATA_WIDTH/8+TUSER_WIDTH downto TDATA_WIDTH/8+1);
    TX_AXIS_TDATA <= crossing_out(CROSSING_WIDTH-1 downto TDATA_WIDTH/8+TUSER_WIDTH+1);

end architecture;
