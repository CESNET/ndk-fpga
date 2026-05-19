-- axis_pipe.vhd: AXI-Stream Bus pipeline
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Radek Hajek     <hajek@dyna-nic.com>, 2024
--            Vlastimil Kosar <kosar@dyna-nic.com>, 2025
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

-- Component for pipelining AXI-Stream data paths with source and destination ready signals.
entity AXIS_PIPE is
    generic (
        -- =========================================================================
        -- AXI STREAM parameters
        -- =========================================================================

        -- Data width
        TDATA_WIDTH     : natural := 512;
        -- User metadata width
        TUSER_WIDTH     : natural := 0;

        -- =============================
        -- Others
        -- =============================

        FAKE_PIPE      : boolean := false;

        -- "SHREG" or "REG"
        PIPE_TYPE      : string  := "SHREG";
        DEVICE         : string  := "VERSAL"
    );
    port (
        -- =============================
        -- Clock and Reset
        -- =============================

        CLK            : in std_logic;
        RESET          : in std_logic;

        -- =============================
        -- AXI-Stream input interface
        -- =============================

        RX_AXIS_TDATA  : in  std_logic_vector(TDATA_WIDTH-1 downto 0);
        RX_AXIS_TUSER  : in  std_logic_vector(TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXIS_TKEEP  : in  std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        RX_AXIS_TLAST  : in  std_logic;
        RX_AXIS_TVALID : in  std_logic;
        RX_AXIS_TREADY : out std_logic;

        -- =============================
        -- AXI-Stream output interface
        -- =============================

        TX_AXIS_TDATA  : out std_logic_vector(TDATA_WIDTH-1 downto 0);
        TX_AXIS_TUSER  : out std_logic_vector(TUSER_WIDTH-1 downto 0) := (others => '0');
        TX_AXIS_TKEEP  : out std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        TX_AXIS_TLAST  : out std_logic;
        TX_AXIS_TVALID : out std_logic;
        TX_AXIS_TREADY : in  std_logic
    );
end entity;



architecture ARCH of AXIS_PIPE is

    constant TLAST_WIDTH       : integer := 1;
    constant ITEM_WIDTH        : integer := 8;
    constant TKEEP_WIDTH       : integer := TDATA_WIDTH / ITEM_WIDTH;

    constant PIPE_WIDTH        : integer := TDATA_WIDTH + TUSER_WIDTH + TKEEP_WIDTH + TLAST_WIDTH;

    subtype  PIPE_DATA         is natural range TLAST_WIDTH + TKEEP_WIDTH + TUSER_WIDTH + TDATA_WIDTH-1 downto TLAST_WIDTH + TKEEP_WIDTH + TUSER_WIDTH;
    subtype  PIPE_USER         is natural range TLAST_WIDTH + TKEEP_WIDTH + TUSER_WIDTH - 1             downto TLAST_WIDTH + TKEEP_WIDTH;
    subtype  PIPE_KEEP         is natural range TLAST_WIDTH + TKEEP_WIDTH - 1                           downto TLAST_WIDTH;
    constant PIPE_LAST         : natural := 0;


    signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
    signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);

begin
    pipe_in_data(PIPE_LAST) <= RX_AXIS_TLAST;
    pipe_in_data(PIPE_KEEP) <= RX_AXIS_TKEEP;
    pipe_in_data(PIPE_DATA) <= RX_AXIS_TDATA;
    pipe_in_data(PIPE_USER) <= RX_AXIS_TUSER;

    -- Real pipe implementation
    pipe_core : entity work.PIPE
    generic map (
        DATA_WIDTH      => PIPE_WIDTH,
        USE_OUTREG      => not FAKE_PIPE,
        FAKE_PIPE       => FAKE_PIPE,
        PIPE_TYPE       => PIPE_TYPE,
        RESET_BY_INIT   => false,
        DEVICE          => DEVICE
    ) port map (
        CLK          => CLK,
        RESET        => RESET,
        IN_DATA      => pipe_in_data,
        IN_SRC_RDY   => RX_AXIS_TVALID,
        IN_DST_RDY   => RX_AXIS_TREADY,
        OUT_DATA     => pipe_out_data,
        OUT_SRC_RDY  => TX_AXIS_TVALID,
        OUT_DST_RDY  => TX_AXIS_TREADY
    );

    TX_AXIS_TLAST <= pipe_out_data(PIPE_LAST);
    TX_AXIS_TKEEP <= pipe_out_data(PIPE_KEEP);
    TX_AXIS_TDATA <= pipe_out_data(PIPE_DATA);
    TX_AXIS_TUSER <= pipe_out_data(PIPE_USER);
end architecture;
