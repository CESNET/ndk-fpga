-- axi_pipe.vhd: AXI Bus pipeline
-- Copyright (C) 2024 BrnoLogic, Ltd.
-- Author(s): Radek Hajek <hajek@brnologic.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

-- Component for pipelining AXI data paths with source and destination ready signals.
-- Compatible with Xilinx and Intel FPGAs.
entity AXI_PIPE is
    generic(
        -- =========================================================================
        -- AXI STREAM parameters
        -- =========================================================================
        -- AXI stream data width
        AXI_DATA_WIDTH          : natural := 256;

        -- =============================
        -- Others
        -- =============================

        FAKE_PIPE      : boolean := false;
        USE_DST_RDY    : boolean := true;
        -- "SHREG" or "REG"
        PIPE_TYPE      : string  := "SHREG";
        DEVICE         : string  := "7SERIES"
    );
    port(
        -- =============================
        -- Clock and Reset
        -- =============================

        CLK            : in std_logic;
        RESET          : in std_logic;

        -- =============================
        -- AXI input interface
        -- =============================

        RX_AXI_TDATA     : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- =============================
        -- AXI input interface
        -- =============================

        TX_AXI_TDATA     : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
    );
end entity;



architecture arch of AXI_PIPE is

    constant TLAST_WIDTH        : integer := 1;
    constant TKEEP_WIDTH        : integer := AXI_DATA_WIDTH / 8;
    constant TDATA_WIDTH        : integer := AXI_DATA_WIDTH;
    constant PIPE_WIDTH         : integer := TLAST_WIDTH + TKEEP_WIDTH + TDATA_WIDTH;

    subtype  PIPE_TDATA         is natural range TLAST_WIDTH+TKEEP_WIDTH+TDATA_WIDTH-1 downto TLAST_WIDTH+TKEEP_WIDTH;
    subtype  PIPE_TKEEP         is natural range TLAST_WIDTH+TKEEP_WIDTH-1 downto TLAST_WIDTH;
    constant PIPE_TLAST         : natural := 0;

    signal pipe_in_data         : std_logic_vector(PIPE_WIDTH-1 downto 0);
    signal pipe_out_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);

begin

    pipe_in_data(PIPE_TLAST) <= RX_AXI_TLAST;
    pipe_in_data(PIPE_TKEEP) <= RX_AXI_TKEEP;
    pipe_in_data(PIPE_TDATA) <= RX_AXI_TDATA;

    true_pipe_gen : if USE_DST_RDY generate
        pipe_i :  entity  work.PIPE
        generic map(
            DATA_WIDTH      => PIPE_WIDTH,
            USE_OUTREG      => not FAKE_PIPE,
            FAKE_PIPE       => FAKE_PIPE,
            PIPE_TYPE       => PIPE_TYPE,
            RESET_BY_INIT   => false,
            DEVICE          => DEVICE
         )
        port map(
              CLK           => CLK,
            RESET         => RESET,
            IN_DATA       => pipe_in_data,
            IN_SRC_RDY    => RX_AXI_TVALID,
            IN_DST_RDY    => RX_AXI_TREADY,
            OUT_DATA      => pipe_out_data,
            OUT_SRC_RDY   => TX_AXI_TVALID,
            OUT_DST_RDY   => TX_AXI_TREADY,
            DEBUG_BLOCK   => '0',
            DEBUG_DROP    => '0',
            DEBUG_SRC_RDY => open,
            DEBUG_DST_RDY => open
        );
    end generate;



    -- Register only implementation
    simple_pipe_gen : if not USE_DST_RDY generate
        RX_AXI_TREADY <= '1';
        fake_gen : if FAKE_PIPE generate
            TX_AXI_TVALID <= RX_AXI_TVALID;
            pipe_out_data <= pipe_in_data;
        end generate;
        full_gen : if not FAKE_PIPE generate
            pipe_core : process(CLK)
            begin
                if CLK'event and CLK='1' then
                if RESET='1' then
                    TX_AXI_TVALID <= '0';
                else
                    TX_AXI_TVALID <= RX_AXI_TVALID;
                end if;
                pipe_out_data <= pipe_in_data;
                end if;
            end process;
        end generate;
    end generate;

    TX_AXI_TLAST <= pipe_out_data(PIPE_TLAST);
    TX_AXI_TKEEP <= pipe_out_data(PIPE_TKEEP);
    TX_AXI_TDATA <= pipe_out_data(PIPE_TDATA);
end architecture;
