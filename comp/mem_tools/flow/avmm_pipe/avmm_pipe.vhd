-- avmm_pipe.vhd: Avalon-MM Bus pipeline
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity AVMM_PIPE is
    generic (
        -- =========================================================================
        -- Avalon-MM parameters
        -- =========================================================================

        -- Data width of the AVMM_WRITEDATA and AVMM_READDATA signals
        DATA_WIDTH     : natural := 512;
        -- Width of the AVMM_ADDRESS signal
        ADDR_WIDTH     : natural := 26;
        -- Width of the AVMM_BURSTCOUNT signal
        BURST_WIDTH    : natural := 8;

        -- =============================
        -- Others
        -- =============================

        -- Wires only (to disable the pipe easily), affects both directions
        FAKE_PIPE      : boolean := false;

        -- "SHREG" or "REG"
        PIPE_TYPE      : string  := "REG";
        DEVICE         : string  := "AGILEX"
    );
    port (
        -- =============================
        -- Clock and Reset
        -- =============================

        CLK                   : in  std_logic;
        RESET                 : in  std_logic;

        -- =============================================
        -- Avalon-MM slave interface
        -- =============================================

        RX_AVMM_READY         : out std_logic;
        RX_AVMM_READ          : in  std_logic;
        RX_AVMM_WRITE         : in  std_logic;
        RX_AVMM_ADDRESS       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        RX_AVMM_BURSTCOUNT    : in  std_logic_vector(BURST_WIDTH-1 downto 0);
        RX_AVMM_WRITEDATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_AVMM_READDATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_AVMM_READDATAVALID : out std_logic;

        -- =============================================
        -- Avalon-MM master interface
        -- =============================================

        TX_AVMM_READY         : in  std_logic;
        TX_AVMM_READ          : out std_logic;
        TX_AVMM_WRITE         : out std_logic;
        TX_AVMM_ADDRESS       : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        TX_AVMM_BURSTCOUNT    : out std_logic_vector(BURST_WIDTH-1 downto 0);
        TX_AVMM_WRITEDATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_AVMM_READDATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_AVMM_READDATAVALID : in  std_logic
    );
end entity;



architecture ARCH of AVMM_PIPE is
    constant FLAGS_WIDTH       : natural := 2;

    constant PIPE_WIDTH        : natural := DATA_WIDTH + ADDR_WIDTH + BURST_WIDTH + FLAGS_WIDTH;

    constant PIPE_WRITE        : natural := 0;
    constant PIPE_READ         : natural := 1;
    subtype  PIPE_BURST        is natural range FLAGS_WIDTH + BURST_WIDTH - 1                           downto FLAGS_WIDTH;
    subtype  PIPE_ADDR         is natural range FLAGS_WIDTH + BURST_WIDTH + ADDR_WIDTH - 1              downto FLAGS_WIDTH + BURST_WIDTH;
    subtype  PIPE_DATA         is natural range FLAGS_WIDTH + BURST_WIDTH + ADDR_WIDTH + DATA_WIDTH - 1 downto FLAGS_WIDTH + BURST_WIDTH + ADDR_WIDTH;

    signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
    signal pipe_in_src_rdy     : std_logic;
    signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);
    signal pipe_out_src_rdy    : std_logic;

    signal readdata_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal readdatavalid_reg   : std_logic;

begin

    -- =========================================================================
    -- COMMAND PATH (master -> slave)
    -- =========================================================================

    pipe_in_data(PIPE_WRITE) <= RX_AVMM_WRITE;
    pipe_in_data(PIPE_READ)  <= RX_AVMM_READ;
    pipe_in_data(PIPE_BURST) <= RX_AVMM_BURSTCOUNT;
    pipe_in_data(PIPE_ADDR)  <= RX_AVMM_ADDRESS;
    pipe_in_data(PIPE_DATA)  <= RX_AVMM_WRITEDATA;

    pipe_in_src_rdy <= RX_AVMM_READ or RX_AVMM_WRITE;

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
        IN_SRC_RDY   => pipe_in_src_rdy,
        IN_DST_RDY   => RX_AVMM_READY,
        OUT_DATA     => pipe_out_data,
        OUT_SRC_RDY  => pipe_out_src_rdy,
        OUT_DST_RDY  => TX_AVMM_READY
    );

    -- READ/WRITE must be masked by the pipe output validity
    TX_AVMM_WRITE      <= pipe_out_data(PIPE_WRITE) and pipe_out_src_rdy;
    TX_AVMM_READ       <= pipe_out_data(PIPE_READ)  and pipe_out_src_rdy;
    TX_AVMM_BURSTCOUNT <= pipe_out_data(PIPE_BURST);
    TX_AVMM_ADDRESS    <= pipe_out_data(PIPE_ADDR);
    TX_AVMM_WRITEDATA  <= pipe_out_data(PIPE_DATA);

    -- =========================================================================
    -- READ RESPONSE PATH (slave -> master)
    -- =========================================================================
    -- There is no flow control on the read response path, the signals are
    -- therefore registered only.

    real_resp_pipe_g : if not FAKE_PIPE generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                readdata_reg <= TX_AVMM_READDATA;

                if (RESET = '1') then
                    readdatavalid_reg <= '0';
                else
                    readdatavalid_reg <= TX_AVMM_READDATAVALID;
                end if;
            end if;
        end process;

        RX_AVMM_READDATA      <= readdata_reg;
        RX_AVMM_READDATAVALID <= readdatavalid_reg;
    end generate;

    fake_resp_pipe_g : if FAKE_PIPE generate
        RX_AVMM_READDATA      <= TX_AVMM_READDATA;
        RX_AVMM_READDATAVALID <= TX_AVMM_READDATAVALID;
    end generate;

end architecture;
