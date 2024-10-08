-- bus_capture.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity BUS_CAPTURE is
    generic(
        -- Data word width in bits.
        DATA_WIDTH : natural := 64;
        -- The number of words you can capture.
        ITEMS      : natural := 512;
        -- Select memory implementation. Options:
        -- "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32),
        -- "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32),
        -- "URAM"  - effective when ITEMS*DATA_WIDTH >= 288000
        --           and DATA_WIDTH >= 72 (URAM is only for Xilinx Ultrascale(+)),
        -- "AUTO"  - effective implementation dependent on ITEMS and DEVICE.
        RAM_TYPE   : string  := "AUTO";
        -- Enabled output registers allow better timing for a few flip-flops.
        -- When OUTPUT_REG=True then read latency is 2 cycle else 1 cycle.
        OUTPUT_REG : boolean := True;
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        -- "7SERIES", "ULTRASCALE", "STRATIX10", "ARRIA10"
        DEVICE     : string  := "ULTRASCALE"
    );
    port(
        CLK          : in  std_logic;
        RESET        : in  std_logic;

        BUS_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        BUS_VALID    : in  std_logic;
        STOP_TRIGGER : in  std_logic;

        CTL_RESET    : in  std_logic;
        CTL_STOP_DLY : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        CTL_STOP_REG : out std_logic;
        CTL_RD_SETUP : in  std_logic;
        CTL_RD_EN    : in  std_logic;
        CTL_RD_DATA  : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of BUS_CAPTURE is

    constant ADDR_WIDTH : natural := log2(ITEMS);

    signal bus_data_reg     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal bus_valid_reg    : std_logic;
    signal wr_en            : std_logic;
    signal wr_addr_cnt      : unsigned(ADDR_WIDTH-1 downto 0);
    signal rd_addr_cnt      : unsigned(ADDR_WIDTH-1 downto 0);
    signal stop_trigger_reg : std_logic;
    signal stop_delay_cnt   : unsigned(ADDR_WIDTH-1 downto 0);
    signal stop_delay_done  : std_logic;
    signal stop_reg         : std_logic;

begin

    -- =========================================================================
    --  CAPTURE LOGIC
    -- =========================================================================

    bus_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            bus_data_reg  <= BUS_DATA;
            bus_valid_reg <= BUS_VALID;
        end if;
    end process;

    wr_en <= bus_valid_reg and not stop_reg;

    wr_addr_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or CTL_RESET = '1') then
                wr_addr_cnt <= (others => '0');
            elsif (wr_en = '1') then
                wr_addr_cnt <= wr_addr_cnt + 1;
            end if;
        end if;
    end process;

    sdp_memx_i : entity work.SDP_MEMX
    generic map(
        DATA_WIDTH => DATA_WIDTH,
        ITEMS      => ITEMS,
        RAM_TYPE   => RAM_TYPE,
        DEVICE     => DEVICE,
        OUTPUT_REG => OUTPUT_REG
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,
        WR_DATA    => bus_data_reg,
        WR_ADDR    => std_logic_vector(wr_addr_cnt),
        WR_EN      => wr_en,
        RD_DATA    => CTL_RD_DATA,
        RD_ADDR    => std_logic_vector(rd_addr_cnt),
        RD_PIPE_EN => CTL_RD_EN
    );

    rd_addr_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (CTL_RD_SETUP = '1') then
                rd_addr_cnt <= wr_addr_cnt;
            elsif (CTL_RD_EN = '1') then
                rd_addr_cnt <= rd_addr_cnt + 1;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  STOP TRIGGER LOGIC
    -- =========================================================================

    stop_trigger_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or CTL_RESET = '1') then
                stop_trigger_reg <= '0';
            elsif (STOP_TRIGGER = '1') then
                stop_trigger_reg <= '1';
            end if;
        end if;
    end process;

    stop_delay_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or CTL_RESET = '1') then
                stop_delay_cnt <= (others => '0');
            elsif (stop_delay_done = '0' and stop_trigger_reg = '1') then
                stop_delay_cnt <= stop_delay_cnt + 1;
            end if;
        end if;
    end process;

    stop_delay_done <= '1' when (stop_delay_cnt = unsigned(CTL_STOP_DLY)) else '0';

    stop_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            stop_reg <= stop_delay_done;
        end if;
    end process;

    CTL_STOP_REG <= stop_reg;

end architecture;
