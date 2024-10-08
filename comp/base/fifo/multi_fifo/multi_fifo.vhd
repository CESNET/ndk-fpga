-- multi_fifo.vhd: Universal FIFO with multiple channels memory
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- README:
-- This component is a universal FIFO with multiple channels.
-- The FIFO is parametrically implemented in MEMX memory.
-- Number of channels is generic.

-- ----------------------------------------------------------------------------
--                           Entity declaration
-- ----------------------------------------------------------------------------

entity MULTI_FIFO is
    generic(
        -- Data word width in bits.
        DATA_WIDTH          : natural := 64;
        -- FIFO depth, number of data words
        ITEMS               : natural := 512;
        -- Number of channels
        CHANNELS            : natural := 64

    );
    port(
        CLK      : in  std_logic;
        RESET    : in  std_logic;

        -- =======================================================================
        --  WRITE INTERFACE
        -- =======================================================================
        RX_DATA  : in std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_CH    : in std_logic_vector(log2(CHANNELS)-1 downto 0);
        -- Write enable
        RX_WR    : in std_logic;
        -- FIFO is full, react without latency
        RX_FULL  : out std_logic;

        -- =======================================================================
        --  READ INTERFACE
        -- =======================================================================
        -- When TX_RD is set TX_RD = '1', valid data are read from FIFO
        TX_DATA  : out std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_CH    : in std_logic_vector(log2(CHANNELS)-1 downto 0);
        -- Data on TX_DATA were read
        TX_RD    : in std_logic;
        -- FIFO is empty, react without latency
        TX_EMPTY : out std_logic;

        -- =======================================================================
        --  CLEAR INTERFACE
        -- =======================================================================
        -- This signal clear FIFO
        CLR      : in std_logic_vector(CHANNELS-1 downto 0)
    );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of MULTI_FIFO is

    -- Write address pointer
    signal wr_addr_ptr    : slv_array_t(CHANNELS-1 downto 0)(log2(ITEMS+1)-1 downto 0);
    signal wr_addr_ptr_en : std_logic_vector(CHANNELS-1 downto 0) := (others => '0');
    -- Read address pointer
    signal rd_addr_ptr    : slv_array_t(CHANNELS-1 downto 0)(log2(ITEMS+1)-1 downto 0);
    signal rd_addr_ptr_en : std_logic_vector(CHANNELS-1 downto 0);
    -- Full statement
    signal full_i         : std_logic_vector(CHANNELS-1 downto 0);
    -- Empty statement
    signal ptr_eq         : std_logic_vector(CHANNELS-1 downto 0);
    -- Data from memory
    signal mem_out        : std_logic_vector(DATA_WIDTH-1 downto 0);
    -- When mem_vld = '1' then data from memory are valid (FIFO is not empty)
    signal mem_vld        : std_logic_vector(CHANNELS-1 downto 0);
    -- Data in storage register
    signal data_reg       : slv_array_t(CHANNELS-1 downto 0)(DATA_WIDTH-1 downto 0);
    -- Valid signal of storage register
    signal reg_vld        : std_logic_vector(CHANNELS-1 downto 0);
    -- When data_out_vld = '1' then memory output data or register output data are valid
    signal data_out_vld   : std_logic_vector(CHANNELS-1 downto 0);
    signal read_reg       : std_logic_vector(CHANNELS-1 downto 0);
    -- Is asserted when there are valid data (FIFO is not empty) and read is requested
    signal read_internal  : std_logic_vector(CHANNELS-1 downto 0);
    -- Channels convert to integer
    signal tx_ch_int      : natural;
    signal rx_ch_int      : natural;

begin

-- ----------------------------------------------------------------------------
--                      MEMX MEMORY GENERATION
-- ----------------------------------------------------------------------------
    memx_i : entity work.SDP_MEMX
    generic map(
        DATA_WIDTH => DATA_WIDTH,
        ITEMS      => CHANNELS*ITEMS,
        OUTPUT_REG => false
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        WR_DATA    => RX_DATA,
        WR_ADDR    => RX_CH & wr_addr_ptr(rx_ch_int)(log2(ITEMS)-1 downto 0),
        WR_EN      => wr_addr_ptr_en(rx_ch_int),

        RD_DATA    => mem_out,
        RD_ADDR    => TX_CH & rd_addr_ptr(tx_ch_int)(log2(ITEMS)-1 downto 0),
        RD_PIPE_EN => '1'
    );

    tx_ch_int <= to_integer(unsigned(TX_CH));
    rx_ch_int <= to_integer(unsigned(RX_CH));

    -- Data at memory or in register are valid
    TX_EMPTY  <= not data_out_vld(tx_ch_int);
    RX_FULL   <= full_i(rx_ch_int);

    -- Set read_internal when output data are not valid or read is set
    -- This proccess calculate counter enables and data valid signal
    read_internal_gen : for i in CHANNELS-1 downto 0 generate
        read_internal(i)  <= '1' when ((TX_RD = '1' or data_out_vld(i) = '0') and (unsigned(TX_CH) = i or CHANNELS < 2) and CLR(i) = '0') else '0';
        rd_addr_ptr_en(i) <= (read_internal(i) and not ptr_eq(i));
        wr_addr_ptr_en(i) <= '1' when ((RX_WR = '1' and full_i(i) = '0') and (unsigned(RX_CH) = i or CHANNELS < 2)) else '0';
        data_out_vld(i)   <= mem_vld(i) or reg_vld(i);
    end generate ;

    --  mem_vld = '1' when data at memory are valid
    mem_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            for i in CHANNELS-1 downto 0 loop
                if(RESET = '1') then
                    mem_vld(i) <= '0';
                end if;
            mem_vld(i)     <= '1' when ((ptr_eq(i) = '0') and (unsigned(TX_CH) = i or CHANNELS < 2)) else '0';
            end loop;
        end if;
    end process;

    --  Register for read statement
    read_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            for i in CHANNELS-1 downto 0 loop
                read_reg(i) <= read_internal(i);
            end loop;
        end if;
    end process;

    -- Storage register (Is used when read in previous clock drop and in memory are valid data)
    strg_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            for i in CHANNELS-1 downto 0 loop
                if (RESET = '1' or read_internal(i) = '1' or CLR(i) = '1') then
                    reg_vld(i)  <= '0';
                elsif ((read_internal(i) /= read_reg(i)) and mem_vld(i) = '1' and read_internal(i) = '0') then
                    reg_vld(i)  <= '1';
                    data_reg(i) <= mem_out;
                end if;
            end loop;
        end if;
    end process;

    -- Input counter (Count write requests)
    wr_addr_cnt_p : process (CLK) -- Input address incrementation
    begin
        if (rising_edge(CLK)) then
            for i in CHANNELS-1 downto 0 loop
                if (RESET = '1' or CLR(i) = '1') then
                    wr_addr_ptr(i) <= (others => '0');
                elsif (wr_addr_ptr_en(i) = '1') then
                    wr_addr_ptr(i) <= std_logic_vector(unsigned(wr_addr_ptr(i)) + 1);
                end if;
            end loop;
        end if;
    end process;

    -- Output counter (count read requests)
    rd_addr_cnt_p : process (CLK) -- Output address incrementation
    begin
        if (rising_edge(CLK)) then
            for i in CHANNELS-1 downto 0 loop
                if (RESET = '1' or CLR(i) = '1') then
                    rd_addr_ptr(i) <= (others => '0');
                elsif (rd_addr_ptr_en(i) = '1') then
                    rd_addr_ptr(i) <= std_logic_vector(unsigned(rd_addr_ptr(i)) + 1);
                end if;
            end loop;
        end if;
    end process;

    -- When upper bits are not same and lower bits are same, then full statement is set to log 1
    comp_full_p : process (all)
    begin
        for i in CHANNELS-1 downto 0 loop
            full_i(i)     <= '0';
            if (wr_addr_ptr(i)(log2(ITEMS)) /= rd_addr_ptr(i)(log2(ITEMS)) and wr_addr_ptr(i)(log2(ITEMS)-1 downto 0 ) = rd_addr_ptr(i)(log2(ITEMS)-1 downto 0 )) then
                full_i(i) <= '1';
            end if;
        end loop;
    end process;

    -- When upper and lower bits are same, then empty statement is set to log 0
    comp_empty_p : process (all)
    begin
        for i in CHANNELS-1 downto 0 loop
            ptr_eq(i)     <= '1';
            if (not (wr_addr_ptr(i)(log2(ITEMS)) = rd_addr_ptr(i)(log2(ITEMS)) and wr_addr_ptr(i)(log2(ITEMS)-1 downto 0 ) = rd_addr_ptr(i)(log2(ITEMS)-1 downto 0 ))) then
                ptr_eq(i) <= '0';
            end if;
        end loop;
    end process;

    TX_DATA <= mem_out when (reg_vld(tx_ch_int) = '0') else data_reg(tx_ch_int);

end architecture;
