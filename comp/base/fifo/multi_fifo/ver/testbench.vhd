-- testbench.vhd: Testbench of universal FIFO with multiple channels memory
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

    constant DATA_WIDTH      : natural := 4;
    constant ITEMS           : natural := 8;
    constant CHANNELS        : natural := 4;
    constant CLK_PERIOD      : time := 10 ns;
    constant K_W             : natural := 70;
    constant K_R             : natural := 50;
    constant VER_LENGTH      : natural := 400;
    constant VER_LENGTH_ENHC : natural := VER_LENGTH + ITEMS*CHANNELS+2;

    signal clk               : std_logic;
    signal rst               : std_logic;

    signal rx_data           : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rx_ch             : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal rx_wr             : std_logic;
    signal rx_full           : std_logic;
    signal set_read          : std_logic := '0';

    signal tx_data           : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal tx_rd             : std_logic;
    signal tx_ch             : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal tx_empty          : std_logic;

    signal clr               : std_logic_vector(CHANNELS-1 downto 0) := (others => '0');
    signal clr_reg           : std_logic_vector(CHANNELS-1 downto 0) := (others => '0');
    signal asyn_clr          : std_logic_vector(CHANNELS-1 downto 0) := (others => '0');

    signal rx_data_reg       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rx_ch_reg         : integer := 0;
    signal rx_wr_reg         : std_logic;
    signal rx_full_reg       : std_logic;

    signal tx_empty_reg      : std_logic;
    signal tx_rd_reg         : std_logic;
    signal tx_data_reg       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal tx_ch_reg         : integer := 0;

    shared variable seed1    : positive := 4;
    shared variable seed2    : positive := 4;
    shared variable X        : integer;
    shared variable tmp_data : std_logic_vector(DATA_WIDTH-1 downto 0);

    shared variable fifo : slv_fifo_array_t(CHANNELS-1 downto 0)
                          (fifo (ITEMS*2-1 downto 0)(DATA_WIDTH-1 downto 0)) := (others =>
                          (fifo     => (others => (others => 'U')),
                           fill     => 0,
                           full     => '0',
                           empty    => '1',
                           fill_max => 0,
                           fill_sum => 0,
                           fill_num => 0));

begin

    uut : entity work.MULTI_FIFO
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        ITEMS      => ITEMS,
        CHANNELS   => CHANNELS
    )
    port map(
        CLK      => clk,
        RESET    => rst,

        RX_DATA  => rx_data,
        RX_CH    => rx_ch,
        RX_WR    => rx_wr,
        RX_FULL  => rx_full,

        TX_DATA  => tx_data,
        TX_CH    => tx_ch,
        TX_RD    => tx_rd,
        TX_EMPTY => tx_empty,

        CLR      => asyn_clr
    );

    -- generate clk
    clock_p : process
    begin
        for i in (VER_LENGTH_ENHC+4) downto 0 loop
            clk <= '1';
            wait for CLK_PERIOD/2;
            clk <= '0';
            wait for CLK_PERIOD/2;
        end loop;
        wait;
    end process;

--  Clear FIFO at the end of the verification
    fifo_emptying_p : process
    begin
        wait for VER_LENGTH*CLK_PERIOD;
            set_read <= '1';
        wait for  (ITEMS*CHANNELS+4)*CLK_PERIOD;
        report "All items from fifo were successfully read";
        report "Verification finished successfully!";
        stop;
    end process;

    -- generate rst
    reset_p : process
    begin
        rst <= '1';
        wait for 3*CLK_PERIOD + 1 ns;
        rst <= '0';
        wait;
    end process;

--  Write data to verification FIFO and compare them with actual data in Multi FIFO
    fifo_put_p : process(clk)
    begin
        if (rising_edge(clk)) then
            if (rx_wr_reg = '1' and rx_full_reg = '0') then
                slv_fifo_put(fifo(rx_ch_reg), rx_data_reg);
            end if;
            if (tx_rd_reg = '1' and tx_empty_reg = '0') then
                slv_fifo_pop(fifo(tx_ch_reg), tmp_data);
                if (tmp_data /= tx_data_reg) then
                    report "expected data " & integer'image(to_integer(unsigned(tmp_data))) & " received data " & integer'image(to_integer(unsigned(tx_data_reg))) severity failure;
                end if;
            end if;
        end if;
    end process;

--  Generate signals for verification and write them to Multi FIFO memory
    fifo_write_p : process(clk)
    begin
        if (rising_edge(clk)) then
            rx_ch <= random_vector(log2(CHANNELS), seed1);
            randint(seed1, seed2, 0, 99, X);
            if (X < K_W) then
                rx_wr   <= '1';
            else
                rx_wr   <= '0';
            end if;
            rx_data     <= random_vector(DATA_WIDTH, seed1);
            rx_wr_reg   <= rx_wr and not rst;
            rx_full_reg <= rx_full;
            rx_data_reg <= rx_data;
            rx_ch_reg   <= to_integer(unsigned(rx_ch));
            tx_ch_reg   <= to_integer(unsigned(tx_ch));
            if (rst = '1') then
                for i in CHANNELS-1 downto 0 loop
                    slv_fifo_new(fifo(i));
                end loop;
            end if;
            if (set_read = '1') then
                rx_wr   <= '0';
            end if;
        end if;
    end process;

--  Generate read and channel signal for verification
    fifo_read_p : process(clk)
    begin
        if (rising_edge(clk)) then
            tx_ch <= random_vector(log2(CHANNELS), seed1);
            randint(seed1, seed2, 0, 99, X);
            if (X < K_R) then
                tx_rd <= '1';
            else
                tx_rd <= '0';
            end if;
            tx_data_reg  <= tx_data;
            tx_rd_reg    <= tx_rd;
            tx_empty_reg <= tx_empty;
            if (clr_reg(to_integer(unsigned(tx_ch))) = '1') then
                tx_empty_reg <= '1';
            end if;
            if(set_read = '1') then
                tx_ch <= std_logic_vector(unsigned(tx_ch)+1);
                tx_rd <= '1';
            end if;
        end if;
    end process;

-- Generate clear signal
   asyn_clear_p : process(all)
   begin
       asyn_clr <= clr;
       if (rx_wr_reg = '1') then
           asyn_clr(rx_ch_reg) <= '0';
       end if;
       if (tx_rd_reg = '1') then
           asyn_clr(tx_ch_reg) <= '0';
       end if;
   end process;

   reg_clr_p : process(clk)
   begin
       if (rising_edge(clk)) then
           clr     <= random_vector(CHANNELS, seed1);
           clr_reg <= asyn_clr;
       end if;
   end process;

-- Clear verification FIFO when clear is set
   fifo_clr_p : process(clk)
   begin
       if (rising_edge(clk)) then
           for i in CHANNELS-1 downto 0 loop
               if(clr_reg(i) = '1') then
                   slv_fifo_new(fifo(i));
               end if;
           end loop;
       end if;
   end process;

end architecture behavioral;
