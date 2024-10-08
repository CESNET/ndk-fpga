-- testbench.vhd: Testbench
-- Copyright (C) 2019 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;
use work.type_pack.all;
use work.math_pack.all;
use work.dma_bus_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

use work.test_pkg.all;

-- ----------------------------------------------------------------------------
--                                  Entity
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------

architecture full of testbench is

    constant DATA_BLOCKS : integer := DATA_WIDTH/BLOCK_WIDTH;

    -- Synchronization
    signal wclk   : std_logic;
    signal wreset : std_logic := '1';
    signal rclk   : std_logic;
    signal rreset : std_logic := '1';

    -- uut I/O

    signal wr_en       : std_logic;
    signal wr_be       : std_logic_vector(max((DATA_WIDTH/BLOCK_WIDTH),1)-1 downto 0);
    signal wr_addr     : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal wr_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rd_en       : std_logic;
    signal rd_pipe_en  : std_logic;
    signal rd_addr     : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal rd_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rd_data_vld : std_logic;

    -- tb signals and variables

    -- common tb variables

    shared variable l     : line;
    shared variable seed1 : positive := RAND_SEED+415;
    shared variable seed2 : positive := RAND_SEED+80;
    shared variable X     : integer;
    shared variable Y     : integer;

    -- tb functions and procedures

    signal model_mem           : slv_array_2d_t(ITEMS-1 downto 0)(DATA_BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0) := (others => (others => (others => 'X')));
    signal model_mem_block_vld : slv_array_t(ITEMS-1 downto 0)(DATA_BLOCKS-1 downto 0) := (others =>(others => 'X'));
    signal out_reg0_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal out_reg0_block_vld  : std_logic_vector(DATA_BLOCKS-1 downto 0);
    signal out_reg0_vld        : std_logic;
    signal out_reg1_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal out_reg1_block_vld  : std_logic_vector(DATA_BLOCKS-1 downto 0);
    signal out_reg1_vld        : std_logic;

begin

    -- -------------------------------------------------------------------------
    -- UUT
    -- -------------------------------------------------------------------------

    uut : entity work.SDP_BRAM_BE
    generic map (
        DATA_WIDTH   => DATA_WIDTH  ,
        ITEMS        => ITEMS       ,
        BLOCK_ENABLE => BLOCK_ENABLE,
        BLOCK_WIDTH  => BLOCK_WIDTH ,
        COMMON_CLOCK => (C_WCLK_PER=C_RCLK_PER),
        OUTPUT_REG   => OUTPUT_REG  ,
        DEVICE       => DEVICE
    )
    port map (
        WR_CLK      => wclk       ,
        WR_RST      => wreset     ,
        WR_EN       => wr_en      ,
        WR_BE       => wr_be      ,
        WR_ADDR     => wr_addr    ,
        WR_DATA     => wr_data    ,

        RD_CLK      => rclk       ,
        RD_RST      => rreset     ,
        RD_EN       => rd_en      ,
        RD_PIPE_EN  => rd_pipe_en ,
        RD_ADDR     => rd_addr    ,
        RD_DATA     => rd_data    ,
        RD_DATA_VLD => rd_data_vld
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    wclk_gen: process
    begin
        wclk <= '1';
        wait for C_WCLK_PER / 2;
        wclk <= '0';
        wait for C_WCLK_PER / 2;
    end process;

    rclk_gen: process
    begin
        rclk <= '1';
        wait for C_RCLK_PER / 2;
        rclk <= '0';
        wait for C_RCLK_PER / 2;
    end process;

    -- generating reset
    wrst_gen: process
    begin
        wreset <= '1';
        wait for C_WRST_TIME;
        wreset <= '0';
        wait;
    end process;

    rrst_gen: process
    begin
        rreset <= '1';
        wait for C_RRST_TIME;
        rreset <= '0';
        wait;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- test processes
    -- -------------------------------------------------------------------------

    -- WR driver
    wr_driver_gen_pr : process(wclk)
        variable wr_addr_var : integer range 0 to ITEMS-1;
    begin
        if (rising_edge(wclk)) then

            -- default values
            wr_en   <= '0';
            wr_be   <= random_vector(wr_be'length,seed1);
            randint(seed1, seed2, 0, ITEMS-1, wr_addr_var);
            wr_addr <= std_logic_vector(to_unsigned(wr_addr_var, wr_addr'length));
            wr_data <= random_vector(wr_data'length,seed1);

            randint(seed1,seed2,0,99,X);

            if (X<WR_CH) then
                wr_en   <= '1';
            end if;

            if (wreset='1') then
                wr_en   <= '0';
            end if;

        end if;
    end process;
    ----

    -- RD driver
    rd_driver_gen_pr : process(rclk)
        variable rd_addr_var : integer range 0 to ITEMS-1;
    begin
        if (rising_edge(rclk)) then

            -- default values
            rd_en   <= '0';
            randint(seed1, seed2, 0, ITEMS-1, rd_addr_var);
            rd_addr <= std_logic_vector(to_unsigned(rd_addr_var, rd_addr'length));

            randint(seed1,seed2,0,99,X);

            if (X<RD_CH) then
                rd_en   <= '1';
            end if;

            if (rreset='1') then
                rd_en   <= '0';
            end if;

        end if;
    end process;
    ----

    -- PIPE_EN driver
    pipe_en_driver_gen_pr : process(rclk)
    begin
        if (rising_edge(rclk)) then

            -- default values
            rd_pipe_en <= '0';

            randint(seed1,seed2,0,99,X);

            if (X<PIPE_EN_CH) then
                rd_pipe_en <= '1';
            end if;

            if (rreset='1') then
                rd_pipe_en <= '0';
            end if;

        end if;
    end process;
    ----

    -- model memory
    model_mem_pr : process (wclk,rclk)
    begin
        if (rising_edge(wclk)) then
            if (wr_en='1') then
                for i in 0 to DATA_BLOCKS-1 loop
                    if (BLOCK_ENABLE=false or wr_be(i)='1') then
                        model_mem(to_integer(unsigned(wr_addr)))(i) <= wr_data((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH);
                        model_mem_block_vld(to_integer(unsigned(wr_addr)))(i) <= '1';
                    end if;
                end loop;
            end if;

            if (wreset='1') then
                model_mem_block_vld <= (others => (others => '0'));
            end if;
        end if;

        if (rising_edge(rclk)) then
            if (rd_pipe_en='1') then
                out_reg0_data      <= slv_array_ser(model_mem(to_integer(unsigned(rd_addr))));
                out_reg0_vld       <= rd_en;
                out_reg0_block_vld <= model_mem_block_vld(to_integer(unsigned(rd_addr)));
                out_reg1_data      <= out_reg0_data;
                out_reg1_block_vld <= out_reg0_block_vld;
                out_reg1_vld       <= out_reg0_vld;
            end if;

            if (rreset='1') then
                out_reg0_vld <= '0';
                out_reg1_vld <= '0';
            end if;
        end if;

    end process;
    ----

    -- RD monitor
    rd_monitor_pr : process (rclk)
        variable out_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
        variable out_block_vld : std_logic_vector(DATA_BLOCKS-1 downto 0);
        variable out_vld       : std_logic;
    begin
        if (rising_edge(rclk)) then
            if (OUTPUT_REG) then
                out_data       := out_reg1_data;
                out_block_vld  := out_reg1_block_vld;
                out_vld        := out_reg1_vld;
            else
                out_data       := out_reg0_data;
                out_block_vld  := out_reg0_block_vld;
                out_vld        := out_reg0_vld;
            end if;

            if (out_vld='1' and rd_data_vld='0') then
                write(l,string'("ERROR: missing data on read interface"));
                writeline(output,l);
                stop(1);
            end if;

            if (out_vld='0' and rd_data_vld='1') then
                write(l,string'("ERROR: unexpected data on read interface"));
                writeline(output,l);
                stop(2);
            end if;

            if (out_vld='1' and rd_data_vld='1') then

                for i in 0 to DATA_BLOCKS-1 loop
                    if (out_block_vld(i)='1') then
                        if (out_data((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH)/=rd_data((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH)) then
                            write(l,string'("ERROR: data block "));
                            write_dec(l,i);
                            write(l,string'(" read on the read interface does not match the expected value!"));
                            writeline(output,l);
                            write(l,string'("Read value: 0x"));
                            write_hex(l,rd_data((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH));
                            writeline(output,l);
                            write(l,string'("Expected value: 0x"));
                            write_hex(l,out_data((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH));
                            writeline(output,l);
                            stop(3);
                        end if;
                    end if;
                end loop;
            end if;
        end if;
    end process;
    ----

    -- verification ending
    ver_end_pr : process
    begin
        wait for VER_LENGTH*C_WCLK_PER;
        write(l,string'(" : Verification finished Successfully!"));
        writeline(output,l);
        stop(0);
    end process;
    ----

end architecture;
