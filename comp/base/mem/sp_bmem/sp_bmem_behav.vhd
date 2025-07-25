--
-- sp_bmem_behav.vhd: Single port generic BlockRAM memory (behavioral)
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use work.math_pack.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture BEHAVIORAL of SP_BMEM is

    attribute ram_style   : string;  -- for XST
    attribute block_ram   : boolean; -- for precision

    type t_mem is array(0 to ITEMS-1) of std_logic_vector(DATA_WIDTH-1 downto 0);

    -- ----------------------------------------------------------------------
    -- Function to Zero out the memory
    -- This is to prevent 'U' signals in simulations
    function bram_init_mem return t_mem is
        variable init : t_mem;
    begin
        for i in 0 to ITEMS - 1 loop
            init(i) := (others => '0');
        end loop;

        return init;
    end function;
    -- ----------------------------------------------------------------------

    signal memory : t_mem := bram_init_mem;

    attribute ram_style of memory : signal is "block"; -- auto,block,distributed
    attribute block_ram of memory : signal is true;    -- true,false

    signal do_to_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal reg_do           : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal reg_do_dv1       : std_logic;
    signal reg_do_dv2       : std_logic;

begin

    -- ------------------------------ memory -----------------------------------

    gen_write_first: if (WRITE_MODE = "WRITE_FIRST") generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (PIPE_EN = '1') then
                    if (WE = '1') then
                        memory(conv_integer(unsigned(ADDR))) <= DI;
                    end if;
                    do_to_reg <= memory(conv_integer(unsigned(ADDR)));
                end if;
            end if;
        end process;
    end generate;

    gen_read_first: if (WRITE_MODE = "READ_FIRST") generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (PIPE_EN = '1') then
                    do_to_reg <= memory(conv_integer(unsigned(ADDR)));
                    if (WE = '1') then
                        memory(conv_integer(unsigned(ADDR))) <= DI;
                    end if;
                end if;
            end if;
        end process;
    end generate;


    -- doesn't work
    gen_no_change: if (WRITE_MODE = "NO_CHANGE") generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (PIPE_EN = '1') then
                    if (WE = '1' and RE = '0') then
                        memory(conv_integer(unsigned(ADDR))) <= DI;
                    end if;
                    do_to_reg <= memory(conv_integer(unsigned(ADDR)));
                end if;
            end if;
        end process;
    end generate;


    -- ------------------------ Output registers -------------------------------
    outputreg : if (OUTPUT_REG = true) generate
        -- DO Register
        process (RESET, CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    reg_do     <= (others => '0');
                    reg_do_dv1 <= '0';
                    reg_do_dv2 <= '0';
                elsif (PIPE_EN = '1') then
                    reg_do     <= do_to_reg;
                    reg_do_dv1 <= RE;
                    reg_do_dv2 <= reg_do_dv1;
                end if;
            end if;
        end process;

        -- mapping registers to output
        DO    <= reg_do;
        DO_DV <= reg_do_dv2;
    end generate;


    -- --------------------- No Output registers -------------------------------
    nooutputreg : if (OUTPUT_REG = false) generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    DO_DV <= '0';
                elsif (PIPE_EN = '1') then
                    DO_DV <= RE;
                end if;
            end if;
        end process;

        -- mapping memory to output
        DO <= do_to_reg;
    end generate;

end architecture;
