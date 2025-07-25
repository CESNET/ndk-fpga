-- sdp_bmem_behav.vhd: Half dual port generic BlockRAM memory (behavioral)
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Puš <puš@liberouter.org>
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
architecture BEHAVIORAL of SDP_BMEM is

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

    shared variable memory : t_mem := bram_init_mem;

    signal dob_to_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal reg_dob           : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal reg_dob_dv1       : std_logic;
    signal reg_dob_dv2       : std_logic;
    signal reset_data_b      : std_logic;

    attribute ram_style of memory : variable is "block"; -- auto,block,distributed
    attribute block_ram of memory : variable is true;    -- true,false

begin

    -- ------------------------- memory - port A ------------------------------

    process (CLKA)
    begin
        if (rising_edge(CLKA)) then
            if (WEA = '1') then
                memory(conv_integer(unsigned(ADDRA))) := DIA;
            end if;
        end if;
    end process;


    -- ------------------------- memory - port B ------------------------------

    process (CLKB)
    begin
        if (rising_edge(CLKB)) then
            if (PIPE_ENB = '1') then
                dob_to_reg <= memory(conv_integer(unsigned(ADDRB)));
            end if;
        end if;
    end process;


    -- ------------------------ Output registers -------------------------------

    gen_data_rst: if (RESET_DATA_PATH) generate
        reset_data_b <= RSTB;
    end generate;

    gen_data_not_rst: if (not RESET_DATA_PATH) generate
        reset_data_b <= '0';
    end generate;

    outputreg: if (OUTPUT_REG = true) generate
        -- DOB DV Register
        process (CLKB)
        begin
            if (rising_edge(CLKB)) then
                if (RSTB = '1') then
                    reg_dob_dv1 <= '0';
                    reg_dob_dv2 <= '0';
                elsif (PIPE_ENB = '1') then
                    reg_dob_dv1 <= REB;
                    reg_dob_dv2 <= reg_dob_dv1;
                end if;
            end if;
        end process;

        -- DOB Data Register
        process (CLKB)
        begin
            if (rising_edge(CLKB)) then
                if (reset_data_b = '1') then
                    reg_dob <= (others => '0');
                elsif (PIPE_ENB = '1') then
                    reg_dob <= dob_to_reg;
                end if;
            end if;
        end process;

        -- Mapping registers to output
        DOB    <= reg_dob;
        DOB_DV <= reg_dob_dv2;
    end generate;


    -- --------------------- No Output registers -------------------------------

    nooutputreg: if (OUTPUT_REG = false) generate
        -- DOB DV Register
        process (CLKB)
        begin
            if (rising_edge(CLKB)) then
                if (RSTB = '1') then
                    DOB_DV <= '0';
                elsif (PIPE_ENB = '1') then
                    DOB_DV <= REB;
                end if;
            end if;
        end process;

        -- Mapping memory to output
        DOB <= dob_to_reg;
    end generate;

end architecture;
