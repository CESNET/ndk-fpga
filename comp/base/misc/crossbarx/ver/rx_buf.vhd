-- rx_buf.vhd: Verification unit for CrossbarX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.basics_test_pkg.all;
use work.test_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_VER_RX_BUF is
port(
    -- Clock and Reset
    CLK                : in  std_logic;
    CLK2               : in  std_logic;
    RESET              : in  std_logic;

    -- Generated Transactions
    RX_TRANS_RECORD    : in  trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    RX_TRANS_SRC_RDY   : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    -- Read Interface
    SRC_BUF_RD_ADDR    : in  slv_array_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)(log2(tsel(DATA_DIR,BUF_A_COLS,BUF_B_COLS))-1 downto 0);
    SRC_BUF_RD_DATA    : out slv_array_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0)
);
end entity;

architecture FULL of CROSSBARX_VER_RX_BUF is

    signal mem          : slv_array_2d_t(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)(tsel(DATA_DIR,BUF_A_COLS,BUF_B_COLS)-1 downto 0)(ROW_ITEMS*ITEM_WIDTH-1 downto 0);
    signal read_data    : slv_array_2d_t(RD_LATENCY+1-1 downto 0)(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0);

    signal d_clk : std_logic;

begin

    -- data transfer clock select
    use_clk2_gen : if (USE_CLK2) generate
        d_clk <= CLK2;
    else generate
        d_clk <= CLK;
    end generate;

    write_pr : process (CLK)
        variable col       : integer;
        variable row       : integer;
        variable item      : integer;
        variable item_data : std_logic_vector(ITEM_WIDTH-1 downto 0);
        variable t         : trans_t;
        variable section_i : unsigned(log2(tsel(DATA_DIR,BUF_A_SECTIONS,BUF_B_SECTIONS))-1 downto 0);
        variable col_i     : unsigned(log2(tsel(DATA_DIR,BUF_A_SECTION_COLS,BUF_B_SECTION_COLS))-1 downto 0);
        variable stream_i  : unsigned(log2(tsel(DATA_DIR,TRANS_STREAMS,1))-1 downto 0);
        variable row_i     : unsigned(log2(tsel(DATA_DIR,BUF_A_STREAM_ROWS,BUF_B_ROWS))-1 downto 0);
        variable item_i    : unsigned(log2(ROW_ITEMS)-1 downto 0);
        -- hotfix for questasim simulatior
        variable tmp_addr  : unsigned(col_i'length+row_i'length+item_i'length-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            for i in 0 to TRANS_STREAMS-1 loop
                for e in 0 to TRANSS-1 loop
                    if (RX_TRANS_SRC_RDY(i)(e)='1') then

                        t := RX_TRANS_RECORD(i)(e);

                        for g in 0 to TRANS_LENGTH_MAX-1 loop

                            exit when (g>=t.length);

                            item_data := t.data((g+1)*ITEM_WIDTH-1 downto g*ITEM_WIDTH);

                            section_i := to_unsigned(tsel(DATA_DIR,t.a_section,t.b_section),section_i'length);
                            --hotfix
                            --(col_i, row_i, item_i) := to_unsigned(tsel(DATA_DIR,t.a_ptr,t.b_ptr)+g,col_i'length+row_i'length+item_i'length);
                            tmp_addr := to_unsigned(tsel(DATA_DIR,t.a_ptr,t.b_ptr)+g,col_i'length+row_i'length+item_i'length);
                            col_i  := tmp_addr(col_i'length+row_i'length+item_i'length-1 downto row_i'length+item_i'length);
                            row_i  := tmp_addr(row_i'length+item_i'length-1 downto item_i'length);
                            item_i := tmp_addr(item_i'length-1 downto 0);

                            stream_i  := to_unsigned(t.a_stream,stream_i'length);
                            row  := to_integer(stream_i & row_i);
                            col  := to_integer(section_i & col_i);
                            item := to_integer(item_i);

                            --report "section_i : " & to_string(section_i) & CR &
                            --       "col_i     : " & to_string(col_i)     & CR &
                            --       "row_i     : " & to_string(row_i)     & CR &
                            --       "item_i    : " & to_string(item_i)    & CR &
                            --       "stream_i  : " & to_string(stream_i)  & CR &
                            --       "data      : " & to_hstring(item_data);

                            --report "row      : " & to_string(row)  & CR &
                            --       "col      : " & to_string(col)  & CR &
                            --       "item_i   : " & to_string(item_i) & CR &
                            --       "item     : " & to_string(item) & CR &
                            --       "data     : " & to_hstring(item_data);

                            mem(row)(col)((item+1)*ITEM_WIDTH-1 downto item*ITEM_WIDTH) <= item_data;

                        end loop;

                    end if;
                end loop;
            end loop;

            if (RESET='1') then
                mem <= (others => (others => (others => 'X')));
            end if;
        end if;
    end process;

    zero_lat_gen : if (RD_LATENCY=0) generate
        data_read_gen : for i in 0 to tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 generate
            read_data(0)(i) <= mem(i)(to_integer(unsigned(SRC_BUF_RD_ADDR(i))));
        end generate;

        SRC_BUF_RD_DATA <= read_data(0);
    else generate
        data_read_delay : process (d_clk)
        begin
            if (rising_edge(d_clk)) then
                for i in 0 to tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 loop
                    read_data(0)(i) <= mem(i)(to_integer(unsigned(SRC_BUF_RD_ADDR(i))));
                end loop;

                for i in 0 to RD_LATENCY-1-1 loop
                    read_data(i+1) <= read_data(i);
                end loop;
            end if;
        end process;

        SRC_BUF_RD_DATA <= read_data(RD_LATENCY-1);
    end generate;

end architecture;
