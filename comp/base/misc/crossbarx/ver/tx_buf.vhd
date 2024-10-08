-- tx_buf.vhd: Verification unit for CrossbarX
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

entity CROSSBARX_VER_TX_BUF is
port(
    -- Clock and Reset
    CLK                : in  std_logic;
    CLK2               : in  std_logic;
    RESET              : in  std_logic;

    -- Completed Transactions
    RX_TRANS_RECORD    : in  trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    RX_TRANS_SRC_RDY   : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    RX_TRANS_DST_RDY   : out slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    -- Completed Transactions with data
    TX_TRANS_RECORD    : out trans_array_2d_t(TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    TX_TRANS_SRC_RDY   : out slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);
    TX_TRANS_DST_RDY   : in  slv_array_t     (TRANS_STREAMS-1 downto 0)(TRANSS-1 downto 0);

    -- Destination Buffer write interface
    DST_BUF_WR_ADDR    : in  slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(log2(tsel(DATA_DIR,BUF_B_COLS,BUF_A_COLS))-1 downto 0);
    DST_BUF_WR_DATA    : in  slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)((ROW_ITEMS*ITEM_WIDTH)-1 downto 0);
    DST_BUF_WR_IE      : in  slv_array_t     (tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(ROW_ITEMS-1 downto 0); -- Item enable
    DST_BUF_WR_EN      : in  std_logic_vector(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)
);
end entity;

architecture FULL of CROSSBARX_VER_TX_BUF is

    shared variable mem : slv_array_2d_t(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(tsel(DATA_DIR,BUF_B_COLS,BUF_A_COLS)-1 downto 0)(ROW_ITEMS*ITEM_WIDTH-1 downto 0);

    signal d_clk : std_logic;

begin

    -- data transfer clock select
    use_clk2_gen : if (USE_CLK2) generate
        d_clk <= CLK2;
    else generate
        d_clk <= CLK;
    end generate;

    read_pr : process (all)
        variable s1     : natural := SEED1+1;
        variable s2     : natural := SEED2+1;
        variable rand   : natural;
        variable col       : natural;
        variable row       : natural;
        variable item      : natural;
        variable item_data : std_logic_vector(ITEM_WIDTH-1 downto 0);
        variable t         : trans_t;
        variable section_i : unsigned(log2(tsel(DATA_DIR,BUF_B_SECTIONS,BUF_A_SECTIONS))-1 downto 0);
        variable col_i     : unsigned(log2(tsel(DATA_DIR,BUF_B_SECTION_COLS,BUF_A_SECTION_COLS))-1 downto 0);
        variable stream_i  : unsigned(log2(tsel(DATA_DIR,1,TRANS_STREAMS))-1 downto 0);
        variable row_i     : unsigned(log2(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_STREAM_ROWS))-1 downto 0);
        variable item_i    : unsigned(log2(ROW_ITEMS)-1 downto 0);
        -- hotfix for questasim simulatior
        variable tmp_addr  : unsigned(col_i'length+row_i'length+item_i'length-1 downto 0);
    begin
        TX_TRANS_SRC_RDY <= RX_TRANS_SRC_RDY;
        RX_TRANS_DST_RDY <= TX_TRANS_DST_RDY;

        for i in 0 to TRANS_STREAMS-1 loop

            for e in 0 to TRANSS-1 loop

                -- add data from Buffer
                t := RX_TRANS_RECORD(i)(e);
                t.data := (others => '0');

                for g in 0 to TRANS_LENGTH_MAX-1 loop

                    exit when (g>=t.length);

                    section_i := to_unsigned(tsel(DATA_DIR,t.b_section,t.a_section),section_i'length);
                    --hotfix
                    --(col_i, row_i, item_i) := to_unsigned(tsel(DATA_DIR,t.b_ptr,t.a_ptr)+g,col_i'length+row_i'length+item_i'length);
                    tmp_addr := to_unsigned(tsel(DATA_DIR,t.b_ptr,t.a_ptr)+g,col_i'length+row_i'length+item_i'length);
                    col_i  := tmp_addr(col_i'length+row_i'length+item_i'length-1 downto row_i'length+item_i'length);
                    row_i  := tmp_addr(row_i'length+item_i'length-1 downto item_i'length);
                    item_i := tmp_addr(item_i'length-1 downto 0);

                    stream_i  := to_unsigned(t.a_stream,stream_i'length);
                    row  := to_integer(stream_i & row_i);
                    col  := to_integer(section_i & col_i);
                    item := to_integer(item_i);

                    item_data := mem(row)(col)((item+1)*ITEM_WIDTH-1 downto item*ITEM_WIDTH);

--                  report "section_i : " & to_string(section_i) & CR &
--                         "col_i     : " & to_string(col_i)     & CR &
--                         "row_i     : " & to_string(row_i)     & CR &
--                         "item_i    : " & to_string(item_i)    & CR &
--                         "stream_i  : " & to_string(stream_i)  & CR &
--                         "row       : " & to_string(row)       & CR &
--                         "col       : " & to_string(col)       & CR &
--                         "item      : " & to_string(item)      & CR &
--                         "item_data : " & to_string(item_data);

                    t.data((g+1)*ITEM_WIDTH-1 downto g*ITEM_WIDTH) := item_data;

                end loop;

                TX_TRANS_RECORD(i)(e) <= t;

            end loop;

        end loop;
    end process;

    data_wr_pr : process (d_clk)
    begin
        if (rising_edge(d_clk)) then

            for i in 0 to tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 loop
                if (DST_BUF_WR_EN(i)='1') then
                    for e in 0 to ROW_ITEMS-1 loop
                        if (DST_BUF_WR_IE(i)(e)='1') then
                            mem(i)(to_integer(unsigned(DST_BUF_WR_ADDR(i))))((e+1)*ITEM_WIDTH-1 downto e*ITEM_WIDTH) := DST_BUF_WR_DATA(i)((e+1)*ITEM_WIDTH-1 downto e*ITEM_WIDTH);
                        end if;
                    end loop;
                end if;
            end loop;

            if (RESET='1') then
                mem := (others => (others => (others => 'X')));
            end if;
        end if;
    end process;

end architecture;
