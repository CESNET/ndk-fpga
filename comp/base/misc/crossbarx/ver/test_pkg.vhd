-- test_pkg.vhd
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
use STD.textio.all;

package test_pkg is

    -------------------------------------------------------------
    -- Verification parameters
    -------------------------------------------------------------

    constant C_CLK_PER     : time := 1 ns;
    constant C_CLK_ARB_PER : time := 0.7 ns;

    constant SEED1 : natural := 44;
    constant SEED2 : natural := 555;

    constant TRANSACTIONS            : natural := 2048;

    constant TRANS_LENGTH_MIN        : natural := 1;
    constant TRANS_LENGTH_MAX        : natural := 256;

    constant TRANS_GAP_LENGTH_MIN    : natural := 0;
    constant TRANS_GAP_LENGTH_MAX    : natural := 128;

    constant RX_TRANS_NOT_RDY_CH     : natural := 10; -- [%] Chance that a Transaction will NOT be generated, even though it could
    constant TX_TRANS_NOT_RDY_CH     : natural := 10; -- [%] Chance that Confirmed Transaction will not be accepted

    constant TRANS_AB_ALIGNED_CH     : natural := 10; -- [%] Chance that a generated Transaction will be forcefully aligned to the start on the same Item within a Row in Buffer A and Buffer B (no uInstruction splitting will be needed)
    constant TRANS_START_ALIGNED_CH  : natural := 10; -- [%] Chance that a generated Transaction will have forcefully address aligned start of a Row
    constant TRANS_LENGTH_ALIGNED_CH : natural := 10; -- [%] Chance that a generated Transaction will have length aligned to number of Rows

    constant VERBOSITY_LEVEL         : natural := 0;

    constant GENERATING_LOG_PERIOD   : natural := 0;--2*1024; -- set to 0 to turn OFF
    constant THROUGHPUT_LOG_PERIOD   : natural := 0;--2*1024; -- set to 0 to turn OFF

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- CrossbarX paramters
    -------------------------------------------------------------

    constant DATA_DIR            : boolean := true;
    constant USE_CLK2            : boolean := true;
    constant USE_CLK_ARB         : boolean := true;
    constant TRANS_STREAMS       : integer := 2;
    constant BUF_A_COLS          : integer := 256;
    constant BUF_A_STREAM_ROWS   : integer := 2;
    constant BUF_B_COLS          : integer := 256;
    constant BUF_B_ROWS          : integer := 4*TRANS_STREAMS;
    constant BUF_A_SECTIONS      : integer := 2;
    constant BUF_B_SECTIONS      : integer := 4;
    constant ROW_ITEMS           : integer := 4;
    constant ITEM_WIDTH          : integer := 8;
    constant TRANSS              : integer := 2;
    constant TRANS_MTU           : integer := ceil2N(TRANS_LENGTH_MAX);
    constant METADATA_WIDTH      : integer := 16;
    constant TRANS_FIFO_ITEMS    : integer := TRANSS*16;
    constant COLOR_TIMEOUT_WIDTH : integer := 6;
    constant COLOR_CONF_DELAY    : integer := 16;
    constant RD_LATENCY          : integer := 1;
    constant DATA_MUX_LAT        : integer := 0;
    constant DATA_MUX_OUTREG_EN  : boolean := true;
    constant DATA_ROT_LAT        : integer := 0;
    constant DATA_ROT_OUTREG_EN  : boolean := true;
    constant DEVICE              : string  := "STRATIX10"; -- "ULTRASCALE", "7SERIES", "STRATIX10" ...

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Verification package
    -------------------------------------------------------------

    constant BUF_A_ITEMS        : natural := TRANS_STREAMS*BUF_A_COLS*BUF_A_STREAM_ROWS*ROW_ITEMS;
    constant BUF_B_ITEMS        : natural := BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS;

    constant BUF_A_ROWS         : integer := BUF_A_STREAM_ROWS*TRANS_STREAMS; -- constant alias, DO NOT CHANGE!

    constant BUF_A_SECTION_COLS : natural := BUF_A_COLS/BUF_A_SECTIONS;
    constant BUF_B_SECTION_COLS : natural := BUF_B_COLS/BUF_B_SECTIONS;

    type trans_t is record
        a_stream     : natural;
        a_section    : natural;
        a_ptr        : natural;
        b_section    : natural;
        b_ptr        : natural;
        length       : natural;
        a_gap_length : natural; -- number of empty Items before this Transaction
        b_gap_length : natural; -- number of empty Items before this Transaction
        meta         : std_logic_vector(METADATA_WIDTH-1 downto 0);
        data         : std_logic_vector(TRANS_LENGTH_MAX*ITEM_WIDTH-1 downto 0);
    end record;

    constant TRANS_WIDTH : natural := 32*8+METADATA_WIDTH+TRANS_LENGTH_MAX*ITEM_WIDTH;

    function trans_ser  (t : trans_t) return std_logic_vector;
    function trans_deser(vec : std_logic_vector) return trans_t;

    procedure trans_print(l : inout line; t : in trans_t);

    type trans_array_t is array (natural range <>) of trans_t;
    type trans_array_2d_t is array (natural range <>) of trans_array_t;

    function get_a_start_addr(t : trans_t) return natural;
    function get_a_end_addr  (t : trans_t) return natural;
    function get_b_start_addr(t : trans_t) return natural;
    function get_b_end_addr  (t : trans_t) return natural;

    procedure gen_random(seed1, seed2 : inout natural; t : out trans_t);

    type fifo_array_t is array (natural range <>) of slv_fifo_t;

    -------------------------------------------------------------

end package;

package body test_pkg is

    function trans_ser  (t : trans_t) return std_logic_vector is
        variable vec : std_logic_vector(TRANS_WIDTH-1 downto 0);
    begin
        vec := std_logic_vector(to_unsigned(t.a_stream    ,32))
              &std_logic_vector(to_unsigned(t.a_section   ,32))
              &std_logic_vector(to_unsigned(t.a_ptr       ,32))
              &std_logic_vector(to_unsigned(t.b_section   ,32))
              &std_logic_vector(to_unsigned(t.b_ptr       ,32))
              &std_logic_vector(to_unsigned(t.length      ,32))
              &std_logic_vector(to_unsigned(t.a_gap_length,32))
              &std_logic_vector(to_unsigned(t.b_gap_length,32))
              &t.meta
              &t.data;
        return vec;
    end function;

    function trans_deser(vec : std_logic_vector) return trans_t is
        variable tmp_a_stream     : std_logic_vector(32-1 downto 0);
        variable tmp_a_section    : std_logic_vector(32-1 downto 0);
        variable tmp_a_ptr        : std_logic_vector(32-1 downto 0);
        variable tmp_b_section    : std_logic_vector(32-1 downto 0);
        variable tmp_b_ptr        : std_logic_vector(32-1 downto 0);
        variable tmp_length       : std_logic_vector(32-1 downto 0);
        variable tmp_a_gap_length : std_logic_vector(32-1 downto 0);
        variable tmp_b_gap_length : std_logic_vector(32-1 downto 0);
        variable tmp_meta         : std_logic_vector(METADATA_WIDTH-1 downto 0);
        variable tmp_data         : std_logic_vector(TRANS_LENGTH_MAX*ITEM_WIDTH-1 downto 0);
        variable t : trans_t;
    begin
        (tmp_a_stream    ,
         tmp_a_section   ,
         tmp_a_ptr       ,
         tmp_b_section   ,
         tmp_b_ptr       ,
         tmp_length      ,
         tmp_a_gap_length,
         tmp_b_gap_length,
         tmp_meta        ,
         tmp_data         ) := vec;

        t.a_stream     := to_integer(unsigned(tmp_a_stream    ));
        t.a_section    := to_integer(unsigned(tmp_a_section   ));
        t.a_ptr        := to_integer(unsigned(tmp_a_ptr       ));
        t.b_section    := to_integer(unsigned(tmp_b_section   ));
        t.b_ptr        := to_integer(unsigned(tmp_b_ptr       ));
        t.length       := to_integer(unsigned(tmp_length      ));
        t.a_gap_length := to_integer(unsigned(tmp_a_gap_length));
        t.b_gap_length := to_integer(unsigned(tmp_b_gap_length));
        t.meta         := tmp_meta;
        t.data         := tmp_data;

        return t;
    end function;

    procedure trans_print(l : inout line; t : in trans_t) is
        variable ptr : natural;
    begin
         write(l,string'("Buffer A Stream   :   ")); write_dec(l,t.a_stream); writeline(output,l);
         write(l,string'("Buffer A Section  : 0x")); write_hex(l,t.a_section);writeline(output,l);
         write(l,string'("Buffer A Column   : 0x")); write_hex(l,t.a_ptr  /  (BUF_A_STREAM_ROWS*ROW_ITEMS));writeline(output,l);
         write(l,string'("Buffer A Item     : 0x")); write_hex(l,t.a_ptr mod (BUF_A_STREAM_ROWS*ROW_ITEMS));writeline(output,l);
         write(l,string'("Buffer B Section  : 0x")); write_hex(l,t.b_section);writeline(output,l);
         write(l,string'("Buffer B Column   : 0x")); write_hex(l,t.b_ptr  /  (BUF_B_ROWS*ROW_ITEMS));writeline(output,l);
         write(l,string'("Buffer B Item     : 0x")); write_hex(l,t.b_ptr mod (BUF_B_ROWS*ROW_ITEMS));writeline(output,l);
         write(l,string'("Length            :   ")); write_dec(l,t.length);   writeline(output,l);
         write(l,string'("Metadata          : 0x")); write_hex(l,t.meta);     writeline(output,l);
         write(l,string'("Data:")); writeline(output,l);
         ptr := 0;
         for i in 0 to t.length-1 loop
             for e in 0 to 4-1 loop
                 for g in 0 to 8-1 loop
                     write_hex(l,t.data((ptr+1)*ITEM_WIDTH-1 downto ptr*ITEM_WIDTH)); write(l,string'(" "));
                     ptr := ptr+1;
                     exit when (ptr=t.length);
                 end loop;
                 write(l,string'(" "));
                 exit when (ptr=t.length);
             end loop;
             writeline(output,l);
             exit when (ptr=t.length);
         end loop;
    end procedure;

    function get_a_start_addr(t : trans_t) return natural is
    begin
        return t.a_section*BUF_A_SECTION_COLS+t.a_ptr;
    end function;

    function get_a_end_addr  (t : trans_t) return natural is
        variable addr : natural;
    begin
        addr := get_a_start_addr(t);
        addr := (addr+t.length) mod BUF_A_SECTION_COLS;
        addr := t.a_section*BUF_A_SECTION_COLS+addr;
        return addr;
    end function;

    function get_b_start_addr(t : trans_t) return natural is
    begin
        return t.b_section*BUF_B_SECTION_COLS+t.b_ptr;
    end function;

    function get_b_end_addr  (t : trans_t) return natural is
        variable addr : natural;
    begin
        addr := get_b_start_addr(t);
        addr := (addr+t.length) mod BUF_B_SECTION_COLS;
        addr := t.b_section*BUF_B_SECTION_COLS+addr;
        return addr;
    end function;

    procedure gen_random(seed1, seed2 : inout natural; t : out trans_t) is
    begin
        randint(seed1,seed2,0,TRANS_STREAMS-1,t.a_stream);
        randint(seed1,seed2,0,BUF_A_SECTIONS-1,t.a_section);
        t.a_ptr := 0;
        randint(seed1,seed2,0,BUF_B_SECTIONS-1,t.b_section);
        t.b_ptr := 0;
        randint(seed1,seed2,TRANS_LENGTH_MIN,TRANS_LENGTH_MAX,t.length);
        randint(seed1,seed2,TRANS_GAP_LENGTH_MIN,TRANS_GAP_LENGTH_MAX,t.a_gap_length);
        randint(seed1,seed2,TRANS_GAP_LENGTH_MIN,TRANS_GAP_LENGTH_MAX,t.b_gap_length);
        t.meta  := random_vector(METADATA_WIDTH, seed1);
        t.data  := random_vector(TRANS_LENGTH_MAX*ITEM_WIDTH, seed2);
        t.data(TRANS_LENGTH_MAX*ITEM_WIDTH-1 downto t.length*ITEM_WIDTH) := (others => '0');
    end procedure;

end;
