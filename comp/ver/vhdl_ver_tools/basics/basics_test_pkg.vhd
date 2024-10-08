-- basics_test_pkg.vhd: Test Package containing basics for VHDL verification
-- Copyright (C) 2018 CESNET
-- Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields
use std.env.stop;
use STD.textio.all;

   -- ----------------------------------------------------------------------------
   --                        package declarations
   -- ----------------------------------------------------------------------------

package basics_test_pkg is

   type str_array_t is array (natural range <>) of string;

   -- FIFO of std_logic_vectors
   type slv_fifo_t is record
      fifo  : slv_array_t; -- transactions
      fill  : integer; -- number of items
      full  : std_logic;
      empty : std_logic;
      -- statistics
      fill_max : natural;
      fill_sum : natural;
      fill_num : natural;
   end record;

   type slv_fifo_array_t is array (natural range <>) of slv_fifo_t;
   type slv_fifo_array_2d_t is array (natural range <>) of slv_fifo_array_t;
   ----

   -- function and procedure declarations

   -- number operations
   function ceil2N(x : integer) return integer;

   -- random values
   procedure randint(seed1 : inout positive; seed2 : inout positive; min_val : integer; max_val : integer; X : out integer);
   function random_vector(width : natural; seed : positive) return std_logic_vector; -- DEPRACATED
   procedure random_vector_proc(seed1 : inout positive; seed2 : inout positive; vector : out std_logic_vector);
   procedure random_val_index(vec : std_logic_vector; val : std_logic; seed1 : inout positive; seed2 : inout positive; index : out integer);

   -- value printing
   procedure write_dec(l : inout line; i : integer);
   procedure write_dec(l : inout line; i : std_logic_vector);
   procedure write_dec(l : inout line; i : unsigned);
   procedure write_hex(l : inout line; i : integer);
   procedure write_hex(l : inout line; i : std_logic_vector);
   procedure write_hex(l : inout line; i : unsigned);
   procedure write_log(l : inout line; i : std_logic);

   -- slv FIFO operations
   procedure slv_fifo_new(f : inout slv_fifo_t);
   procedure slv_fifo_put(f : inout slv_fifo_t; item : in  std_logic_vector);
   procedure slv_fifo_pop(f : inout slv_fifo_t; item : out std_logic_vector);
   procedure fifo_print_stats(f : slv_fifo_t; name : string);

   -- fill std_logic_vector
   procedure repeated_fill(vec : out std_logic_vector; value : integer);

   -- count 0s or 1s in vector
   function count_val(vec : std_logic_vector; val : std_logic) return integer;
   ----
end basics_test_pkg;

   -- ----------------------------------------------------------------------------
   --                            package body
   -- ----------------------------------------------------------------------------

package body basics_test_pkg is

   -- function for 2**N ceiling
   function ceil2N(x : integer) return integer is
      variable v : integer := 1;
   begin
      while (v<x) loop
         v := v*2;
      end loop;

      return v;
   end function;

   -- generates random std_logic_vector (DEPRACATED use random_vector_proc instead)
   function random_vector(width : natural; seed : positive) return std_logic_vector is
      variable vec : std_logic_vector(width-1 downto 0) := (others => '0');
      variable s1,s2 : positive;
   begin
      s1 := seed;
      s2 := seed;
      random_vector_proc(s1,s2,vec);
      return vec;
   end function;
   ----

   -- generates random std_logic_vector
   procedure random_vector_proc(seed1 : inout positive; seed2 : inout positive; vector : out std_logic_vector) is
      variable rand  : real;
      variable X     : integer;
      variable width : integer;
   begin
      width := vector'length;
      for i in 0 to width/30-1 loop
         uniform(seed1,seed2,rand);
         X := integer(rand*real(2**30));
         vector(30*(i+1)-1 downto 30*i) := std_logic_vector(to_unsigned(X,30));
      end loop;

      uniform(seed1,seed2,rand);
      X := integer(rand*real(2**30));
      vector(width-1 downto (width/30)*30) := std_logic_vector(to_unsigned(X,width mod 30));
   end procedure;
   ----

   -- random integer from min_val to max_val inclusive
   procedure randint(seed1 : inout positive; seed2 : inout positive; min_val : integer; max_val : integer; X : out integer) is
      variable rand : real;
   begin
      uniform(seed1,seed2,rand);
      X := integer(rand*real(max_val+1-min_val)-0.5)+min_val;
   end procedure;
   ----

   -- sets index to vector vec, that has value val; -1 if no such index found
   procedure random_val_index(vec : std_logic_vector; val : std_logic; seed1 : inout positive; seed2 : inout positive; index : out integer) is
      variable rand : real;
      variable X : integer;
   begin
      index := -1;

      uniform(seed1,seed2,rand);
      X := integer(rand*real(vec'length-1));
      for i in 0 to vec'length-1 loop
         if (vec(X)='1') then
            index := X;
            exit;
         end if;
         X := X+1;
         if (X=vec'length) then
            X := 0;
         end if;
      end loop;
   end procedure;
   ----

   -- string line procedures
   procedure write_dec(l : inout line; i : integer) is
   begin
      write(l,integer'image(i));
   end procedure;

   procedure write_dec(l : inout line; i : std_logic_vector) is
   begin
      write_dec(l,to_integer(unsigned(i)));
   end procedure;

   procedure write_dec(l : inout line; i : unsigned) is
   begin
      write_dec(l,to_integer(i));
   end procedure;

   procedure write_log(l : inout line; i : std_logic) is
   begin
      if (i='1') then
          write(l,string'("'1'"));
      elsif (i='0') then
          write(l,string'("'0'"));
      elsif (i='X') then
          write(l,string'("'X'"));
      elsif (i='U') then
          write(l,string'("'U'"));
      else
          write(l,string'("'X'"));
      end if;
   end procedure;

   procedure write_hex(l : inout line; i : integer) is
      variable v : integer;
      variable hex_values : string(1 to 16) := "0123456789abcdef";
      variable rev_line : string(1 to 16);
      variable ptr : integer := 16;
   begin
      if (i=0) then
         write(l,string'("00"));
      else
         v := i;
         while (v>0 or (ptr mod 2)=1) loop -- print on an even number of digits
            rev_line(ptr) := hex_values((v mod 16)+1);
            ptr := ptr-1;
            v := v/16;
         end loop;

         --write(l,string'(rev_line(ptr+1 to 16)));
         for i in ptr+1 to 16 loop
            write(l, rev_line(i));
         end loop;
      end if;
   end procedure;

   procedure write_hex(l : inout line; i : std_logic_vector) is
   begin
      if (i'length mod 8/=0) then
         write_hex(l,to_integer(unsigned(i(i'high downto i'high-(i'length mod 8)+1))));
      end if;

      for e in i'length/8-1 downto 0 loop
         write_hex(l,to_integer(unsigned(i(i'low+8*(e+1)-1 downto i'low+8*e))));
      end loop;
   end procedure;

   procedure write_hex(l : inout line; i : unsigned) is
   begin
      write_hex(l,std_logic_vector(i));
   end procedure;

   ----

   -- prints statistics about given FIFO
   procedure fifo_print_stats(f : slv_fifo_t; name : string) is
      variable l : line;
      variable avg : real;
   begin
      write(l,string'("  ::: " & name &" info :::"));writeline(output,l);
      write(l,string'("size    : " & integer'image(f.fifo'length)));writeline(output,l);
      write(l,string'("fill max: " & integer'image(f.fill_max)));writeline(output,l);
      if (f.fill_num=0) then
         avg := 0.0;
      else
         avg := real(f.fill_sum)/real(f.fill_num);
      end if;
      if (avg<10.0) then
         write(l,string'("fill avg: " & real'image(avg)));writeline(output,l);
      else
         write(l,string'("fill avg: " & integer'image(integer(avg))));writeline(output,l);
      end if;
      write(l,string'(""));writeline(output,l);
   end procedure;
   ----

   -- std_logic_vector fifo procedures
   procedure slv_fifo_new(f : inout slv_fifo_t) is
   begin
      f.fill  := 0;
      f.full  := '0';
      f.empty := '1';

      f.fill_max := 0;
      f.fill_sum := 0;
      f.fill_num := 0;
   end procedure;

   procedure slv_fifo_put(f : inout slv_fifo_t; item : in  std_logic_vector) is
      variable new_fill : integer := f.fill+1;
   begin
      if (f.full='1') then
         report "Writing in full slv FIFO!" severity failure;
      end if;

      f.fifo(new_fill-1) := item;

      f.empty := '0';

      f.fill := new_fill;

      if (new_fill=f.fifo'length) then
         f.full := '1';
      end if;

      f.fill_num := f.fill_num+1;
      f.fill_sum := f.fill_sum+f.fill;
      if (f.fill_max<f.fill) then
         f.fill_max := f.fill;
      end if;
   end procedure;

   procedure slv_fifo_pop(f : inout slv_fifo_t; item : out std_logic_vector) is
      variable new_fill : integer := f.fill-1;
   begin
      if (f.empty='1') then
         report "Reading from empty slv FIFO!" severity failure;
      end if;

      item := f.fifo(0);
      f.fifo(new_fill-1 downto 0) := f.fifo(new_fill+1-1 downto 1);

      f.full := '0';

      f.fill := new_fill;

      if (new_fill=0) then
         f.empty := '1';
      end if;

      f.fill_num := f.fill_num+1;
      f.fill_sum := f.fill_sum+f.fill;
   end procedure;
   ----

   -- fill std_logic_vector with repeated 8-bit value
   procedure repeated_fill(vec : out std_logic_vector; value : integer) is
   begin
      for i in 0 to vec'length/8-1 loop
         vec(vec'low+8*(i+1)-1 downto vec'low+8*i) := std_logic_vector(to_unsigned(value,8));
      end loop;
      vec(vec'low+vec'length-1 downto vec'low+8*(vec'length/8)) := std_logic_vector(to_unsigned(value,vec'length mod 8));
   end procedure;
   ----

   -- MFB word pointer operations
   function count_val(vec : std_logic_vector; val : std_logic) return integer is
      variable ret : integer := 0;
   begin
      for i in vec'low to vec'high loop
         if (vec(i)=val) then
            ret := ret+1;
         end if;
      end loop;

      return ret;
   end function;
   ----

end basics_test_pkg;

