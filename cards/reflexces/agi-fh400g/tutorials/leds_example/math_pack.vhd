-- math_pack.vhd
--!
--! \file
--! \brief Math package
--! \author Zdenek Salvet <salvet@ics.muni.cz>
--! \author Tomas Martinek <martinek@liberouter.org>
--! \author Viktor Pus <pus@liberouter.org>
--! \author Petr Kobiersky <kobiersky@liberouter.org>
--! \date 2003
--!
--! \section License
--!
--! Copyright (C) 2003 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

--! \brief Package with basic math functions 
--! \details This package contains math functions: log2, max, min and div_roundup.
package math_pack is

   --! \brief Logarithm with base 2.
   --! \details Founds first integer larger or equal to real base 2 logarithm of given number.
   --! @param n Given number.
   --! @return Logarithm value of given number.
   function log2 (n : integer) return integer;
   --! \brief Logarithm with base 2.
   --! \details Founds first integer larger or equal to real base 2 logarithm of given number.
   --! @param n Given number.
   --! @return Logarithm value of given number.
   function log2 (n : std_logic_vector(31 downto 0)) return integer;
   --! \brief Selects higher number from two given.
   --! @param l First given number.
   --! @param r Second given number.
   --! @return Higher number from l r.
   function max(l, r: integer) return integer;
   --! \brief Selects lower number from two given.
   --! @param l First given number.
   --! @param r Second given number.
   --! @return Lower number from l r.
   function min(l, r: integer) return integer;
   --! \brief Selects lower number from two given.
   --! @param l First given number.
   --! @param r Second given number.
   --! @return Lower number from l r.
   function minimum(l, r: integer) return integer;
   --! \brief Integer roundup division.
   --! \details Founds first integer larger or equal to real result of division.
   --! @param dividend A number that is going to be devided.
   --! @param divisor The number by which dividend is divided.
   --! @return Result of division rounded up to nearest integer.
   function div_roundup(dividend, divisor: integer) return integer;

    --! \brief Return the count of '1' values in std_logic_vector
    function count_ones(slv : std_logic_vector) return natural;

   --! \brief Ternary conditional assignment operator (like ?: in C).
   --! \details Select one of two given values based on condition evaluation.
   --! @param cond Boolean selection condition.
   --! @param true_val Value returned when condition is true.
   --! @param false_val Value returned when condition is false.
   --! @return Selected value.
   function tsel(cond : boolean; true_val: integer; false_val: integer) return integer;
   function tsel(cond : boolean; true_val: real; false_val: real) return real;
   function tsel(cond : boolean; true_val: std_logic; false_val: std_logic) return std_logic;
   function tsel(cond : boolean; true_val: bit; false_val: bit) return bit;
   function tsel(cond : boolean; true_val: std_logic_vector; false_val: std_logic_vector) return std_logic_vector;
   function tsel(cond : boolean; true_val: string; false_val: string) return string;

   --!\brief returns smalest value witch is diveded by base and is not smallest that x 
   function ceil(x,base : integer) return integer;

   -- Round the given 'value' up, so that the lower 'rounding_width' bits are zero
   function round_up(value : std_logic_vector; rounding_width : natural) return std_logic_vector;
   function round_up(value : unsigned;  rounding_width : natural) return unsigned;
   function round_up(value : signed; rounding_width : natural) return signed;
   function round_up(value : integer; rounding_width : natural) return integer;
   -- Round the given 'value' down, so that the lower 'rounding_width' bits are zero
   function round_down(value : std_logic_vector; rounding_width : natural) return std_logic_vector;
   function round_down(value : unsigned; rounding_width : natural) return unsigned;
   function round_down(value : signed; rounding_width : natural) return signed;
   function round_down(value : integer; rounding_width : natural) return integer;

   -- Resize the given 'vector' by setting 'new_width'
   -- Bits are added to (or removed from) the vector on the highest (left) or the lowest (right) position
   -- example:
   --   constant A : unsigned(10-1 downto 5) := "01001";
   --   constant B : unsigned( 4-1 downto 0) := resize_left(A,4);
   --   constant C : unsigned( 7-1 downto 0) := resize_right(A,7);
   --   -> B=="1001" and C=="0100100"
   alias resize_left is resize [unsigned,natural return unsigned]; -- defined in numeric_std
   alias resize_left is resize [signed,natural return signed]; -- defined in numeric_std
   function resize_right(vector : unsigned; new_width : natural) return unsigned;
   function resize_right(vector : signed; new_width : natural) return signed;

   -- Enlarge the given 'vector' by adding 'width_addition' bits to the highest (left) or lowest (right) position
   -- example:
   --    constant A : unsigned(10-1 downto 5) := "01001";
   --    constant B : unsigned(12-1 downto 5) := enlarge_left(A,2);
   --    constant C : unsigned( 8-1 downto 5) := enlarge_right(A,-2);
   --    -> B=="0001001" and C=="010"
   function enlarge_left(vector : unsigned; width_addition : integer) return unsigned;
   function enlarge_left(vector : signed; width_addition : integer) return signed;
   function enlarge_right(vector : unsigned; width_addition : integer) return unsigned;
   function enlarge_right(vector : signed; width_addition : integer) return signed;
   
end math_pack;

--! \brief Body of package with basic math functions 
package body math_pack is

   --! \brief Logarithm with base 2.
   function log2 (n : integer) return integer is
      variable a, m : integer;
   begin
      if (n = 1) then
         return 0;
      end if;
      a := 0;
      m := 1;
      while m < n loop
         a := a + 1;
         m := m * 2;
      end loop;
      return a;
   end log2;

   --! \brief Logarithm with base 2.
   function log2 (n : std_logic_vector(31 downto 0)) return integer is
      variable m     : std_logic_vector(32 downto 0);
      variable aux_n : std_logic_vector(32 downto 0);
      variable a     : integer;
   begin
      if (n = X"00000001") then
         return 0;
      end if;
      a     := 0;
      m     := '0' & X"00000001";
      aux_n := '0' & n;
      while m < aux_n loop
         a := a + 1;
         m := m(31 downto 0) & '0';
      end loop;
      return a;
   end log2;

   --! \brief Selects higher number from two given.
   function max(L, R: integer) return integer is
   begin
      if L > R then
         return L;
      else
         return R;
      end if;
   end;
   
   --! \brief Selects lower number from two given.
   function min(L, R: integer) return integer is
   begin
      if L < R then
         return L;
      else
         return R;
      end if;
   end;
   
   --! \brief Selects lower number from two given.
   function minimum(L, R: integer) return integer is
   begin
      if L < R then
         return L;
      else
         return R;
      end if;
   end;

   --! \brief Integer roundup division.
   function div_roundup(dividend, divisor: integer) return integer is
   begin
      if dividend mod divisor = 0 then
         return dividend / divisor;
      else
         return (dividend / divisor) + 1;
      end if;
   end;

    function count_ones(slv : std_logic_vector) return natural is
        variable n_ones : natural := 0;
    begin
        for i in slv'range loop
            if slv(i) = '1' then
                n_ones := n_ones + 1;
            end if;
        end loop;
        return n_ones;
    end;

   --! \brief Ternary conditional assignment operator (like ?: in C).
   function tsel(cond : boolean; true_val: integer; false_val: integer) return integer is
   begin
      if cond then
         return true_val;
      else
         return false_val;
      end if;
   end;

   function tsel(cond : boolean; true_val: real; false_val: real) return real is
   begin
      if cond then
         return true_val;
      else
         return false_val;
      end if;
   end;

   function tsel(cond : boolean; true_val: std_logic; false_val: std_logic) return std_logic is
   begin
      if cond then
         return true_val;
      else
         return false_val;
      end if;
   end;

   function tsel(cond : boolean; true_val: bit; false_val: bit) return bit is
   begin
      if cond then
         return true_val;
      else
         return false_val;
      end if;
   end;

   function tsel(cond : boolean; true_val: std_logic_vector; false_val: std_logic_vector) return std_logic_vector is
   begin
      assert true_val'length = false_val'length report "TSEL: Selection between vectors of different lengths!" severity FAILURE;
      if cond then
         return true_val;
      else
         return false_val;
      end if;
   end;

   function tsel(cond : boolean; true_val: string; false_val: string) return string is
   begin
      if cond then
         return true_val;
      else
         return false_val;
      end if;
   end;


   function ceil(x,base : integer) return integer is
     variable m : integer;
   begin
     m := x mod base;
     if(m = 0) then
       return x;
     else
       return x + (base - m);
     end if;
   end;

   function round_up(value : std_logic_vector; rounding_width : natural) return std_logic_vector is
      variable v : std_logic_vector(value'high downto value'low);
   begin
      v := std_logic_vector(round_up(unsigned(value),rounding_width));
      return v;
   end;

   function round_up(value : unsigned;  rounding_width : natural) return unsigned is
      variable v : unsigned(value'high downto value'low);
   begin
      v := value;
      v(value'low+rounding_width-1 downto value'low) := (others => '0');
      if ((or value(value'low+rounding_width-1 downto value'low))='1') then
          v := v+2**rounding_width;
      end if;
      return v;
   end;

   function round_up(value : signed; rounding_width : natural) return signed is
      variable v : signed(value'high downto value'low);
   begin
      -- works the same for positive and negative numbers in binary 2's complement
      v := signed(round_up(unsigned(value),rounding_width));
      return v;
   end;

   function round_up(value : integer; rounding_width : natural) return integer is
      variable v : integer;
   begin
      v := to_integer(round_up(to_unsigned(value,32),rounding_width));
      return v;
   end;

   function round_down(value : std_logic_vector; rounding_width : natural) return std_logic_vector is
      variable v : std_logic_vector(value'high downto value'low);
   begin
      v := std_logic_vector(round_down(unsigned(value),rounding_width));
      return v;
   end;

   function round_down(value : unsigned; rounding_width : natural) return unsigned is
      variable v : unsigned(value'high downto value'low);
   begin
      v := value;
      v(value'low+rounding_width-1 downto value'low) := (others => '0');
      return v;
   end;

   function round_down(value : signed; rounding_width : natural) return signed is
      variable v : signed(value'high downto value'low);
   begin
      -- works the same for positive and negative numbers in binary 2's complement
      v := signed(round_down(unsigned(value),rounding_width));
      return v;
   end;

   function round_down(value : integer; rounding_width : natural) return integer is
      variable v : integer;
   begin
      v := to_integer(round_down(to_unsigned(value,32),rounding_width));
      return v;
   end;

   function resize_right(vector : unsigned; new_width : natural) return unsigned is
   begin
      return enlarge_right(vector,new_width-vector'length);
   end;

   function resize_right(vector : signed; new_width : natural) return signed is
   begin
      return enlarge_right(vector,new_width-vector'length);
   end;

   function enlarge_left(vector : unsigned; width_addition : integer) return unsigned is
   begin
      return resize(vector,vector'length+width_addition);
   end;

   function enlarge_left(vector : signed; width_addition : integer) return signed is
   begin
      return resize(vector,vector'length+width_addition);
   end;

   function enlarge_right(vector : unsigned; width_addition : integer) return unsigned is
      variable v : unsigned(width_addition+vector'high downto vector'low);
   begin
      if (width_addition>=0) then
         v(width_addition+vector'high downto width_addition+vector'low) := vector;
         v(width_addition+vector'low-1 downto vector'low) := (others => '0');
      else
         v := (others => '0');
         v(width_addition+vector'high downto vector'low) := vector(vector'high downto vector'low-width_addition);
      end if;
      return v;
   end;

   function enlarge_right(vector : signed; width_addition : integer) return signed is
      variable v : signed(width_addition+vector'high downto vector'low);
   begin
      if (width_addition>=0) then
         v(width_addition+vector'high downto width_addition+vector'low) := vector;
         v(width_addition+vector'low-1 downto vector'low) := (others => '0');
      else
         v := (others => '0');
         v(width_addition+vector'high downto vector'low) := vector(vector'high downto vector'low-width_addition);
      end if;
      return v;
   end;

   -- ----------------------------------------------------------------------
end math_pack;

