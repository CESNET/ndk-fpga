-- type_pack.vhd: Definitions with special data types
-- Copyright (C) 2016 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

package type_pack is

  -- Vector of integers.
  -- type integer_vector is array(integer range <>) of integer; -- VHDL-2008 adds the same integer_vector as standard type

  -- Selection of maximum value from vector of integers.
  function max(v : integer_vector) return integer;

  -- Vector of bits.
  function conv_bit_vector(v : natural; l : natural) return bit_vector;

  -- Array of std_logic_vector
  -- type slv_array_t is array (natural range <>) of std_logic_vector
  type slv_array_t is array (natural range <>) of std_logic_vector;

  function slv_array_ser(slv_array: slv_array_t; ITEMS_X: integer; DATA_WIDTH: integer) return std_logic_vector;
  function slv_array_ser(slv_array: slv_array_t) return std_logic_vector;

  -- default version is downto_deser
  function slv_array_deser(slv_array: std_logic_vector; ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t;
  function slv_array_deser(slv_array: std_logic_vector; ITEMS_X: integer) return slv_array_t;

  function slv_array_downto_deser(slv_array: std_logic_vector; ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t;
  function slv_array_downto_deser(slv_array: std_logic_vector; ITEMS_X: integer) return slv_array_t;
  function slv_array_to_deser(slv_array: std_logic_vector; ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t;
  function slv_array_to_deser(slv_array: std_logic_vector; ITEMS_X: integer) return slv_array_t;

  -- Utility function designed to extract a specific range of bits from each element within slv_array_t.
  -- This function returns a new array where each element is a sliced portion of the original array's elements.
  function slv_array_slice (arr: slv_array_t; hi, lo: natural) return slv_array_t;

  -- Array of std_array_t
  -- type slv_array_2d_t is array (natural range <>) of slv_array_t
  type slv_array_2d_t is array (natural range <>) of slv_array_t;

  function slv_array_2d_ser(slv_array_2d: slv_array_2d_t; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return std_logic_vector;
  function slv_array_2d_ser(slv_array_2d: slv_array_2d_t) return std_logic_vector;

  -- default version is downto_deser
  function slv_array_2d_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return slv_array_2d_t;
  function slv_array_2d_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer) return slv_array_2d_t;

  function slv_array_2d_downto_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return slv_array_2d_t;
  function slv_array_2d_to_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return slv_array_2d_t;

  -- Array of slv_array_2d_t
  -- type slv_array_3d_t is array (natural range <>) of slv_array_2d_t
  type slv_array_3d_t is array (natural range <>) of slv_array_2d_t;

  -- Other arrays
  type u_array_t is array (natural range <>) of unsigned;
  type u_array_2d_t is array (natural range <>) of u_array_t;
  type u_array_3d_t is array (natural range <>) of u_array_2d_t;
  type s_array_t is array (natural range <>) of signed;
  type s_array_2d_t is array (natural range <>) of s_array_t;
  type s_array_3d_t is array (natural range <>) of s_array_2d_t;
  alias i_array_t is integer_vector;
  type i_array_2d_t is array (natural range <>) of i_array_t;
  type i_array_3d_t is array (natural range <>) of i_array_2d_t;
  type n_array_t is array (natural range <>) of natural;
  type n_array_2d_t is array (natural range <>) of n_array_t;
  type n_array_3d_t is array (natural range <>) of n_array_2d_t;
  type b_array_t is array (natural range <>) of boolean;
  type b_array_2d_t is array (natural range <>) of b_array_t;
  type b_array_3d_t is array (natural range <>) of b_array_2d_t;
  type str_array_t is array (natural range <>) of string;

  -- Conversion functions
  -- std_logic_vector -> unsigned
  function slv_arr_to_u_arr   (slv_array   : slv_array_t) return u_array_t;
  function slv_arr_to_u_arr_2d(slv_array_2d: slv_array_2d_t) return u_array_2d_t;
  -- unsigned -> std_logic_vector
  function u_arr_to_slv_arr   (u_array   : u_array_t) return slv_array_t;
  function u_arr_to_slv_arr_2d(u_array_2d: u_array_2d_t) return slv_array_2d_t;

  -- Serialize array of strings
  function str_array_ser(str_array: str_array_t) return string;
  -- Serialize array of strings in reverse order (item(0) will be on the left)
  function str_array_ser_rev(str_array: str_array_t) return string;

  -- Sumation of different types of array
  function sum(v : slv_array_t) return std_logic_vector;
  function sum(v :   u_array_t) return unsigned;
  function sum(v :   s_array_t) return signed;
  function sum(v :   i_array_t) return integer;
  function sum(v :   n_array_t) return integer;

  -- Make and absolute value from a signed vector.
  function absolute    (v : signed) return signed;
  -- Same as function "absolute" with a conversion to unsigned at the end.
  function absolute2uns(v : signed) return unsigned;
  -- Same as function "absolute2uns" with a conversion to std_logic_vector at the end.
  function absolute2slv(v : signed) return std_logic_vector;

  pure function resize(in_val : std_logic_vector; in_size : natural) return std_logic_vector;

end type_pack;

package body type_pack is

  function max(v : integer_vector) return integer is
    variable m : integer;
  begin
    m := integer'low;
    for i in v'low to v'high loop
      if v(i) > m then
        m := v(i);
      end if;
    end loop;
    return m;
  end function;

  function sum(v : slv_array_t) return std_logic_vector is
     variable s : integer := 0;
  begin
     if (v'length=0) then
         return (-1 downto 0 => '0'); -- null vector
     end if;
     for i in v'low to v'high loop
        s := s + to_integer(unsigned(v(i)));
     end loop;
     return std_logic_vector(to_unsigned(s,log2(v'length)+v(0)'length));
  end;

  function sum(v :   u_array_t) return unsigned is
     variable s : integer := 0;
  begin
     if (v'length=0) then
         return (-1 downto 0 => '0'); -- null vector
     end if;
     for i in v'low to v'high loop
        s := s + to_integer(v(i));
     end loop;
     return to_unsigned(s,log2(v'length)+v(0)'length);
  end;

  function sum(v :   s_array_t) return signed is
     variable s : integer := 0;
  begin
     if (v'length=0) then
         return (-1 downto 0 => '0'); -- null vector
     end if;
     for i in v'low to v'high loop
        s := s + to_integer(v(i));
     end loop;
     return to_signed(s,log2(v'length)+v(0)'length);
  end;

  function sum(v :   i_array_t) return integer is
     variable s : integer := 0;
  begin
     for i in v'low to v'high loop
        s := s + v(i);
     end loop;
     return s;
  end;

  function sum(v :   n_array_t) return integer is
     variable s : natural := 0;
  begin
     for i in v'low to v'high loop
        s := s + v(i);
     end loop;
     return s;
  end;

  function absolute(v : signed) return signed is
  begin
     if (v(v'high) = '0') then
        return v; -- no change when it is positive
     end if;
     return -v;
  end;

  function absolute2uns(v : signed) return unsigned is
  begin
     return unsigned(absolute(v));
  end;

  function absolute2slv(v : signed) return std_logic_vector is
  begin
     return std_logic_vector(absolute2uns(v));
  end;

  function conv_bit_vector(v : natural; l : natural) return bit_vector is
    variable ret : bit_vector(l-1 downto 0);
    variable vv : natural := v;
  begin
    ret := (others => '0');
    for i in 0 to l-1 loop
      if (vv mod 2) = 1 then
        ret(i) := '1';
      end if;
      vv := vv / 2;
    end loop;
    if vv /= 0 then
      assert false report "CONV_BIT_VECTOR: vector truncated" severity WARNING;
    end if;
    return ret;
  end function;

   function slv_array_ser(slv_array: slv_array_t; ITEMS_X: integer; DATA_WIDTH: integer) return std_logic_vector is
      variable rv : std_logic_vector(ITEMS_X*DATA_WIDTH-1 downto 0);
   begin
      for i in 0 to ITEMS_X-1 loop
         rv((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH) := slv_array(i);
      end loop;
      return rv;
   end;

   function slv_array_ser(slv_array: slv_array_t) return std_logic_vector is
   begin
      if (slv_array'length=0) then
          return (-1 downto 0 => 'X'); -- null std_logic_vector
      else
          return slv_array_ser(slv_array,slv_array'length,slv_array(0)'length);
      end if;
   end function;

   function slv_array_downto_deser(slv_array: std_logic_vector; ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t is
      variable rv : slv_array_t(ITEMS_X-1 downto 0)(DATA_WIDTH-1 downto 0);
   begin
      for i in 0 to ITEMS_X-1 loop
         rv(i) := slv_array((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH);
      end loop;
      return rv;
   end;

   function slv_array_downto_deser(slv_array: std_logic_vector; ITEMS_X: integer) return slv_array_t is
      variable DATA_WIDTH : integer := 0;
   begin
      if (ITEMS_X=0) then
         return (0 downto 1 => "X"); -- null slv_array
      else
         DATA_WIDTH := slv_array'length/ITEMS_X;
         assert ((ITEMS_X*DATA_WIDTH)=slv_array'length)
            report "ERROR : TYPE_PACK : slv_array_downto_deser : The width of the given std_logic_vector is not divisible by the number of items it is supposed to be deserialized to!"
            severity failure;
         return slv_array_downto_deser(slv_array,ITEMS_X,DATA_WIDTH);
      end if;
   end function;

   function slv_array_to_deser(slv_array: std_logic_vector; ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t is
      variable rv : slv_array_t(0 to ITEMS_X-1)(DATA_WIDTH-1 downto 0);
   begin
      for i in 0 to ITEMS_X-1 loop
         rv(i) := slv_array((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH);
      end loop;
      return rv;
   end;

   function slv_array_to_deser(slv_array: std_logic_vector; ITEMS_X: integer) return slv_array_t is
      variable DATA_WIDTH : integer := 0;
   begin
      if (ITEMS_X=0) then
         return (1 to 0 => "X"); -- null slv_array
      else
         DATA_WIDTH := slv_array'length/ITEMS_X;
         assert ((ITEMS_X*DATA_WIDTH)=slv_array'length)
            report "ERROR : TYPE_PACK : slv_array_to_deser : The width of the given std_logic_vector is not divisible by the number of items it is supposed to be deserialized to!"
            severity failure;
         return slv_array_to_deser(slv_array,ITEMS_X,DATA_WIDTH);
      end if;
   end function;

   function slv_array_deser(slv_array: std_logic_vector; ITEMS_X: integer; DATA_WIDTH: integer) return slv_array_t is
   begin
      return slv_array_downto_deser(slv_array,ITEMS_X,DATA_WIDTH);
   end;

   function slv_array_deser(slv_array: std_logic_vector; ITEMS_X: integer) return slv_array_t is
   begin
      return slv_array_downto_deser(slv_array,ITEMS_X);
   end function;

   function slv_array_slice (arr: slv_array_t; hi, lo: natural) return slv_array_t is
      variable ret    : slv_array_t(arr'range)(hi-lo downto 0);
   begin
      for i in arr'range loop
          ret(i) := arr(i)(hi downto lo);
      end loop;
      return ret;
   end function;

   function slv_array_2d_ser(slv_array_2d: slv_array_2d_t; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return std_logic_vector is
      variable rv : std_logic_vector(ITEMS_X*ITEMS_Y*DATA_WIDTH-1 downto 0);
   begin
      for i in 0 to ITEMS_X-1 loop
         for j in 0 to ITEMS_Y-1 loop
            rv(i*(ITEMS_Y*DATA_WIDTH)+(j+1)*DATA_WIDTH-1 downto i*(ITEMS_Y*DATA_WIDTH)+j*DATA_WIDTH) := slv_array_2d(i)(j);
         end loop;
      end loop;
      return rv;
   end;

   function slv_array_2d_ser(slv_array_2d: slv_array_2d_t) return std_logic_vector is
   begin
      if (slv_array_2d'length=0) then
         return (-1 downto 0 => '0'); -- null vector
      elsif (slv_array_2d(0)'length=0) then
         return (-1 downto 0 => '0'); -- null vector
      else
         return slv_array_2d_ser(slv_array_2d,slv_array_2d'length,slv_array_2d(0)'length,slv_array_2d(0)(0)'length);
      end if;
   end;

   function slv_array_2d_downto_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return slv_array_2d_t is
      variable rv : slv_array_2d_t(ITEMS_X-1 downto 0)(ITEMS_Y-1 downto 0)(DATA_WIDTH-1 downto 0);
   begin
      for i in 0 to ITEMS_X-1 loop
         for j in 0 to ITEMS_Y-1 loop
            rv(i)(j) := slv_array_2d(i*(ITEMS_Y*DATA_WIDTH)+(j+1)*DATA_WIDTH-1 downto i*(ITEMS_Y*DATA_WIDTH)+j*DATA_WIDTH);
         end loop;
      end loop;
      return rv;
   end;

   function slv_array_2d_downto_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer) return slv_array_2d_t is
      variable DATA_WIDTH : integer := 0;
   begin
      if (ITEMS_X=0 or ITEMS_Y=0) then
         return (0 downto 1 => (0 downto 1 => "X")); -- null slv_array_2d
      else
         DATA_WIDTH := slv_array_2d'length/ITEMS_X/ITEMS_Y;
         assert ((ITEMS_X*ITEMS_Y*DATA_WIDTH)=slv_array_2d'length)
            report "ERROR : TYPE_PACK : slv_array_2d_downto_deser : The width of the given std_logic_vector is not divisible by the number of items it is supposed to be deserialized to!"
            severity failure;
         return slv_array_2d_downto_deser(slv_array_2d,ITEMS_X,ITEMS_Y,DATA_WIDTH);
      end if;
   end;

   function slv_array_2d_to_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return slv_array_2d_t is
      variable rv : slv_array_2d_t(0 to ITEMS_X-1)(0 to ITEMS_Y-1)(DATA_WIDTH-1 downto 0);
   begin
      for i in 0 to ITEMS_X-1 loop
         for j in 0 to ITEMS_Y-1 loop
            rv(i)(j) := slv_array_2d(i*(ITEMS_Y*DATA_WIDTH)+(j+1)*DATA_WIDTH-1 downto i*(ITEMS_Y*DATA_WIDTH)+j*DATA_WIDTH);
         end loop;
      end loop;
      return rv;
   end;

   function slv_array_2d_to_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer) return slv_array_2d_t is
      variable DATA_WIDTH : integer := 0;
   begin
      if (ITEMS_X=0 or ITEMS_Y=0) then
         return (1 to 0 => (1 to 0 => "X")); -- null slv_array_2d
      else
         DATA_WIDTH := slv_array_2d'length/ITEMS_X/ITEMS_Y;
         assert ((ITEMS_X*ITEMS_Y*DATA_WIDTH)=slv_array_2d'length)
            report "ERROR : TYPE_PACK : slv_array_2d_to_deser : The width of the given std_logic_vector is not divisible by the number of items it is supposed to be deserialized to!"
            severity failure;
         return slv_array_2d_to_deser(slv_array_2d,ITEMS_X,DATA_WIDTH,DATA_WIDTH);
      end if;
   end;

   function slv_array_2d_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer; DATA_WIDTH: integer) return slv_array_2d_t is
   begin
      return slv_array_2d_downto_deser(slv_array_2d,ITEMS_X,ITEMS_Y,DATA_WIDTH);
   end;

   function slv_array_2d_deser(slv_array_2d: std_logic_vector; ITEMS_X: integer; ITEMS_Y: integer) return slv_array_2d_t is
   begin
      return slv_array_2d_downto_deser(slv_array_2d,ITEMS_X,ITEMS_Y);
   end;

   function slv_arr_to_u_arr(slv_array: slv_array_t) return u_array_t is
      variable u_array : u_array_t(slv_array               'high downto slv_array               'low)
                                  (slv_array(slv_array'low)'high downto slv_array(slv_array'low)'low);
   begin
      for i in slv_array'low to slv_array'high loop
         u_array(i) := unsigned(slv_array(i));
      end loop;
      return u_array;
   end;

   function slv_arr_to_u_arr_2d(slv_array_2d: slv_array_2d_t) return u_array_2d_t is
      variable u_array_2d : u_array_2d_t(slv_array_2d                                                      'high downto slv_array_2d                                                      'low)
                                        (slv_array_2d(slv_array_2d'low)                                    'high downto slv_array_2d(slv_array_2d'low)                                    'low)
                                        (slv_array_2d(slv_array_2d'low)(slv_array_2d(slv_array_2d'low)'low)'high downto slv_array_2d(slv_array_2d'low)(slv_array_2d(slv_array_2d'low)'low)'low);
   begin
      for i in slv_array_2d'low to slv_array_2d'high loop
         u_array_2d(i) := slv_arr_to_u_arr(slv_array_2d(i));
      end loop;
      return u_array_2d;
   end;

   function u_arr_to_slv_arr(u_array: u_array_t) return slv_array_t is
      variable slv_array : slv_array_t(u_array             'high downto u_array             'low)
                                      (u_array(u_array'low)'high downto u_array(u_array'low)'low);
   begin
      for i in u_array'low to u_array'high loop
         slv_array(i) := std_logic_vector(u_array(i));
      end loop;
      return slv_array;
   end;

   function u_arr_to_slv_arr_2d(u_array_2d: u_array_2d_t) return slv_array_2d_t is
      variable slv_array_2d : slv_array_2d_t(u_array_2d                                                'high downto u_array_2d                                                'low)
                                            (u_array_2d(u_array_2d'low)                                'high downto u_array_2d(u_array_2d'low)                                'low)
                                            (u_array_2d(u_array_2d'low)(u_array_2d(u_array_2d'low)'low)'high downto u_array_2d(u_array_2d'low)(u_array_2d(u_array_2d'low)'low)'low);
   begin
      for i in u_array_2d'low to u_array_2d'high loop
         slv_array_2d(i) := u_arr_to_slv_arr(u_array_2d(i));
      end loop;
      return slv_array_2d;
   end;

   pure function resize(in_val : std_logic_vector; in_size : natural) return std_logic_vector is
   begin
        return std_logic_vector(resize(unsigned(in_val), in_size));
   end function;

   function str_array_ser(str_array: str_array_t) return string is
      variable ret : string(1 to str_array'length*(str_array(str_array'low)'length));
   begin
      for i in str_array'low to str_array'high loop
         ret(i*str_array(str_array'low)'length+1 to (i+1)*str_array(str_array'low)'length) := str_array(i);
      end loop;
      return ret;
   end;

   function str_array_ser_rev(str_array: str_array_t) return string is
      variable ret : string(1 to str_array'length*(str_array(str_array'low)'length));
   begin
      for i in str_array'low to str_array'high loop
         ret(i*str_array(str_array'low)'length+1 to (i+1)*str_array(str_array'low)'length) := str_array(str_array'high-i);
      end loop;
      return ret;
   end;

end type_pack;

