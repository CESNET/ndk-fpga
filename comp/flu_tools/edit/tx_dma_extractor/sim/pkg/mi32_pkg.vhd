--! \author Mario Kuka <kuka@cesnet.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;

package mi32_pkg is
   signal per : time;

   type mi32_t is record
      ADDR         : std_logic_vector(31 downto 0);
      WR           : std_logic;
      DWR          : std_logic_vector(31 downto 0);
      RD           : std_logic;
      DRD          : std_logic_vector(31 downto 0);
      DRDY         : std_logic;
      ARDY         : std_logic;
      BE           : std_logic_vector(3 downto 0);
   end record;

   procedure mi32_init (
      signal mi32 : inout mi32_t
   );

   procedure mi32_write (
      signal mi32 : inout mi32_t
   );

   procedure mi32_write_be (
      signal mi32 : inout mi32_t
   );

   procedure mi32_read (
      signal mi32 : inout mi32_t
   );
end package;

package body mi32_pkg is
   procedure mi32_init (
      signal mi32 : inout mi32_t
   ) is
   begin
      mi32.ADDR <= (others => '0');
      mi32.WR   <= '0';
      mi32.DWR  <= (others => '0');
      mi32.RD   <= '0';
      mi32.BE   <= (others => '0');
   end procedure;


   procedure mi32_write (
      signal mi32 : inout mi32_t
   ) is
   begin
      mi32.WR <= '1';
      mi32.BE <= (others => '1');
      while mi32.ARDY = '0' loop
         wait for per;
      end loop;
      wait for per;
      mi32.WR <= '0';
   end procedure;

   procedure mi32_write_be (
      signal mi32 : inout mi32_t
   ) is
   begin
      mi32.WR <= '1';
      mi32.BE <= "0001";
      while mi32.ARDY = '0' loop
         wait for per;
      end loop;
      wait for per;

      mi32.WR <= '1';
      mi32.BE <= "0010";
      while mi32.ARDY = '0' loop
         wait for per;
      end loop;
      wait for per;

      mi32.WR <= '1';
      mi32.BE <= "0100";
      while mi32.ARDY = '0' loop
         wait for per;
      end loop;
      wait for per;

      mi32.WR <= '1';
      mi32.BE <= "1000";
      while mi32.ARDY = '0' loop
         wait for per;
      end loop;
      wait for per;

      mi32.WR <= '0';
   end procedure;

   procedure mi32_read (
      signal mi32 : inout mi32_t
   ) is
   begin
      mi32.RD <= '1';
      while mi32.ARDY = '0' loop
         wait for per;
      end loop;
      wait for per;
      mi32.RD <= '0';
   end procedure;
end mi32_pkg;
