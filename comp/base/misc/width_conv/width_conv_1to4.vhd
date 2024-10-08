-- width_conv_1to4.vhd: Bus width conversion from x1 to x4 (fast clock to slow
--                      clock). The second bus D1 (and corresponding Q1 output) are
--                      optional
--                      Clocks must be synchronous with 4 multiple frequency
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_misc.all;

entity width_conv_1to4 is
generic (
   DATA_WIDTH  : natural := 64; -- Input data (D) width
   DATA_WIDTH1 : natural :=  8; -- Input data (D1) width
   C3_FF       : boolean := false
);
port (
   CLKx4                 : in  std_logic; -- Fast clock for input D
   D                     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
   D1                    : in  std_logic_vector(DATA_WIDTH1-1 downto 0) := (others => '0');
   --
   CLKx1                 : in  std_logic; -- Slow clock for output Q
   Q                     : out std_logic_vector(4*DATA_WIDTH-1 downto 0);
   Q1                    : out std_logic_vector(4*DATA_WIDTH1-1 downto 0);
   Q_EN                  : in  std_logic := '1'
);
end entity;

architecture behavioral of width_conv_1to4 is

signal edge   : std_logic;
signal edge_r : std_logic;
signal cycle  : std_logic_vector(1 downto 0);
signal sync, sync_r, sync_r2  : std_logic := '0';
signal d_sync : std_logic_vector(Q'range);
signal d1_sync: std_logic_vector(Q1'range);
signal en_sync: std_logic;
signal d_c0 : std_logic_vector(D'range);
signal d1_c0: std_logic_vector(D1'range);
signal d_c1 : std_logic_vector(D'range);
signal d1_c1: std_logic_vector(D1'range);
signal d_c2 : std_logic_vector(D'range);
signal d1_c2: std_logic_vector(D1'range);
signal d_c3 : std_logic_vector(D'range);
signal d1_c3: std_logic_vector(D1'range);

begin

   WDTH_CONV_FFS: process(CLKx4)
   begin
      if CLKx4'event and CLKx4 = '1' then
         -- Synchronize slow and fast clock data MUX
         sync_r  <= sync;
         sync_r2 <= sync_r;
         edge    <= sync_r xor sync_r2;
         edge_r  <= edge;
         if edge_r = '1' then
             cycle <= "00";
         else
            cycle <= cycle + 1;
         end if;
         case cycle is
            when "00"   => d_c0  <= D;-- 3 cycles setup, 2 hold
                           d1_c0 <= D1;
            when "01"   => d_c1  <= D;-- 2 cycles setup, 1 hold
                           d1_c1 <= D1;
            when "10"   => d_c2  <= D; -- 1 cycle setup, 0 hold
                           d1_c2 <= D1;
            when others =>
                           if C3_FF then
                              d_c3  <= D;
                              d1_c3 <= D1;
                           end if;
            null;
         end case;
      end if;
   end process;

   no_c3_ff_g: if (not C3_FF) generate
      d_c3  <= D;
      d1_c3 <= D1;
   end generate;

   SYNC_FF: process(CLKx1)
   begin
      if CLKx1'event and CLKx1 = '1' then
         sync <= not sync;
         if (Q_EN = '1') then
            Q  <= d_c3  & d_c2  & d_c1  & d_c0;
            Q1 <= d1_c3 & d1_c2 & d1_c1 & d1_c0;
         end if;
      end if;
   end process;

end behavioral;
