-- width_conv_4to1.vhd: Bus width conversion from x4 to x1 (slow to fast clock)
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

entity width_conv_4to1 is
generic (
   DATA_WIDTH : natural := 256; -- Input data width
   DATA_WIDTH1 : natural:= 32   -- Input data (D1) width
);
port (
   CLKx1  : in  std_logic;
   D      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
   D1     : in  std_logic_vector(DATA_WIDTH1-1 downto 0) := (others => '0');
   D_EN   : in  std_logic := '1';
   --
   CLKx4  : in  std_logic;
   Q      : out std_logic_vector(DATA_WIDTH/4-1 downto 0);
   Q1     : out std_logic_vector(DATA_WIDTH1/4-1 downto 0);
   Q_EN   : out  std_logic
);
end entity;

architecture behavioral of width_conv_4to1 is

signal edge   : std_logic;
signal cycle  : std_logic_vector(1 downto 0) := "00";
signal sync, sync_r, sync_r2  : std_logic := '0';
signal d_resync : std_logic_vector(DATA_WIDTH-1 downto 0);
signal d1_resync: std_logic_vector(DATA_WIDTH1-1 downto 0);
signal en_resync: std_logic;

begin

WDTH_CONV_FFS: process(CLKx4)
begin
   if CLKx4'event and CLKx4 = '1' then
      -- Synchronize slow and fast clock data MUX
      sync_r <= sync;
      sync_r2 <= sync_r;
      edge <= sync_r xor sync_r2;
      if edge = '1' then
         cycle <= "00";
      else
         cycle <= cycle + 1;
      end if;
      case cycle is
          when "00"   => Q <= d_resync (1*(DATA_WIDTH/4)-1  downto 0*(DATA_WIDTH/4));
                         Q1<= d1_resync(1*(DATA_WIDTH1/4)-1 downto 0*(DATA_WIDTH1/4));
          when "01"   => Q <= d_resync (2*(DATA_WIDTH/4)-1  downto 1*(DATA_WIDTH/4));
                         Q1<= d1_resync(2*(DATA_WIDTH1/4)-1 downto 1*(DATA_WIDTH1/4));
          when "10"   => Q <= d_resync (3*(DATA_WIDTH/4)-1  downto 2*(DATA_WIDTH/4));
                         Q1<= d1_resync(3*(DATA_WIDTH1/4)-1 downto 2*(DATA_WIDTH1/4));
          when others => Q <= d_resync (4*(DATA_WIDTH/4)-1  downto 3*(DATA_WIDTH/4));
                         Q1<= d1_resync(4*(DATA_WIDTH1/4)-1 downto 3*(DATA_WIDTH1/4));
      end case;
      Q_EN <= en_resync;
      -- Sample data on edge 3
      if cycle = "11" then
         d_resync  <= D;
         d1_resync <= D1;
         en_resync <= D_EN;
      end if;
   end if;
end process;

SYNC_FF: process(CLKx1)
begin
   if CLKx1'event and CLKx1 = '1' then
      sync <= not sync;
   end if;
end process;

-- Following constraints should be added (for Vivado synthesis):
--    set_multicycle_path -end -setup -to [get_pins {d?_resync_reg[*]/D}] 4
--    set_multicycle_path -end -hold  -to [get_pins {d?_resync_reg[*]/D}] 3
--    set_multicycle_path -end -setup -from [get_pins {d?_resync_reg[2*DATA_WIDTH-1:1*DATA_WIDTH]/D}] -to [get_pins {Q?_reg[*]/D}] 2
--    set_multicycle_path -end -setup -from [get_pins {d?_resync_reg[3*DATA_WIDTH-1:2*DATA_WIDTH]/D}] -to [get_pins {Q?_reg[*]/D}] 3
--    set_multicycle_path -end -setup -from [get_pins {d?_resync_reg[4*DATA_WIDTH-1:3*DATA_WIDTH]/D}] -to [get_pins {Q?_reg[*]/D}] 4
--    set_multicycle_path -end -hold  -from [get_pins {d?_resync_reg[2:DATA_WIDTH-1:1*DATA_WIDTH]/D}] -to [get_pins {Q?_reg[*]/D}] 1
--    set_multicycle_path -end -hold  -from [get_pins {d?_resync_reg[3:DATA_WIDTH-1:2*DATA_WIDTH]/D}] -to [get_pins {Q?_reg[*]/D}] 2
--    set_multicycle_path -end -hold  -from [get_pins {d?_resync_reg[4:DATA_WIDTH-1:3*DATA_WIDTH]/D}] -to [get_pins {Q?_reg[*]/D}] 3

end behavioral;
