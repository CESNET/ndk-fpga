-- dut.vhd:
-- Copyright (C) 2015 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity MI_MEMORY is
   generic (
      ITEMS        : integer := 1024
   );
   port(
      -- Master interface
      CLK          : in  std_logic;
      RESET        : in  std_logic;
      MI_DWR       : in  std_logic_vector(31 downto 0);   -- Input Data
      MI_ADDR      : in  std_logic_vector(31 downto 0);   -- Address
      MI_RD        : in  std_logic;                       -- Read Request
      MI_WR        : in  std_logic;                       -- Write Request
      MI_BE        : in  std_logic_vector(3  downto 0);   -- Byte Enable
      MI_DRD       : out std_logic_vector(31 downto 0);   -- Output Data
      MI_ARDY      : out std_logic;                       -- Address Ready
      MI_DRDY      : out std_logic                       -- Data Ready
   );
end entity;

architecture full of MI_MEMORY is

   type memory_t is array(0 to ITEMS-1) of std_logic_vector(31 downto 0);
   signal memory : memory_t := (others => (others => '0'));

begin

   mem : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         if MI_WR='1' then
            memory(conv_integer(MI_ADDR(log2(ITEMS)+1 downto 2))) <= MI_DWR;
         end if;
         MI_DRD  <= memory(conv_integer(MI_ADDR(log2(ITEMS)+1 downto 2)));
         MI_DRDY <= MI_RD and not MI_WR;
      end if;
   end process;

   MI_ARDY <= MI_RD or MI_WR;

end architecture full;
