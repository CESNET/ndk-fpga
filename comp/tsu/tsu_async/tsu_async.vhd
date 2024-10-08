-- tsu_async.vhd: component which makes async ts and ts_dv signal to
--                synchronous.
-- Copyright (C) 2014 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
--            Jan Kucera <xkucer73@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity tsu_async is
 -- PORTS
 port (
   -- Input interface
   IN_CLK         : in std_logic;
   IN_RESET       : in std_logic;

   IN_TS          : in std_logic_vector(63 downto 0);
   IN_TS_NS       : in std_logic_vector(63 downto 0) := (others => '0');
   IN_TS_DV       : in std_logic;

   -- Output interface
   OUT_CLK        : in std_logic;
   OUT_RESET      : in std_logic;

   OUT_TS         : out std_logic_vector(63 downto 0);
   OUT_TS_NS      : out std_logic_vector(63 downto 0);
   OUT_TS_DV      : out std_logic
 );
end tsu_async;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of tsu_async is

   signal data_in            : std_logic_vector(127 downto 0);
   signal data_full          : std_logic;
   signal data_write         : std_logic;

   signal data_out           : std_logic_vector(127 downto 0);
   signal data_reg           : std_logic_vector(127 downto 0);
   signal data_empty         : std_logic;

begin

   data_in <= IN_TS & IN_TS_NS;
   data_write <= IN_TS_DV and not data_full;

   ts_data_asfifo : entity work.asfifo
   generic map (
      -- Data Width
      DATA_WIDTH   => 128,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS        => 8,
      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH => 2
   )
   port map (
      -- Write interface
      CLK_WR   => IN_CLK,
      RST_WR   => IN_RESET,
      DI       => data_in,
      WR       => data_write,
      FULL     => data_full,
      STATUS   => open,

      -- Read interface
      CLK_RD   => OUT_CLK,
      RST_RD   => OUT_RESET,
      DO       => data_out,
      RD       => '1',
      EMPTY    => data_empty
   );

   data_reg_p: process(OUT_CLK)
   begin
      if (OUT_CLK'event and OUT_CLK = '1') then
         if (data_empty = '0') then
            data_reg <= data_out;
         end if;
      end if;
   end process;

   OUT_TS    <= data_reg(127 downto 64);
   OUT_TS_NS <= data_reg(63 downto 0);
   OUT_TS_DV <= '1';

end architecture behavioral;
