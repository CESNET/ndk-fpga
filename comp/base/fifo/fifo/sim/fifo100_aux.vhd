--
-- fifo100aux.vhd: - auxiliary file ONLY FOR TESTING FIFO at 100MHz
--
-- Copyright (C) 2003 CESNET
-- Author(s): Pecenka Tomas pecenka@liberouter.org
--            Pus Viktor pus@liberouter.org
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FIFO100_AUX is
   generic (
      data_width     : integer := 16;
      items          : integer := 17;
      block_size     : integer := 4
      );
   port(
      -- =================
      -- FIFO reset
      -- =================

      -- FIFO reset signal
      RESET     : in std_logic;

      -- ================
      -- FIFO input part
      -- ================
      -- Data input
      DATA_IN   : in std_logic_vector((data_width-1) downto 0);
      -- Write request
      WRITE_REQ : in std_logic;

      -- =================
      -- FIFO output part
      -- =================

      -- Data output
      DATA_OUT  : out std_logic_vector((data_width-1) downto 0);
      -- Read request
      READ_REQ  : in std_logic;

      -- ============================
      -- FIFO full and empty signals
      -- ============================

      -- FIFO is empty
      EMPTY     : out std_logic;
      -- FIFO is full
      FULL      : out std_logic;
      LSTBLK    : out std_logic;

      -- =======================
      -- CLK inputs and outputs
      -- =======================

      -- CLK_GEN 50MHz input
      CLK_50    : in std_logic;
      -- CLK_GEN 100MHz locked signal
      CLK_LOCK  : out std_logic;
      -- CLK_GEN 100MHz clock signal
      CLK_100   : out std_logic

   );
end entity FIFO100_AUX;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture fifo100_aux_arch of FIFO100_AUX is

   -- FIFO component ----------------------------------------------------------
   component FIFO is
   generic (
      data_width     : integer;
      items          : integer;
      block_size     : integer
      );
   port(
      RESET    : in std_logic;  -- Global reset signal
      CLK      : in std_logic;  -- Global clock signal

      -- Write interface
      DATA_IN  : in std_logic_vector((data_width-1) downto 0); -- Data input
      WRITE_REQ: in std_logic;  -- Write request
      FULL     : out std_logic; -- FIFO is full
      LSTBLK   : out std_logic;  -- Last block remaining

      -- Read interface
      DATA_OUT : out std_logic_vector((data_width-1) downto 0); -- Data output
      READ_REQ : in std_logic;  -- Read request
      EMPTY    : out std_logic  -- FIFO is empty

   );
   end component FIFO;

   -- clk_gen -----------------------------------------------------------------
   component CLK_GEN is
   Port (
      -- Input
      CLK50_IN    : in  std_logic;     -- Input clock freqvency (50MHz)
      RESET       : in  std_logic;     -- Global reset signal
      -- Output
      CLK50_OUT   : out std_logic;  -- 50MHz  output clock
      CLK100      : out std_logic;  -- 100MHz output clock
      CLK200      : out std_logic;  -- 200MHz output clock
      LOCK        : out std_logic   -- clock lock
   );
   end component CLK_GEN;

   -- 100MHz clock signal
   signal clk100 : std_logic;

   -- input register
   signal sig_data_in   : std_logic_vector((data_width-1) downto 0);
   signal sig_write_req : std_logic;

   -- output register
   signal sig_data_out  : std_logic_vector((data_width-1) downto 0);
   signal sig_read_req  : std_logic;
   signal sig_empty     : std_logic;
   signal sig_full      : std_logic;
   signal sig_lstblk    : std_logic;

begin
   -- connect CLK_100MHz to output
   CLK_100 <= clk100;

   -- FIFO component ----------------------------------------------------------
   u_fifo: FIFO
   generic map (
      data_width     => data_width,
      items          => items,
      block_size     => block_size
   )
   port map (
      reset     => reset,
      clk       => clk100,

      -- write interface
      data_in   => sig_data_in,
      write_req => sig_write_req,
      full      => sig_full,
      lstblk    => sig_lstblk,

      -- read interface
      data_out  => sig_data_out,
      read_req  => sig_read_req,
      empty     => sig_empty
   );

   -- clk_gen -----------------------------------------------------------------
   u_clk_gen: clk_gen
   port map(
      -- Input
      clk50_in   => CLK_50,   -- Input clock freqvency (50MHz)
      reset      => '0',      -- Global reset signal
      -- Output
      clk50_out  => open,     -- 50MHz  output clock
      clk100     => clk100,   -- 100MHz output clock
      clk200     => open,     -- 200MHz output clock
      lock       => CLK_LOCK  -- 200MHz lock
   );

   -- register reg_input ------------------------------------------------------
   reg_input: process(RESET, clk100)
   begin
      if (RESET = '1') then
         sig_data_in   <= (others => '0');
         sig_write_req <= '0';
         sig_read_req  <= '0';
      elsif (clk100'event AND clk100 = '1') then
         sig_data_in   <= DATA_IN;
         sig_write_req <= WRITE_REQ;
         sig_read_req  <= READ_REQ;
      end if;
   end process;

   -- register reg_output -----------------------------------------------------
   reg_output: process(RESET, clk100)
   begin
      if (RESET = '1') then
         DATA_OUT <= (others => '0');
         EMPTY    <= '0';
         FULL     <= '0';
      elsif (clk100'event AND clk100 = '1') then
         DATA_OUT <= sig_data_out;
         EMPTY    <= sig_empty;
         FULL     <= sig_full;
         LSTBLK   <= sig_lstblk;
      end if;
   end process;

end architecture fifo100_aux_arch;
