--
-- sh_fifo.vhd: Shift-registers FIFO
--
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Mikusek <petr.mikusek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sh_fifo is
   generic (
      FIFO_WIDTH     : integer := 16;
      FIFO_DEPTH     : integer := 16; -- depth of FIFO >= 2
      USE_INREG      : boolean := false; -- use registers on input of write ifc.
      USE_OUTREG     : boolean := false  -- use registers on output of read ifc.
   );
   port (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- write interface
      DIN            : in  std_logic_vector(FIFO_WIDTH-1 downto 0);
      WE             : in  std_logic;
      FULL           : out std_logic;

      -- read interface
      DOUT           : out std_logic_vector(FIFO_WIDTH-1 downto 0);
      RE             : in  std_logic;
      EMPTY          : out std_logic;

      -- status
      STATUS         : out std_logic_vector(log2(FIFO_DEPTH)-1 downto 0)
   );
end entity sh_fifo;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of sh_fifo is

   constant ADDR_WIDTH : integer := log2(FIFO_DEPTH);

   type t_shreg is array (0 to FIFO_WIDTH-1)
         of std_logic_vector(FIFO_DEPTH-1 downto 0);

   -- shift registers
   signal shreg         : t_shreg := (others => (others => '0'));
   signal shreg_ce      : std_logic;

   -- address counter
   signal cnt_addr      : std_logic_vector(ADDR_WIDTH-1 downto 0) := (others => '0');
   signal cnt_addr_ce   : std_logic;
   signal cnt_addr_dir  : std_logic;

   -- comparators
   signal cmp_full      : std_logic;
   signal cmp_empty     : std_logic;

   -- optional input register signals
   signal din_int       : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal reg_din       : std_logic_vector(FIFO_WIDTH-1 downto 0)
         := (others => '0');

   signal we_int        : std_logic;
   signal reg_we        : std_logic := '0';

   signal full_int      : std_logic;

   -- optional output register signals
   signal dout_int      : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal reg_dout      : std_logic_vector(FIFO_WIDTH-1 downto 0)
         := (others => '0');

   signal empty_int     : std_logic;
   signal reg_empty     : std_logic := '1';

   signal re_int        : std_logic;

begin

   -- Assertions --------------------------------------------------------------
   assert (FIFO_DEPTH >= 2)
   report "SH_FIFO: FIFO_DEPTH must be greater or equal than 2"
   severity error;

   -- FSM ---------------------------------------------------------------------
   fsm_u: entity work.sh_fifo_fsm
   port map (
      CLK            => CLK,
      RESET          => RESET,

      WE             => we_int,
      RE             => re_int,
      CMP_FULL       => cmp_full,
      CMP_EMPTY      => cmp_empty,

      FULL           => full_int,
      EMPTY          => empty_int,
      CNT_ADDR_CE    => cnt_addr_ce,
      CNT_ADDR_DIR   => cnt_addr_dir,
      SHREG_CE       => shreg_ce
   );

   -- Behaviorally described shift registers ----------------------------------
   shreg_g: for i in 0 to FIFO_WIDTH-1 generate
      shreg_u: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (shreg_ce = '1') then
               shreg(i) <= shreg(i)((FIFO_DEPTH-2) downto 0) & din_int(i);
            end if;
         end if;
      end process;

      dout_int(i) <= shreg(i)(conv_integer(cnt_addr));
   end generate;

   -- Up/down counter ---------------------------------------------------------
   cnt_addr_p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt_addr <= (others => '0');
         elsif (cnt_addr_ce = '1') then
            if (cnt_addr_dir = '1') then
               cnt_addr <= cnt_addr + 1;
            else
               cnt_addr <= cnt_addr - 1;
            end if;
         end if;
      end if;
   end process;

   -- Full and empty comparators ----------------------------------------------
   cmp_full <= '1'
         when (cnt_addr = conv_std_logic_vector(FIFO_DEPTH-2, ADDR_WIDTH))
         else '0';

   cmp_empty <= '1'
         when (cnt_addr = conv_std_logic_vector(0, ADDR_WIDTH))
         else '0';

   -- Optional input registers generation -------------------------------------
   use_inreg_false_g: if (USE_INREG = false) generate
      din_int  <= DIN;
      we_int   <= WE;
      FULL     <= full_int;
   end generate;

   use_inreg_true_g: if (USE_INREG = true) generate
      din_int  <= reg_din;
      we_int   <= reg_we;
      FULL     <= full_int;

      reg_din_p: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (reg_we = '0' or full_int = '0') then
               reg_din <= DIN;
            end if;
         end if;
      end process;

      reg_we_p: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_we <= '0';
            elsif (reg_we = '0' or full_int = '0') then
               reg_we <= WE;
            end if;
         end if;
      end process;
   end generate;

   -- Optional output register generation -------------------------------------
   use_outreg_false_g: if (USE_OUTREG = false) generate
      DOUT     <= dout_int;
      EMPTY    <= empty_int;
      re_int   <= RE;
   end generate;

   use_outreg_true_g: if (USE_OUTREG = true) generate
      DOUT     <= reg_dout;
      EMPTY    <= reg_empty;
      re_int   <= RE or reg_empty; -- auto pipeline

      reg_dout_p: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (re_int = '1') then
               reg_dout <= dout_int;
            end if;
         end if;
      end process;

      reg_empty_p: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_empty <= '1';
            elsif (re_int = '1') then
               reg_empty <= empty_int;
            end if;
         end if;
      end process;
   end generate;

   -- Status port mapping ------------------------------------------------------
   STATUS <= cnt_addr;

end architecture full;
