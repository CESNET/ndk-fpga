--
-- mi_splitter_addr32.vhd: MI Splitter wrapper with 32bit OUT_ADDRs
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

entity MI_SPLITTER_ADDR32 is
   generic(
      ITEMS       : integer;   -- number of output MI interfaces
      ADDR_WIDTH  : integer;   -- width of address spaces on output ports (1-32)
      DATA_WIDTH  : integer;   -- data width (8-128)
      PIPE        : boolean := false; -- insert pipeline
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      PIPE_TYPE   : string := "SHREG";
      PIPE_OUTREG : boolean := false
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_ADDR     : in  std_logic_vector((ADDR_WIDTH+log2(ITEMS))-1 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;

      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ITEMS*32-1 downto 0);
      OUT_BE      : out std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_WR      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_ARDY    : in  std_logic_vector(ITEMS-1 downto 0);
      OUT_DRD     : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic_vector(ITEMS-1 downto 0)

   );
end entity MI_SPLITTER_ADDR32;


architecture mi_splitter_addr32_arch of MI_SPLITTER_ADDR32 is

   signal out_addr_aux : std_logic_vector(ITEMS*ADDR_WIDTH-1 downto 0);

begin

   MI_SPLITTER : entity work.MI_SPLITTER
   generic map (
      ITEMS       => ITEMS,
      ADDR_WIDTH  => ADDR_WIDTH,
      DATA_WIDTH  => DATA_WIDTH,
      PIPE        => PIPE,
      PIPE_TYPE   => PIPE_TYPE,
      PIPE_OUTREG => PIPE_OUTREG
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK         => CLK,
      RESET       => RESET,

      -- Input MI interface ---------------------------------------------------
      IN_DWR      => IN_DWR,
      IN_ADDR     => IN_ADDR,
      IN_BE       => IN_BE,
      IN_RD       => IN_RD,
      IN_WR       => IN_WR,
      IN_ARDY     => IN_ARDY,
      IN_DRD      => IN_DRD,
      IN_DRDY     => IN_DRDY,

      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     => OUT_DWR,
      OUT_ADDR    => out_addr_aux,
      OUT_BE      => OUT_BE,
      OUT_RD      => OUT_RD,
      OUT_WR      => OUT_WR,
      OUT_ARDY    => OUT_ARDY,
      OUT_DRD     => OUT_DRD,
      OUT_DRDY    => OUT_DRDY
   );

   addr_gen: for i in 0 to ITEMS-1 generate
      OUT_ADDR(i*32+ADDR_WIDTH-1 downto i*32) <=
                           out_addr_aux((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH);
      OUT_ADDR((i+1)*32-1 downto i*32+ADDR_WIDTH) <= (others => '0');
   end generate;

end architecture;
