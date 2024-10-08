--
-- cam.vhd: Top level of CAM component
-- Copyright (C) 2006 CESNET
-- Author(s): Martin kosek <kosek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CAM is
   generic (
      -- Data row width (bits, should be a multiple of ELEM_WIDTH)
      CAM_ROW_WIDTH     : integer := 128;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer := 32;
      -- Width of address bus
      -- set to log2(CAM_ROW_COUNT)
      CAM_ADDR_WIDTH    : integer := 5;
      -- Width of internal storage element
      -- 4 for VirtexII SRL16E (legacy, but works also for V5,6,7)
      -- 5 for Virtex5,6,7 SRLC32E
      -- 6 for Virtex5,6,7 RAM64x1S (stores 6 bits/LUT, most effective)
      ELEM_WIDTH        : integer := 4;
      -- Width of "bank" addres within each storage element.
      -- Saves resources, but slows down the search.
      -- Search time is 2^SEQUENCED_SEARCH.
      -- Write time is 2^(ELEM_WIDTH-SEQUENCED_SEARCH).
      -- !!! Only with ELEM_WIDTH = 6 !!!
      SEQUENCED_SEARCH  : integer := 0;
      -- If true, writing a masked bit (mask=0) has two different meanings:
      --    If data bit is 0, then it is don't care
      --    But if data bit is 1, then it is UNMATCHABLE!
      USE_UNMATCHABLE   : boolean := false;
      -- Forced usage of carry chains in match aggregation
      -- NOTE: DO NOT USE! Vivado (2016.3 and older) cannot aggregate carry chains into slices effectively!
      USE_CARRY_CHAINS  : boolean := false;
      -- Enable registers for better timing inside matching logic.
      -- Do not use together with carry chains!
      MATCH_REG         : boolean := false
   );
   port (
      -- common interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- insert interface
      ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
      MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_EN          : in std_logic;

      -- insert/search interface
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);

      -- search interface
      MATCH_EN          : in std_logic;
      MATCH_RDY         : out std_logic; -- Accept new MATCH_EN
                                         -- Const 1 for SEQUENCED_SEARCH = 0
      MATCH_RST         : in std_logic;
      MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
      MATCH_BUS_VLD     : out std_logic
   );
end entity CAM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_arch of CAM is


-- ------------------ Signals declaration -------------------------------------
   signal reg_addr         : std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
   signal reg_addr_we      : std_logic;
   signal reg_data_in      : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal reg_data_in_we   : std_logic;
   signal reg_mask_in      : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal reg_mask_in_we   : std_logic;
   signal reg_match_en     : std_logic;
   signal reg_match_rst    : std_logic;

   signal sig_match_rdy    : std_logic;

   attribute keep : string;
   attribute keep of reg_data_in_we : signal is "true";
   attribute keep of reg_mask_in_we : signal is "true";

begin

   assert (CAM_ROW_WIDTH mod ELEM_WIDTH) = 0
      report "CAM_ROW_WIDTH must be multiple of ELEM_WIDTH!"
   severity error;

   assert (ELEM_WIDTH = 6 or SEQUENCED_SEARCH = 0)
      report "SEQUENCED_SEARCH can be used only with ELEM_WIDTH=6!"
   severity error;

   MATCH_RDY <= sig_match_rdy;

   reg_addr_we <= WRITE_EN;
   reg_data_in_we <= WRITE_EN or MATCH_EN;
   reg_mask_in_we <= WRITE_EN or MATCH_EN;

-- -------- Generating and maping cam_data_array ------------------------------
   DATA_ARRAY: entity work.cam_data_array
      generic map (
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
         CAM_ROW_COUNT     => CAM_ROW_COUNT,
         CAM_ADDR_WIDTH    => CAM_ADDR_WIDTH,
         ELEM_WIDTH        => ELEM_WIDTH,
         SEQUENCED_SEARCH  => SEQUENCED_SEARCH,
         USE_UNMATCHABLE   => USE_UNMATCHABLE,
         USE_CARRY_CHAINS  => USE_CARRY_CHAINS,
         MATCH_REG         => MATCH_REG
      )
      port map (
         ADDR              => reg_addr,
         DATA_IN           => reg_data_in,
         MASK_IN           => reg_mask_in,
         WRITE_ENABLE      => WRITE_EN,
         MATCH_ENABLE      => reg_match_en,
         MATCH_RDY         => sig_match_rdy,
         MATCH_RST         => reg_match_rst,
         RESET             => RESET,
         CLK               => CLK,
         MATCH_BUS         => MATCH_BUS,
         MATCH_VLD         => MATCH_BUS_VLD
      );


-- register reg_addr ----------------------------------------------------------
reg_addrp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (reg_addr_we = '1') then
         reg_addr <= ADDR;
      end if;
   end if;
end process;

-- register reg_data_in -------------------------------------------------------
reg_data_inp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (reg_data_in_we = '1') then
         reg_data_in <= DATA_IN;
      end if;
   end if;
end process;

-- register reg_mask_in -------------------------------------------------------
reg_mask_inp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (reg_mask_in_we = '1') then
         reg_mask_in <= MASK_IN;
      end if;
   end if;
end process;

-- register reg_match_enable --------------------------------------------------
reg_match_enablep: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         reg_match_en <= '0';
      elsif sig_match_rdy = '1' then
         reg_match_en <= MATCH_EN;
      end if;
   end if;
end process;

reg_match_resetp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if sig_match_rdy = '1' then
         reg_match_rst <= MATCH_RST;
      end if;
   end if;
end process;

end architecture cam_arch;
