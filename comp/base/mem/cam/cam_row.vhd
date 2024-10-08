--
-- cam_row.vhd: One memory row of CAM.
-- Copyright (C) 2005 CESNET
-- Author(s): Martin kosek <xkosek00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_misc.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_row is
   generic(
      -- Data row width (bits, should be a multiple of ELEM_WIDTH)
      CAM_ROW_WIDTH  : integer;
      -- Width of internal storage element
      -- 4 for VirtexII SRL16E (legacy, but works also for V5,6,7)
      -- 5 for Virtex5,6,7 SRLC32E
      -- 6 for Virtex5,6,7 RAM64x1S (stores 6 bits/LUT, most effective)
      ELEM_WIDTH        : integer := 4;
      -- Forced usage of carry chains in match aggregation
      USE_CARRY_CHAINS  : boolean := false;
      -- Enable registers for better timing inside matching logic.
      -- Do not use together with carry chains!
      MATCH_REG         : boolean := false
   );
   port(
      DATA_FILL      : in std_logic_vector(((CAM_ROW_WIDTH / ELEM_WIDTH)-1) downto 0);
      DATA_IN        : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_ENABLE   : in std_logic;
      MATCH_ENABLE   : in std_logic;
      CLK            : in std_logic;
      MATCH          : out std_logic
   );
end entity cam_row;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_row_arch of cam_row is

-- ----------------- Constants declaration ------------------------------------
   -- Number of elements (cam_element)
   constant ELEM_COUNT  : integer := (CAM_ROW_WIDTH / ELEM_WIDTH);


-- ------------------ Signals declaration -------------------------------------
   signal muxcy_sel, muxcy_sel_reg : std_logic_vector(ELEM_COUNT-1 downto 0);
   signal reg_result : std_logic := '0';
   signal match_result : std_logic;
   signal match_enable_reg : std_logic;

begin

-- --------- Generating and maping cam_elements -------------------------------
   DATA_ROW: for i in 0 to (ELEM_COUNT - 1) generate
      signal local_data_in : std_logic_vector(ELEM_WIDTH-1 downto 0);
   begin
      local_data_in <= DATA_IN((((i+1)*ELEM_WIDTH)-1) downto (i*ELEM_WIDTH));
      srl16e_gen : if ELEM_WIDTH = 4 generate
      shift_register : SRL16E
         generic map (
            INIT => X"0000"
         ) port map (
            d => DATA_FILL(i),
            ce => WRITE_ENABLE,
            clk => CLK,
            a0 => local_data_in(0),
            a1 => local_data_in(1),
            a2 => local_data_in(2),
            a3 => local_data_in(3),
            q => muxcy_sel(i)
         );
      end generate;
      srlc32e_gen : if ELEM_WIDTH = 5 generate
         shift_register : SRLC32E
         generic map (
            INIT => X"00000000"
         ) port map (
            d  => DATA_FILL(i),
            ce => WRITE_ENABLE,
            clk=> CLK,
            a  => local_data_in,
            q  => muxcy_sel(i),
            q31=> open -- Cascading not used
         );
      end generate;
      ram64x1s_gen : if ELEM_WIDTH = 6 generate
         RAM64X1S_inst : RAM64X1S
         generic map (
            INIT => X"0000000000000000")
         port map (
            O => muxcy_sel(i),        -- 1-bit data output
            A0 => local_data_in(0),      -- Address[0] input bit
            A1 => local_data_in(1),      -- Address[1] input bit
            A2 => local_data_in(2),      -- Address[2] input bit
            A3 => local_data_in(3),      -- Address[3] input bit
            A4 => local_data_in(4),      -- Address[4] input bit
            A5 => local_data_in(5),      -- Address[5] input bit
            D => DATA_FILL(i),        -- 1-bit data input
            WCLK => CLK,  -- Write clock input
            WE => WRITE_ENABLE       -- Write enable input
         );
      end generate;
   end generate;

-- match result aggregation ---------------------------------------------------
   carry_gen : if USE_CARRY_CHAINS generate
      signal reg_match_bus : std_logic_vector(ELEM_COUNT-1 downto 0);
   begin
      match_aggregate : entity work.CARRY_CHAIN
      generic map(
         -- DEVICE      => DEVICE,
         CARRY_WIDTH    => ELEM_COUNT
      ) port map (
        CI  => match_enable_reg,
        DI  => (others => '0'),
        S   => muxcy_sel_reg,
        CO  => reg_match_bus,
        DO  => open
      );
      match_result <= reg_match_bus(ELEM_COUNT-1);
   end generate;

   logic_gen : if not USE_CARRY_CHAINS generate
      match_result <= match_enable_reg and and_reduce(muxcy_sel_reg);
   end generate;

-- register reg_result --------------------------------------------------------
   reg_resultp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_result <= match_result;
      end if;
   end process;
   MATCH <= reg_result;

   match_reg_gen : if MATCH_REG generate
      reg : process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            muxcy_sel_reg <= muxcy_sel;
            match_enable_reg <= MATCH_ENABLE;
         end if;
      end process;
   end generate;
   match_noreg_gen : if not MATCH_REG generate
      muxcy_sel_reg <= muxcy_sel;
      match_enable_reg <= MATCH_ENABLE;
   end generate;

end architecture cam_row_arch;
