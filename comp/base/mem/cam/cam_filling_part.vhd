--
-- cam_filling_part.vhd: An important part of CAM responsible for filling
--                       memory rows
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_filling_part is
   generic(
      -- Data row width (bits, should be a multiple of ELEM_WIDTH)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer;
      -- Width of address bus
      -- should be greater or equal to log2(CAM_ROW_COUNT)
      CAM_ADDR_WIDTH    : integer;
      -- Width of internal storage element
      -- 4 for VirtexII SRL16E (legacy, but works also for V5,6,7)
      -- 5 for Virtex5,6,7 SRLC32E
      -- 6 for Virtex5,6,7 RAM64x1S (stores 6 bits/LUT, most effective)
      ELEM_WIDTH        : integer := 4;
      -- Width of "bank" addres within each storage element.
      -- Saves resources, but slows down the search.
      -- Search time is 2^SEQUENCED_SEARCH.
      -- Write time is 2^(ELEM_WIDTH-SEQUENCED_SEARCH).
      SEQUENCED_SEARCH  : integer := 0;
      -- Helper value
      ELEM_COUNT        : integer;
      -- If true, writing a masked bit (mask=0) has two different meanings:
      --    If the bit is 0, then it is don't care
      --    But if the bit is 1, then it is UNMATCHABLE!
      USE_UNMATCHABLE   : boolean := false
   );
   port(
      ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_ENABLE      : in std_logic;
      RESET             : in std_logic;
      CLK               : in std_logic;
      -- Write address (needed only for RAM64x1S)
      ADDR_OUT          : out std_logic_vector(ELEM_WIDTH-1 downto 0);
      WRITE_ENABLE_OUT  : out std_logic;
      -- Write enable for each row
      WRITE_ENABLE_BUS  : out std_logic_vector
         ((CAM_ROW_COUNT/(2**SEQUENCED_SEARCH) - 1) downto 0);
      -- Write data for each element
      DATA_FILL_BUS     : out std_logic_vector(ELEM_COUNT - 1 downto 0)
   );
end entity cam_filling_part;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_filling_part_arch of cam_filling_part is

-- ------------------ Signals declaration -------------------------------------
   signal fill_result      : std_logic_vector((ELEM_COUNT - 1) downto 0);
   signal dec1fn_we        : std_logic;
   signal counter
      : std_logic_vector((ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto 0);
   signal counter_ce       : std_logic;
   signal cnt_busy         : std_logic;
   signal dec1fn_out
      : std_logic_vector((CAM_ROW_COUNT/(2**SEQUENCED_SEARCH)) - 1 downto 0);
   signal dec1fn_reduced
      : std_logic_vector((log2(CAM_ROW_COUNT)-SEQUENCED_SEARCH) - 1 downto 0);

   -- Extend MASK_IN signal to the required width
   signal mask_in_ext
      : std_logic_vector(ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto 0);
   -- Extend DATA_IN signal to the required width
   signal data_in_ext
      : std_logic_vector(ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto 0);

begin
   DATA_FILL_BUS     <= fill_result;
   counter_ce        <= WRITE_ENABLE;
   WRITE_ENABLE_OUT  <= dec1fn_we;
   WRITE_ENABLE_BUS  <= dec1fn_out;
   ADDR_OUT(counter'length-1 downto 0) <= counter;
   seq_addr_gen : if(SEQUENCED_SEARCH>0) generate
      ADDR_OUT(ADDR_OUT'length-1 downto ADDR_OUT'length-SEQUENCED_SEARCH) <= ADDR(SEQUENCED_SEARCH-1 downto 0);
   end generate;

   no_extend_gen : if ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH) = CAM_ROW_WIDTH
   generate
      mask_in_ext <= MASK_IN;
      data_in_ext <= DATA_IN;
   end generate;

   -- Need to deal with unused bits of the last element
   extend_gen : if ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH) /= CAM_ROW_WIDTH
   generate
      mask_in_ext(CAM_ROW_WIDTH-1 downto 0) <= MASK_IN;
      data_in_ext(CAM_ROW_WIDTH-1 downto 0) <= DATA_IN;

      mask_in_ext(ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto CAM_ROW_WIDTH)
         <= (others => '0'); -- Store zeros in unused bits mask->always matched
      data_in_ext(ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto CAM_ROW_WIDTH)
         <= (others => '0'); -- Store zeros in unused bits (masked anyway)
   end generate;

-- --------- Generating and maping cam_elements -------------------------------
   FILL_ROW: for i in 0 to (ELEM_COUNT - 1) generate
   -- generate all filling elements
      ELEMENT_INST: entity work.cam_fill_element
         generic map(
            ELEM_WIDTH     => ELEM_WIDTH-SEQUENCED_SEARCH,
            USE_UNMATCHABLE=> USE_UNMATCHABLE
         )
         port map (
            CNT_IN         => counter,
            MASK_IN        => mask_in_ext((i+1)*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto i*(ELEM_WIDTH-SEQUENCED_SEARCH)),
            DATA_IN        => data_in_ext((i+1)*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto i*(ELEM_WIDTH-SEQUENCED_SEARCH)),
            DATA_FILL      => fill_result(i)
         );
   end generate;


-- counter ---------------------------------------------------------
   counterp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            counter <= (others => '1');
            dec1fn_we <= '0';
            cnt_busy <= '0';
         elsif (counter_ce = '1' AND cnt_busy /= '1') then
            counter <= (others => '1');
            cnt_busy <= '1';
            dec1fn_we <= '1';
         elsif (cnt_busy = '1') then
            if (counter = 0) then
               cnt_busy <= '0';
               dec1fn_we <= '0';
            else
               counter <= counter - 1;
            end if;
         end if;
      end if;
   end process;

-- --------- Generating and maping generic decoder ----------------------------
   DEC1FN : entity work.dec1fn_enable
      generic map (
         ITEMS       => CAM_ROW_COUNT / (2**SEQUENCED_SEARCH)
      )
      port map (
         ADDR        => dec1fn_reduced,
         ENABLE      => dec1fn_we,
         DO          => dec1fn_out
      );

-- -------- Maping decoder input (have to adjust ADDR) ------------------------
   MAP_DEC1FN_OUT: for i in 0 to (log2(CAM_ROW_COUNT)-SEQUENCED_SEARCH) - 1
   generate
      dec1fn_reduced(i) <= ADDR(i+SEQUENCED_SEARCH);
   end generate;

end architecture cam_filling_part_arch;
