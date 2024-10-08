--
-- cam_data_array.vhd: Array of memory elements + filling part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin kosek <xkosek00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--$Id$
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
entity cam_data_array is
   generic (
      -- Data row width (bits, should be a multiple of ELEM_WIDTH)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer;
      -- Width of address bus
      -- should be greater or equal to log2(CAM_ROW_COUNT)
      CAM_ADDR_WIDTH    : integer;
      -- Width of internal element
      -- 4 for VirtexII SRL16E (legacy, but works also for V5,6,7)
      -- 5 for Virtex5,6,7 SRLC32E
      -- 6 for Virtex5,6,7 RAM64x1S (stores 6 bits/LUT, most effective)
      ELEM_WIDTH        : integer := 4;
      -- Width of "bank" addres within each storage element.
      -- Saves resources, but slows down the search.
      -- Search time is 2^SEQUENCED_SEARCH.
      -- Write time is 2^(ELEM_WIDTH-SEQUENCED_SEARCH).
      SEQUENCED_SEARCH  : integer := 0;
      -- If true, writing a masked bit (mask=0) has two different meanings:
      --    If the bit is 0, then it is don't care
      --    But if the bit is 1, then it is UNMATCHABLE!
      USE_UNMATCHABLE   : boolean := false;
      -- Forced usage of carry chains in match aggregation
      USE_CARRY_CHAINS  : boolean := false;
      -- Enable registers for better timing inside matching logic.
      -- Do not use together with carry chains!
      MATCH_REG         : boolean := false
   );
   port (
      ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_ENABLE      : in std_logic;

      MATCH_ENABLE      : in std_logic;
      MATCH_RDY         : out std_logic;
      MATCH_RST         : in std_logic;
      RESET             : in std_logic;
      CLK               : in std_logic;
      MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
      MATCH_VLD         : out std_logic
   );
end entity cam_data_array;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_data_array_arch of cam_data_array is

   -- SEQUENCED_SEARCH needs less rows
   constant CAM_ROW_COUNT_SEQ : integer := CAM_ROW_COUNT/(2**SEQUENCED_SEARCH);

   -- Number of bits matched in one element
   constant MATCH_PER_ELEM : integer := ELEM_WIDTH - SEQUENCED_SEARCH;

   -- Number of elements to match the whole word
   constant ELEM_COUNT : integer := div_roundup(CAM_ROW_WIDTH, MATCH_PER_ELEM);

   -- SEQUENCED_SEARCH needs wider words
   constant CAM_ROW_WIDTH_SEQ : integer := ELEM_COUNT * ELEM_WIDTH;


-- ------------------ Signals declaration -------------------------------------
   signal write_enable_bus : std_logic_vector((CAM_ROW_COUNT_SEQ - 1) downto 0);
   signal data_fill_bus : std_logic_vector(ELEM_COUNT - 1 downto 0);
   signal match_out : std_logic_vector((CAM_ROW_COUNT_SEQ - 1) downto 0);

   signal write_addr       : std_logic_vector(ELEM_WIDTH-1 downto 0);
   signal write_addr_mult  : std_logic_vector(CAM_ROW_WIDTH_SEQ-1 downto 0);
   signal write_enable_out : std_logic;
   signal data_in_mx       : std_logic_vector(CAM_ROW_WIDTH_SEQ-1 downto 0);

   signal data_in_seq      : std_logic_vector(CAM_ROW_WIDTH_SEQ-1 downto 0);
   signal cnt_search       : std_logic_vector(max(1,SEQUENCED_SEARCH)-1 downto 0);
   signal cnt_search_dly   : std_logic_vector(max(1,SEQUENCED_SEARCH)-1 downto 0);
   signal cnt_search_dly2  : std_logic_vector(max(1,SEQUENCED_SEARCH)-1 downto 0);
   signal max_search       : std_logic_vector(max(1,SEQUENCED_SEARCH)-1 downto 0);
   signal min_search       : std_logic_vector(max(1,SEQUENCED_SEARCH)-1 downto 0);
   signal sig_match_rdy    : std_logic;

   -- Store all but the last bank
   -- Signal width is for the whole result for easier indexing
   signal reg_match_out    : std_logic_vector(CAM_ROW_COUNT-1 downto 0);

   signal sig_match_out    : std_logic_vector(CAM_ROW_COUNT - 1 downto 0);
   signal reg_match_vld    : std_logic;
   signal reg_match_enable : std_logic;
   signal rows_match_enable: std_logic;

   -- Extend DATA_IN signal to the required width
   signal data_in_ext
      : std_logic_vector(ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto 0);
begin

-- -------- Generating and maping cam_filling_part ----------------------------
   FILLING_PART: entity work.cam_filling_part
      generic map (
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
         CAM_ROW_COUNT     => CAM_ROW_COUNT,
         CAM_ADDR_WIDTH    => CAM_ADDR_WIDTH,
         ELEM_WIDTH        => ELEM_WIDTH,
         SEQUENCED_SEARCH  => SEQUENCED_SEARCH,
         ELEM_COUNT        => ELEM_COUNT,
         USE_UNMATCHABLE   => USE_UNMATCHABLE
      )
      port map (
         ADDR              => ADDR,
         DATA_IN           => DATA_IN,
         MASK_IN           => MASK_IN,
         WRITE_ENABLE      => WRITE_ENABLE,
         RESET             => RESET,
         CLK               => CLK,
         ADDR_OUT          => write_addr,
         WRITE_ENABLE_OUT  => write_enable_out,
         WRITE_ENABLE_BUS  => write_enable_bus,
         DATA_FILL_BUS     => data_fill_bus
      );

   -- Write address is the same for all elems
   multiply_addr_out : for i in 0 to ELEM_COUNT - 1 generate
      write_addr_mult((i+1)*ELEM_WIDTH-1 downto i*ELEM_WIDTH) <= write_addr;
   end generate;

   -- When using RAM64x1S, address must be sent with each write
   use_mux : if ELEM_WIDTH = 6 generate
      data_in_mx_p : process(data_in_seq, write_addr_mult, write_enable_out)
      begin
         if write_enable_out = '0' then
            data_in_mx <= data_in_seq;
         else
            data_in_mx <= write_addr_mult;
         end if;
      end process;
   end generate;

   -- When using SRL16E or SRL32E, addressing is automatic by shifting
   dont_use_mux : if ELEM_WIDTH /= 6 generate
      data_in_mx <= data_in_seq;
   end generate;

-- -------- Generating and maping cam_rows ------------------------------------
   ROW_GEN: for i in 0 to (CAM_ROW_COUNT_SEQ - 1) generate
   -- generate all memory rows
      ROW_INST: entity work.cam_row
         generic map (
            CAM_ROW_WIDTH  => CAM_ROW_WIDTH_SEQ,
            ELEM_WIDTH     => ELEM_WIDTH,
            USE_CARRY_CHAINS => USE_CARRY_CHAINS,
            MATCH_REG        => MATCH_REG
         )
         port map (
            DATA_FILL      => data_fill_bus,
            DATA_IN        => data_in_mx,
            WRITE_ENABLE   => write_enable_bus(i),
            MATCH_ENABLE   => rows_match_enable,
            CLK            => CLK,
            MATCH          => match_out(i)
         );
   end generate;

   match_reg_gen : if MATCH_REG generate
      signal reg2 : std_logic;
   begin
      reg_match_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg2 <= '0';
               reg_match_enable <= '0';
            else
               reg2 <= MATCH_ENABLE;
               reg_match_enable <= reg2;
            end if;
            cnt_search_dly <= cnt_search;
            cnt_search_dly2 <= cnt_search_dly;
         end if;
      end process;
   end generate;
   match_noreg_gen : if not MATCH_REG generate
      cnt_search_dly <= cnt_search;
      reg_match_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_match_enable <= '0';
            else
               reg_match_enable <= MATCH_ENABLE;
            end if;
            cnt_search_dly2 <= cnt_search_dly;
         end if;
      end process;
   end generate;

   no_extend_gen : if ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH) = CAM_ROW_WIDTH
   generate
      data_in_ext <= DATA_IN;
   end generate;

   -- Need to deal with unused bits of the last element
   extend_gen : if ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH) /= CAM_ROW_WIDTH
   generate
      data_in_ext(CAM_ROW_WIDTH-1 downto 0) <= DATA_IN;
      data_in_ext(ELEM_COUNT*(ELEM_WIDTH-SEQUENCED_SEARCH)-1 downto CAM_ROW_WIDTH)
         <= (others => '0'); -- Store zeros in unused bits (masked anyway)
   end generate;

   -- Code for sequenced version
   gen_sequenced : if SEQUENCED_SEARCH > 0 generate

      --* Counter for searching in multiple banks
      cnt_search_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               cnt_search <= (others => '0');
            else
               if MATCH_ENABLE = '1' or cnt_search /= min_search then
                  cnt_search <= cnt_search + 1;
               end if;
            end if;
         end if;
      end process;

      max_search <= (others => '1');
      min_search <= (others => '0');

      -- Not ready when currently matching in non-last bank.
      sig_match_rdy <= '0' when MATCH_ENABLE = '1' and
                              cnt_search /= max_search
                     else '1';

      -- Match bus also contains bank addressing
      split_data_in : for i in 0 to ELEM_COUNT - 1 generate
         data_in_seq((i+1)*ELEM_WIDTH-1 downto i*ELEM_WIDTH) <=
            cnt_search &
            data_in_ext((i+1)*MATCH_PER_ELEM-1 downto i*MATCH_PER_ELEM);
      end generate;

      -- Store outputs from all but the last bank
      -- (The last bank is also stored, but not used, actually)
      reg_match_gen : for i in 0 to CAM_ROW_COUNT_SEQ-1 generate
         reg_match_gen2: for j in 0 to 2**SEQUENCED_SEARCH-1 generate
            reg_match_out_p : process(CLK)
            begin
               if CLK'event and CLK = '1' then
                  if j = conv_integer(cnt_search_dly2) then
                  reg_match_out((i*(2**SEQUENCED_SEARCH)) + j) <=
                     match_out(i);
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      -- Map registered and direct outputs to one vector
      mach_out_gen : for i in 0 to (CAM_ROW_COUNT/(2**SEQUENCED_SEARCH)) - 1
      generate
         sig_match_out(((2**SEQUENCED_SEARCH)*(i+1))-1 downto
                        (2**SEQUENCED_SEARCH)*i) <=
            match_out(i) &
            reg_match_out(((2**SEQUENCED_SEARCH)*(i+1))-2 downto
                           (2**SEQUENCED_SEARCH)*i);
      end generate;

      MATCH_BUS <= sig_match_out;

      -- Match will be ready one cycle after last search
      reg_match_vld_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_match_vld <= '0';
            else
               if cnt_search_dly = max_search then
                  reg_match_vld <= '1';
               else
                  reg_match_vld <= '0';
               end if;
            end if;
         end if;
      end process;

      MATCH_VLD <= reg_match_vld;

      rows_match_enable <= '1' when (MATCH_ENABLE = '1' or cnt_search /= min_search) and MATCH_RST='0' else '0';

   end generate;

   -- Code for classical (non-sequenced) version
   gen_not_sequenced : if SEQUENCED_SEARCH = 0 generate
      sig_match_rdy <= '1';
      data_in_seq <= DATA_IN;
      MATCH_BUS <= match_out;
      MATCH_VLD <= reg_match_enable;
      rows_match_enable <= MATCH_ENABLE and not MATCH_RST;
   end generate;

   MATCH_RDY <= sig_match_rdy;

end architecture cam_data_array_arch;
