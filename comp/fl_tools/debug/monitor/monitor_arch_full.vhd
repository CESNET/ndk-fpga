--
-- fl_monitor_arch_full.vhd: Monitors Framelink for certain data at defined
--                      position. Full architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Lukas Solanka <solanka@liberouter.org>
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
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture fl_monitor_arch of fl_monitor is

   -- Constants declarations

   -- Position of the word within the Frame
   constant FL_WORD_COUNT : integer := WORD_POS/(FL_WIDTH/WORD_WIDTH);

   -- Position of the monitored word within the Framelink data word
   constant MX_POS : integer := WORD_POS rem (FL_WIDTH/WORD_WIDTH);

   -- Number of 32b words per reg_data_match
   -- This constant is only used when WORD_WIDTH > 32 (MI32 data width)
   constant MATCH_MI_COUNT : integer := WORD_WIDTH / 32;



   -- Signals declarations

   signal monitored_data : std_logic_vector(WORD_WIDTH - 1 downto 0);

   signal cmp_data_match : std_logic;
   signal cmp_pos_match : std_logic;

   signal reg_data_match : std_logic_vector(WORD_WIDTH - 1 downto 0);
   signal reg_data_match_we : std_logic_vector(MATCH_MI_COUNT downto 0);


--    signal match_parts :
--                array (MATCH_MI_COUNT - 1 downto 0) of
--                std_logic_vector(31 downto 0);
--    signal match_part_we : std_logic_vector(MATCH_MI_COUNT - 1 downto 0);


   signal cnt_word : std_logic_vector(log2(FL_WORD_COUNT) downto 0);
   signal cnt_word_ce : std_logic;
   signal cnt_word_ld : std_logic;

   signal cnt_match : std_logic_vector(31 downto 0);
   signal cnt_match_ce : std_logic;
   signal cnt_match_ld : std_logic;

   signal addr_int : std_logic_vector(31 downto 0);

   signal cs_mon : std_logic;
   signal cs_control : std_logic;
   signal reg_pos_matched : std_logic;
   signal reg_pos_matched_we : std_logic;
   signal fl_transaction : std_logic;
   signal reg_pos_matched_ld : std_logic;
   signal do_control : std_logic_vector(31 downto 0);
   signal do_mon : std_logic_vector(31 downto 0);

begin

   fl_transaction <= not (SRC_RDY_N or DST_RDY_N);

   -- This comparator checks if the data matches with the pattern
   cmp_data_match <= '1' when monitored_data = reg_data_match else '0';



   -- ---------------------------------------------------------------------
   --                      Input data selector
   -- Data word can be selected statically during compilation
   -- ---------------------------------------------------------------------

   -- Mapping data signals to the edit position ------------------------
   gen_sig_map: for i in 0 to FL_WIDTH/WORD_WIDTH - 1 generate
      gen_sig_sel: if (i = MX_POS) generate
         -- Select word within one FL word
         monitored_data <= DATA((i+1)*WORD_WIDTH - 1 downto i*WORD_WIDTH);
      end generate;
   end generate;



   -- ---------------------------------------------------------------------
   --                Match registers and counters
   -- ---------------------------------------------------------------------

   -- register reg_data_match -------------------------------------------------
   -- Set this register to the value you want to monitor
   -- Generate more registers
   gen_more_regs: if (WORD_WIDTH > 32) generate

      gen_reg: for i in 0 to MATCH_MI_COUNT - 1 generate

         process(RESET, CLK)
         begin
            if (RESET = '1') then
               reg_data_match(32*(i+1) - 1 downto 32*i) <=
                  DEFAULT_DATA(32*(i+1) - 1 downto 32*i);
            elsif (CLK'event AND CLK = '1') then
               if (reg_data_match_we(i) = '1') then
                  reg_data_match(32*(i+1) - 1 downto 32*i) <= ADC_DI;
               end if;
            end if;
         end process;

      end generate;

   end generate;

   -- Generate only one register <= 32bits long
   gen_one_reg: if (WORD_WIDTH <= 32) generate

         process(RESET, CLK)
         begin
            if (RESET = '1') then
               reg_data_match <= DEFAULT_DATA;
            elsif (CLK'event AND CLK = '1') then
               if (reg_data_match_we(0) = '1') then
                  reg_data_match <= ADC_DI(reg_data_match'length - 1 downto 0);
               end if;
            end if;
         end process;

   end generate;


   gen_non0_cnt: if (FL_WORD_COUNT > 0) generate

      -- cnt_word counter ------------------------------------------------
      -- Counts number of transactions from the start of the frame
      cnt_wordp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            cnt_word <= (others => '0');
         elsif (CLK'event AND CLK = '1') then
            if (cnt_word_ce = '1') then
               if (cnt_word_ld = '1') then
                  cnt_word <= (others => '0');
               else
                  cnt_word <= cnt_word + 1;
               end if;
            end if;
         end if;
      end process;

      cnt_word_ce <= fl_transaction;
      cnt_word_ld <= not EOF_N;

      -- This comparator compares if the desired position in the frame
      -- has been reached
      cmp_pos_match <= '1' when cnt_word = FL_WORD_COUNT else '0';


   end generate;

   gen_0_cnt: if (FL_WORD_COUNT = 0) generate
      cmp_pos_match <= '1';
   end generate;


   -- cnt_match counter ------------------------------------------------
   -- Counts number of matched words for the given pattern
   cnt_matchp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_match <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_match_ce = '1') then
            if (cnt_match_ld = '1') then
               cnt_match <= (others => '0');
            else
               cnt_match <= cnt_match + 1;
            end if;
         end if;
      end if;
   end process;

   cnt_match_ce <= cmp_data_match and cmp_pos_match and not reg_pos_matched
                   and fl_transaction;
   cnt_match_ld <= cs_mon and ADC_WR;



   -- register reg_pos_matched -------------------------------------------
   reg_pos_matchedp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_pos_matched <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg_pos_matched_ld = '1') then
            reg_pos_matched <= '0';
         elsif (reg_pos_matched = '0' and cmp_pos_match = '1' and
             fl_transaction = '1') then
            reg_pos_matched <= '1';
         end if;
      end if;
   end process;

   -- Reset the register after end of the frame
   reg_pos_matched_ld <= fl_transaction and not EOF_N;



   -- ---------------------------------------------------------------------
   --                      Memory connection
   -- ---------------------------------------------------------------------

   addr_int <= "00" & X"000000" & ADC_ADDR(7 downto 2);


   -- Read logic

   -- data output multiplexor
   with addr_int(4) select
      ADC_DO <= do_control       when '0',
                do_mon           when '1',
                (others => 'X')  when others;


   do_control <= cnt_match;


   -- Control or Monitored data select
   cs_control  <= '1' when addr_int(4) = '0'  and ADC_WR = '1' else
                  '0';

   cs_mon      <= '1' when addr_int(4) = '1' and ADC_WR = '1' else
                  '0';


   -- Monitored data multiplexor and decoder
   -- Generate only when the monitored data width is more than
   -- MI32 data width
   gen_more_data: if (WORD_WIDTH > 32) generate

      -- mx logic
      mx_do_monp: process(addr_int, reg_data_match)
      begin
         do_mon <= (others => '0');

         for i in 0 to MATCH_MI_COUNT - 1 loop
            if (addr_int(3 downto 0) = i) then
               do_mon <= reg_data_match(32*(i+1) - 1 downto 32*i);
            end if;
         end loop;
      end process;


      -- WE decoder logic
      dec_wep: process(addr_int, cs_mon)
      begin
         reg_data_match_we <= (others => '0');

         -- write logic
         for i in 0 to MATCH_MI_COUNT - 1 loop
            if (cs_mon = '1' and addr_int(3 downto 0) = i) then
               reg_data_match_we(i) <= '1';
            end if;
         end loop;
      end process;

   end generate;

   gen_one_data: if (WORD_WIDTH <= 32) generate

      -- Data output
      do_mon(reg_data_match'length - 1 downto 0) <= reg_data_match;
      do_mon(31 downto reg_data_match'length) <= (others => '0');

      reg_data_match_we(0) <= cs_mon and not addr_int(0);
   end generate;


   -- MI stuff
   ADC_ARDY <= '1';
   ADC_DRDY <= ADC_RD;

end architecture fl_monitor_arch;

