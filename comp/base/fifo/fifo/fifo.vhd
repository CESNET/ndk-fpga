-- fifo.vhd: FIFO - m x n bit
--                  - synchronous write, asynchronous read
--                  - Status signal
-- Copyright (C) 2006 CESNET
-- Author(s):  Pecenka Tomas pecenka@liberouter.org
--             Pus Viktor    pus@liberouter.org
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
use IEEE.std_logic_arith.all;
use work.math_pack.all;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fifo is

   constant ADDRESS_WIDTH  : integer := LOG2(ITEMS);

   signal do : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
   signal re, out_empty : std_logic;

   -- Read and write address signals
   signal read_address  : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal write_address : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   -- Signals for read and write address counters
   signal cnt_write_address : std_logic_vector(ADDRESS_WIDTH downto 0);
   signal cnt_read_address  : std_logic_vector(ADDRESS_WIDTH downto 0);

   -- Read and write address registers
   signal reg_write_address : std_logic_vector(ADDRESS_WIDTH downto 0);
   signal reg_read_address  : std_logic_vector(ADDRESS_WIDTH downto 0);

   -- Address comparators
   signal cmp_empty : std_logic;
   signal cmp_full  : std_logic;

   -- Read and Write operation from/to FIFO allowed signal
   signal sig_write_allowed : std_logic;
   signal sig_read_allowed  : std_logic;
   signal sig_empty_full_we : std_logic;

   -- FULL and EMPY internal signals
   signal reg_full   : std_logic;
   signal reg_empty  : std_logic;
   signal reg_lstblk : std_logic := '0';
   signal sig_full   : std_logic;
   signal sig_empty  : std_logic;

   -- last block signals
   signal cnt_diff            : std_logic_vector(ADDRESS_WIDTH downto 0) := (others => '0');
   signal cnt_diff_ce         : std_logic;
   signal cnt_diff_dir        : std_logic;
   signal lstblk_plus_one     : std_logic;
   signal lstblk_minus_one     : std_logic;

begin

   assert (ITEMS >= 2) report "FIFO: ITEMS lower than 2 is not supported" severity failure;

   -- Actual write address
   write_address <= reg_write_address(ADDRESS_WIDTH-1 downto 0);
   -- Actual read address
   read_address <= reg_read_address(ADDRESS_WIDTH-1 downto 0);

   -- Memory connection -------------------------------------------------------
   storage_memory : entity work.SDP_DISTMEM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         ITEMS          => ITEMS
      )
      port map (
         WCLK        => CLK,
         ADDRA       => write_address,
         DI          => DATA_IN,
         WE          => sig_write_allowed,
         ADDRB       => read_address,
         DOB         => do
      );

   -- register reg_write_address ----------------------------------------------
   reg_write_addressp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_write_address <= (others => '0');
         elsif (sig_write_allowed = '1') then
            reg_write_address <= cnt_write_address;
         end if;
      end if;
   end process;

   -- Write address counter ---------------------------------------------------
   cnt_write_addressp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_write_address <=
               conv_std_logic_vector(1, cnt_write_address'length);
         elsif (sig_write_allowed = '1') then
            cnt_write_address <= cnt_write_address + 1;

            if (cnt_write_address(ADDRESS_WIDTH-1 downto 0) = ITEMS-1) then
               cnt_write_address(ADDRESS_WIDTH-1 downto 0) <= (others => '0');
               cnt_write_address(ADDRESS_WIDTH) <=
                     not cnt_write_address(ADDRESS_WIDTH);
            end if;

         end if;
      end if;
   end process;

   -- register reg_read_address ------------------------------------------------------
   reg_read_addressp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_read_address <= (others => '0');
         elsif (sig_read_allowed = '1') then
            reg_read_address <= cnt_read_address;
         end if;
      end if;
   end process;

   -- Read counter ------------------------------------------------------------
   cnt_read_addressp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_read_address <=
               conv_std_logic_vector(1, cnt_read_address'length);
         elsif (sig_read_allowed = '1') then
            cnt_read_address <= cnt_read_address + 1;

            if (cnt_read_address(ADDRESS_WIDTH-1 downto 0) = ITEMS-1) then
               cnt_read_address(ADDRESS_WIDTH-1 downto 0) <= (others => '0');
               cnt_read_address(ADDRESS_WIDTH) <=
                     not cnt_read_address(ADDRESS_WIDTH);
            end if;

         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
-- CONTROL LOGIC
-- ----------------------------------------------------------------------------

   -- Read and Write allowed signals
   sig_write_allowed <= WRITE_REQ and not reg_full;
   sig_read_allowed  <= re and not reg_empty;

   sig_empty_full_we <= sig_read_allowed or sig_write_allowed;


   -- Comparator for EMPTY signal ---------------------------------------------
   cmp_emptyp: process(cnt_read_address, reg_write_address)
   begin
      cmp_empty <= '0';
      -- pragma translate_off
      if (RESET='0') then
      -- pragma translate_on
      if ( cnt_read_address = reg_write_address ) then
         cmp_empty <= '1';
      end if;
      -- pragma translate_off
      end if;
      -- pragma translate_on
   end process;

   -- Comparator for FULL signal ----------------------------------------------
   cmp_fullp: process(reg_read_address, cnt_write_address)
   begin
      cmp_full <= '0';
      -- pragma translate_off
      if (RESET='0') then
      -- pragma translate_on
      if ((reg_read_address (ADDRESS_WIDTH-1 downto 0) =
          cnt_write_address(ADDRESS_WIDTH-1 downto 0) ) and
         (reg_read_address (ADDRESS_WIDTH) /=
          cnt_write_address(ADDRESS_WIDTH) )) then
         cmp_full <= '1';
      end if;
      -- pragma translate_off
      end if;
      -- pragma translate_on
   end process;

   -- Full and empty signals --------------------------------------------------
   sig_empty <= cmp_empty and sig_read_allowed and not sig_write_allowed;
   sig_full  <= cmp_full and not sig_read_allowed and sig_write_allowed;


   -- register reg_empty -----------------------------------------------------
   reg_emptyp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_empty <= '1';
         elsif (sig_empty_full_we = '1') then
            reg_empty <= sig_empty;
         end if;
      end if;
   end process;

   -- register reg_full ------------------------------------------------------
   reg_fullp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_full <= '0';
         elsif (sig_empty_full_we = '1') then
            reg_full <= sig_full;
         end if;
      end if;
   end process;

   -- last block identification ----------------------------------------------
   LAST_BLOCK_DETECTION : if (BLOCK_SIZE > 0) or STATUS_ENABLED generate

   lstblk_plus_one <= '1' when (cnt_diff = BLOCK_SIZE) and
                        (sig_read_allowed = '1') and
                        (sig_write_allowed = '0')
             else
                   '0';

   lstblk_minus_one <= '1' when (cnt_diff = BLOCK_SIZE + 1 ) and
                           (sig_write_allowed = '1') and
                           (sig_read_allowed = '0')
         else
                    '0';

   -- cnt_diff counter
   cnt_diff_ce <= sig_read_allowed xor sig_write_allowed;
   cnt_diff_dir <= sig_read_allowed;
   process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_diff <= conv_std_logic_vector(ITEMS, cnt_diff'length);
         elsif (cnt_diff_ce = '1') then
            if (cnt_diff_dir = '1') then
               cnt_diff <= cnt_diff + 1;
            else
               cnt_diff <= cnt_diff - 1;
            end if;
         end if;
      end if;
   end process;

   -- reg_lstblk register and comparator
   process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            if (BLOCK_SIZE < ITEMS) then
               reg_lstblk <= '0';
            else
               reg_lstblk <= '1';
            end if;
         elsif (lstblk_plus_one = '1') or (lstblk_minus_one = '1') then
            reg_lstblk <= lstblk_minus_one and not lstblk_plus_one;
         end if;
      end if;
   end process;

   end generate;

   -- Output signals ----------------------------------------------------------
   FULL  <= reg_full;
   LSTBLK <= reg_lstblk;
   STATUS <= cnt_diff;

   -- Optional output register -------------------------------------------------
   no_do_reg_gen : if not DO_REG generate
     EMPTY <= reg_empty;
     DATA_OUT <= do;
     re <= READ_REQ;
   end generate;
   do_reg_gen : if DO_REG generate
     EMPTY <= out_empty;
     re <= READ_REQ or out_empty;
     regs : process(CLK)
     begin
       if CLK'event and CLK='1' then
         if RESET='1' then
           out_empty <= '1';
         elsif re='1' then
           out_empty <= reg_empty;
         end if;
         if re='1' then
           DATA_OUT <= do;
         end if;
       end if;
     end process;
   end generate;

end architecture behavioral;
