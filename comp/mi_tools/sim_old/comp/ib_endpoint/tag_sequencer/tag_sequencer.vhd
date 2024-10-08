-- tag_sequencer.vhd: Retagger and returned tag order-forcing module
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use ieee.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TAG_SEQUENCER is
   generic (
      --+ Width of TAG signals to Endpoint. Has impact on memory depth.
      EP_TAG_WIDTH      : integer := 8;
      --+ Width of TAG signals to user. Has impact on memory width.
      USR_TAG_WIDTH     : integer := 8
   );
   port (
      --+ Common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      --+ UP direction
      USR_TAG        : in  std_logic_vector(USR_TAG_WIDTH-1 downto 0);
      USR_REQ        : in  std_logic;
      USR_ACK        : out std_logic;
      USR_TRANS_TYPE : in  std_logic_vector(1 downto 0);
      EP_TAG         : out std_logic_vector(EP_TAG_WIDTH-1 downto 0);
      EP_REQ         : out std_logic;
      EP_ACK         : in  std_logic;
      EP_TRANS_TYPE  : OUT std_logic_vector(1 downto 0);

      --+ DOWN direction
      EP_OP_TAG      : in  std_logic_vector(EP_TAG_WIDTH-1 downto 0);
      EP_OP_DONE     : in  std_logic;
      USR_OP_TAG     : out std_logic_vector(USR_TAG_WIDTH-1 downto 0);
      USR_OP_DONE    : out std_logic;

      --* Completition buffer is full
      FULL           : out std_logic;
      --* Completition buffer is empty
      EMPTY          : out std_logic;

      --* Sibling Tag Sequencer wants to send USR_OP_DONE
      --* (set to 0 if you don't know what that is)
      SIBLING_PAUSE_IN : in  std_logic;

      --* This Tag Sequencer wants its sibling to pause its USR_OP_DONE stream
      --* (ignore if you don't know what that is)
      SIBLING_PAUSE_OUT : out std_logic
   );
end entity TAG_SEQUENCER;

-- ----------------------------------------------------------------------------
--                                 Architecture
-- ----------------------------------------------------------------------------
architecture FULL of TAG_SEQUENCER is

   signal start_ptr     : std_logic_vector(EP_TAG_WIDTH downto 0);
   signal end_ptr       : std_logic_vector(EP_TAG_WIDTH downto 0);
   signal start_ptr_en  : std_logic;
   signal end_ptr_en    : std_logic;

   signal sig_full      : std_logic;
   signal sig_empty     : std_logic;

   signal tag_dob       : std_logic_vector(USR_TAG_WIDTH-1 downto 0);

   signal pend_we       : std_logic;
   signal pend_di       : std_logic;
   signal pend_addra    : std_logic_vector(EP_TAG_WIDTH-1 downto 0);
   signal pend_dob      : std_logic;

   signal fifo_do       : std_logic_vector(EP_TAG_WIDTH-1 downto 0);
   signal fifo_read     : std_logic;
   signal fifo_empty    : std_logic;

   signal reg_ep_op_tag : std_logic_vector(EP_TAG_WIDTH-1 downto 0);
   signal reg_ep_op_done: std_logic;

-- ----------------------------------------------------------------------------
--                        Architecture implementation
-- ----------------------------------------------------------------------------
begin

   -- Normal FIFO addressing

   --* Full detection comparator
   full_p : process(start_ptr, end_ptr)
   begin
      sig_full <= '0';
      if (start_ptr(EP_TAG_WIDTH-1 downto 0) = end_ptr(EP_TAG_WIDTH-1 downto 0)) and
         (start_ptr(EP_TAG_WIDTH) /= end_ptr(EP_TAG_WIDTH)) then
         sig_full <= '1';
      end if;
   end process;

   --* Empty detection comparator
   empty_p : process(start_ptr, end_ptr)
   begin
      sig_empty <= '0';
      if (start_ptr = end_ptr) then
         sig_empty <= '1';
      end if;
   end process;

   FULL <= sig_full;
   EMPTY <= sig_empty;

   --* Start pointer
   start_ptr_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            start_ptr <= (others => '0');
         else
            if start_ptr_en = '1' then
               start_ptr <= start_ptr + 1;
            end if;
         end if;
      end if;
   end process;

   --* End pointer
   end_ptr_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            end_ptr <= (others => '0');
         else
            if end_ptr_en = '1' then
               end_ptr <= end_ptr + 1;
            end if;
         end if;
      end if;
   end process;
   -- Step pointer only for acknowledged transactions
   end_ptr_en <= EP_ACK;

   -- Use pointer as TAG.
   EP_TAG <= end_ptr(EP_TAG_WIDTH-1 downto 0);

   -- Do not change transaction type.
   EP_TRANS_TYPE <= USR_TRANS_TYPE;

   -- Forward request only if not full
   EP_REQ <= USR_REQ and (not sig_full);

   -- Forward ACK always
   USR_ACK <= EP_ACK;

   --* TAG translation memory
   tag_mem_i : entity work.dp_distmem
   generic map(
      DATA_WIDTH     => USR_TAG_WIDTH,
      ITEMS          => 2**EP_TAG_WIDTH
   )
   port map(
      DI             => USR_TAG,
      WE             => EP_ACK,
      WCLK           => CLK,
      ADDRA          => end_ptr(EP_TAG_WIDTH-1 downto 0),
      DOA            => open,

      ADDRB          => start_ptr(EP_TAG_WIDTH-1 downto 0),
      DOB            => tag_dob
   );

   --* Pending transactions memory
   pending_mem_i : entity work.dp_distmem
   generic map(
      DATA_WIDTH     => 1,
      ITEMS          => 2**EP_TAG_WIDTH
   )
   port map(
      DI(0)          => pend_di,
      WE             => pend_we,
      WCLK           => CLK,
      ADDRA          => pend_addra,
      DOA            => open,

      ADDRB          => start_ptr(EP_TAG_WIDTH-1 downto 0),
      DOB(0)         => pend_dob
   );

   fifo_i : entity work.fifo
   generic map(
      DATA_WIDTH     => EP_TAG_WIDTH,
      ITEMS          => 2**EP_TAG_WIDTH,
      BLOCK_SIZE     => 0
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,

      DATA_IN  => EP_OP_TAG,
      WRITE_REQ=> EP_OP_DONE,
      FULL     => open,
      LSTBLK   => open,

      DATA_OUT => fifo_do,
      READ_REQ => fifo_read,
      EMPTY    => fifo_empty
   );

   -- Read if not empty and (EP does not ack, or we're full)
   fifo_read <= (not fifo_empty) and ((not EP_ACK) or sig_full);

   -- 0 if processing DONEs, 1 else
   pend_di <= not fifo_read;

   -- Write to pending memory if transaction was sent to EP,
   -- or if processing DONEs
   pend_we <= EP_ACK or fifo_read;

   --* Address multiplexer
   pend_addra_mx : process(fifo_do, fifo_read, end_ptr)
   begin
      if (fifo_read = '1') then
         pend_addra <= fifo_do;
      else
         pend_addra <= end_ptr(EP_TAG_WIDTH-1 downto 0);
      end if;
   end process;

   USR_OP_TAG <= tag_dob;

   start_ptr_en <= (not pend_dob) and (not sig_empty) and
                   (not SIBLING_PAUSE_IN);

   SIBLING_PAUSE_OUT <= (not pend_dob) and (not sig_empty);

   USR_OP_DONE <= start_ptr_en;

end architecture FULL;
