-- switch_impl_fifo.vhd: Switch with FIFO (IFNUM is in the non-first word)
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

--* Implementation of switching logic with FIFO.
--* The implementation uses FL_DFIFO, that can discard the last frame that
--* is stored there. This is useful to solve critical situations:
--* <ul>
--*   <li>The frame is too short, so it does not contain the FINUM.</li>
--*   <li>The IFNUM is placed in a non-first FrameLink Part and at the end
--*         of one of the preceding Part there was some bits (Bytes) discarded
--*         by RX_REM signal (so the computation of the IFNUM position is wrong now.</li>
--*   <li>The IFNUM is located at the end of a FrameLink Part and it is
--*         cutted by RX_REM. the IFNUM is incomplete and can not be used.</li>
--*   <li>The extracted IFNUM disallows all TX interfaces, so the current frame
--*         should be discarded.</li>
--* </ul>
architecture fifo of fl_switch_impl is

   --* Offset of the IFNUM in WORDs
   constant WORD_OFFSET : integer := (INUM_OFFSET / DATA_WIDTH) / 8;
   --* Offset of the IFNUM in bits (location in the word)
   constant BITS_OFFSET : integer := INUM_OFFSET mod DATA_WIDTH;
   --* The space needed in the FIFO
   constant FIFO_ITEMS  : integer := WORD_OFFSET + 1;
   --* Data width of cnt_scan counter
   constant CNT_SCAN_WIDTH : integer := log2(max(FIFO_ITEMS, 1));

   --* Bit vector of 1 (for comparation with RX_REM)
   constant ONES_REM    : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0) := (others => '1');
   --* Bit vector of 0 (for comparation with IFNUM)
   constant ZEROS_IFNUM : std_logic_vector(TX_COUNT - 1 downto 0) := (others => '0');

   --* RELOAD signal from tx_out_array component
   signal tx_out_reload : std_logic;
   --* IFNUM signal that is connected to tx_out_array component
   signal tx_out_ifnum  : std_logic_vector(TX_COUNT - 1 downto 0);
   --* Enable/disable sending in the tx_out_array component
   signal send_en_n     : std_logic;

   --* Register from storing the IFNUM
   signal reg_ifnum     : std_logic_vector(TX_COUNT - 1 downto 0);
   signal reg_ifnum_ce  : std_logic;
   signal reg_ifnum_clr : std_logic;

   --+ Control signals of the FIFO
   signal fifo_read_rdy_n     : std_logic;
   signal fifo_read_en_n      : std_logic;
   signal fifo_write_rdy_n    : std_logic;
   signal fifo_write_en_n     : std_logic;
   signal fifo_discard        : std_logic;

   --+ Critical situation detection
   signal frame_end_too_early : std_logic;
   signal space_between_parts : std_logic;
   signal ifnum_incomplete    : std_logic;
   signal ifnum_eq_zeros      : std_logic;

   --* The switch just now reads from RX
   signal rx_reading    : std_logic;
   --* The next incoming word will contain the IFNUM (when rx_reading is active)
   signal next_is_ifnum : std_logic;
   --* The current word contains the FIFO (when rx_reading is active)
   signal ifnum_comes   : std_logic;

   --* Counter of incoming words (counts from RX_SOF_N)
   signal cnt_scan      : std_logic_vector(CNT_SCAN_WIDTH - 1 downto 0);
   signal cnt_scan_ce   : std_logic;
   signal cnt_scan_clr  : std_logic;

begin

   -- on next CLK a word will be read
   rx_reading     <= not(fifo_read_en_n or fifo_read_rdy_n);
   -- the next word contains IFNUM
   next_is_ifnum  <= '1' when cnt_scan + 1 = conv_std_logic_vector(WORD_OFFSET, CNT_SCAN_WIDTH) else '0';
   -- IFNUM is contained in the current word
   ifnum_comes    <= '1' when cnt_scan = WORD_OFFSET else '0';

   fifo_discard   <= rx_reading and (frame_end_too_early
                                       or space_between_parts
                                       or ifnum_incomplete
                                       or ifnum_eq_zeros);

   fifo_write_en_n   <= tx_out_reload;
   send_en_n         <= fifo_write_rdy_n;
   fifo_read_en_n    <= RX_SRC_RDY_N;
   RX_DST_RDY_N      <= fifo_read_rdy_n;

   -- detecting the critical sitations
   frame_end_too_early  <= '1' when RX_EOF_N = '0' and next_is_ifnum = '0'    else '0';
   space_between_parts  <= '1' when RX_EOP_N = '0' and RX_REM < ONES_REM      else '0';
   ifnum_incomplete     <= '1' when RX_EOP_N = '0' and next_is_ifnum = '1'
                                    and (BITS_OFFSET + TX_COUNT)/8 < RX_REM   else '0';
   ifnum_eq_zeros       <= '1' when IFNUM = ZEROS_IFNUM and ifnum_incomplete = '0' else '0';

   -- reg_ifnum and cnt_scan ctrl
   reg_ifnum_ce   <= next_is_ifnum;
   reg_ifnum_clr  <= fifo_discard or RESET;

   cnt_scan_ce    <= rx_reading;
   cnt_scan_clr   <= '1' when rx_reading = '1' and RX_EOF_N = '0' else '0';

   -- multiplexor to set up a new IFNUM to tx_out_array or to use the stored one
   tx_out_ifnum   <= IFNUM when ifnum_comes = '1' else reg_ifnum;

   register_ifnum : process(CLK, reg_ifnum_ce, reg_ifnum_clr)
   begin
      if CLK = '1' and CLK'event then
         if reg_ifnum_clr = '1' then
            reg_ifnum <= (others => '0');
         elsif reg_ifnum_ce = '1' then
            reg_ifnum <= IFNUM;
         end if;
      end if;
   end process;

   --* The counter is used when scanning for the word with the IFNUM.
   --* It stops when the word with IFNUM comes. When the word with the IFNUM
   --* is read, the counter must be cleared for another job first.
   counter_scan : process(CLK, cnt_scan_ce, cnt_scan_clr)
   begin
      if CLK'event and CLK = '1' then
         if cnt_scan_clr = '1' then
            cnt_scan <= (others => '0');
         elsif cnt_scan_ce = '1' and ifnum_comes = '0' then
            cnt_scan <= cnt_scan + 1;
         end if;
      end if;
   end process;

   -- FL_DFIFO used to store temporary data from RX until the IFNUM comes.
   out_fifo : entity work.fl_dfifo
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      ITEMS => FIFO_ITEMS,
      PARTS => PARTS
   )
   port map (
      CLK   => CLK,
      RESET => RESET,
      DISCARD  => fifo_discard,

      -- Read interface
      RX_DATA  => RX_DATA,
      RX_REM   => RX_REM,
      RX_SOP_N => RX_SOP_N,
      RX_EOP_N => RX_EOP_N,
      RX_SOF_N => RX_SOF_N,
      RX_EOF_N => RX_EOF_N,
      RX_SRC_RDY_N   => fifo_read_en_n,
      RX_DST_RDY_N   => fifo_read_rdy_n,

      -- Write interface
      TX_DATA  => TX_DATA,
      TX_REM   => TX_REM,
      TX_SOP_N => TX_SOP_N,
      TX_EOP_N => TX_EOP_N,
      TX_SOF_N => TX_SOF_N,
      TX_EOF_N => TX_EOF_N,
      TX_SRC_RDY_N   => fifo_write_rdy_n,
      TX_DST_RDY_N   => fifo_write_en_n
   );

   -- Block of TX_OUT units. Solves the TX_SRC_RDY_N/TX_DST_RDY_N logic.
   tx_out_array  : entity work.tx_out_array
   generic map (
      TX_COUNT    => TX_COUNT,
      DATA_WIDTH  => DATA_WIDTH
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,
      IFNUM    => tx_out_ifnum,
      RELOAD   => tx_out_reload,
      SEND_EN_N      => send_en_n,
      TX_SRC_RDY_N   => TX_SRC_RDY_N,
      TX_DST_RDY_N   => TX_DST_RDY_N
   );

end architecture;
