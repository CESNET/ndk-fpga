-- distributor_ifsel_word_non0.vhd: FrameLink distributor full architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture inum_in_word_non0 of fl_distributor_ifsel is

   -- width needed for the INUM (number of interface)
   constant INUM_WIDTH : integer := log2(INTERFACES_COUNT);

   -- width of the RX_REM signal
   constant REM_WIDTH : integer := log2(DATA_WIDTH/8);

	constant INUM_FIFO_LEN : integer := (INUM_OFFSET / DATA_WIDTH) + 1;
	-- word that contains the INUM
   constant INUM_POS_WORD : integer := INUM_FIFO_LEN - 1;


   signal reg_inum         : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal reg_inum_set     : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal reg_inum_ce      : std_logic;

   signal out_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_rem          : std_logic_vector(REM_WIDTH-1 downto 0);
   signal out_sop_n        : std_logic;
   signal out_eop_n        : std_logic;
   signal out_sof_n        : std_logic;
   signal out_eof_n        : std_logic;

   signal fifo_rx_src_rdy_n : std_logic;
   signal fifo_rx_dst_rdy_n : std_logic;
   signal fifo_tx_src_rdy_n : std_logic;
   signal fifo_tx_dst_rdy_n : std_logic;

   signal fifo_write_en : std_logic;
   signal is_reading    : std_logic;
   signal is_writing    : std_logic;

   signal cnt_scan   : std_logic_vector(log2(INUM_FIFO_LEN + 1)-1 downto 0);
   signal cnt_scan_ce : std_logic;
   signal cnt_scan_clr : std_logic;

	signal cnt_total : std_logic_vector(log2(INUM_FIFO_LEN + 1)-1 downto 0);
	signal cnt_total_inc : std_logic;
	signal cnt_total_dec : std_logic;

begin

RX_DST_RDY_N <= fifo_rx_dst_rdy_n;
is_reading <= not(RX_SRC_RDY_N or fifo_rx_dst_rdy_n);
fifo_rx_src_rdy_n <= RX_SRC_RDY_N;

TX_SRC_RDY_N <= fifo_tx_src_rdy_n or not(fifo_write_en);
is_writing <= not(fifo_tx_dst_rdy_n or fifo_tx_src_rdy_n);
fifo_tx_dst_rdy_n <= TX_DST_RDY_N or not(fifo_write_en);

cnt_scan_clr <= '1' when is_reading = '1' and RX_EOF_N = '0' else '0';
cnt_scan_ce <= '1' when is_reading = '1' and cnt_scan <= conv_std_logic_vector(INUM_FIFO_LEN, cnt_scan'length) else '0';

cnt_total_inc <= is_reading;
cnt_total_dec <= is_writing;

reg_inum_ce <= '1' when (is_reading = '1' and cnt_scan = INUM_POS_WORD)
                        or (RX_EOP_N = '0' and RX_REM = (REM_WIDTH-1 downto 0 => '1') ) else '0';
fifo_write_en <= '1' when cnt_total > cnt_scan or
               (cnt_scan = conv_std_logic_vector(INUM_FIFO_LEN, cnt_scan'length)) else '0';

TX_DATA <= out_data;
TX_REM <= out_rem;
TX_SOP_N <= out_sop_n;
TX_EOP_N <= out_eop_n;
TX_SOF_N <= out_sof_n;
TX_EOF_N <= out_eof_n;

TX_INTERFACE <= reg_inum;

register_inum : process(CLK, reg_inum_ce, reg_inum_set)
   begin
      if CLK'event and CLK = '1' then
			if RESET = '1' then
				reg_inum <= conv_std_logic_vector(DEFAULT_INTERFACE, reg_inum'length);

         elsif reg_inum_ce = '1' then
            reg_inum <= reg_inum_set;

         end if;
      end if;
   end process;

counter_scan : process(CLK, RESET, cnt_scan_ce, cnt_scan_clr)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' or cnt_scan_clr = '1' then
            cnt_scan <= (others => '0');

         elsif cnt_scan_ce = '1' then
            cnt_scan <= cnt_scan + 1;

         end if;
      end if;
   end process;

counter_total : process(CLK, RESET, cnt_total_inc, cnt_total_dec, cnt_total)
	begin
		if CLK'event and CLK = '1' then
			if RESET = '1' then
				cnt_total <= (others => '0');

			elsif cnt_total_inc = '1' and cnt_total_dec = '0' and cnt_total < INUM_FIFO_LEN then
				cnt_total <= cnt_total + 1;

			elsif cnt_total_inc = '0' and cnt_total_dec = '1' and cnt_total > 0 then
				cnt_total <= cnt_total - 1;

			end if;
		end if;
	end process;

out_fifo : entity work.FL_FIFO
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      USE_BRAMS => false,
      ITEMS => INUM_FIFO_LEN,
      PARTS => PARTS
   )
   port map (
      CLK => CLK,
      RESET => RESET,

      RX_DATA => RX_DATA,
      RX_REM => RX_REM,
      RX_SRC_RDY_N => fifo_rx_src_rdy_n,
      RX_DST_RDY_N => fifo_rx_dst_rdy_n,
      RX_SOP_N => RX_SOP_N,
      RX_EOP_N => RX_EOP_N,
      RX_SOF_N => RX_SOF_N,
      RX_EOF_N => RX_EOF_N,

      TX_DATA => out_data,
      TX_REM => out_rem,
      TX_SRC_RDY_N => fifo_tx_src_rdy_n,
      TX_DST_RDY_N => fifo_tx_dst_rdy_n,
      TX_SOP_N => out_sop_n,
      TX_EOP_N => out_eop_n,
      TX_SOF_N => out_sof_n,
      TX_EOF_N => out_eof_n,

      FULL => open,
      EMPTY => open,
      FRAME_RDY => open,

      STATUS => open,
      LSTBLK => open
   );

inum_extract : entity work.inum_extract
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      INUM_WIDTH => INUM_WIDTH,
      INUM_OFFSET => INUM_OFFSET,
      MASK       => MASK
   )
   port map (
      RX_DATA => RX_DATA,
      RX_REM => RX_REM,
      RX_EOP_N => RX_EOP_N,
		LAST_INUM => reg_inum,
      INUM => reg_inum_set
   );

end architecture;
