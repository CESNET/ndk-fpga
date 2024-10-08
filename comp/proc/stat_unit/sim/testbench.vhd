-- testbench.vhd: Testbench of stat_unit entity
-- Copyright (C) 2011 CESNET
-- Author(s): Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use std.textio.all;
use IEEE.std_logic_textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

    constant CLKPER         : time      := 10 ns;
    constant RESET_TIME     : time      := 10 * CLKPER;

    constant LAST_REG_READ_ADDR	: std_logic_vector(31 downto 0) := X"00000048";
    constant LAST_SIZE_HIST_ADDR	: std_logic_vector(31 downto 0) := X"000010FC";
    constant BASE_ADDR 		: std_logic_vector := X"00000000";
    constant LIMIT_ADDR		: std_logic_vector := X"00010000";

    signal clk           : std_logic;
    signal reset         : std_logic;

    -- ibuf status interface
    signal sop_n          : std_logic := '0';
    signal eop            : std_logic := '0';
    signal eop_pos        : std_logic_vector(2 downto 0) := (others=>'0');
    signal sop_align_size : std_logic_vector(0 downto 0) := "1";

    signal payload_len    : std_logic_vector(15 downto 0) := (others=>'0');
    signal frame_error    : std_logic := '0'; -- 0: OK, 1: Error occured
    signal crc_check_failed:std_logic := '0'; -- 0: OK, 1: Bad CRC
    signal mac_check_failed:std_logic := '0'; -- 0: OK, 1: Bad MAC
    signal len_below_min  : std_logic := '0'; -- 0: OK, 1: Length is below min
    signal len_over_mtu   : std_logic := '0'; -- 0: OK, 1: Length is over MTU
    signal frame_rec      : std_logic := '0';
    signal frame_dis      : std_logic := '0';
    signal buff_ovf       : std_logic := '0';
    signal stat_dv        : std_logic := '0';
    signal stat_bcast     : std_logic := '0';
    signal stat_mcast     : std_logic := '0';

    --control
    signal   start_en               : std_logic;
    signal   sw_reset               : std_logic;
    signal   reset_after_read       : std_logic_vector(25 downto 0); --reset after read bits
    signal   read_en                : std_logic;
    signal   last_addr_en           : std_logic;

    --stat output
    signal   out_stat_dv            : std_logic;
    signal   out_mac_check_failed   : std_logic_vector(63 downto 0);
    signal   out_frames_received    : std_logic_vector(63 downto 0);
    signal   out_frames_discarded   : std_logic_vector(63 downto 0);
    signal   out_total_packet_traf  : std_logic_vector(63 downto 0);
    signal   out_buffer_ovf         : std_logic_vector(63 downto 0);
    signal   out_size_sum_count     : std_logic_vector(63 downto 0);
    signal   out_size_sum           : std_logic_vector(63 downto 0);
    signal   out_crc_err            : std_logic_vector(63 downto 0);
    signal   out_over_mtu           : std_logic_vector(63 downto 0);
    signal   out_below_mtu          : std_logic_vector(63 downto 0);
    signal   out_max_size           : std_logic_vector(15 downto 0);
    signal   out_min_size           : std_logic_vector(15 downto 0);
    signal   out_min_delay          : std_logic_vector(63 downto 0);
    signal   out_max_delay          : std_logic_vector(63 downto 0);
    signal   out_last_read_delay    : std_logic_vector(63 downto 0);
    signal   out_bcast_frames       : std_logic_vector(63 downto 0);
    signal   out_mcast_frames       : std_logic_vector(63 downto 0);
    signal   out_fragment_frames    : std_logic_vector(63 downto 0);
    signal   out_jabber_frames      : std_logic_vector(63 downto 0);
    signal   out_undersize_frames   : std_logic_vector(63 downto 0);
    signal   out_frames_64          : std_logic_vector(63 downto 0);
    signal   out_frames_65_127      : std_logic_vector(63 downto 0);
    signal   out_frames_128_255     : std_logic_vector(63 downto 0);
    signal   out_frames_256_511     : std_logic_vector(63 downto 0);
    signal   out_frames_512_1023    : std_logic_vector(63 downto 0);
    signal   out_frames_1024_1518   : std_logic_vector(63 downto 0);
    signal   out_frames_over_1518   : std_logic_vector(63 downto 0);

begin

-----------------
-- Stat unit	--
-----------------
uut:entity work.stat_unit
 port map(
	CLK   => clk,
	RESET	=> reset,

	--stat. inputs
   SOP      => sop_n,
   EOP      => eop,
   EOP_POS  => eop_pos,
   SOP_ALIGN_SIZE => sop_align_size,

   STAT_PAYLOAD_LEN       => payload_len,
   STAT_FRAME_ERROR       => frame_error,
   STAT_CRC_CHECK_FAILED  => crc_check_failed,
   STAT_MAC_CHECK_FAILED  => mac_check_failed,
   STAT_LEN_BELOW_MIN     => len_below_min,
   STAT_LEN_OVER_MTU      => len_over_mtu,
   STAT_FRAME_RECEIVED    => frame_rec,
   STAT_FRAME_DISCARDED   => frame_dis,
   STAT_BUFFER_OVF        => buff_ovf,
   STAT_MAC_BCAST         => stat_bcast,
   STAT_MAC_MCAST         => stat_mcast,
   STAT_DV                => stat_dv,

  --control
   START_EN               => start_en,
   SW_RESET               => sw_reset,
   RESET_AFTER_READ       => reset_after_read,
   READ_EN                => read_en,
   LAST_ADDR_EN           => last_addr_en,

  --stat output
   OUT_STAT_DV            => out_stat_dv,
   OUT_MAC_CHECK_FAILED   => out_mac_check_failed,
   OUT_FRAMES_RECEIVED    => out_frames_received,
   OUT_FRAMES_DISCARDED   => out_frames_discarded,
   OUT_TOTAL_PACKET_TRAF  => out_total_packet_traf,
   OUT_BUFFER_OVF         => out_buffer_ovf,
   OUT_SIZE_SUM_COUNT     => out_size_sum_count,
   OUT_SIZE_SUM           => out_size_sum,
   OUT_CRC_ERR            => out_crc_err,
   OUT_OVER_MTU           => out_over_mtu,
   OUT_BELOW_MIN          => out_below_mtu,
   OUT_MAX_SIZE           => out_max_size,
   OUT_MIN_SIZE           => out_min_size,
   OUT_MIN_DELAY          => out_min_delay,
   OUT_MAX_DELAY          => out_max_delay,
   OUT_LAST_READ_DELAY    => out_last_read_delay,
   OUT_BCAST_FRAMES       => out_bcast_frames,
   OUT_MCAST_FRAMES       => out_mcast_frames,
   OUT_FRAGMENT_FRAMES    => out_fragment_frames,
   OUT_JABBER_FRAMES      => out_jabber_frames,
   OUT_UNDERSIZE_FRAMES   => out_undersize_frames,
   OUT_FRAMES_64          => out_frames_64,
   OUT_FRAMES_65_127      => out_frames_65_127,
   OUT_FRAMES_128_255     => out_frames_128_255,
   OUT_FRAMES_256_511     => out_frames_256_511,
   OUT_FRAMES_512_1023    => out_frames_512_1023,
   OUT_FRAMES_1024_1518   => out_frames_1024_1518,
   OUT_FRAMES_OVER_1518   => out_frames_over_1518
 );

-----------------------
--	Clocks & Resets	--
-----------------------

--User clk
clkgen: process
begin
   clk <= '1';
   wait for CLKPER/2;
   clk <= '0';
   wait for CLKPER/2;
end process;

--reset generator
reset_gen : process
begin
   RESET <= '1';
   wait for RESET_TIME;
   wait for 1 ns;
   RESET <= '0';
   wait;
end process reset_gen;

-----------------
--	Testbench	--
-----------------
tb: process

		-- support for stat signals
		-- reset stat signals and waits one clock
		procedure reset_stat is
		begin
			sop_n <= '0';
         eop <= '0';
         eop_pos <= (others=>'0');

			payload_len <= (others=>'0');
			frame_error <= '0';
			crc_check_failed <= '0'; -- 0: OK, 1: Bad CRC
			mac_check_failed <= '0'; -- 0: OK, 1: Bad MAC
			len_below_min <= '0'; -- 0: OK, 1: Length is below min
			len_over_mtu <=  '0'; -- 0: OK, 1: Length is over MTU
			frame_rec <= '0';
         frame_dis <= '0';
         buff_ovf <= '0';
         stat_mcast <= '0';
         stat_bcast <= '0';
         stat_dv <= '0';
         sop_align_size <= (others=>'0');

			--wait one clock
			wait for CLKPER;
		end reset_stat;

begin

	--Reset & wait
	wait until RESET = '0';
	wait for 2*CLKPER;
   reset_stat; --restart stat. signals

   --set unit
   start_en <= '1';
   reset_after_read <= (others=>'0');
   sw_reset <= '0';
   sop_align_size <= "0";
   wait for CLKPER;

   --1)delay measure test
   sop_n <= '1';
   wait for CLKPER;
   sop_n <= '0';
   wait for CLKPER;
   eop <= '1';
   eop_pos <= "011";
   wait for CLKPER;
   eop <= '0';
   wait for CLKPER;
   sop_n <= '1';
   wait for CLKPER;
   sop_n <= '0';
   eop <= '1';
   eop_pos <= "000";
   wait for CLKPER;
   sop_n <= '1';
   eop <= '0';
   wait for CLKPER;
   sop_n <= '0';
   eop <= '1';
   eop_pos <= "110";
   wait for CLKPER;
   reset_stat;

   --2)read to read measure
   read_en <= '1'; --make snapshot
   wait for 2*CLKPER;
   read_en <= '0';
   wait for 4*CLKPER;
   last_addr_en <= '1';
   wait for CLKPER;
   last_addr_en <= '0';
   wait for 4*CLKPER;
   read_en <= '1';
   wait for CLKPER;
   read_en<= '0';
   last_addr_en <= '1';
   wait for CLKPER;
   last_addr_en <= '0';

   --3) try reset after read(reset all registers and counters)
   reset_after_read <= (others=>'1');
   wait for 2*CLKPER;
   read_en <= '1';
   wait for 2*CLKPER;
   read_en<= '0';
   last_addr_en <= '1';
   wait for CLKPER;
   last_addr_en <= '0';
   reset_after_read <= (others=>'0');
   wait for CLKPER;

   --3)try to change all counters (based on stat_dv)
   stat_dv <= '1';
   buff_ovf <= '1';
   frame_dis <= '1';
   frame_rec <= '1';
   len_below_min <= '1';
   len_over_mtu <= '1';
   mac_check_failed <= '1';
   crc_check_failed <= '1';
   payload_len <= (others=>'1');
   wait for CLKPER;
   reset_stat;

   --4)try sw_reset (reset all counters and registers, leave snapshot untouched)
   read_en <= '1'; --make snapshot
   wait for CLKPER;
   read_en <= '0';
   sw_reset <= '1';
   wait for CLKPER;
   sw_reset <= '0';
   wait for 2*CLKPER;
   last_addr_en <= '1';
   wait for CLKPER;
   last_addr_en <= '0';

   wait;
end process;

end architecture behavioral;
