-- stat_unit_arch.vhd: Architecture of statistical unit with RFC2819 support
-- Copyright (C) 2011,2013,2016 CESNET
-- Author(s): Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of stat_unit is

   -- ----------------------------------------------------
   -- Input signals
   -- -----------------------------------------------------
   --! Input stat. signals
   signal input_sop					      : std_logic;
   signal input_sop_tmp1               : std_logic;
   signal input_sop_tmp2               : std_logic;

   signal input_eop                    : std_logic;
   signal input_eop_pos                : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal input_stat_payload_len	      : std_logic_vector(15 downto 0);
   signal input_stat_payload_len_64	   : std_logic_vector(63 downto 0);
   signal input_stat_frame_error	      : std_logic;
   signal input_stat_crc_check_failed 	: std_logic;
   signal input_stat_mac_check_failed 	: std_logic;
   signal input_stat_len_below_min		: std_logic;
   signal input_stat_len_over_mtu		: std_logic;
   signal input_stat_dv	               : std_logic;
   signal input_stat_frame_received    : std_logic;
   signal input_stat_frame_discarded   : std_logic;
   signal input_stat_buffer_ovf        : std_logic;
   signal input_stat_mcast             : std_logic;
   signal input_stat_bcast             : std_logic;

   -- -----------------------------------------------------
   -- Command register	and control signals
   -- -----------------------------------------------------
   signal snapshot_en	      : std_logic_vector(6-1 downto 0);
   signal stat_sampling_en	   : std_logic;
   signal last_snap_addr_en   : std_logic;
   signal snap_addr_sel_en	   : std_logic;
   attribute keep : string;
   attribute keep of snapshot_en : signal is "true";

   -- -----------------------------------------------------
   -- Packet shift
   -- -----------------------------------------------------
   --! CLK shift engine
   signal packet_shift_tmp	   : std_logic_vector(63 downto 0);
   signal sop_eop_shift			: std_logic_vector(63 downto 0);
   signal sop_shift           : std_logic_vector(63 downto 0);
   signal packet_shift        : std_logic_vector(63 downto 0);
   signal sop_eop_en			   : std_logic;
   signal sop_eop_en2		   : std_logic;
   signal delay_reg_en	      : std_logic;

   -- -----------------------------------------------------
   -- Counters & control signals
   -- -----------------------------------------------------

   --! Signals for reset generating engine
   signal rd_reset_en                    : std_logic_vector(25 downto 0);
   signal reg_reset_en			           : std_logic;
   signal reset_vector                   : std_logic_vector(25 downto 0);
   signal cnt_last_read_delay_reset      : std_logic;

   --! Counters & registers
   signal cnt_bad_mac_packets       : std_logic_vector(63 downto 0); --Bad mac packets
   signal cnt_frame_received        : std_logic_vector(63 downto 0); --Good frames
   signal cnt_frame_discarded       : std_logic_vector(63 downto 0); --Discarded frames
   signal cnt_total_packet_trfc     : std_logic_vector(63 downto 0); --Total traffic
   signal cnt_buff_ovf_traff        : std_logic_vector(63 downto 0); --Buffer overflow
   signal cnt_proc_packets 		   : std_logic_vector(63 downto 0); --Total count of proc pkt
   signal cnt_crc_packets 		      : std_logic_vector(63 downto 0); --Pkt err
   signal cnt_pkt_over_mtu		      : std_logic_vector(63 downto 0); --Pkt over mtu
   signal cnt_pkt_below_min		   : std_logic_vector(63 downto 0); --Pkt below mtu
   signal reg_max_size		         : std_logic_vector(15 downto 0); --Max size
   signal reg_min_size		         : std_logic_vector(15 downto 0); --Min_size
   signal reg_min_pkt_delay 	      : std_logic_vector(63 downto 0); --Min pkt delay
   signal reg_max_pkt_delay 	      : std_logic_vector(63 downto 0); --Max pkt delay
   signal cnt_sum_pkt_size_ok       : std_logic_vector(63 downto 0);
   signal cnt_sum_pkt_size		      : std_logic_vector(63 downto 0); --A number of pkt in sum
   signal cnt_last_read_delay       : std_logic_vector(63 downto 0); --Read to read delay
   signal cnt_bcast_frames          : std_logic_vector(63 downto 0); --A number of bcast frames
   signal cnt_mcast_frames          : std_logic_vector(63 downto 0); --A number of mcast frames
   signal cnt_fragment_frames       : std_logic_vector(63 downto 0); --A number of frag. frames
   signal cnt_jabber_frames         : std_logic_vector(63 downto 0); --A number of jabber frames
   signal cnt_undersize_frames      : std_logic_vector(63 downto 0); --A number of frames below 64 Bytes
   --! Packet size histograms (with respect to RFC2819)
   signal cnt_frames_64             : std_logic_vector(63 downto 0);
   signal cnt_frames_65_127         : std_logic_vector(63 downto 0);
   signal cnt_frames_128_255        : std_logic_vector(63 downto 0);
   signal cnt_frames_256_511        : std_logic_vector(63 downto 0);
   signal cnt_frames_512_1023       : std_logic_vector(63 downto 0);
   signal cnt_frames_1024_1518      : std_logic_vector(63 downto 0);
   signal cnt_frames_over_1518      : std_logic_vector(63 downto 0);

   --! Counter & register enable signals
   signal max_pkt_delay    : std_logic;
   signal min_pkt_delay    : std_logic;
   signal total_frames     : std_logic;
   signal received_frames  : std_logic;
   signal discarded_frames : std_logic;
   signal crc_err          : std_logic;
   signal bad_mac_err      : std_logic;
   signal pkt_over_mtu     : std_logic;
   signal pkt_below_min    : std_logic;
   signal proc_packets     : std_logic;
   signal sum_pkt_size     : std_logic;
   signal sum_pkt_size_ok  : std_logic;
   signal min_size         : std_logic;
   signal max_size         : std_logic;
   signal buff_ovf_traff   : std_logic;
   signal bcast_frames     : std_logic;
   signal mcast_frames     : std_logic;
   signal fragment_frames  : std_logic;
   signal jabber_frames    : std_logic;
   signal undersize_frames : std_logic;
   signal frames_64        : std_logic;
   signal frames_65_127    : std_logic;
   signal frames_128_255   : std_logic;
   signal frames_256_511   : std_logic;
   signal frames_512_1023  : std_logic;
   signal frames_1024_1518 : std_logic;
   signal frames_over_1518 : std_logic;

   -- Counters add signals
   signal cnt_add_bad_mac_packets   : std_logic_vector(63 downto 0);
   signal cnt_add_frame_received    : std_logic_vector(63 downto 0);
   signal cnt_add_frame_discarded   : std_logic_vector(63 downto 0);
   signal cnt_add_total_packet_trfc : std_logic_vector(63 downto 0);
   signal cnt_add_buff_ovf_traff    : std_logic_vector(63 downto 0);
   signal cnt_add_proc_packets      : std_logic_vector(63 downto 0);
   signal cnt_add_crc_packets       : std_logic_vector(63 downto 0);
   signal cnt_add_pkt_over_mtu      : std_logic_vector(63 downto 0);
   signal cnt_add_pkt_below_min     : std_logic_vector(63 downto 0);
   signal cnt_add_sum_pkt_size_ok   : std_logic_vector(63 downto 0);
   signal cnt_add_sum_pkt_size      : std_logic_vector(63 downto 0);
   signal cnt_add_last_read_delay   : std_logic_vector(63 downto 0);
   signal cnt_add_bcast_frames      : std_logic_vector(63 downto 0);
   signal cnt_add_mcast_frames      : std_logic_vector(63 downto 0);
   signal cnt_add_fragment_frames   : std_logic_vector(63 downto 0);
   signal cnt_add_jabber_frames     : std_logic_vector(63 downto 0);
   signal cnt_add_frames_64         : std_logic_vector(63 downto 0);
   signal cnt_add_frames_65_127     : std_logic_vector(63 downto 0);
   signal cnt_add_frames_128_255    : std_logic_vector(63 downto 0);
   signal cnt_add_frames_256_511    : std_logic_vector(63 downto 0);
   signal cnt_add_frames_512_1023   : std_logic_vector(63 downto 0);
   signal cnt_add_frames_1024_1518  : std_logic_vector(63 downto 0);
   signal cnt_add_frames_over_1518  : std_logic_vector(63 downto 0);
   signal cnt_add_undersize_frames  : std_logic_vector(63 downto 0);

   --Repaired stat payload len
   signal repaired_stat_payload_len	   : std_logic_vector(63 downto 0);

begin

-- --------------------------------------------------------
-- Map input
-- --------------------------------------------------------

input_pipe:process(CLK)
begin
   if(CLK = '1' and CLK'event)then
      if(RESET = '1')then
         input_sop_tmp1 <= '0';
         --input_eop <= '0';
         input_stat_dv <= '0';
      else --pipeline input signals
         input_sop_tmp1 <= SOP;
         --input_eop <= EOP;
         input_stat_dv <= STAT_DV;
      end if;
      input_eop_pos <= EOP_POS;
      input_stat_payload_len <= STAT_PAYLOAD_LEN;
      input_stat_frame_error <= STAT_FRAME_ERROR;
      input_stat_crc_check_failed <= STAT_CRC_CHECK_FAILED;
      input_stat_mac_check_failed <= STAT_MAC_CHECK_FAILED;
      input_stat_len_below_min <= STAT_LEN_BELOW_MIN;
      input_stat_len_over_mtu <= STAT_LEN_OVER_MTU;
      input_stat_frame_received <= STAT_FRAME_RECEIVED;
      input_stat_frame_discarded <= STAT_FRAME_DISCARDED;
      input_stat_buffer_ovf <= STAT_BUFFER_OVF;
      input_stat_mcast <= STAT_MAC_MCAST;
      input_stat_bcast <= STAT_MAC_BCAST;
   end if;
end process;

   -- -----------------------------------------------------
   -- Control signals
   -- -----------------------------------------------------

   --Position(bit):	||		Action:
   --================================
   --	0					||		Start(1)/Stop(0)
   -- 1					||		Reset(All counters and registers) -> software reset

   --read reset generation
   read_resetp:process(READ_EN,RESET_AFTER_READ,snapshot_en)
   begin
      for i in 0 to RESET_AFTER_READ'length-1 loop
         rd_reset_en(i) <= READ_EN and RESET_AFTER_READ(i) and not(snapshot_en(0));
      end loop;
   end process;

   --reset generation(registers, couters and snapshot registers)
   reg_reset_en <= RESET or SW_RESET;

   -- deriving value for reset_vector bits
   reset_vector <= rd_reset_en OR (25 downto 0 => reg_reset_en);

   --sampling signal
   stat_sampling_en  <= input_stat_dv and START_EN;

   -- -----------------------------------------------------
   -- Snapshot signal generation
   -- -----------------------------------------------------

   --Waits for READ_EN (take snapshot) and release iff LAST_ADDR_EN is active
   read_reqp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            snapshot_en <= (others => '0');
         else
            if(snapshot_en(0) = '0')then
               if(READ_EN = '1')then
                  snapshot_en <= (others => '1');
               end if;
            else
               if(LAST_ADDR_EN = '1')then
                  snapshot_en <= (others => '0');
               end if;
            end if;
         end if;
      end if;
   end process;

   --output stats valid.
   OUT_STAT_DV <= snapshot_en(0);

delay_genp:if(DELAY_EN)generate
   -- -----------------------------------------------------
   -- Byte delay
   -- -----------------------------------------------------
   delay_cntp : process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(SW_RESET = '1' or RESET = '1')then
            packet_shift_tmp <= (others=>'0');
         else
            if(EOP = '1' and SOP='0')then
               packet_shift_tmp <= conv_std_logic_vector((ETH_CLK_SIZE - conv_integer(EOP_POS) - 1),64); --unused place :)
				elsif(EOP='1' and SOP='1')then
					packet_shift_tmp <= conv_std_logic_vector(conv_integer(unsigned(SOP_ALIGN_SIZE))*4,64); --SOP byte offset
            else
               packet_shift_tmp <= packet_shift_tmp + ETH_CLK_SIZE;  --everything is unused
            end if;
         end if;
      end if;
   end process;

	sop_eop_enp1:process(CLK)
	begin
		if(CLK='1' and CLK'event)then
			sop_eop_en <= SOP and EOP;
		end if;
	end process;

	--sop='1' & eop='0'
   sop_shiftp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         sop_shift <= packet_shift_tmp +
                      conv_std_logic_vector(conv_integer(unsigned(SOP_ALIGN_SIZE))*4,64);
      end if;
   end process;

	--repair byte ofsset for (EOP='1' and SOP='1')
	sop_eop_shiftp:process(CLK)
	begin
		if(CLK='1' and CLK'event)then
			sop_eop_shift <= packet_shift_tmp - conv_integer(input_eop_pos) - 1;
		end if;
	end process;

	sop_eop_enp2:process(CLK)
	begin
		if(CLK='1' and CLK'event)then
			sop_eop_en2 <= sop_eop_en;
		end if;
	end process;

   --packet_shift <= packet_shift_tmp + sop_shift;
	--shift multiplexer
	shift_mux:process(sop_eop_en2,sop_eop_shift,sop_shift)
	begin
		if(sop_eop_en2 = '0')then
			packet_shift <= sop_shift;
		else
			packet_shift <= sop_eop_shift;
		end if;
	end process;

   --sop distritbution
   sop_tmp2_regp:process(CLK)
   begin
      if(CLK='1' and CLK'event)then
         if(RESET = '1')then
            input_sop_tmp2 <= '0';
         else
            input_sop_tmp2 <= input_sop_tmp1;
         end if;
      end if;
   end process;

   input_sop_muxp:process(input_sop_tmp1,input_sop_tmp2,sop_eop_en,sop_eop_en2)
   begin
      if(sop_eop_en='1' or sop_eop_en2='1')then
         input_sop <= input_sop_tmp2;
      else
         input_sop <= input_sop_tmp1;
      end if;
   end process;

   ------------ DELAY STATS enable
   --enable delay write iff:
   --	1] first pkt has been received

   first_packet_recp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(SW_RESET = '1' or RESET = '1')then
			   delay_reg_en <= '0';
		else
			if(EOP = '1' and START_EN = '1')then
				delay_reg_en <= '1';
			end if;
		end if;
	end if;
   end process;

   -- --------------------------------------------------------
   -- Min, Max delay regs
   -- --------------------------------------------------------

   --Trigger signal generation
   max_pkt_delay <= '1' when(input_sop = '1' and reg_max_pkt_delay < packet_shift
                              and delay_reg_en = '1')
                     else '0';

   min_pkt_delay <= '1' when(input_sop = '1' and reg_min_pkt_delay > packet_shift
                              and delay_reg_en = '1')
                    else '0';

   max_delayp:process(CLK)
   begin
   	if(CLK = '1' and CLK'event)then
   		if(reset_vector(13) = '1')then
   			reg_max_pkt_delay <= (others=>'0');
   		else
   			if(max_pkt_delay = '1')then
   				reg_max_pkt_delay <= packet_shift;
   			end if;
   		end if;
   	end if;
   end process;

   min_delayp:process(CLK)
   begin
   	if(CLK = '1' and CLK'event)then
   		if(reset_vector(12)='1')then
   			reg_min_pkt_delay <= (others=>'1');
   		else
   			if(min_pkt_delay = '1')then
   				reg_min_pkt_delay <= packet_shift;
   			end if;
   		end if;
   	end if;
   end process;

   --snapshot register
   delay_snapshotp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(snapshot_en(1) = '0')then
            OUT_MIN_DELAY <= reg_min_pkt_delay;
            OUT_MAX_DELAY <= reg_max_pkt_delay;
         end if;
      end if;
   end process;
   end generate;

   no_delay_genp:if(DELAY_EN = false)generate
      OUT_MIN_DELAY <= (others=>'0');
      OUT_MAX_DELAY <= (others=>'0');
   end generate;

   -- --------------------------------------------------------
   -- Total trafic & Received & Discarded
   -- --------------------------------------------------------

   -- Trigger signal generation ------------------------------
   total_frames <= '1' when(stat_sampling_en = '1' and (input_stat_frame_received = '1' or
                           input_stat_frame_discarded = '1'))
                   else '0';

   received_frames <= '1' when(stat_sampling_en = '1' and input_stat_frame_received = '1')
                     else '0';

   discarded_frames <= '1' when(stat_sampling_en = '1' and input_stat_frame_discarded = '1')
                       else '0';

   buff_ovf_traff <= '1' when(stat_sampling_en = '1' and input_stat_buffer_ovf = '1' and
                              input_stat_frame_discarded = '1')
                     else '0';

   -- Counters -----------------------------------------------
   cnt_traffg: if NOT CNT_DSP generate

      total_packet_cntp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(reset_vector(3) = '1')then
               cnt_total_packet_trfc <= (others=>'0');
            else
               if(total_frames = '1')then
                  cnt_total_packet_trfc <= cnt_total_packet_trfc + 1;
               end if;
            end if;
         end if;
      end process;

      rec_packet_cntp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(reset_vector(1) ='1')then
               cnt_frame_received <= (others=>'0');
            else
               if(received_frames = '1')then
                  cnt_frame_received <= cnt_frame_received + 1;
               end if;
            end if;
         end if;
      end process;

      discarded_frames_cntp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(reset_vector(2) = '1')then
               cnt_frame_discarded <= (others=>'0');
            else
               if(discarded_frames = '1')then
                  cnt_frame_discarded <= cnt_frame_discarded + 1;
               end if;
            end if;
         end if;
      end process;

      buff_ovf_cntp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(reset_vector(4) = '1')then
               cnt_buff_ovf_traff <= (others=>'0');
            else
               if(buff_ovf_traff = '1')then
                  cnt_buff_ovf_traff <= cnt_buff_ovf_traff + 1;
               end if;
            end if;
         end if;
      end process;

   end generate;

   cnt_dsp_traffg: if CNT_DSP generate

      cnt_add_total_packet_trfc <= (63 downto 1 => '0') & total_frames;

      cnt_total_packet_trfc_i : entity work.COUNT_DSP
      generic map (
         DATA_WIDTH => 64,
         REG_IN     => 1
      )
      port map (
         CLK        => CLK,
         ENABLE     => '1',
         RESET      => reset_vector(3),
         A          => cnt_add_total_packet_trfc,
         MAX        => (others => '0'),
         P          => cnt_total_packet_trfc
      );


      cnt_add_frame_received <= (63 downto 1 => '0') & received_frames;

      cnt_frame_received_i : entity work.COUNT_DSP
      generic map (
         DATA_WIDTH => 64,
         REG_IN     => 1
      )
      port map (
         CLK        => CLK,
         ENABLE     => '1',
         RESET      => reset_vector(1),
         A          => cnt_add_frame_received,
         MAX        => (others => '0'),
         P          => cnt_frame_received
      );


      cnt_add_frame_discarded <= (63 downto 1 => '0') & discarded_frames;

      cnt_frame_discarded_i : entity work.COUNT_DSP
      generic map (
         DATA_WIDTH => 64,
         REG_IN     => 1
      )
      port map (
         CLK        => CLK,
         ENABLE     => '1',
         RESET      => reset_vector(2),
         A          => cnt_add_frame_discarded,
         MAX        => (others => '0'),
         P          => cnt_frame_discarded
      );


      cnt_add_buff_ovf_traff <= (63 downto 1 => '0') & buff_ovf_traff;

      cnt_buff_ovf_traff_i : entity work.COUNT_DSP
      generic map (
         DATA_WIDTH => 64,
         REG_IN     => 1
      )
      port map (
         CLK        => CLK,
         ENABLE     => '1',
         RESET      => reset_vector(4),
         A          => cnt_add_buff_ovf_traff,
         MAX        => (others => '0'),
         P          => cnt_buff_ovf_traff
      );

   end generate;

   -- snapshot register for CRC err & Rec. packets & len_(over|below)_mtu
   traff_snapshotp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(snapshot_en(2) = '0')then
            OUT_TOTAL_PACKET_TRAF   <= cnt_total_packet_trfc;
            OUT_FRAMES_RECEIVED     <= cnt_frame_received;
            OUT_FRAMES_DISCARDED    <= cnt_frame_discarded;
            OUT_BUFFER_OVF          <= cnt_buff_ovf_traff;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------
   -- CRC & MTU & MAC
   -- -------------------------------------------------------

   -- Trigger signal generation ------------------------------
   crc_err         <= '1' when(discarded_frames = '1' and input_stat_crc_check_failed = '1')
                      else '0';

   bad_mac_err     <= '1' when(discarded_frames = '1' and input_stat_mac_check_failed = '1')
                      else '0';

   pkt_over_mtu    <= '1' when(discarded_frames = '1' and input_stat_len_over_mtu = '1')
                      else '0';

   pkt_below_min   <= '1' when(discarded_frames = '1' and input_stat_len_below_min = '1')
                      else '0';

   -- Counters -----------------------------------------------
   cnt_crcg: if NOT CNT_DSP generate

      crc_genp:if(CRC_EN)generate
         crc_pckg_errp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(7) = '1')then
                  cnt_crc_packets <= (others=>'0');
               else
                  if(crc_err = '1')then
                     cnt_crc_packets <= cnt_crc_packets + 1;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      mac_genp:if(MAC_EN)generate
         mac_pckg_errp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(0) = '1')then
                  cnt_bad_mac_packets <= (others=>'0');
               else
                  if(bad_mac_err = '1')then
                     cnt_bad_mac_packets <= cnt_bad_mac_packets + 1;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      mtu_genp:if(MTU_EN)generate
         pkt_over_mtup:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(8) = '1')then
                  cnt_pkt_over_mtu <= (others=>'0');
               else
                  if(pkt_over_mtu = '1')then
                     cnt_pkt_over_mtu <= cnt_pkt_over_mtu + 1;
                  end if;
               end if;
            end if;
         end process;

         pkt_below_mtup:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(9) = '1')then
                  cnt_pkt_below_min <= (others=>'0');
               else
                  if(pkt_below_min = '1')then
                     cnt_pkt_below_min <= cnt_pkt_below_min + 1;
                  end if;
               end if;
            end if;
         end process;

      -- snapshot register for CRC err & Rec. packets & len_(over|below)_mtu
      mtu_crc_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(3) = '0')then
               OUT_CRC_ERR <= cnt_crc_packets;
               OUT_OVER_MTU <= cnt_pkt_over_mtu;
               OUT_BELOW_MIN <= cnt_pkt_below_min;
               OUT_MAC_CHECK_FAILED <= cnt_bad_mac_packets;
            end if;
         end if;
      end process;
      end generate;

   end generate;

   cnt_dsp_crcg: if CNT_DSP generate

      crc_genp:if(CRC_EN)generate
         cnt_add_crc_packets <= (63 downto 1 => '0') & crc_err;

         cnt_crc_packets_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(7),
            A          => cnt_add_crc_packets,
            MAX        => (others => '0'),
            P          => cnt_crc_packets
         );
      end generate;

      mac_genp:if(MAC_EN)generate
         cnt_add_bad_mac_packets <= (63 downto 1 => '0') & bad_mac_err;

         cnt_bad_mac_packets_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(0),
            A          => cnt_add_bad_mac_packets,
            MAX        => (others => '0'),
            P          => cnt_bad_mac_packets
         );
      end generate;

      mtu_genp:if(MTU_EN)generate
         cnt_add_pkt_over_mtu <= (63 downto 1 => '0') & pkt_over_mtu;

         cnt_pkt_over_mtu_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(8),
            A          => cnt_add_pkt_over_mtu,
            MAX        => (others => '0'),
            P          => cnt_pkt_over_mtu
         );


         cnt_add_pkt_below_min <= (63 downto 1 => '0') & pkt_below_min;

         cnt_pkt_below_min_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(9),
            A          => cnt_add_pkt_below_min,
            MAX        => (others => '0'),
            P          => cnt_pkt_below_min
         );

      -- snapshot register for CRC err & Rec. packets & len_(over|below)_mtu
      mtu_crc_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(3) = '0')then
               OUT_CRC_ERR <= cnt_crc_packets;
               OUT_OVER_MTU <= cnt_pkt_over_mtu;
               OUT_BELOW_MIN <= cnt_pkt_below_min;
               OUT_MAC_CHECK_FAILED <= cnt_bad_mac_packets;
            end if;
         end if;
      end process;
      end generate;

   end generate;

   no_crc_genp:if(CRC_EN = false)generate
      OUT_CRC_ERR    <= (others=>'0');
      OUT_OVER_MTU   <= (others=>'0');
      OUT_BELOW_MIN  <= (others=>'0');
      OUT_MAC_CHECK_FAILED <= (others=>'0');
   end generate;

   -- --------------------------------------------------------
   -- Packet  Min,Max,sum size
   -- --------------------------------------------------------

   --Trigger signal generation -------------------------------
      -- All processed packets(we are processing packet when the sampling of
      -- the input statistic is enabled)
   sum_pkt_size   <= '1' when(total_frames = '1')
                     else '0';

   sum_pkt_size_ok <= '1' when(total_frames = '1' and input_stat_frame_received = '1')
                      else '0';

   min_size       <= '1' when(total_frames = '1' and reg_min_size > repaired_stat_payload_len)
                     else '0';

   max_size       <= '1' when(total_frames = '1' and reg_max_size < repaired_stat_payload_len)
                     else '0';

   -- Value preparation -------------------------------------
   --! Prepare paylod length (RFC defines frame length with CRC!)
   REMOVE_CRC_GEN:if(INBANDFCS = false)generate
      repaired_stat_payload_len <= (X"000000000000" & input_stat_payload_len) + 4;
   end generate;

   NO_REMOVE_CRC_GEN:if(INBANDFCS = true)generate
      repaired_stat_payload_len <= (X"000000000000" & input_stat_payload_len);
   end generate;

   -- Counters -----------------------------------------------
   size_genp:if(SIZE_EN)generate

      cnt_sizeg: if NOT CNT_DSP generate
         proc_pckp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(5) = '1')then
                  cnt_proc_packets <= (others=>'0');
               else
                  if(total_frames = '1')then
                     cnt_proc_packets <= cnt_proc_packets + 1;
                  end if;
               end if;
            end if;
         end process;

         size_sump:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(6) = '1')then
                  cnt_sum_pkt_size <= (others=>'0');
               else
                  if(sum_pkt_size = '1')then
                     --add the recent value in register with actual value
                     cnt_sum_pkt_size <= cnt_sum_pkt_size +
                                             repaired_stat_payload_len;
                  end if;
               end if;
            end if;
         end process;

         ok_size_sump:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(6) = '1')then
                  cnt_sum_pkt_size_ok <= (others=>'0');
               else
                  if(sum_pkt_size_ok = '1')then
                     --add the recent value in register with actual value
                     cnt_sum_pkt_size_ok <= cnt_sum_pkt_size_ok +
                                             repaired_stat_payload_len;
                  end if;
               end if;
            end if;
         end process;

         min_pck_sizep:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(11) = '1')then
                  reg_min_size <= (others=>'1');
               else
                  if(min_size = '1')then
                     reg_min_size <= input_stat_payload_len;
                  end if;
               end if;
            end if;
         end process;

         max_pck_sizep:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(10) = '1')then
                  reg_max_size <= (others=>'0');
               else
                  if(max_size = '1')then
                     reg_max_size <= input_stat_payload_len;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      cnt_dsp_sizeg: if CNT_DSP generate

         cnt_add_proc_packets <= (63 downto 1 => '0') & total_frames;

         --A number of packets in sum
         cnt_proc_packets_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(5),
            A          => cnt_add_proc_packets,
            MAX        => (others => '0'),
            P          => cnt_proc_packets
         );


         cnt_add_sum_pkt_size <= repaired_stat_payload_len when (sum_pkt_size = '1') else
                                 (others => '0');

         cnt_sum_pkt_size_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(6),
            A          => cnt_add_sum_pkt_size,
            MAX        => (others => '0'),
            P          => cnt_sum_pkt_size
         );


         cnt_add_sum_pkt_size_ok <= repaired_stat_payload_len when (sum_pkt_size_ok = '1') else
                                    (others => '0');

         cnt_sum_pkt_size_ok_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(6),
            A          => cnt_add_sum_pkt_size_ok,
            MAX        => (others => '0'),
            P          => cnt_sum_pkt_size_ok
         );

         min_pck_sizep:process(CLK)
         begin
         	if(CLK = '1' and CLK'event)then
         		if(reset_vector(11) = '1')then
         			reg_min_size <= (others=>'1');
         		else
         			if(min_size = '1')then
         				reg_min_size <= input_stat_payload_len;
         			end if;
         		end if;
         	end if;
         end process;

         max_pck_sizep:process(CLK)
         begin
         	if(CLK = '1' and CLK'event)then
         		if(reset_vector(10) = '1')then
         			reg_max_size <= (others=>'0');
         		else
         			if(max_size = '1')then
         				reg_max_size <= input_stat_payload_len;
         			end if;
         		end if;
         	end if;
         end process;
      end generate;

      size_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(4) = '0')then
               OUT_MIN_SIZE <= reg_min_size;
               OUT_MAX_SIZE <= reg_max_size;
               OUT_SIZE_SUM <= cnt_sum_pkt_size;
               OUT_SIZE_SUM_OK      <= cnt_sum_pkt_size_ok;
               OUT_SIZE_SUM_COUNT   <= cnt_proc_packets;
            end if;
         end if;
      end process;
   end generate;

   no_size_genp:if(SIZE_EN = false)generate
      OUT_MIN_SIZE   <= (others=>'0');
      OUT_MAX_SIZE   <= (others=>'0');
      OUT_SIZE_SUM   <= (others=>'0');
      OUT_SIZE_SUM_OK      <= (others=>'0');
      OUT_SIZE_SUM_COUNT   <= (others=>'0');
   end generate;

   -- --------------------------------------------------------
   -- Read to read delay
   -- --------------------------------------------------------

   read_delay_genp:if(READ_DELAY_EN)generate

      cnt_delayg: if NOT CNT_DSP generate
         --read to read delay (-> iff snapshot is not taken)
         read_to_readp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reg_reset_en = '1' or (READ_EN = '1' and snapshot_en(0) = '0'))then
                  cnt_last_read_delay <= (others=>'0');
               else
                  if(START_EN = '1')then
                     cnt_last_read_delay <= cnt_last_read_delay + 1;
                  end if;
              end if;
            end if;
         end process;
      end generate;

      cnt_dsp_delayg: if CNT_DSP generate
         cnt_last_read_delay_reset <= reg_reset_en OR (READ_EN AND NOT snapshot_en(0));
         cnt_add_last_read_delay   <= (63 downto 1 => '0') & START_EN;

         --read to read delay (-> iff snapshot is not taken)
         cnt_last_read_delay_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => cnt_last_read_delay_reset,
            A          => cnt_add_last_read_delay,
            MAX        => (others => '0'),
            P          => cnt_last_read_delay
         );
      end generate;

      --read delay snapshot
      read_to_read_snapshot:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(0) = '0')then
               OUT_LAST_READ_DELAY <= cnt_last_read_delay;
            end if;
         end if;
      end process;

   end generate;

   no_read_delay_genp:if(READ_DELAY_EN = false)generate
      OUT_LAST_READ_DELAY <= (others=>'0');
   end generate;

   -- --------------------------------------------------------
   -- Multicast and broadcast counters
   -- --------------------------------------------------------
   -- Trigger signal generation ------------------------------
   bcast_frames <=   '1' when(stat_sampling_en = '1' and input_stat_bcast = '1' and
                              input_stat_frame_received = '1')
                     else '0';

   mcast_frames <=   '1' when(stat_sampling_en = '1' and input_stat_mcast = '1' and
                              input_stat_bcast = '0' and input_stat_frame_received = '1')
                     else '0';

   bcast_gen:if(BCAST_MCAST_EN)generate
      -- Counters -----------------------------------------------

      cnt_mcast_bcastg: if NOT CNT_DSP generate
         bcast_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(14) = '1')then
                  cnt_bcast_frames <= (others=>'0');
               else
                  if(bcast_frames = '1')then
                     cnt_bcast_frames <= cnt_bcast_frames + 1;
                  end if;
               end if;
            end if;
         end process;

         mcast_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(15) = '1')then
                  cnt_mcast_frames <= (others=>'0');
               else
                  if(mcast_frames = '1')then
                     cnt_mcast_frames <= cnt_mcast_frames + 1;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      cnt_dsp_mcast_bcastg: if CNT_DSP generate
         cnt_add_bcast_frames <= (63 downto 1 => '0') & bcast_frames;

         cnt_bcast_frames_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(14),
            A          => cnt_add_bcast_frames,
            MAX        => (others => '0'),
            P          => cnt_bcast_frames
         );

         cnt_add_mcast_frames <= (63 downto 1 => '0') & mcast_frames;

         cnt_mcast_frames_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(15),
            A          => cnt_add_mcast_frames,
            MAX        => (others => '0'),
            P          => cnt_mcast_frames
         );
      end generate;

      mcast_bcast_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(1) = '0')then
               OUT_MCAST_FRAMES <= cnt_mcast_frames;
               OUT_BCAST_FRAMES <= cnt_bcast_frames;
            end if;
         end if;
      end process;
   end generate;

   no_bcast_genp:if(BCAST_MCAST_EN = false)generate
      OUT_MCAST_FRAMES <= (others=>'0');
      OUT_BCAST_FRAMES <= (others=>'0');
   end generate;

   -- --------------------------------------------------------
   -- Multicast and broadcast counters
   -- --------------------------------------------------------
   -- Trigger signal generation ------------------------------
   fragment_frames <= '1' when(crc_err = '1' and input_stat_len_below_min = '1')
                      else '0';

   -- Jabber frame is a frame where the packet lenght is over 1518 bytes and it has a
   -- bad crc.
   jabber_frames  <= '1' when(crc_err = '1' and repaired_stat_payload_len > 1518)
                     else '0';

   fragment_jabber_gen:if(FRAGMENT_JABBER_EN)generate
      -- Counters -----------------------------------------------
      cnt_jabberg: if NOT CNT_DSP generate
         fragment_frames_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(16) = '1')then
                  cnt_fragment_frames <= (others=>'0');
               else
                  if(fragment_frames = '1')then
                     cnt_fragment_frames <= cnt_fragment_frames + 1;
                  end if;
               end if;
            end if;
         end process;

         jabber_frames_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(17) = '1')then
                  cnt_jabber_frames <= (others=>'0');
               else
                  if(jabber_frames = '1')then
                     cnt_jabber_frames <= cnt_jabber_frames + 1;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      cnt_dsp_jabberg: if CNT_DSP generate
         cnt_add_fragment_frames <= (63 downto 1 => '0') & fragment_frames;

         cnt_fragment_frames_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(16),
            A          => cnt_add_fragment_frames,
            MAX        => (others => '0'),
            P          => cnt_fragment_frames
         );


         cnt_add_jabber_frames <= (63 downto 1 => '0') & jabber_frames;

         cnt_jabber_frames_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(17),
            A          => cnt_add_jabber_frames,
            MAX        => (others => '0'),
            P          => cnt_jabber_frames
         );
      end generate;

      fragment_jabber_frames_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(1) = '0')then
               OUT_FRAGMENT_FRAMES  <= cnt_fragment_frames;
               OUT_JABBER_FRAMES    <= cnt_jabber_frames;
            end if;
         end if;
      end process;
   end generate;

   no_fragment_jabber_gen:if(FRAGMENT_JABBER_EN = false)generate
      OUT_FRAGMENT_FRAMES  <= (others=>'0');
      OUT_JABBER_FRAMES    <= (others=>'0');
   end generate;

   -- -----------------------------------------------------
   -- Undersize frames
   -- -----------------------------------------------------
   -- Trigger signal generation ---------------------------
   -- Process the length if sampling of the input is enabled
   undersize_frames  <= '1' when(stat_sampling_en = '1' and
                                repaired_stat_payload_len < 64)
                        else '0';

   undersize_gen: if UNDERSIZE_FRAMES_EN generate
      -- Generate the DSP version
      undersize_dsp: if CNT_DSP generate
            cnt_add_undersize_frames <= (63 downto 1 => '0') & undersize_frames;

            cnt_undersize_frames_i : entity work.COUNT_DSP
            generic map (
               DATA_WIDTH => 64,
               REG_IN     => 1
            )
            port map (
               CLK        => CLK,
               ENABLE     => '1',
               RESET      => reset_vector(25),
               A          => cnt_add_undersize_frames,
               MAX        => (others => '0'),
               P          => cnt_undersize_frames
            );
       end generate;

       -- Generate the behaviraol version of the counter
       undersize_cnt_gen: if NOT CNT_DSP generate
         fragment_frames_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(25) = '1')then
                  cnt_undersize_frames <= (others=>'0');
               else
                  if(undersize_frames = '1')then
                     cnt_undersize_frames <= cnt_undersize_frames + 1;
                  end if;
               end if;
            end if;
         end process;
       end generate;

       -- Snapshot register
      undersize_frames_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(1) = '0')then
               OUT_UNDERSIZE_FRAMES <= cnt_undersize_frames;
            end if;
         end if;
      end process;

   end generate;

   no_undersize_gen:if(NOT UNDERSIZE_FRAMES_EN)generate
      OUT_UNDERSIZE_FRAMES <= (others=>'0');
   end generate;

   -- -----------------------------------------------------
   -- Packet length histograms
   -- -----------------------------------------------------
   -- Trigger signal generation ---------------------------
   -- Process the length if sampling of the input is enabled

   frames_64         <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len = 64)
                        else '0';

   frames_65_127     <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len >=65 and
                                 repaired_stat_payload_len <= 127)
                        else '0';

   frames_128_255    <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len >= 128 and
                                 repaired_stat_payload_len <= 255)
                        else '0';

   frames_256_511    <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len >= 256 and
                                 repaired_stat_payload_len <= 511)
                        else '0';

   frames_512_1023   <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len >= 512 and
                                 repaired_stat_payload_len <= 1023)
                        else '0';

   frames_1024_1518  <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len >= 1024 and
                                 repaired_stat_payload_len <= 1518)
                        else '0';

   frames_over_1518  <= '1' when(stat_sampling_en = '1' and
                                 repaired_stat_payload_len > 1518)
                        else '0';


   payload_hist_gen:if(PAYLOAD_HISTOGRAM_EN)generate
      -- Counters --------------------------------------------
      cnt_size_histogramg: if NOT CNT_DSP generate
         frames_64_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(18) = '1')then
                  cnt_frames_64 <= (others=>'0');
               else
                  if(frames_64 = '1')then
                     cnt_frames_64 <= cnt_frames_64 + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_frames_65_127_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(19) = '1')then
                  cnt_frames_65_127 <= (others=>'0');
               else
                  if(frames_65_127 = '1')then
                     cnt_frames_65_127 <= cnt_frames_65_127 + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_frames_128_255_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(20) = '1')then
                  cnt_frames_128_255 <= (others=>'0');
               else
                  if(frames_128_255 = '1')then
                     cnt_frames_128_255 <= cnt_frames_128_255 + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_frames_256_511_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(21) = '1')then
                  cnt_frames_256_511 <= (others=>'0');
               else
                  if(frames_256_511 = '1')then
                     cnt_frames_256_511 <= cnt_frames_256_511 + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_frames_512_1023_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(22) = '1')then
                  cnt_frames_512_1023 <= (others=>'0');
               else
                  if(frames_512_1023 = '1')then
                     cnt_frames_512_1023 <= cnt_frames_512_1023 + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_frames_1024_1518_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(23) = '1')then
                  cnt_frames_1024_1518 <= (others=>'0');
               else
                  if(frames_1024_1518 = '1')then
                     cnt_frames_1024_1518 <= cnt_frames_1024_1518 + 1;
                  end if;
               end if;
            end if;
         end process;

         cnt_frames_over_1518_cntp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(reset_vector(24) = '1')then
                  cnt_frames_over_1518 <= (others=>'0');
               else
                  if(frames_over_1518 = '1')then
                     cnt_frames_over_1518 <= cnt_frames_over_1518 + 1;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      cnt_dsp_size_histogramg: if CNT_DSP generate
         cnt_add_frames_64 <= (63 downto 1 => '0') & frames_64;

         cnt_frames_64_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(18),
            A          => cnt_add_frames_64,
            MAX        => (others => '0'),
            P          => cnt_frames_64
         );


         cnt_add_frames_65_127 <= (63 downto 1 => '0') & frames_65_127;

         cnt_frames_65_127_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(19),
            A          => cnt_add_frames_65_127,
            MAX        => (others => '0'),
            P          => cnt_frames_65_127
         );


         cnt_add_frames_128_255 <= (63 downto 1 => '0') & frames_128_255;

         cnt_frames_128_255_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(20),
            A          => cnt_add_frames_128_255,
            MAX        => (others => '0'),
            P          => cnt_frames_128_255
         );


         cnt_add_frames_256_511 <= (63 downto 1 => '0') & frames_256_511;

         cnt_frames_256_511_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(21),
            A          => cnt_add_frames_256_511,
            MAX        => (others => '0'),
            P          => cnt_frames_256_511
         );


         cnt_add_frames_512_1023 <= (63 downto 1 => '0') & frames_512_1023;

         cnt_frames_512_1023_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(22),
            A          => cnt_add_frames_512_1023,
            MAX        => (others => '0'),
            P          => cnt_frames_512_1023
         );


         cnt_add_frames_1024_1518 <= (63 downto 1 => '0') & frames_1024_1518;

         cnt_frames_1024_1518_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(23),
            A          => cnt_add_frames_1024_1518,
            MAX        => (others => '0'),
            P          => cnt_frames_1024_1518
         );


         cnt_add_frames_over_1518 <= (63 downto 1 => '0') & frames_over_1518;

         cnt_frames_over_1518_i : entity work.COUNT_DSP
         generic map (
            DATA_WIDTH => 64,
            REG_IN     => 1
         )
         port map (
            CLK        => CLK,
            ENABLE     => '1',
            RESET      => reset_vector(24),
            A          => cnt_add_frames_over_1518,
            MAX        => (others => '0'),
            P          => cnt_frames_over_1518
         );
      end generate;

      size_histogram_snapshotp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(snapshot_en(5) = '0')then
               OUT_FRAMES_64          <= cnt_frames_64;
               OUT_FRAMES_65_127      <= cnt_frames_65_127;
               OUT_FRAMES_128_255     <= cnt_frames_128_255;
               OUT_FRAMES_256_511     <= cnt_frames_256_511;
               OUT_FRAMES_512_1023    <= cnt_frames_512_1023;
               OUT_FRAMES_1024_1518   <= cnt_frames_1024_1518;
               OUT_FRAMES_OVER_1518   <= cnt_frames_over_1518;
            end if;
         end if;
      end process;
   end generate;

   no_payload_hist_gen:if(PAYLOAD_HISTOGRAM_EN = false)generate
      OUT_FRAMES_64          <= (others=>'0');
      OUT_FRAMES_65_127      <= (others=>'0');
      OUT_FRAMES_128_255     <= (others=>'0');
      OUT_FRAMES_256_511     <= (others=>'0');
      OUT_FRAMES_512_1023    <= (others=>'0');
      OUT_FRAMES_1024_1518   <= (others=>'0');
      OUT_FRAMES_OVER_1518   <= (others=>'0');
   end generate;

end architecture behavioral;
