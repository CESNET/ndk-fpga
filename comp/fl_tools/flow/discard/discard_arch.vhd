-- discard_arch.vhd: FrameLink Discard full architecture.
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
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl_discard is

constant STATUS_WIDTH_B : integer := STATUS_WIDTH+log2(DATA_WIDTH/8);

type t_vect_status is array(0 to CHANNELS-1) of std_logic_vector(STATUS_WIDTH_B-1 downto 0);

signal cmp_en     : std_logic;
signal cmp_en_vect : std_logic_vector(CHANNELS-1 downto 0);
signal cmp_ok     : std_logic;

signal reg_cmp_ok : std_logic_vector(0 downto 0);
signal reg_cmp_ok_vect : std_logic_vector(CHANNELS-1 downto 0);

signal pass_frame : std_logic;

signal status_mux_bytes:t_vect_status;
signal free       : t_vect_status;
signal free_sub   : t_vect_status;
signal free_len   : std_logic_vector(CHANNELS*17-1 downto 0);
signal reg_free_len:std_logic_vector(CHANNELS*17-1 downto 0);
signal status_mux : std_logic_vector(16 downto 0);

signal frame_len  : std_logic_vector(16 downto 0);

constant zeros      : std_logic_vector(31 downto 0) := X"00000000";
signal max_free        : std_logic_vector(STATUS_WIDTH_B-1 downto 0);

signal reg_rx_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
signal reg_rx_drem     : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
signal reg_rx_src_rdy_n: std_logic;
signal reg_rx_sop_n    : std_logic;
signal reg_rx_eop_n    : std_logic;
signal reg_rx_sof_n    : std_logic;
signal reg_rx_eof_n    : std_logic;
signal reg_rx_chan     : std_logic_vector(log2(CHANNELS) - 1 downto 0);

begin

   assert CHANNELS > 1
      report "FL_DISCARD: CHANNELS must be > 1!"
      severity ERROR;

   assert STATUS_WIDTH+log2(DATA_WIDTH/8) <= 16
      report "FL_DISCARD: STATUS_WIDTH+log2(DATA_WIDTH/8) must be <= 16!"
      severity ERROR;

   assert DATA_WIDTH >= 16
      report "FL_DISCARD: DATA_WIDTH must be >= 16!"
      severity ERROR;


   -- Get frame length in BYTES from the first frame word
   frame_len <= '0' & RX_DATA(15 downto 0);


   -- Create number of all BYTES in the target (constant)
   max_free   <= '1' & zeros(STATUS_WIDTH-2 downto 0) &
                   zeros(log2(DATA_WIDTH/8)-1 downto 0);

   -- Severe logic duplication before pipelining register
   convert_status : for i in 0 to CHANNELS-1 generate

      -- Create number of non-free BYTES (not WORDS) by shifting
      status_mux_bytes(i)
         <= STATUS((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH)
            & zeros(log2(DATA_WIDTH/8)-1 downto 0);

      -- Compute number of free bytes in the target (substract)
      free(i) <= max_free - status_mux_bytes(i);

      latency1_gen : if OUTPUT_REG = false generate
         -- Substract one WORD, because STATUS input will be delayed for
         -- one cycle
         -- (But only if number overflow wouldn't occur)
         free_mux_sub_p : process(free)
         begin
            if free(i) > conv_std_logic_vector(DATA_WIDTH/8, STATUS_WIDTH_B) then
               free_sub(i)
                  <= free(i) - DATA_WIDTH/8;
            else -- Overflow would occur -> pretend there's no space left
               free_sub(i) <= zeros(STATUS_WIDTH_B-1 downto 0);
            end if;
         end process;
      end generate;

      latency2_gen : if OUTPUT_REG = true generate
         -- Substract two WORDS, because STATUS input will be delayed for
         -- one cycle, and FrameLink will be delayed also for one cycle
         -- (But only if number overflow wouldn't occur)
         free_mux_sub_p : process(free)
         begin
            if free(i) > conv_std_logic_vector(2*DATA_WIDTH/8, STATUS_WIDTH_B) then
               free_sub(i)
                  <= free(i) - 2*DATA_WIDTH/8;
            else -- Overflow would occur -> pretend there's no space left
               free_sub(i) <= zeros(STATUS_WIDTH_B-1 downto 0);
            end if;
         end process;
      end generate;

      -- Widen to 17bit width
      status_n16 : if STATUS_WIDTH_B < 17 generate
         free_len((i+1)*17-1 downto i*17)
            <= zeros(16 downto STATUS_WIDTH_B) & free_sub(i);
      end generate;
      status_16 : if STATUS_WIDTH_B = 17 generate
         free_len((i+1)*17-1 downto i*17) <= free_sub(i);
      end generate;

   end generate;

   --* Register for pipelining
   reg_free_len_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         reg_free_len <= free_len;
      end if;
   end process;

   --* Select appropriate information about free space
   status_mux_inst : entity work.gen_mux
   generic map(
      DATA_WIDTH  => 17,
      MUX_WIDTH   => CHANNELS
   )
   port map(
      DATA_IN     => reg_free_len,
      SEL         => RX_CHAN,
      DATA_OUT    => status_mux
   );
-------------------------------------------

   -- Compare frame length and available buffer space
   cmp_ok_p : process(frame_len, status_mux)
   begin
      if status_mux >= frame_len then
         cmp_ok <= '1';
      else
         cmp_ok <= '0';
      end if;
   end process;

   -- Detect when cmp_ok is valid (at the start of the frame)
   cmp_en <= (not RX_SRC_RDY_N) and (not RX_SOF_N);

   -- Send cmp_en to appropriate cmp_ok register
   cmp_en_dec1fn_inst : entity work.dec1fn_enable
   generic map (
     ITEMS  => CHANNELS
   )
   port map (
     ADDR   => RX_CHAN,
     ENABLE => cmp_en,
     DO     => cmp_en_vect
   );

GEN_REG_CMP_OK: for j in 0 to CHANNELS-1 generate

    -- Store compare result for the whole frame
    reg_cmp_ok_p : process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          reg_cmp_ok_vect(j) <= '0';
        else
          if (cmp_en_vect(j) = '1') then
            reg_cmp_ok_vect(j) <= cmp_ok;
          end if;
        end if;
      end if;
    end process;

   -- RDY logic
   RX_DST_RDY_N(j) <= STAT_CLEARING; -- active low when not clearing


end generate;

   -- Select appropriate reg_cmp_ok signal from its registers
   reg_cmp_ok_mux_inst : entity work.gen_mux
   generic map (
      DATA_WIDTH  => 1,
      MUX_WIDTH   => CHANNELS
   )
   port map (
      DATA_IN     => reg_cmp_ok_vect,
      SEL         => RX_CHAN,
      DATA_OUT    => reg_cmp_ok
   );

   -- This signal finally decides whether each word should, or should not be
   -- forwarded.
   pass_frame <= (cmp_ok and cmp_en) -- First frame word
                  or
                 (reg_cmp_ok(0) and not cmp_en); -- Other frame words

GEN_OUTPUT_REG: if OUTPUT_REG = true generate

   fl_reg_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_rx_chan <= (others => '0');
            reg_rx_data <= (others => '0');
            reg_rx_drem <= (others => '0');
            reg_rx_sop_n <= '1';
            reg_rx_eop_n <= '1';
            reg_rx_sof_n <= '1';
            reg_rx_eof_n <= '1';
            reg_rx_src_rdy_n <= '1';
         else
            reg_rx_chan <= RX_CHAN;
            reg_rx_data <= RX_DATA;
            reg_rx_drem <= RX_DREM;
            reg_rx_sop_n <= RX_SOP_N;
            reg_rx_eop_n <= RX_EOP_N;
            reg_rx_sof_n <= RX_SOF_N;
            reg_rx_eof_n <= RX_EOF_N;
            reg_rx_src_rdy_n <= RX_SRC_RDY_N or
                                (not pass_frame) or
                                (STAT_CLEARING);
         end if;
      end if;
   end process;

   -- RX_CHAN to TX_CHAN route through
   TX_CHAN <= reg_rx_chan;

   TX_SRC_RDY_N <= reg_rx_src_rdy_n;

   -- Rest of output signals (route through)
   TX_DATA     <= reg_rx_data;
   TX_DREM     <= reg_rx_drem;
   TX_SOP_N    <= reg_rx_sop_n;
   TX_EOP_N    <= reg_rx_eop_n;
   TX_SOF_N    <= reg_rx_sof_n;
   TX_EOF_N    <= reg_rx_eof_n;

end generate;

GEN_NOT_OUTPUT_REG: if OUTPUT_REG = false generate

   -- RX_CHAN to TX_CHAN route through
   TX_CHAN <= RX_CHAN;

   TX_SRC_RDY_N <= RX_SRC_RDY_N or (not pass_frame) or (STAT_CLEARING);

   -- Rest of output signals (route through)
   TX_DATA     <= RX_DATA;
   TX_DREM     <= RX_DREM;
   TX_SOP_N    <= RX_SOP_N;
   TX_EOP_N    <= RX_EOP_N;
   TX_SOF_N    <= RX_SOF_N;
   TX_EOF_N    <= RX_EOF_N;

end generate;

   -- Statistic interface
   STAT_PASS <= cmp_ok and cmp_en;
   STAT_DROP <= (not cmp_ok) and cmp_en;
   STAT_CHAN <= RX_CHAN;
   STAT_LEN <= frame_len(15 downto 0);
   STAT_FREE <= status_mux(15 downto 0);

end architecture full;

