-- multiplexer.vhd: FrameLink Multiplexer
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Puš <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               ENTITY DECLARATION
-- ----------------------------------------------------------------------------

-- * FrameLink Multiplexer merges more FrameLinks into one Multiplexed FL.
entity FL_MULTIPLEXER is
   generic(
      --* FrameLink data width
      DATA_WIDTH     : integer := 64;
      --* Number of FrameLink channels
      CHANNELS       : integer := 4
   );
   port(
      --+ Common interface
      CLK            : in std_logic;
      RESET          : in std_logic;

      --+ Input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(CHANNELS-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(CHANNELS-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(CHANNELS-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(CHANNELS-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(CHANNELS-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(CHANNELS-1 downto 0);
      RX_DATA        : in  std_logic_vector(DATA_WIDTH*CHANNELS-1 downto 0);
      RX_DREM        : in  std_logic_vector(CHANNELS*log2(DATA_WIDTH/8)-1 downto 0);

      --+ Output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_DREM        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      --* Output FrameLink interface: one bit for each channel
      TX_DST_RDY_N   : in  std_logic_vector(CHANNELS-1 downto 0);

      --* Determines the number of active input channel
      TX_CHANNEL     : out std_logic_vector(log2(CHANNELS)-1 downto 0)
   );
end entity FL_MULTIPLEXER;

-- ----------------------------------------------------------------------------
--                            ARCHITECTURE DECLARATION
-- ----------------------------------------------------------------------------
--* FULL arhitecture implementing the module
architecture fl_multiplexer_arch of FL_MULTIPLEXER is

   constant REM_WIDTH : integer := log2(DATA_WIDTH/8);
   --* data, drem, (s/e)o(p/f)
   constant MUX_WORD:integer:=DATA_WIDTH+REM_WIDTH+4; -- data, rem, (s/e)o(f/p)

   signal reg_last_sel     : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal shift            : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal firstone         : std_logic_vector(log2(CHANNELS)-1 downto 0);
   signal sel              : std_logic_vector(log2(CHANNELS)-1 downto 0);

   signal channel_rdy      : std_logic_vector(CHANNELS-1 downto 0);
   signal channel_rdy_sh   : std_logic_vector(CHANNELS-1 downto 0);
   signal rx_dst_rdy       : std_logic_vector(CHANNELS-1 downto 0);

   signal output_enable    : std_logic;

   signal mux_din          : std_logic_vector(CHANNELS*MUX_WORD-1 downto 0);
   signal mux_dout         : std_logic_vector(MUX_WORD-1 downto 0);

begin
   channel_gen : for i in 0 to CHANNELS-1 generate
      channel_rdy(i) <= not(RX_SRC_RDY_N(i) or TX_DST_RDY_N(i));

      mux_din(i*MUX_WORD) <= RX_SOP_N(i);
      mux_din(i*MUX_WORD+1) <= RX_EOP_N(i);
      mux_din(i*MUX_WORD+2) <= RX_SOF_N(i);
      mux_din(i*MUX_WORD+3) <= RX_EOF_N(i);
      mux_din((i*MUX_WORD)+4+REM_WIDTH-1 downto (i*MUX_WORD)+4) <=
         RX_DREM((i+1)*REM_WIDTH-1 downto i*REM_WIDTH);
      mux_din((i*MUX_WORD)+4+REM_WIDTH+DATA_WIDTH-1 downto
              (i*MUX_WORD)+4+REM_WIDTH) <=
         RX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH);
   end generate;

   shift <= reg_last_sel + 1;

   --* This module mixes channel priorities.
   shifter_i : entity work.barrel_bit_shifter
   generic map(
      DATA_WIDTH  => CHANNELS,
      SHIFT_LEFT  => false
   )
   port map(
      DATA_IN     => channel_rdy,
      DATA_OUT    => channel_rdy_sh,
      SEL         => shift
   );

   --* This module selects active input
   firstone_i : entity work.first_one_detector
   generic map(
      DATA_WIDTH  => CHANNELS
   )
   port map(
      MASK              => channel_rdy_sh,
      FIRST_ONE_ONEHOT  => open,
      FIRST_ONE_BINARY  => firstone,
      FIRST_ONE_PRESENT => output_enable
   );

   sel <= firstone + shift;

   --* Store the last selected channel
   reg_last_sel_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_last_sel <= (others => '0');
         else
            if output_enable = '1' then
               reg_last_sel <= sel;
            end if;
         end if;
      end if;
   end process;

   --* Output multiplexer
   out_mux_i : entity work.gen_mux
   generic map(
      DATA_WIDTH  => MUX_WORD,
      MUX_WIDTH   => CHANNELS
   )
   port map(
      DATA_IN     => mux_din,
      SEL         => sel,
      DATA_OUT    => mux_dout
   );

   --* Binary to onehot encoder for RX_DST_RDY_N setting
   dec1ofn_i : entity work.dec1fn_enable
   generic map(
      ITEMS    => CHANNELS
   )
   port map(
      ADDR     => sel,
      ENABLE   => output_enable,
      DO       => rx_dst_rdy
   );

   -- Output interface mapping
   TX_DATA     <= mux_dout(4+REM_WIDTH+DATA_WIDTH-1 downto 4+REM_WIDTH);
   TX_DREM     <= mux_dout(4+REM_WIDTH-1 downto 4);
   TX_EOF_N    <= mux_dout(3);
   TX_SOF_N    <= mux_dout(2);
   TX_EOP_N    <= mux_dout(1);
   TX_SOP_N    <= mux_dout(0);
   TX_SRC_RDY_N<= not output_enable;
   TX_CHANNEL  <= sel;

   rx_dst_rdy_n_p : process(rx_dst_rdy, output_enable, TX_DST_RDY_N)
   begin
      if output_enable = '1' then
         RX_DST_RDY_N<= not rx_dst_rdy;
      else
         RX_DST_RDY_N <= TX_DST_RDY_N;
      end if;
   end process;

end fl_multiplexer_arch;

