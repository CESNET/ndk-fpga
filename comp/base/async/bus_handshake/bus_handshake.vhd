--!
--! bus_handshake.vhd: Bus handshake synchronizer.
--! Copyright (C) 2014 CESNET
--! Author(s): Jakub Cabal <cabal@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!
--! TODO:

library IEEE;
use IEEE.std_logic_1164.all;

   --! -------------------------------------------------------------------------
   --!                      Entity declaration
   --! -------------------------------------------------------------------------

entity ASYNC_BUS_HANDSHAKE is
   Generic (
      DATA_WIDTH : integer := 32;  --! Data BUS width
      DATA_RESET : boolean := true
   );
   Port (
      --! A clock domain
      ACLK     : in  STD_LOGIC; --! Source clock
      ARST     : in  STD_LOGIC; --! Source reset
      ADATAIN  : in  STD_LOGIC_VECTOR(DATA_WIDTH-1 downto 0); --! Data in
      ASEND    : in  STD_LOGIC; --! Data send signal
      AREADY   : out STD_LOGIC; --! Ready signal

      --! B clock domain
      BCLK     : in  STD_LOGIC; --! Target clock
      BRST     : in  STD_LOGIC; --! Target reset
      BDATAOUT : out STD_LOGIC_VECTOR(DATA_WIDTH-1 downto 0) := (others => '0'); --! Data out
      BLOAD    : in  STD_LOGIC; --! Data load signal
      BVALID   : out STD_LOGIC  --! Data valid signal
   );
end ASYNC_BUS_HANDSHAKE;

   --! -------------------------------------------------------------------------
   --!                      Architecture declaration
   --! -------------------------------------------------------------------------

architecture FULL of ASYNC_BUS_HANDSHAKE is

   signal anxt_data       : std_logic;
   signal adata           : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
   signal a_ack           : std_logic;
   signal a_en            : std_logic := '0';
   signal a_en_next       : std_logic;
   signal b_en            : std_logic;
   signal b_ack           : std_logic := '0';
   signal b_ack_next      : std_logic;
   signal bload_data      : std_logic;
   signal bdata           : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
   signal signal_aready   : std_logic;
   signal signal_bvalid   : std_logic;
   signal signal_bvalid_n : std_logic;

   --! -------------------------------------------------------------------------
begin
   --! -------------------------------------------------------------------------

   --! Control logic
   anxt_data     <= ASEND AND signal_aready;
   a_en_next     <= a_en XOR anxt_data;
   bload_data    <= signal_bvalid AND BLOAD;
   b_ack_next    <= b_ack XOR bload_data;
   signal_bvalid <= not signal_bvalid_n;

   --! Outputs signals
   AREADY <= signal_aready;
   BVALID <= signal_bvalid;

   --! -------------------------------------------------------------------------

   --! a_ack PULSE GENRATOR
   a_ack_PULSE_GENRATOR: entity work.SYNC_PGEN
   port map(
      ADATAIN  => b_ack,
      BCLK     => ACLK,
      ACLK     => BCLK,
      BRST     => ARST,
      ARST     => BRST,
      BEN      => a_ack,
      BDATAOUT => open
   );

   --! -------------------------------------------------------------------------

   --! b_en PULSE GENRATOR
   b_en_PULSE_GENRATOR: entity work.SYNC_PGEN
   port map(
      ADATAIN  => a_en,
      BCLK     => BCLK,
      ACLK     => ACLK,
      BRST     => BRST,
      ARST     => ARST,
      BEN      => b_en,
      BDATAOUT => open
   );

   --! -------------------------------------------------------------------------

   --! TRANSMIT FSM
   TRANSMIT_FSM: entity work.BUS_HANDSHAKE_FSM
   port map(
      CLK    => ACLK,
      RST    => ARST,
      ACK    => a_ack,
      EVENT  => ASEND,
      READY  => signal_aready
   );

   --! -------------------------------------------------------------------------

   --! RECEIVE FSM
   RECEIVE_FSM: entity work.BUS_HANDSHAKE_FSM
   port map(
      CLK    => BCLK,
      RST    => BRST,
      ACK    => BLOAD,
      EVENT  => b_en,
      READY  => signal_bvalid_n
   );

   --! -------------------------------------------------------------------------

   --! a_en REGISTER
   process(ACLK)
   begin
      if (rising_edge(ACLK)) then
         if (ARST = '1') then
            a_en <= '0';
         else
            a_en <= a_en_next;
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------------------

   --! b_ack REGISTER
   process(BCLK)
   begin
      if (rising_edge(BCLK)) then
         if (BRST = '1') then
            b_ack <= '0';
         else
            b_ack <= b_ack_next;
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------------------

   --! TRANSMIT DATA REGISTER
   process(ACLK)
   begin
      if (rising_edge(ACLK)) then
         if (DATA_RESET and ARST = '1') then
            adata <= (others => '0');
         elsif (anxt_data = '1') then
            adata <= ADATAIN;
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------------------

   --! RECEIVE DATA REGISTER
   process(BCLK)
   begin
      if (rising_edge(BCLK)) then
         if (DATA_RESET and BRST = '1') then
            bdata <= (others => '0');
         elsif (b_en = '1') then
            bdata <= adata;
         end if;
      end if;
   end process;

   BDATAOUT <= bdata;

   --! -------------------------------------------------------------------------

end architecture FULL;
