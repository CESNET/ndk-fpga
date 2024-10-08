-- general.vhd: Closed-loop solution CDC
-- Copyright (C) 2014 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;

   --! -------------------------------------------------------------------------
   --!                      Entity declaration
   --! -------------------------------------------------------------------------

entity ASYNC_GENERAL is
   Generic (
      --! For two synchronization registers TWO_REG=true.
      --! For three synchronization registers TWO_REG=false.
      TWO_REG             : BOOLEAN := false;

      --! When DETECT_RISING_EDGE=true  and DETECT_FALLING_EDGE=true
      --! are detected rising edges and falling edges.
      --! When DETECT_RISING_EDGE=true  and DETECT_FALLING_EDGE=false
      --! are detected rising edges.
      --! When DETECT_RISING_EDGE=false and DETECT_FALLING_EDGE=true
      --! are detected falling edges.
      --! When DETECT_RISING_EDGE=false and DETECT_FALLING_EDGE=false
      --! are detected log.1.
      DETECT_RISING_EDGE  : BOOLEAN := false;
      DETECT_FALLING_EDGE : BOOLEAN := false
   );
   Port (
      --! A clock domain
      ACLK      : in  STD_LOGIC;   --! Source clock
      ARST      : in  STD_LOGIC;   --! Source reset
      ADATAIN   : in  STD_LOGIC;   --! Data in
      AREADY    : out STD_LOGIC;   --! Ready signal

      --! B clock domain
      BCLK      : in  STD_LOGIC;   --! Target clock
      BRST      : in  STD_LOGIC;   --! Target reset
      BDATAOUT  : out STD_LOGIC    --! Data out
   );
end ASYNC_GENERAL;

   --! -------------------------------------------------------------------------
   --!                      Architecture declaration
   --! -------------------------------------------------------------------------

architecture FULL of ASYNC_GENERAL is

   signal adata         : std_logic := '0';
   signal adata_next    : std_logic := '0';
   signal bdata         : std_logic;
   signal bdata_q       : std_logic := '0';
   signal aack          : std_logic;
   signal signal_aready : std_logic;

--! -------------------------------------------------------------------------
begin
--! -------------------------------------------------------------------------

   signal_aready <= aack XNOR adata;
   BDATAOUT      <= bdata XOR bdata_q;

   --! -------------------------------------------------------------------------
   --! Generics detect rising edge on
   detect_edge_on : if ((DETECT_RISING_EDGE AND DETECT_FALLING_EDGE) OR (NOT DETECT_RISING_EDGE AND DETECT_FALLING_EDGE) OR (DETECT_RISING_EDGE AND NOT DETECT_FALLING_EDGE)) generate

      --! FSM
      FSM: entity work.ASYNC_GENERAL_FSM
      generic map(
         DETECT_RISING_EDGE  => DETECT_RISING_EDGE,
         DETECT_FALLING_EDGE => DETECT_FALLING_EDGE
      )
      port map(
         ACLK       => ACLK,
         ARST       => ARST,
         ADATAIN    => ADATAIN,
         ADATA      => adata,
         SIG_AREADY => signal_aready,
         AREADY     => AREADY
      );

   --! -------------------------------------------------------------------------
   end generate;
   --! -------------------------------------------------------------------------

   --! Generics detect rising edge off
   detect_edge_off : if NOT DETECT_RISING_EDGE AND NOT DETECT_FALLING_EDGE generate

      AREADY     <= signal_aready;
      adata_next <= adata XOR ADATAIN;

      --! adata register
      process(ACLK)
      begin
         if (rising_edge(ACLK)) then
            if (ARST = '1') then
               adata <= '0';
            elsif (signal_aready = '1') then
               adata <= adata_next;
            end if;
         end if;
      end process;

   --! -------------------------------------------------------------------------
   end generate;
   --! -------------------------------------------------------------------------

   --! Open-loop
   ASYNC_OPEN_LOOP: entity work.ASYNC_OPEN_LOOP
   generic map(
      IN_REG  => false,    --! We do not use!
      TWO_REG => TWO_REG
   )
   port map(
      ACLK     => ACLK,
      BCLK     => BCLK,
      ARST     => ARST,
      BRST     => BRST,
      ADATAIN  => adata,
      BDATAOUT => bdata
   );

   --! -------------------------------------------------------------------------

   --! Output register
   process(BCLK)
      begin
      if (rising_edge(BCLK)) then
         if (BRST = '1') then
            bdata_q <= '0';
         else
            bdata_q <= bdata;
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------------------

   --! Open-loop for feedback
   ASYNC_OPEN_LOOP_FEEDBACK: entity work.ASYNC_OPEN_LOOP
   generic map(
      IN_REG  => false,    --! We do not use!
      TWO_REG => TWO_REG
   )
   port map(
      ACLK     => BCLK,
      BCLK     => ACLK,
      ARST     => BRST,
      BRST     => ARST,
      ADATAIN  => bdata,
      BDATAOUT => aack
   );

   --! -------------------------------------------------------------------------

end architecture FULL;
