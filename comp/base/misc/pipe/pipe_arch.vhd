--
-- pipe_arch.vhd : Internal Bus Pipeline
-- Copyright (C) 2013 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--            Lukas Kekely <kekely@cesnet.cz>
--            Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  Internal Bus Pipeline           --
-- ----------------------------------------------------------------------------

architecture pipe_arch of PIPE is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_0, S_1, S_2, S_RESET);
   signal present_state, next_state : fsm_states;

   signal ce,addr        : std_logic;
   signal dout           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_dout       : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
   signal dout_rdy       : std_logic;
   signal reg_dout_rdy   : std_logic;
   signal outreg_we      : std_logic;
   signal sig_in_src_rdy : std_logic;
   signal sig_in_dst_rdy : std_logic;

begin

-- debuging probe connections
debug_probe : entity work.STREAMING_DEBUG_PROBE
   port map (
      RX_SRC_RDY     => IN_SRC_RDY,
      RX_DST_RDY     => IN_DST_RDY,
      RX_SOP         => '0',
      RX_EOP         => '0',
      TX_SRC_RDY     => sig_in_src_rdy,
      TX_DST_RDY     => sig_in_dst_rdy,
      TX_SOP         => open,
      TX_EOP         => open,
      DEBUG_BLOCK    => DEBUG_BLOCK,
      DEBUG_DROP     => DEBUG_DROP,
      DEBUG_SRC_RDY  => DEBUG_SRC_RDY,
      DEBUG_DST_RDY  => DEBUG_DST_RDY,
      DEBUG_SOP      => open,
      DEBUG_EOP      => open
   );

NOT_FAKE_SHREG : if (FAKE_PIPE = false and PIPE_TYPE = "SHREG") generate

   -- -------------------------------------------------------------------------
   --                               DATA PATH                                --
   -- -------------------------------------------------------------------------

   SH_REG_DATA: entity work.SH_REG_BASE_DYNAMIC
     generic map(
       DATA_WIDTH => DATA_WIDTH,
       NUM_BITS   => 2,
       OPT        => OPT,
       DEVICE     => DEVICE
     )
     Port map(
       CLK  => CLK,
       CE   => ce,
       ADDR(0) => addr,

       DIN  => IN_DATA,
       DOUT => dout
     );

   -- without output registers
   OUTREG_NO : if (USE_OUTREG = false) generate

      outreg_we   <= OUT_DST_RDY;

      OUT_DATA    <= dout;
      OUT_SRC_RDY <= dout_rdy;

   end generate;

   -- with output registers
   OUTREG_YES : if (USE_OUTREG = true) generate

      reg_doutp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (outreg_we = '1') then
               reg_dout <= dout;
            end if;
         end if;
      end process;

      reg_dout_rdyp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (not RESET_BY_INIT and RESET = '1') then
               reg_dout_rdy <= '0';
            elsif (outreg_we = '1') then
               reg_dout_rdy <= dout_rdy;
            end if;
         end if;
      end process;

      outreg_we <= OUT_DST_RDY or not reg_dout_rdy;

      OUT_DATA    <= reg_dout;
      OUT_SRC_RDY <= reg_dout_rdy;

   end generate;


   -- -------------------------------------------------------------------------
   --                              CONTROL FSM                               --
   -- -------------------------------------------------------------------------

   -- synchronize logic -------------------------------------------------------
   synchlogp : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            present_state <= S_RESET;
         else
            present_state <= next_state;
         end if;
      end if;
   end process;

   -- next state logic --------------------------------------------------------
   nextstatelogicp : process(present_state,sig_in_src_rdy,outreg_we)
   begin
      next_state <= present_state;

      case (present_state) is

         when  S_0 =>
            if (sig_in_src_rdy = '1') then
               next_state <= S_1;
            end if;

         when  S_1 =>
            if (sig_in_src_rdy = '1') and (outreg_we = '0') then
               next_state <= S_2;
            elsif (outreg_we = '1') and (sig_in_src_rdy = '0') then
               next_state <= S_0;
            end if;

         when  S_2 =>
            if (outreg_we = '1') then
               next_state <= S_1;
            end if;

         when S_RESET =>
            next_state <= S_0;

      end case;
   end process;

   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state,sig_in_src_rdy)
   begin

      case (present_state) is

         when  S_0 =>
            ce             <= sig_in_src_rdy;
            addr           <= '0';
            dout_rdy       <= '0';
            sig_in_dst_rdy <= '1';

         when  S_1 =>
            ce             <= sig_in_src_rdy;
            addr           <= '0';
            dout_rdy       <= '1';
            sig_in_dst_rdy <= '1';

         when  S_2 =>
            ce             <= '0';
            addr           <= '1';
            dout_rdy       <= '1';
            sig_in_dst_rdy <= '0';

         when  S_RESET =>
            ce             <= '0';
            addr           <= 'X';
            dout_rdy       <= '0';
            sig_in_dst_rdy <= '0';

      end case;
   end process;

end generate;

NOT_FAKE_REG : if (FAKE_PIPE = false and PIPE_TYPE = "REG") generate
   pipe_reg_i : entity work.PIPE_REG
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      FAKE_PIPE   => false,
      CASCADE_REG => true
   )
   Port map(
      CLK   => CLK,
      RESET => RESET,

      IN_DATA    => IN_DATA,
      IN_SRC_RDY => sig_in_src_rdy,
      IN_DST_RDY => sig_in_dst_rdy,

      OUT_DATA    => OUT_DATA,
      OUT_SRC_RDY => OUT_SRC_RDY,
      OUT_DST_RDY => OUT_DST_RDY
   );
end generate;

FAKE: if (FAKE_PIPE = true) generate
   OUT_DATA       <= IN_DATA;
   OUT_SRC_RDY    <= sig_in_src_rdy;
   sig_in_dst_rdy <= OUT_DST_RDY;
end generate;

end pipe_arch;
