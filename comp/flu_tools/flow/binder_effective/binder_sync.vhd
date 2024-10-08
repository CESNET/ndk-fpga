-- binder_sync.vhd
--!
--! \brief Synchronization component for FLU and Header
--! \author Pavel Benacek <benacpav@fit.cvut.cz>
--! \date 2015
--!
--! \section License
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity BINDER_SYNC is
   generic(
      --! FLU configuration
      DATA_WIDTH     : integer:= 512;
      SOP_POS_WIDTH  : integer:= 3;

      --! Header withd
      HDR_WIDTH      : integer := 128
   );
   port(
       --! \name  Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      --! \name Frame Link Unaligned input interface
      RX_HDR_DATA       : in std_logic_vector(HDR_WIDTH-1 downto 0);
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      --! \name Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic;

      --! \name Header output interface
      TX_HDR_DATA       : out std_logic_vector(HDR_WIDTH-1 downto 0);
      TX_HDR_SRC_RDY    : out std_logic;
      TX_HDR_DST_RDY    : in std_logic
   );
end entity;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
architecture full of BINDER_SYNC is
   --! States of the FSM
   type FSM_STATES is (DATA_TRANS,DATA_TAKEN,HEADER_TAKEN);

   --! Signals for actual and next states
   signal reg_act_state : FSM_STATES;
   signal next_state    : FSM_STATES;

   --! Control signal from the device to the FLUA Binder unit
   signal sig_rx_dst_rdy      : std_logic;
   --! Control signal from the BINDER_SYNC to other units
   signal sig_tx_src_rdy      : std_logic;
   --! Contol signal from the BINDER_SYNC to other units
   signal sig_tx_hdr_src_rdy  : std_logic;

begin

   --! Map data inputs and outputs
   TX_DATA       <= RX_DATA;
   TX_SOP_POS    <= RX_SOP_POS;
   TX_EOP_POS    <= RX_EOP_POS;
   TX_SOP        <= RX_SOP;
   TX_EOP        <= RX_EOP;
   TX_SRC_RDY    <= sig_tx_src_rdy;
   RX_DST_RDY    <= sig_rx_dst_rdy;


   --! Map header inputs and outputs
   TX_HDR_DATA       <= RX_HDR_DATA;
   TX_HDR_SRC_RDY    <= sig_tx_hdr_src_rdy;


   -- Control FSM -------------------------------------------------------------

   --! \brief Register for storage of the actual FSM state (with synchronous RESET)
   reg_act_statep : process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if RESET = '1' then
            reg_act_state <= DATA_TRANS;
         else
            reg_act_state <= next_state;
         end if;
      end if;
   end process;

   --! \brief Process for comutation of the next state of the FSM
   fsm_next_statep : process(reg_act_state,RX_SRC_RDY,RX_SOP,TX_DST_RDY,TX_HDR_DST_RDY)
   begin
      -- Next state is the actual state (by default)
      next_state <= reg_act_state;

      -- Compute the next state
      case reg_act_state is
         when DATA_TRANS =>
            if(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_DST_RDY = '1' and TX_HDR_DST_RDY = '0') then
               -- Data taken, header not
               next_state <= DATA_TAKEN;
            elsif(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_DST_RDY = '0' and TX_HDR_DST_RDY = '1') then
               -- Header taken, data not
               next_state <= HEADER_TAKEN;
            end if;

         when DATA_TAKEN =>
            -- Wait until header is taken
            if(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_HDR_DST_RDY = '1') then
               next_state <= DATA_TRANS;
            end if;

         when HEADER_TAKEN =>
            -- Wait until data is taken
            if(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_DST_RDY= '1') then
               next_state <= DATA_TRANS;
            end if;

         when others => null;
      end case;

   end process;

   --! \brief Process for computation of the otput signals
   fsm_outp : process(reg_act_state,RX_SRC_RDY,TX_HDR_DST_RDY,TX_DST_RDY,RX_SOP)
   begin
      -- Defatul signal values
      sig_tx_src_rdy <= RX_SRC_RDY;
      sig_rx_dst_rdy <= TX_DST_RDY;

      -- Ready and sop is detected (sop is the place with next header)
      sig_tx_hdr_src_rdy <= RX_SRC_RDY and RX_SOP;

      -- Compute output values
      case reg_act_state is
         when DATA_TRANS =>
            if(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_DST_RDY = '1' and TX_HDR_DST_RDY = '0') then
               -- Data taken, header not
               sig_rx_dst_rdy <= '0';

            elsif(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_DST_RDY = '0' and TX_HDR_DST_RDY = '1') then
               -- Header taken, data not
               sig_rx_dst_rdy <= '0';
            end if;

         when DATA_TAKEN =>
            -- Wait until header is taken
            sig_tx_src_rdy <= '0';

            if(RX_SRC_RDY = '0' or RX_SOP = '0' or TX_HDR_DST_RDY = '0') then
               -- Still waiting
               sig_rx_dst_rdy <= '0';
            elsif(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_HDR_DST_RDY = '1')then
               -- Force the destination ready (commit the stopped word)
               sig_rx_dst_rdy <= '1';
            end if;

         when HEADER_TAKEN =>
            -- Wait until data is taken
            sig_tx_hdr_src_rdy <= '0';

            if(RX_SRC_RDY = '0' or RX_SOP = '0' or TX_DST_RDY = '0') then
               -- Still waiting
               sig_rx_dst_rdy <= '0';
            elsif(RX_SRC_RDY = '1' and RX_SOP = '1' and TX_DST_RDY = '1') then
               -- Force the destination ready (commit the stopped word)
               sig_rx_dst_rdy <= '1';
            end if;

         when others => null;
      end case;
   end process;

end architecture full;
