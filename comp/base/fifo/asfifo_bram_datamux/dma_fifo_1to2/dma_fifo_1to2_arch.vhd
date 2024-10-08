-- dmafifo_1to2_arch.vhd
--!
--! \file
--! \brief Asynchronous fifo mutiplex in BRAMs for Xilinx FPGAs
--! \author Ondrej Dujiček <xdujic02@stud.feec.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
--! Package with log2 function.



-- ----------------------------------------------------------------------------
--                       Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of DMAFIFO_MUX_1TO2 is

   --! Signals declaration

   signal wr_low                    : std_logic;
   signal wr_high                   : std_logic;
   signal full_l                    : std_logic;
   signal full_h                    : std_logic;
   signal afull_l                   : std_logic;
   signal afull_h                   : std_logic;
   signal empty_l                   : std_logic;
   signal empty_h                   : std_logic;
   signal rd                        : std_logic;
   signal rx_dst_rdy_s              : std_logic;
   signal tx_src_rdy_s              : std_logic;
   signal data_high                 : std_logic_vector (INPUT_DATA_WIDTH downto 0);
   signal fifo_out_h                : std_logic_vector (INPUT_DATA_WIDTH downto 0);
   signal data_low                  : std_logic_vector (INPUT_DATA_WIDTH + HDR_WIDTH + 2-1 downto 0);
   signal fifo_out_l                : std_logic_vector (INPUT_DATA_WIDTH + HDR_WIDTH + 2-1 downto 0);

   --! FSM declaration
   type t_state is (LOW, HIGH );
   signal present_state, next_state : t_state;

begin
   -- ----------------------------------------------------------------------------
   --                             Architecture body
   -- ----------------------------------------------------------------------------

   asfifo_low : entity work.ASFIFO_BRAM_XILINX
   generic map(
      DEVICE                  => DEVICE,
      DATA_WIDTH              => INPUT_DATA_WIDTH+HDR_WIDTH+2,
      ITEMS                   => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG                  => true,
      ALMOST_FULL_OFFSET      => ALMOST_FULL_OFFSET,
      ALMOST_EMPTY_OFFSET     => ALMOST_EMPTY_OFFSET
   )
   port map(
      CLK_WR         => CLK_WR,
      RST_WR         => RST_WR,
      DI             => data_low,
      WR             => wr_low,
      FULL           => full_l,
      AFULL          => afull_l,

      CLK_RD         => CLK_RD,
      RST_RD         => RST_RD,
      DO             => fifo_out_l,
      RD             => rd,
      EMPTY          => empty_l,
      AEMPTY         => open
   );

   asfifo_high : entity work.ASFIFO_BRAM_XILINX
   generic map(
      DEVICE                  => DEVICE,
      DATA_WIDTH              => INPUT_DATA_WIDTH +1,
      ITEMS                   => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG                  => true,
      ALMOST_FULL_OFFSET      => ALMOST_FULL_OFFSET,  --
      ALMOST_EMPTY_OFFSET     => ALMOST_EMPTY_OFFSET
   )
   port map(
      CLK_WR         => CLK_WR,
      RST_WR         => RST_WR,
      DI             => data_high,
      WR             => wr_high,
      FULL           => full_h,
      AFULL          => afull_h,

      CLK_RD         => CLK_RD,
      RST_RD         => RST_RD,
      DO             => fifo_out_h,
      RD             => rd,
      EMPTY          => empty_h,
      AEMPTY         => open
       );

   ----------------------------------------------------------------------------
   --                               DATA INPUT
   ----------------------------------------------------------------------------

   data_low        <=  RX_DATA & RX_HDR & RX_SOP & RX_EOP;
   data_high       <=  RX_DATA & RX_EOP;

   ----------------------------------------------------------------------------
   --                               DATA OUTPUT
   ----------------------------------------------------------------------------

   TX_DATA         <= fifo_out_h(INPUT_DATA_WIDTH downto 1) & fifo_out_l(INPUT_DATA_WIDTH+HDR_WIDTH+2-1 downto HDR_WIDTH+2);
   TX_SRC_RDY_H    <= not (fifo_out_l(0) or empty_l);
   TX_HDR          <= fifo_out_l(HDR_WIDTH+2-1 downto 2);
   TX_SOP          <= fifo_out_l(1);
   TX_EOP          <= fifo_out_l(0) or fifo_out_h(0);
   RX_DST_RDY      <= not (full_l or full_h);
   TX_SRC_RDY      <= tx_src_rdy_s;

   RX_AFULL        <= afull_l or afull_h;

   ----------------------------------------------------------------------------
   --                              CONTROl logic
   ----------------------------------------------------------------------------

   rd              <= '1' when TX_DST_RDY = '1' and tx_src_rdy_s = '1' else '0';
   tx_src_rdy_s    <= not (empty_l or empty_h);
   rx_dst_rdy_s    <= not (full_l or full_h) when DISABLE_DST_RDY = false else '1';

   ----------------------------------------------------------------------------
   --                               FSM LOGIC
   ----------------------------------------------------------------------------
   sync_logic: process(CLK_WR)
   begin
      if (rising_edge (CLK_WR)) then
         if (RST_WR = '1') then
            present_state <= LOW;
         else
            present_state <= next_state;
         end if;
      end if ;
   end process;

   next_state_logic: process(present_state,RX_SRC_RDY,rx_dst_rdy_s,RX_EOP)
   begin
      next_state              <= LOW;
      case (present_state) is
         when LOW =>
            if (RX_SRC_RDY ='1' and rx_dst_rdy_s = '1' and RX_EOP = '0') then
               next_state     <= HIGH;
            end if ;
         when HIGH =>
         when others =>
      end case;
   end process;

   output_logic: process(present_state, RX_SRC_RDY,RX_EOP,rx_dst_rdy_s)
   begin
      wr_low               <= '0';
      wr_high              <= '0';
      case (present_state) is
         when LOW =>
            if (rx_dst_rdy_s = '1' and RX_SRC_RDY = '1') then
               wr_low      <= '1';
               if (RX_EOP ='1') then
                  wr_high  <= '1';
                  wr_low   <= '1';
               end if;
            end if ;

         when HIGH =>
            if (rx_dst_rdy_s = '1' and RX_SRC_RDY ='1') then
               wr_high     <= '1';
            end if ;
         when others =>
      end case;
   end process;

end architecture FULL;
