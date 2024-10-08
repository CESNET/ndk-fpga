-- datamux_2to1_arch.vhd
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

library work;
use work.dma_bus_pack.all;

   -------------------------------------------------------------------------------
   --                       Architecture declaration
   -------------------------------------------------------------------------------

architecture FULL of DMAFIFO_MUX_2TO1 is
   --! FSM declaration
   type t_state is (LOW, HIGH );
   signal present_state, next_state : t_state;

   --! Constant declaration
   constant  DATA_HALF_WIDTH        : integer :=INPUT_DATA_WIDTH/2;

   --! Signals declaration
   signal rd_en                     : std_logic;
   signal fifo_empty                : std_logic;
   signal full_s                    : std_logic;
   signal full_sig                  : std_logic;
   signal afull_sig                 : std_logic;
   signal vld_h                     : std_logic;
   signal src_rdy_s                 : std_logic;
   signal wr                        : std_logic;

   --! Data
   signal data_out                  : std_logic_vector (INPUT_DATA_WIDTH-1 downto 0);
   signal fifo_in                   : std_logic_vector (INPUT_DATA_WIDTH+DMA_HDR_WIDTH+2 downto 0);
   signal fifo_out                  : std_logic_vector (INPUT_DATA_WIDTH+DMA_HDR_WIDTH+2 downto 0);
   signal dwords                    : std_logic_vector (10 downto 0);
   signal last_dwords               : std_logic_vector (3 downto 0);

begin
   -------------------------------------------------------------------------------
   --                             Architecture body
   -------------------------------------------------------------------------------

   asfifo_gen : if (not FAKE_FIFO) generate
      asfifo_i : entity work.ASFIFOX
      generic map(
         DATA_WIDTH          => INPUT_DATA_WIDTH + DMA_HDR_WIDTH + 3,
         ITEMS               => 512,
         RAM_TYPE            => "BRAM",
         FWFT_MODE           => true,
         OUTPUT_REG          => true,
         DEVICE              => DEVICE,
         ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
         ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
      )
      port map(
         WR_CLK    => CLK_WR,
         WR_RST    => RST_WR,
         WR_DATA   => fifo_in,

         WR_EN     => wr,

         WR_FULL   => full_sig,
         WR_AFULL  => afull_sig,
         WR_STATUS => open,

         RD_CLK    => CLK_RD,
         RD_RST    => RST_RD,
         RD_DATA   => fifo_out,

         RD_EN     => rd_en,

         RD_EMPTY  => fifo_empty,

         RD_AEMPTY => open,
         RD_STATUS => open
      );
   else generate
      afull_sig <= '0';

      fake_fifo_pr : process (CLK_RD)
      begin
         if (rising_edge(CLK_RD)) then

            if (rd_en='1') then
               full_sig <= '0';
            end if;

            if (wr='1' and (full_sig='0' or rd_en='1')) then
               fifo_out <= fifo_in;
               full_sig <= '1';
            end if;

            if (RST_RD='1') then
               full_sig   <= '0';
            end if;
         end if;
      end process;

      fifo_empty <= not full_sig;
   end generate;

   ----------------------------------------------------------------------------
   --                             INPUT LOGIC
   ----------------------------------------------------------------------------

   dwords      <= RX_HDR(DMA_REQUEST_LENGTH) when (DIRECTION="UP") else RX_HDR(DMA_COMPLETION_LENGTH);
   last_dwords <= dwords(3 downto 0);

   upword_sign: process(RX_SRC_RDY,full_s,RX_HDR,RX_EOP,last_dwords)
   begin
      vld_h                <= '0';
      if (RX_SRC_RDY = '1' and full_s ='0' and (DIRECTION/="UP" or RX_HDR(DMA_REQUEST_TYPE) = DMA_TYPE_WRITE)) then
         vld_h             <= '1';
         if (RX_EOP = '1') then
            if (last_dwords < 9 and last_dwords /= "0000") then
               vld_h       <= '0';
            end if;
         end if;
      end if;
   end process;

   ----------------------------------------------------------------------------
   --                            OUTPUT Logic
   ----------------------------------------------------------------------------

   full_s           <= full_sig when USE_ALMOST_FULL = false else afull_sig;
   TX_SRC_RDY       <= src_rdy_s;
   RX_DST_RDY       <= not full_s;
   TX_HDR           <= fifo_out(DMA_HDR_WIDTH+2 downto 3);

   ----------------------------------------------------------------------------
   --                           CONTROL SIGNALS
   ----------------------------------------------------------------------------
   wr               <= '1' when full_s ='0' and RX_SRC_RDY ='1' else '0';
   src_rdy_s        <= not fifo_empty;
   fifo_in          <= RX_DATA & RX_HDR & RX_SOP & RX_EOP & vld_h ;
   data_out         <= fifo_out(INPUT_DATA_WIDTH+2+DMA_HDR_WIDTH downto 3+DMA_HDR_WIDTH);

   ----------------------------------------------------------------------------
   --                             FSM Logic
   ----------------------------------------------------------------------------

   sync_logic: process(CLK_RD)
   begin
      if (rising_edge (CLK_RD)) then
         if (RST_RD = '1' ) then
            present_state  <= LOW;
         else
            present_state  <= next_state;
         end if;
      end if;
   end process;

   next_state_logic: process(present_state, fifo_out,fifo_empty,TX_DST_RDY)
   begin
      next_state           <= present_state;
      case (present_state) is
         when LOW =>
            if (fifo_out(0) = '1' and fifo_empty = '0' and TX_DST_RDY ='1') then
               next_state  <= HIGH;
            end if ;
         when HIGH =>
            if (TX_DST_RDY ='1') then
               next_state  <= LOW;
            end if;
         when others =>
      end case;
   end process;

   output_logic: process(present_state,data_out,src_rdy_s,TX_DST_RDY,fifo_out)
   begin
      rd_en                <= '0';
      TX_DATA              <= data_out (DATA_HALF_WIDTH-1 downto 0);
      TX_SOP               <= '0';
      TX_EOP               <= '0';
      case (present_state) is
      --! lower part of word
         when LOW =>
            TX_DATA        <= data_out (DATA_HALF_WIDTH-1 downto 0);
            TX_SOP         <= fifo_out(2);
            if (fifo_out(0) = '0') then
               TX_EOP      <= fifo_out(1);
               if (src_rdy_s ='1' and TX_DST_RDY ='1' ) then
                  rd_en    <= '1';
               end if;
            end if;
      --! upper part of word
         when HIGH =>
            TX_DATA        <= data_out (INPUT_DATA_WIDTH-1 downto DATA_HALF_WIDTH);
            TX_EOP         <= fifo_out(1);
            if (src_rdy_s ='1' and TX_DST_RDY ='1' ) then
               rd_en       <= '1';
            end if;
      when others =>
      end case;
   end process;

end architecture FULL;
