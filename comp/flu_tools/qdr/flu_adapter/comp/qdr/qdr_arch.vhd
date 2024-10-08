-- qdr_arch.vhd
--!
--! \file
--! \brief QDR adapter architecture
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function.
use work.math_pack.all;

--! \brief Implementation of QDR module
architecture FULL of QDR is

   signal cal_done_s : std_logic;
   signal cal_done_reg1 : std_logic;
   signal cal_done_reg2 : std_logic;

   --! Signals for read request FIFO
   signal fifo_rdin_wr      : std_logic;
   signal fifo_rdin_di      : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal fifo_rdin_full    : std_logic;
   signal fifo_rdin_do      : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal fifo_rdin_rd      : std_logic;
   signal fifo_rdin_empty   : std_logic;

   --! Read request FSM
   type fsmrd_t is (fsmrd_default, fsmrd_word0);
   signal current_staterd  : fsmrd_t;
   signal next_staterd     : fsmrd_t;
   signal rd_addr_lsb      : std_logic;

   --! Signals for write request FIFO
   signal fifo_wrin_wr    : std_logic;
   signal fifo_wrin_di    : std_logic_vector(ADDR_WIDTH-1+2*DATA_WIDTH*QDR_NUMBER-1 downto 0);
   signal fifo_wrin_full  : std_logic;
   signal fifo_wrin_do    : std_logic_vector(ADDR_WIDTH-1+2*DATA_WIDTH*QDR_NUMBER-1 downto 0);
   signal fifo_wrin_rd    : std_logic;
   signal fifo_wrin_empty : std_logic;

   --! Signals for write request MUX
   signal mux_wrin_di     : std_logic_vector(2*DATA_WIDTH*QDR_NUMBER-1 downto 0);
   signal mux_wrin_sel    : std_logic;
   signal mux_wrin_do     : std_logic_vector(DATA_WIDTH*QDR_NUMBER-1 downto 0);

   --! Signals for DATA_OUT FIFO
   signal reg_data_out : std_logic_vector(DATA_WIDTH*QDR_NUMBER-1 downto 0);
   signal reg_data_out_we : std_logic_vector(QDR_NUMBER-1 downto 0);
   signal reg_data_out_we_sel : std_logic_vector(QDR_NUMBER-1 downto 0);
   signal fifo_out_wr    : std_logic_vector(QDR_NUMBER-1 downto 0);
   signal fifo_out_di    : std_logic_vector(DATA_WIDTH*2*QDR_NUMBER-1 downto 0);
   signal fifo_out_do    : std_logic_vector(2*DATA_WIDTH*QDR_NUMBER-1 downto 0);
   signal fifo_out_rd    : std_logic_vector(QDR_NUMBER-1 downto 0);
   signal fifo_out_empty : std_logic_vector(QDR_NUMBER-1 downto 0);
   signal fifo_out_empty_s : std_logic;

begin

   --! QDR calibration signals -------------------------------------------------
   CAL_DONE_AND : entity work.GEN_AND
   generic map (QDR_NUMBER)
   port map (CAL_DONE, cal_done_s);

   cal_done_reg1p: process(APP_CLK)
   begin
      if (APP_CLK'event and APP_CLK = '1') then
         cal_done_reg1 <= cal_done_s;
      end if;
   end process;

   cal_done_reg2p: process(APP_CLK)
   begin
      if (APP_CLK'event and APP_CLK = '1') then
         cal_done_reg2 <= cal_done_reg1;
      end if;
   end process;

   REG_CAL_DONE <= cal_done_reg2;

   --! Read request FIFO part -------------------------------------------------
   fifo_rdin_di <= QDR_RX_RD_ADDR;
   fifo_rdin_wr <= (not fifo_rdin_full) and QDR_RX_RD_SRC_RDY;
   QDR_RX_RD_DST_RDY <= (not fifo_rdin_full);

   fifo_rdin: entity work.ASFIFO_BRAM_XILINX
   generic map (
      DEVICE => "7SERIES",
      DATA_WIDTH => ADDR_WIDTH-1,
      ITEMS => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG => true
   )
   port map (
      --! Write interface
      CLK_WR => APP_CLK,
      RST_WR => APP_RST,
      DI => fifo_rdin_di,
      WR => fifo_rdin_wr,
      AFULL => open,
      FULL => fifo_rdin_full,

      --! Read interface
      CLK_RD => QDR_CLK,
      RST_RD => QDR_RST,
      DO => fifo_rdin_do,
      RD => fifo_rdin_rd,
      AEMPTY => open,
      EMPTY => fifo_rdin_empty
   );

   --! QDR read request FSM
   --! FSM process
   fsmrdp: process(QDR_CLK)
   begin
      if (QDR_CLK'event AND QDR_CLK = '1') then
         if (QDR_RST = '1') then
            current_staterd <= fsmrd_default;
         else
            current_staterd <= next_staterd;
         end if;
      end if;
   end process;

   --! FSM output/next state logic
   next_state_logicrdp: process (current_staterd, fifo_rdin_empty)
   begin
      --! Default values
      fifo_rdin_rd <= '0';
      rd_addr_lsb <= '0';
      USER_RD_CMD <= '0';
      case current_staterd is
         when fsmrd_default =>
            next_staterd <= current_staterd;
            if (fifo_rdin_empty = '0') then
               next_staterd <= fsmrd_word0;
               USER_RD_CMD <= '1';
            end if;
         when fsmrd_word0 =>
            next_staterd <= fsmrd_default;
            fifo_rdin_rd <= '1';
            rd_addr_lsb <= '1';
            USER_RD_CMD <= '1';
      end case;
   end process;

   --! QDR IP core signals assignment
   USER_RD_ADDR <= fifo_rdin_do & rd_addr_lsb;

   --! Write request FIFO part -------------------------------------------------
   fifo_wrin_di <= QDR_RX_WR_ADDR & QDR_RX_WR_DATA;
   fifo_wrin_wr <= (not fifo_wrin_full) and QDR_RX_WR_SRC_RDY;
   QDR_RX_WR_DST_RDY <= (not fifo_wrin_full);

   --! FIFO
   fifo_wrin: entity work.ASFIFO_BRAM_XILINX
   generic map (
      DEVICE => "7SERIES",
      DATA_WIDTH => ADDR_WIDTH-1+2*DATA_WIDTH*QDR_NUMBER,
      ITEMS => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG => true
   )
   port map (
      --! Write interface
      CLK_WR => APP_CLK,
      RST_WR => APP_RST,
      DI => fifo_wrin_di,
      WR => fifo_wrin_wr,
      AFULL => open,
      FULL => fifo_wrin_full,

      --! Read interface
      CLK_RD => QDR_CLK,
      RST_RD => QDR_RST,
      DO => fifo_wrin_do,
      RD => fifo_wrin_rd,
      AEMPTY => open,
      EMPTY => fifo_wrin_empty
   );

   fifo_wrin_rd <= mux_wrin_sel;

   mux_wrin_di <= fifo_wrin_do(2*DATA_WIDTH*QDR_NUMBER-1 downto 0);

   mux_wrin_do <= mux_wrin_di(DATA_WIDTH*QDR_NUMBER-1 downto 0) when (mux_wrin_sel = '0')
                else mux_wrin_di(DATA_WIDTH*QDR_NUMBER*2-1 downto DATA_WIDTH*QDR_NUMBER);

   --! multiplexor selection signal
   mux_wrin_selp : process(QDR_CLK)
   begin
      if (QDR_CLK'event and QDR_CLK = '1') then
         if (QDR_RST = '1') then
            mux_wrin_sel <= '0';
         else
            if (mux_wrin_sel = '1') then
               mux_wrin_sel <= '0';
            else
               if (fifo_wrin_empty = '0') then
                  mux_wrin_sel <= '1';
               end if;
            end if;
         end if;
      end if;
   end process;

   --! QDR IP core signals assignment
   USER_WR_BW_N <= (others => '0');

   USER_WR_DATA <= mux_wrin_do;

   USER_WR_ADDR <= fifo_wrin_do(ADDR_WIDTH-1+2*DATA_WIDTH*QDR_NUMBER-1 downto 2*DATA_WIDTH*QDR_NUMBER)
                   & mux_wrin_sel;

   USER_WR_CMD <= not (fifo_wrin_empty);

   --! DATA_OUT FIFO part ------------------------------------------------------

   data_out_fifog: for i in 0 to QDR_NUMBER-1 generate
      --! half word FIFO register
      reg_data_outp : process(QDR_CLK)
      begin
         if (QDR_CLK'event and QDR_CLK = '1') then
            if (reg_data_out_we(i) = '1') then
               reg_data_out((DATA_WIDTH)*(i+1)-1 downto (DATA_WIDTH)*i)
               <= USER_RD_DATA((DATA_WIDTH)*(i+1)-1 downto (DATA_WIDTH)*i);
            end if;
         end if;
      end process;

      --! reg_data_out_we multiplexor
      reg_data_out_we(i) <= USER_RD_VALID(i) when (reg_data_out_we_sel(i) = '0') else '0';

      fifo_out_wr(i) <= USER_RD_VALID(i) when (reg_data_out_we_sel(i) = '1') else '0';

      fifo_out_di((2*DATA_WIDTH)*(i+1)-1 downto (2*DATA_WIDTH)*i)
      <= USER_RD_DATA((DATA_WIDTH)*(i+1)-1 downto (DATA_WIDTH)*i)
      & reg_data_out((DATA_WIDTH)*(i+1)-1 downto (DATA_WIDTH)*i);

      --! DATA_OUT FIFO
      fifo_out: entity work.ASFIFO_BRAM_XILINX
      generic map (
         DEVICE => "7SERIES",
         DATA_WIDTH => 2*DATA_WIDTH,
         ITEMS => 512,
         FIRST_WORD_FALL_THROUGH => true,
         DO_REG => true
      )
      port map (
         --! Write interface
         CLK_WR => QDR_CLK,
         RST_WR => QDR_RST,
         DI => fifo_out_di((2*DATA_WIDTH)*(i+1)-1 downto (2*DATA_WIDTH)*i),
         WR => fifo_out_wr(i),
         AFULL => open,
         FULL => open,

         --! Read interface
         CLK_RD => APP_CLK,
         RST_RD => APP_RST,
         DO => fifo_out_do((2*DATA_WIDTH)*(i+1)-1 downto (2*DATA_WIDTH)*i),
         RD => fifo_out_rd(i),
         AEMPTY => open,
         EMPTY => fifo_out_empty(i)
      );

      fifo_out_rd(i) <= (not fifo_out_empty_s) and QDR_TX_DST_RDY;

      QDR_TX_DATA(DATA_WIDTH*(QDR_NUMBER+i+1)-1 downto DATA_WIDTH*(QDR_NUMBER+i))
      <= fifo_out_do((DATA_WIDTH)*(i*2+1+1)-1 downto (DATA_WIDTH)*(i*2+1));

      QDR_TX_DATA(DATA_WIDTH*(i+1)-1 downto DATA_WIDTH*(i))
      <= fifo_out_do((DATA_WIDTH)*(i*2+1)-1 downto (DATA_WIDTH)*(i*2));

      --! reg_data_out_we multiplexor selection signal
      reg_data_out_we_selp: process(QDR_CLK)
      begin
         if (QDR_CLK'event and QDR_CLK = '1') then
            if (QDR_RST = '1') then
               reg_data_out_we_sel(i) <= '0';
            elsif (USER_RD_VALID(i) = '1') then
               if (reg_data_out_we_sel(i) = '0')then
                  reg_data_out_we_sel(i) <= '1';
               else
                  reg_data_out_we_sel(i) <= '0';
               end if;
            end if;
         end if;
      end process;
   end generate;

   FIFO_OUT_EMPTY_OR : entity work.GEN_OR
   generic map (QDR_NUMBER)
   port map (fifo_out_empty, fifo_out_empty_s);

   QDR_TX_SRC_RDY <= (not fifo_out_empty_s);

end architecture;
