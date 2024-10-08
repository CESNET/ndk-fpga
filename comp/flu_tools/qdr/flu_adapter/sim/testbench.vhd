-- testbench.vhd: Testbench for QDR
-- Copyright (C) 2013 CESNET
-- Author(s): Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.conv_std_logic_vector;
use IEEE.math_real.all;

use work.math_pack.all;

--! General FLU_ADAPTER package
use work.flu_adapter_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

   -- Constants declaration ---------------------------------------------------

   -- Synchronization
   constant C_APP_CLK_PER    : time := 5.0 ns;
   constant C_APP_RESET_TIME : time := 32 ns;
   constant C_QDR_CLK_PER    : time := 3.0 ns;
   constant C_QDR_RESET_TIME : time := 32 ns;

   -- QDR's generic parameters

   constant C_QDR_NUMBER           : integer := 3;
   constant C_ADDR_WIDTH           : integer := 9;
   constant C_DATA_WIDTH           : integer := 144;

   -- Signals declaration -----------------------------------------------------

   -- Synchronization
   signal app_clk          : std_logic;
   signal app_rst        : std_logic;
   signal qdr_clk          : std_logic;
   signal qdr_rst        : std_logic;
   signal cal_done         : std_logic_vector(C_QDR_NUMBER-1 downto 0);

   -- Input FLU
   signal flu_rx_data            : std_logic_vector(511 downto 0);
   signal flu_rx_sop_pos         : std_logic_vector(2 downto 0);
   signal flu_rx_eop_pos         : std_logic_vector(5 downto 0);
   signal flu_rx_sop             : std_logic;
   signal flu_rx_eop             : std_logic;
   signal flu_rx_src_rdy         : std_logic;
   signal flu_rx_dst_rdy         : std_logic;

   -- Output FLU
   signal flu_tx_data             : std_logic_vector(511 downto 0);
   signal flu_tx_sop_pos          : std_logic_vector(2 downto 0);
   signal flu_tx_eop_pos          : std_logic_vector(5 downto 0);
   signal flu_tx_sop              : std_logic;
   signal flu_tx_eop              : std_logic;
   signal flu_tx_src_rdy          : std_logic;
   signal flu_tx_dst_rdy          : std_logic;

   -- User commands
   signal user_wr_cmd           : std_logic;
   signal user_wr_addr          : std_logic_vector(C_ADDR_WIDTH-1 downto 0);
   signal user_wr_data          : std_logic_vector(C_DATA_WIDTH*C_QDR_NUMBER-1 downto 0);
   signal user_wr_bw_n          : std_logic_vector(C_DATA_WIDTH/9-1 downto 0);
   signal user_rd_cmd           : std_logic;
   signal user_rd_addr          : std_logic_vector(C_ADDR_WIDTH-1 downto 0);

   -- User data
   signal user_rd_valid         : std_logic_vector(C_QDR_NUMBER-1 downto 0);
   signal user_rd_data          : std_logic_vector(C_DATA_WIDTH*C_QDR_NUMBER-1 downto 0);

   --! Control signals, default behaviour as FIFO
   signal current_state       : std_logic_vector(3 downto 0);
   signal next_state          : std_logic_vector(3 downto 0);
   signal next_state_src_rdy  : std_logic;
   signal next_state_dst_rdy  : std_logic;


   -- QDR simulation
   type t_mem is array (0 to 2**C_ADDR_WIDTH-1) of std_logic_vector (C_DATA_WIDTH*C_QDR_NUMBER-1 downto 0);
   signal mem : t_mem := (
   -- |   Addr   |    Action   |    Params   |  Op2  |  Op1  |      Hash3       |    Hash12     | Vld |
      others => (others => '0')
   );
   signal mem_out                : std_logic_vector(C_DATA_WIDTH*C_QDR_NUMBER-1 downto 0);
   signal reg2_mem_out           : std_logic_vector(C_DATA_WIDTH*C_QDR_NUMBER-1 downto 0);
   signal reg3_mem_out           : std_logic_vector(C_DATA_WIDTH*C_QDR_NUMBER-1 downto 0);
   signal reg1_user_rd_cmd       : std_logic;
   signal reg2_user_rd_cmd       : std_logic;
   signal reg3_user_rd_cmd       : std_logic;

   signal flu_counter            : std_logic_vector(511 downto 0);
-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   --                          QDR simulation
   -- -------------------------------------------------------------------------

   -- mem simulation
   mem_p : process (qdr_clk)
      variable tmp : t_mem;
   begin
      if (qdr_clk'event and qdr_clk = '1') then
         tmp := mem;
         mem_out <= (others => '0');

         if (user_rd_cmd = '1') then
            mem_out <= tmp(conv_integer(user_rd_addr));
         end if;

         if (user_wr_cmd = '1') then
            tmp(conv_integer(user_wr_addr)) := user_wr_data;
         end if;

         mem <= tmp;
      end if;
   end process;

   -- mem delay
   mem_delay_p : process(qdr_clk)
   begin
      if (qdr_clk'event and qdr_clk = '1') then
         if (qdr_rst = '1') then
            reg1_user_rd_cmd <= '0';
            reg2_user_rd_cmd <= '0';
            reg3_user_rd_cmd <= '0';
         else
            reg1_user_rd_cmd <= user_rd_cmd;
            reg2_user_rd_cmd <= reg1_user_rd_cmd;
            reg3_user_rd_cmd <= reg2_user_rd_cmd;
            for i in 0 to C_QDR_NUMBER-1 loop
               user_rd_valid(i) <= reg3_user_rd_cmd;
            end loop;
            reg2_mem_out <= mem_out;
            reg3_mem_out <= reg2_mem_out;
            user_rd_data <= reg3_mem_out;
         end if;
      end if;
   end process;

   --FLU counter
   flu_counterp: process(app_clk)
   begin
      if (app_clk'event and app_clk = '1') then
         if (app_rst = '1') then
            flu_counter <= (others => '0');
         elsif (flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1') then
            flu_counter <= flu_counter + 1;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                              FLU_ADAPTER
   -- -------------------------------------------------------------------------

   -- FLU_ADAPTER instantiation
   uut: entity work.FLU_ADAPTER
   generic map(
      --! Width of read request
      ADDR_WIDTH => C_ADDR_WIDTH
   )
   port map(
      --! Resets and clocks ----------------------------------------------------
      APP_CLK => app_clk,
      APP_RST => app_rst,

      --! QDR clock domain
      QDR_CLK => qdr_clk,
      QDR_RST => qdr_rst,

      --! Calibration done from QDR IP core
      CAL_DONE => cal_done,
      REG_CAL_DONE => open,

      --! Input FLU
      FLU_RX_DATA => flu_rx_data,
      FLU_RX_SOP_POS => flu_rx_sop_pos,
      FLU_RX_EOP_POS => flu_rx_eop_pos,
      FLU_RX_SOP => flu_rx_sop,
      FLU_RX_EOP => flu_rx_eop,
      FLU_RX_SRC_RDY => flu_rx_src_rdy,
      FLU_RX_DST_RDY => flu_rx_dst_rdy,


      --! Output FLU
      FLU_TX_DATA => flu_tx_data,
      FLU_TX_SOP_POS => flu_tx_sop_pos,
      FLU_TX_EOP_POS => flu_tx_eop_pos,
      FLU_TX_SOP => flu_tx_sop,
      FLU_TX_EOP => flu_tx_eop,
      FLU_TX_SRC_RDY => flu_tx_src_rdy,
      FLU_TX_DST_RDY => flu_tx_dst_rdy,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => user_wr_addr,
      --! Data to write
      USER_WR_DATA => user_wr_data,
      --! Data write enable - active low
      USER_WR_BW_N => user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => user_rd_valid,
      --! Already read data
      USER_RD_DATA => user_rd_data,

      --! Control signals, default behaviour as FIFO
      CURRENT_STATE => current_state,
      NEXT_STATE => next_state,
      NEXT_STATE_SRC_RDY => next_state_src_rdy,
      NEXT_STATE_DST_RDY => next_state_dst_rdy
   );
   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating app_clk
   app_clk_gen: process
   begin
      app_clk <= '1';
      wait for C_APP_CLK_PER / 2;
      app_clk <= '0';
      wait for C_APP_CLK_PER / 2;
   end process app_clk_gen;

   -- generating app_rst
   app_rst_gen: process
   begin
      app_rst <= '1';
      wait for C_APP_RESET_TIME;
      app_rst <= '0';
      wait;
   end process app_rst_gen;

   -- generating qdr_clk
   qdr_clk_gen: process
   begin
      qdr_clk <= '1';
      wait for C_QDR_CLK_PER / 2;
      qdr_clk <= '0';
      wait for C_QDR_CLK_PER / 2;
   end process qdr_clk_gen;

   -- generating qdr_rst
   qdr_rst_gen: process
   begin
      qdr_rst <= '1';
      wait for C_QDR_RESET_TIME;
      qdr_rst <= '0';
      wait;
   end process qdr_rst_gen;

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   --Simulation
   flu_rx_data <= flu_counter;
   tb:process
   begin
      cal_done <= (others => '1');
      flu_tx_dst_rdy <= '1';
      flu_rx_sop_pos <= "000";
      flu_rx_eop_pos <= "000000";
      flu_rx_sop <= '0';
      flu_rx_eop <= '0';
      flu_rx_src_rdy <= '0';
      next_state_src_rdy <= '0';
      next_state <= STORAGE_FIFO;
      wait until (app_rst = '0' and qdr_rst = '0');
      wait for 5*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      next_state_src_rdy <= '1';
      next_state <= STORAGE_FIFO;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      -- One packet
      for i in 0 to 0 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';
      wait for 25*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- Two packets
      for i in 0 to 1 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';
      wait for 25*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- Three pakets
      for i in 0 to 2 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';
      wait for 25*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- 60 pakets
      for i in 0 to 59 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';
      wait for 25*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      flu_tx_dst_rdy <= '0';
      flu_rx_sop_pos <= "000";
      flu_rx_eop_pos <= "111111";
      flu_rx_sop <= '1';
      flu_rx_eop <= '1';
      flu_rx_src_rdy <= '1';

      wait for 2000*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      flu_tx_dst_rdy <= '1';

      wait for 2000*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      flu_rx_src_rdy <= '0';

      wait for 2000*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- one paket
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 0 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_DISABLE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 10*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 50*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- one paket
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 0 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;


      next_state_src_rdy <= '1';
      next_state <= STORAGE_DISABLE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 10*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 50*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- two pakets
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 1 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 50*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- two pakets
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 1 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '1';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 50*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- three pakets
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 2 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 50*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- 60 pakets
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 400 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 1000*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      -- 60 pakets
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';
      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 100*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_CAPTURE;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      for i in 0 to 59 loop
         flu_rx_sop_pos <= "000";
         flu_rx_eop_pos <= "111111";
         flu_rx_sop <= '1';
         flu_rx_eop <= '1';
         flu_rx_src_rdy <= '1';
         flu_tx_dst_rdy <= '1';
         wait until (app_clk'event and app_clk = '1' and flu_rx_src_rdy = '1' and flu_rx_dst_rdy = '1');
      end loop;

      flu_rx_src_rdy <= '0';

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 1000*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      next_state_src_rdy <= '1';
      next_state <= STORAGE_REPLAY_REPEATED;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait for 5000*C_APP_CLK_PER;
      wait until (app_clk'event and app_clk = '1');

      next_state_src_rdy <= '1';
      next_state <= STORAGE_CLEAR;
      wait until (app_clk'event and app_clk = '1' and next_state_dst_rdy = '1');
      next_state_src_rdy <= '0';

      wait;
   end process;

end architecture behavioral;
