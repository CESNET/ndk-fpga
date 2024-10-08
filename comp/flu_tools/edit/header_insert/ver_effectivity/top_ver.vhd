-- top_ver.vhd
--!
--! \file
--! \brief Top-level verification wrapper for FLU header insert
--! \author Lukas Kekely <kekely@cesnet.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

entity TOP_VER is
   generic (
      DATA_WIDTH     : integer := 512;
      SOP_POS_WIDTH  : integer := 3;
      HDR_WIDTH      : integer := 128
      );
   port (
      CLK              : in  std_logic;
      RESET            : in  std_logic;

      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in  std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0);
      RX_EOP_POS     : in  std_logic_vector(max(1,log2(DATA_WIDTH/8))- 1 downto 0);
      RX_SOP         : in  std_logic;
      RX_EOP         : in  std_logic;
      RX_SRC_RDY     : in  std_logic;
      RX_DST_RDY     : out std_logic;

      HDR_DATA      : in  std_logic_vector(HDR_WIDTH-1 downto 0);
      HDR_READY     : in  std_logic;
      HDR_NEXT      : out std_logic;

      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in  std_logic
   );
end entity;



library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

architecture arch of TOP_VER is
   constant WORD_BYTES : integer := DATA_WIDTH/8;
   constant HDR_BYTES : integer := HDR_WIDTH/8;
   signal rx_in_packet, tx_in_packet, rx_dst_rdy_sig, tx_src_rdy_sig, tx_sop_sig, tx_eop_sig : std_logic;
   signal rx_gap_size_vld, tx_gap_size_vld : std_logic;
   signal rx_gap_size, rx_gap_size_cnt, sync_rx_gap_size, tx_gap_size, tx_gap_size_cnt, sync_tx_gap_size : std_logic_vector(31 downto 0);
   signal rx_eop_pos_fix, rx_sop_pos_fix, tx_eop_pos_fix, tx_sop_pos_fix : std_logic_vector(31 downto 0);
   signal TX_SOP_POS_sig : std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0);
   signal TX_EOP_POS_sig : std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
   signal sync_next, sync_rx_ready_n, sync_tx_ready_n, sync_vld : std_logic;
   signal rx_src_rdy_reg : std_logic;
begin
   dut : entity work.HINS
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      HDR_WIDTH      => HDR_WIDTH
   ) port map (
      CLK           => CLK,
      RESET         => RESET,
      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY_sig,
      HDR_DATA      => HDR_DATA,
      HDR_READY     => HDR_READY,
      HDR_NEXT      => HDR_NEXT,
      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS_sig,
      TX_EOP_POS    => TX_EOP_POS_sig,
      TX_SOP        => TX_SOP_sig,
      TX_EOP        => TX_EOP_sig,
      TX_SRC_RDY    => TX_SRC_RDY_sig,
      TX_DST_RDY    => TX_DST_RDY
   );
   RX_DST_RDY <= RX_DST_RDY_sig;
   TX_SRC_RDY <= TX_SRC_RDY_sig;
   TX_SOP     <= TX_SOP_sig;
   TX_EOP     <= TX_EOP_sig;
   TX_SOP_POS <= TX_SOP_POS_sig;
   TX_EOP_POS <= TX_EOP_POS_sig;

   rx_in_packet_proc : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         if(RESET='1') then
            rx_in_packet <= '0';
         elsif RX_SRC_RDY='1' and RX_DST_RDY_sig='1' then
            rx_in_packet <= rx_in_packet xor RX_SOP xor RX_EOP;
         end if;
      end if;
   end process;

   rx_gap_size_counter : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         if(RESET='1') then
            rx_gap_size_cnt <= (others => '0');
         elsif RX_EOP='1' and RX_SRC_RDY='1' and RX_DST_RDY_sig='1' then
            rx_gap_size_cnt <= WORD_BYTES-rx_eop_pos_fix;
         end if;
      end if;
   end process;
   rx_eop_pos_fix <= conv_std_logic_vector(conv_integer(RX_EOP_POS)+1,32);
   rx_sop_pos_fix <= conv_std_logic_vector(conv_integer(RX_SOP_POS)*(2**SOP_POS_WIDTH),32);
   rx_gap_size     <= rx_gap_size_cnt+rx_sop_pos_fix when rx_in_packet='0' else rx_sop_pos_fix-rx_eop_pos_fix;
   rx_gap_size_vld <= RX_SOP and RX_SRC_RDY and RX_DST_RDY_sig;

   tx_in_packet_proc : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         if(RESET='1') then
            tx_in_packet <= '0';
         elsif TX_SRC_RDY_sig='1' and TX_DST_RDY='1' then
            tx_in_packet <= tx_in_packet xor TX_SOP_sig xor TX_EOP_sig;
         end if;
      end if;
   end process;

   tx_gap_size_counter : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         if(RESET='1') then
            tx_gap_size_cnt <= (others => '0');
         elsif TX_EOP_sig='1' and TX_SRC_RDY_sig='1' and TX_DST_RDY='1' then
            tx_gap_size_cnt <= WORD_BYTES-tx_eop_pos_fix;
         end if;
      end if;
   end process;
   tx_eop_pos_fix <= conv_std_logic_vector(conv_integer(TX_EOP_POS_sig)+1,32);
   tx_sop_pos_fix <= conv_std_logic_vector(conv_integer(TX_SOP_POS_sig)*(2**SOP_POS_WIDTH),32);
   tx_gap_size     <= tx_gap_size_cnt+tx_sop_pos_fix when tx_in_packet='0' else tx_sop_pos_fix-tx_eop_pos_fix;
   tx_gap_size_vld <= TX_SOP_sig and TX_SRC_RDY_sig and TX_DST_RDY;

   rx_sync_fifo : entity work.FIFO
   generic map (
      DATA_WIDTH     => 32,
      ITEMS          => 32
   ) port map (
      RESET    => RESET,
      CLK      => CLK,
      DATA_IN   => rx_gap_size,
      WRITE_REQ => rx_gap_size_vld,
      FULL      => open,
      LSTBLK    => open,
      DATA_OUT  => sync_rx_gap_size,
      READ_REQ  => sync_next,
      EMPTY     => sync_rx_ready_n
   );

   tx_sync_fifo : entity work.FIFO
   generic map (
      DATA_WIDTH     => 32,
      ITEMS          => 32
   ) port map (
      RESET    => RESET,
      CLK      => CLK,
      DATA_IN   => tx_gap_size,
      WRITE_REQ => tx_gap_size_vld,
      FULL      => open,
      LSTBLK    => open,
      DATA_OUT  => sync_tx_gap_size,
      READ_REQ  => sync_next,
      EMPTY     => sync_tx_ready_n
   );

   sync_next <= not sync_tx_ready_n and not sync_rx_ready_n;
   sync_vld_proc : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         if(RESET='1') then
            sync_vld <= '0';
         elsif sync_next='1' then
            sync_vld <= '1';
         end if;
      end if;
   end process;

   rx_rdy_reg : process(CLK)
   begin
      if(CLK'event and CLK='1') then
         rx_src_rdy_reg <= RX_SRC_RDY;
      end if;
   end process;


   assert (sync_next/='1' or sync_vld/='1' or sync_tx_gap_size=sync_rx_gap_size-HDR_BYTES or (sync_tx_gap_size=sync_rx_gap_size+WORD_BYTES-HDR_BYTES and sync_rx_gap_size<HDR_BYTES))
       report "HINS_VER: Sub-optimal gap size detected! (RX="&integer'IMAGE(conv_integer(sync_rx_gap_size))&", TX="&integer'IMAGE(conv_integer(sync_tx_gap_size))&")"
       severity error;
   assert ((TX_SRC_RDY='1' or sync_vld/='1') or not CLK'event or not CLK='1' or not rx_src_rdy_reg='1')
       report "HINS_VER: Wait state from HINS detected!)"
       severity error;
end architecture;

