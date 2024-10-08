-- mfb_asfifo_512to256.vhd: MFB asynch BRAM FIFO with 2-region 512b input and 1-region 256b output
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_misc.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

entity MFB_ASFIFO_512to256 is
   generic(
      FIFO_ITEMS    : integer := 512 -- 512, 1024, 2048, 4096, 8192 (less effective)
   );
   port(
      RX_CLK        : in  std_logic;
      RX_RESET      : in  std_logic;

      RX_DATA       : in  std_logic_vector(2*1*8*32-1 downto 0);
      RX_SOF_POS    : in  std_logic_vector(2*max(1,log2(1))-1 downto 0);
      RX_EOF_POS    : in  std_logic_vector(2*max(1,log2(1*8))-1 downto 0);
      RX_SOF        : in  std_logic_vector(2-1 downto 0);
      RX_EOF        : in  std_logic_vector(2-1 downto 0);
      RX_SRC_RDY    : in  std_logic;
      RX_DST_RDY    : out std_logic;

      TX_CLK        : in  std_logic;
      TX_RESET      : in  std_logic;

      TX_DATA       : out std_logic_vector(1*1*8*32-1 downto 0);
      TX_SOF_POS    : out std_logic_vector(1*max(1,log2(1))-1 downto 0);
      TX_EOF_POS    : out std_logic_vector(1*max(1,log2(1*8))-1 downto 0);
      TX_SOF        : out std_logic_vector(1-1 downto 0);
      TX_EOF        : out std_logic_vector(1-1 downto 0);
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in  std_logic
   );
end entity;

architecture full of MFB_ASFIFO_512to256 is
    signal aux_RX_DATA    : std_logic_vector(2*1*8*32-1 downto 0);
    signal aux_RX_SOF_POS : std_logic_vector(2*max(1,log2(1))-1 downto 0);
    signal aux_RX_EOF_POS : std_logic_vector(2*max(1,log2(1*8))-1 downto 0);
    signal aux_RX_SOF     : std_logic_vector(2-1 downto 0);
    signal aux_RX_EOF     : std_logic_vector(2-1 downto 0);
    signal aux_RX_SRC_RDY : std_logic;
    signal aux_RX_DST_RDY : std_logic;

    signal aux_region_vld : std_logic_vector(1 downto 0);

    signal rx_dst_rdy_s : std_logic_vector(1 downto 0);

    signal asfifo_tx_data       : slv_array_t(1 downto 0)(1*1*8*32-1 downto 0);
    signal asfifo_tx_region_vld : std_logic_vector(1 downto 0);
    signal asfifo_tx_sof_pos    : slv_array_t(1 downto 0)(1*max(1,log2(1))-1 downto 0);
    signal asfifo_tx_eof_pos    : slv_array_t(1 downto 0)(1*max(1,log2(1*8))-1 downto 0);
    signal asfifo_tx_sof        : slv_array_t(1 downto 0)(1-1 downto 0);
    signal asfifo_tx_eof        : slv_array_t(1 downto 0)(1-1 downto 0);
    signal asfifo_tx_src_rdy    : std_logic_vector(1 downto 0);
    signal asfifo_tx_dst_rdy    : std_logic_vector(1 downto 0);

    signal out_ptr_reg : unsigned(0 downto 0) := (others => '0');
begin

   auxiliary_signals_i : entity work.MFB_AUXILIARY_SIGNALS
   generic map(
      REGIONS       => 2    ,
      REGION_SIZE   => 1    ,
      BLOCK_SIZE    => 8    ,
      ITEM_WIDTH    => 32   ,
      REGION_AUX_EN => true ,
      BLOCK_AUX_EN  => false,
      ITEM_AUX_EN   => false
   )
   port map(
      CLK   => RX_CLK  ,
      RESET => RX_RESET,

      RX_DATA          => RX_DATA   ,
      RX_SOF_POS       => RX_SOF_POS,
      RX_EOF_POS       => RX_EOF_POS,
      RX_SOF           => RX_SOF    ,
      RX_EOF           => RX_EOF    ,
      RX_SRC_RDY       => RX_SRC_RDY,
      RX_DST_RDY       => RX_DST_RDY,

      TX_DATA          => aux_RX_DATA   ,
      TX_SOF_POS       => aux_RX_SOF_POS,
      TX_EOF_POS       => aux_RX_EOF_POS,
      TX_SOF           => aux_RX_SOF    ,
      TX_EOF           => aux_RX_EOF    ,
      TX_SRC_RDY       => aux_RX_SRC_RDY,
      TX_DST_RDY       => aux_RX_DST_RDY,

      TX_REGION_SHARED => open          ,
      TX_REGION_VLD    => aux_region_vld,
      TX_BLOCK_VLD     => open          ,
      TX_ITEM_VLD      => open
   );

   aux_RX_DST_RDY <= rx_dst_rdy_s(0) and rx_dst_rdy_s(1);

   asfifo_gen : for i in 0 to 1 generate
      afifo_i : entity work.MFB_ASFIFOX
      generic map(
         DEVICE           => "7SERIES" ,
         MFB_REGIONS      => 1         ,
         MFB_REG_SIZE     => 1         ,
         MFB_BLOCK_SIZE   => 8         ,
         MFB_ITEM_WIDTH   => 32        ,
         FIFO_ITEMS       => FIFO_ITEMS,
         OUTPUT_REG       => true      ,
         METADATA_WIDTH   => 1         ,
         FWFT_MODE        => true      ,
         RAM_TYPE         => "BRAM"
      )
      port map(
         RX_CLK       => RX_CLK  ,
         RX_RESET     => RX_RESET,

         RX_DATA      => aux_RX_DATA   (   (8*32)       *(i+1)-1 downto    (8*32)       *i),
         RX_META(0)   => aux_region_vld(i),
         RX_SOF_POS   => aux_RX_SOF_POS(max(1,log2(1))  *(i+1)-1 downto max(1,log2(1))  *i),
         RX_EOF_POS   => aux_RX_EOF_POS(max(1,log2(1*8))*(i+1)-1 downto max(1,log2(1*8))*i),
         RX_SOF       => aux_RX_SOF(i downto i),
         RX_EOF       => aux_RX_EOF(i downto i),
         RX_SRC_RDY   => aux_RX_SRC_RDY and rx_dst_rdy_s(1-i),
         RX_DST_RDY   => rx_dst_rdy_s(i),

         TX_CLK       => TX_CLK  ,
         TX_RESET     => TX_RESET,

         TX_DATA      => asfifo_tx_data(i),
         TX_META(0)   => asfifo_tx_region_vld(i),
         TX_SOF_POS   => asfifo_tx_sof_pos(i),
         TX_EOF_POS   => asfifo_tx_eof_pos(i),
         TX_SOF       => asfifo_tx_sof(i),
         TX_EOF       => asfifo_tx_eof(i),
         TX_SRC_RDY   => asfifo_tx_src_rdy(i),
         TX_DST_RDY   => asfifo_tx_dst_rdy(i)
      );
   end generate;

   out_ptr_reg_pr : process (TX_CLK)
   begin
      if (TX_CLK'event and TX_CLK='1') then
         if (asfifo_tx_src_rdy(to_integer(out_ptr_reg))='1' and TX_DST_RDY='1') then
            out_ptr_reg(0) <= not out_ptr_reg(0);
         end if;

         if (TX_RESET='1') then
            out_ptr_reg <= (others => '0');
         end if;
      end if;
   end process;

   TX_DATA    <= asfifo_tx_data   (to_integer(out_ptr_reg));
   TX_SOF_POS <= asfifo_tx_sof_pos(to_integer(out_ptr_reg));
   TX_EOF_POS <= asfifo_tx_eof_pos(to_integer(out_ptr_reg));
   TX_SOF     <= asfifo_tx_sof    (to_integer(out_ptr_reg));
   TX_EOF     <= asfifo_tx_eof    (to_integer(out_ptr_reg));
   TX_SRC_RDY <= asfifo_tx_src_rdy(to_integer(out_ptr_reg)) and asfifo_tx_region_vld(to_integer(out_ptr_reg));

   asfifo_tx_dst_rdy(0) <= TX_DST_RDY and not out_ptr_reg(0);
   asfifo_tx_dst_rdy(1) <= TX_DST_RDY and     out_ptr_reg(0);

end architecture;
