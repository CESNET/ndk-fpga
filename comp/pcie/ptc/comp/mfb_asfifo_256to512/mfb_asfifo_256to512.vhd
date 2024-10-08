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

entity MFB_ASFIFO_256to512 is
   generic(
      FIFO_ITEMS         : integer := 512; -- 512, 1024, 2048, 4096, 8192 (less effective)
      ALMOST_FULL_OFFSET : integer := 8
   );
   port(
      RX_CLK        : in  std_logic;
      RX_RESET      : in  std_logic;

      RX_DATA       : in std_logic_vector(2*1*4*32-1 downto 0);
      RX_SOF_POS    : in std_logic_vector(2*max(1,log2(1))-1 downto 0);
      RX_EOF_POS    : in std_logic_vector(2*max(1,log2(1*4))-1 downto 0);
      RX_SOF        : in std_logic_vector(2-1 downto 0);
      RX_EOF        : in std_logic_vector(2-1 downto 0);
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;
      RX_AFULL      : out std_logic;

      TX_CLK        : in  std_logic;
      TX_RESET      : in  std_logic;

      TX_DATA       : out std_logic_vector(4*1*4*32-1 downto 0);
      TX_SOF_POS    : out std_logic_vector(4*max(1,log2(1))-1 downto 0);
      TX_EOF_POS    : out std_logic_vector(4*max(1,log2(1*4))-1 downto 0);
      TX_SOF        : out std_logic_vector(4-1 downto 0);
      TX_EOF        : out std_logic_vector(4-1 downto 0);
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in  std_logic
   );
end entity;

architecture full of MFB_ASFIFO_256to512 is

   signal rx_src_rdy_s : std_logic_vector(1 downto 0);
   signal rx_dst_rdy_s : std_logic_vector(1 downto 0);
   signal afull_s      : std_logic_vector(1 downto 0);

   signal asfifo_tx_data    : slv_array_t(1 downto 0)(2*1*4*32-1 downto 0);
   signal asfifo_tx_sof_pos : slv_array_t(1 downto 0)(2*max(1,log2(1))-1 downto 0);
   signal asfifo_tx_eof_pos : slv_array_t(1 downto 0)(2*max(1,log2(1*4))-1 downto 0);
   signal asfifo_tx_sof     : slv_array_t(1 downto 0)(2-1 downto 0);
   signal asfifo_tx_eof     : slv_array_t(1 downto 0)(2-1 downto 0);
   signal asfifo_tx_src_rdy : std_logic_vector(1 downto 0);
   signal asfifo_tx_dst_rdy : std_logic_vector(1 downto 0);

   signal in_ptr_reg  : unsigned(0 downto 0) := (others => '0');

   signal out_ptr_reg : unsigned(0 downto 0) := (others => '0');

   -- indexing signal
   signal not_out_ptr  : unsigned(0 downto 0) := (others => '0');
   signal not_out_ptrI : integer := 0;
   signal     out_ptrI : integer := 0;

   signal allow_read   : std_logic;
begin

   rx_src_rdy_s(0) <= RX_SRC_RDY and not in_ptr_reg(0);
   rx_src_rdy_s(1) <= RX_SRC_RDY and     in_ptr_reg(0);

   RX_DST_RDY <= rx_dst_rdy_s(to_integer(in_ptr_reg));
   RX_AFULL   <= afull_s     (to_integer(in_ptr_reg));

   asfifo_gen : for i in 0 to 1 generate
      afifo_i : entity work.MFB_ASFIFOX
      generic map(
         DEVICE             => "7SERIES"         ,
         MFB_REGIONS        => 2                 ,
         MFB_REG_SIZE       => 1                 ,
         MFB_BLOCK_SIZE     => 4                 ,
         MFB_ITEM_WIDTH     => 32                ,
         FIFO_ITEMS         => FIFO_ITEMS        ,
         OUTPUT_REG         => true              ,
         FWFT_MODE          => true              ,
         RAM_TYPE           => "BRAM"            ,
         ALMOST_FULL_OFFSET => ALMOST_FULL_OFFSET
      )
      port map(
         RX_CLK       => RX_CLK  ,
         RX_RESET     => RX_RESET,

         RX_DATA      => RX_DATA,
         RX_SOF_POS   => RX_SOF_POS,
         RX_EOF_POS   => RX_EOF_POS,
         RX_SOF       => RX_SOF,
         RX_EOF       => RX_EOF,
         RX_SRC_RDY   => rx_src_rdy_s(i),
         RX_DST_RDY   => rx_dst_rdy_s(i),
         RX_AFULL     => afull_s(i),

         TX_CLK       => TX_CLK  ,
         TX_RESET     => TX_RESET,

         TX_DATA      => asfifo_tx_data(i),
         TX_SOF_POS   => asfifo_tx_sof_pos(i),
         TX_EOF_POS   => asfifo_tx_eof_pos(i),
         TX_SOF       => asfifo_tx_sof(i),
         TX_EOF       => asfifo_tx_eof(i),
         TX_SRC_RDY   => asfifo_tx_src_rdy(i),
         TX_DST_RDY   => asfifo_tx_dst_rdy(i)
      );
   end generate;

   in_ptr_reg_pr : process (RX_CLK)
   begin
      if (RX_CLK'event and RX_CLK='1') then
         if (rx_dst_rdy_s(to_integer(in_ptr_reg))='1' and RX_SRC_RDY='1') then
            in_ptr_reg(0) <= not in_ptr_reg(0);
         end if;

         if (RX_RESET='1') then
            in_ptr_reg <= (others => '0');
         end if;
      end if;
   end process;

   out_ptr_reg_pr : process (TX_CLK)
   begin
      if (TX_CLK'event and TX_CLK='1') then
         if ((allow_read='1' and (and asfifo_tx_src_rdy)='0') and TX_DST_RDY='1') then
            out_ptr_reg(0) <= not out_ptr_reg(0);
         end if;

         if (TX_RESET='1') then
            out_ptr_reg <= (others => '0');
         end if;
      end if;
   end process;

   not_out_ptr(0) <= not out_ptr_reg(0);
   not_out_ptrI   <= to_integer(not_out_ptr);
   out_ptrI       <= to_integer(out_ptr_reg);

   --                      (can read from both fifos ) or ((   can read from first fifo    ) and (((   end of data in region 0    ) and ( no start of data in region 1 )) or ((  end of data in region 1   ))))
   allow_read <= '1' when  (and asfifo_tx_src_rdy)='1' or ( asfifo_tx_src_rdy(out_ptrI)='1'  and (( asfifo_tx_eof(out_ptrI)(0)='1'  and  asfifo_tx_sof(out_ptrI)(1)='0' ) or ( asfifo_tx_eof(out_ptrI)(1)='1' ))) else '0';

   TX_DATA    <= asfifo_tx_data   (not_out_ptrI) & asfifo_tx_data   (out_ptrI);
   TX_SOF_POS <= asfifo_tx_sof_pos(not_out_ptrI) & asfifo_tx_sof_pos(out_ptrI);
   TX_EOF_POS <= asfifo_tx_eof_pos(not_out_ptrI) & asfifo_tx_eof_pos(out_ptrI);

   TX_SOF     <= (asfifo_tx_src_rdy(not_out_ptrI) and asfifo_tx_sof(not_out_ptrI)) & (asfifo_tx_src_rdy(out_ptrI) and asfifo_tx_sof(out_ptrI));
   TX_EOF     <= (asfifo_tx_src_rdy(not_out_ptrI) and asfifo_tx_eof(not_out_ptrI)) & (asfifo_tx_src_rdy(out_ptrI) and asfifo_tx_eof(out_ptrI));

   TX_SRC_RDY <= allow_read;

   asfifo_tx_dst_rdy(0) <= TX_DST_RDY and allow_read;
   asfifo_tx_dst_rdy(1) <= TX_DST_RDY and allow_read;

end architecture;
