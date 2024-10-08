-- fl_rxbuffer.vhd: Frame Link protocol receiving unit architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Libor Polcak <xpolca03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.mi32_pkg.all;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------

architecture FL_RXBUFFER_ARCH of FL_RXBUFFER is
   -- - Constants declaration
   constant const_rem_size         : integer := log2(DATA_WIDTH/8) - 1;
   constant const_fl_sig_size      : integer := 3;
   constant mx_width               : integer := 4 + max(DATA_WIDTH/32, 1);
   -- Address of the registers
   constant const_reg_cmd_addr     : std_logic_vector(4 downto 2) := "000";

   -- - FIFO output signals
   signal flfifo_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flfifo_tx_rem       : std_logic_vector(const_rem_size downto 0);
   signal flfifo_tx_src_rdy_n : std_logic;
   signal flfifo_tx_dst_rdy_n : std_logic;
   signal flfifo_tx_sop_n     : std_logic;
   signal flfifo_tx_eop_n     : std_logic;
   signal flfifo_tx_sof_n     : std_logic;
   signal flfifo_tx_eof_n     : std_logic;
   signal flfifo_rx_src_rdy_n : std_logic;
   signal flfifo_rx_dst_rdy_n : std_logic;
   -- - Signals declaration
   signal reg_cmd            : std_logic_vector(1 downto 0);
   signal reg_cmd_we         : std_logic;
   signal reg_cmd_cs         : std_logic;
   signal reg_status         : std_logic;
   signal reg_fl_data        : std_logic_vector((DATA_WIDTH-1) downto 0);
   signal reg_fl_rem         : std_logic_vector(const_rem_size downto 0);
   signal reg_fl_sig         : std_logic_vector(const_fl_sig_size downto 0);
   signal output_we          : std_logic;
   -- - Output decoder signals declaration
   signal mx_decoder_data_in : std_logic_vector(32*mx_width-1 downto 0);
   signal mx_decoder_data_out: std_logic_vector(31 downto 0);
   signal reg_cmd32          : std_logic_vector(31 downto 0);
   signal reg_status32       : std_logic_vector(31 downto 0);
   signal reg_fl_sig32       : std_logic_vector(31 downto 0);
   signal reg_fl_rem32       : std_logic_vector(31 downto 0);
   signal reg_fl_data32      : std_logic_vector(max(DATA_WIDTH, 32)-1 downto 0);

begin
   -- FL RX Buffer ready interface
   RX_DST_RDY_N        <= flfifo_rx_dst_rdy_n or (not reg_cmd(0));

   -- signals that enable FL FIFO input and output
   flfifo_rx_src_rdy_n <= (not reg_cmd(0)) or RX_SRC_RDY_N;
   flfifo_tx_dst_rdy_n <= not reg_cmd(1);

   -- FrameLink FIFO --------------------------------------------------------
   -- 8-bit DATA_WIDTH
   fl_fifo8: if DATA_WIDTH = 8 generate
      FL_FIFO8 : entity work.FL_FIFO8
         generic map(
            USE_BRAMS      => USE_BRAMS,
            ITEMS          => ITEMS,
            BLOCK_SIZE     => 0,
            PARTS          => PARTS,
            STATUS_WIDTH   => 0
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- write interface
            RX_DATA        => RX_DATA,
            RX_SRC_RDY_N   => flfifo_rx_src_rdy_n,
            RX_DST_RDY_N   => flfifo_rx_dst_rdy_n,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_SOF_N       => RX_SOF_N,
            RX_EOF_N       => RX_EOF_N,
            -- read interface
            TX_DATA        => flfifo_tx_data,
            TX_SRC_RDY_N   => flfifo_tx_src_rdy_n,
            TX_DST_RDY_N   => flfifo_tx_dst_rdy_n,
            TX_SOP_N       => flfifo_tx_sop_n,
            TX_EOP_N       => flfifo_tx_eop_n,
            TX_SOF_N       => flfifo_tx_sof_n,
            TX_EOF_N       => flfifo_tx_eof_n,
            -- FIFO state signals
            LSTBLK         => open,
            FULL           => open,
            EMPTY          => open,
            STATUS         => open,
            FRAME_RDY      => open
         );
   end generate fl_fifo8;

   -- more than 8-bit DATA_WIDTH
   fl_fifo: if DATA_WIDTH >= 16 generate
      FL_FIFO : entity work.FL_FIFO
         generic map(
            DATA_WIDTH     => DATA_WIDTH,
            USE_BRAMS      => USE_BRAMS,
            ITEMS          => ITEMS,
            BLOCK_SIZE     => 0,
            PARTS          => PARTS,
            STATUS_WIDTH   => 1
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- write interface
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            RX_SRC_RDY_N   => flfifo_rx_src_rdy_n,
            RX_DST_RDY_N   => flfifo_rx_dst_rdy_n,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_SOF_N       => RX_SOF_N,
            RX_EOF_N       => RX_EOF_N,
            -- read interface
            TX_DATA        => flfifo_tx_data,
            TX_REM         => flfifo_tx_rem,
            TX_SRC_RDY_N   => flfifo_tx_src_rdy_n,
            TX_DST_RDY_N   => flfifo_tx_dst_rdy_n,
            TX_SOP_N       => flfifo_tx_sop_n,
            TX_EOP_N       => flfifo_tx_eop_n,
            TX_SOF_N       => flfifo_tx_sof_n,
            TX_EOF_N       => flfifo_tx_eof_n,
            -- FIFO state signals
            LSTBLK         => open,
            FULL           => open,
            EMPTY          => open,
            STATUS         => open
         );
   end generate fl_fifo;

   -- register reg_cmd ------------------------------------------------------
   reg_cmdp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_cmd <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_cmd_we = '1') then
            reg_cmd <= MI32.DWR(1 downto 0);
         else
            reg_cmd(1) <= '0'; -- we want to read from the FIFO only once
         end if;
      end if;
   end process;

   -- register reg_status ---------------------------------------------------
   reg_statusp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_status <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_status <= not flfifo_tx_src_rdy_n;
      end if;
   end process;

   -- Output registers ------------------------------------------------------
   -- signals that enable writing to the output registers
   output_we           <= reg_cmd(1) and (not flfifo_tx_src_rdy_n);

   -- register reg_fl_rem ---------------------------------------------------
   reg_fl_remp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_fl_rem <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (output_we = '1') then
            reg_fl_rem <= flfifo_tx_rem;
         end if;
      end if;
   end process;

   -- register reg_fl_data --------------------------------------------------
   reg_fl_datap: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_fl_data <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (output_we = '1') then
            reg_fl_data <= flfifo_tx_data;
         end if;
      end if;
   end process;

   -- register reg_fl_sig ---------------------------------------------------
   reg_fl_sigp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_fl_sig <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (output_we = '1') then
            reg_fl_sig(0) <= flfifo_tx_sof_n;
            reg_fl_sig(1) <= flfifo_tx_eof_n;
            reg_fl_sig(2) <= flfifo_tx_sop_n;
            reg_fl_sig(3) <= flfifo_tx_eop_n;
         end if;
      end if;
   end process;

   --------------------------------------------------------------------------
   -- Address Decoder and MI32 interface
   -- -----------------------------------------------------------------------
   MI32.DRDY           <= MI32.RD;
   MI32.ARDY           <= '1';
   MI32.DRD            <= mx_decoder_data_out;
   -- Input -----------------------------------------------------------------
   reg_cmd_we <= reg_cmd_cs and MI32.WR;
   chip_selectp: process(MI32.ADDR(4 downto 2))
   begin
      reg_cmd_cs <= '0';

      case (MI32.ADDR(4 downto 2)) is
         when const_reg_cmd_addr => reg_cmd_cs <= '1';
         when others =>
      end case;
   end process;

   -- Output ----------------------------------------------------------------
   reg_cmd32       <= (31 downto 2 => '0') & reg_cmd;
   reg_status32    <= (31 downto 1 => '0') & reg_status;
   reg_fl_sig32    <= (31 downto const_fl_sig_size+1 => '0') & reg_fl_sig;
   reg_fl_rem32    <= (31 downto const_rem_size+1 => '0') & reg_fl_rem;

   -- reg_fl_data32 has to be generate generically
   fl_datag8: if DATA_WIDTH = 8 generate
      reg_fl_data32 <= (31 downto 8 => '0') & reg_fl_data;
   end generate fl_datag8;

   fl_datag16: if DATA_WIDTH = 16 generate
      reg_fl_data32 <= (31 downto 16 => '0') & reg_fl_data;
   end generate fl_datag16;

   fl_datago: if DATA_WIDTH >= 32 generate
      reg_fl_data32 <= reg_fl_data;
   end generate fl_datago;

   -- generic multiplexor input are concatenated 32-bit signals
   mx_decoder_data_in <= reg_fl_data32 &
                         reg_fl_rem32 &
                         reg_fl_sig32 &
                         reg_status32 &
                         reg_cmd32;

   MX_DECODER : entity work.GEN_MUX
      generic map (
         DATA_WIDTH  => 32,
         MUX_WIDTH   => mx_width
      )
      port map (
         DATA_IN     => mx_decoder_data_in,
         SEL         => MI32.ADDR(4 downto 2),
         DATA_OUT    => mx_decoder_data_out
      );

end architecture FL_RXBUFFER_ARCH;
