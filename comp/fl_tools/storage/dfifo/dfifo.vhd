-- fl_dfifo.vhd: FIFO with discard capability on input
-- Copyright (C) 2009 CESNET
-- Author(s): Jiri Novotnak <xnovot87@stud.fit.vutbr.cz>
--
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 and min functions
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture fl_dfifo_arch of fl_dfifo is

   constant FRAME_LENGHT       : integer := 4;
   constant ADDRESS_WIDTH  : integer := log2(ITEMS);
   constant JUICE_WIDTH        : integer := 1;

      -- write interface
   signal input_rx_data         : std_logic_vector(RX_DATA'length-1 downto 0);
   signal input_rx_rem            : std_logic_vector(RX_REM'length-1 downto 0);
   signal input_rx_src_rdy_n    : std_logic;
   signal input_rx_dst_rdy_n    : std_logic;
   signal input_rx_sop_n        : std_logic;
   signal input_rx_eop_n        : std_logic;
   signal input_rx_sof_n        : std_logic;
   signal input_rx_eof_n        : std_logic;
   signal sig_discard           : std_logic;

      -- read interface
   signal output_tx_data        : std_logic_vector(TX_DATA'length-1 downto 0);
   signal output_tx_rem         : std_logic_vector(TX_REM'length-1 downto 0);
   signal output_tx_src_rdy_n   : std_logic;
   signal output_tx_dst_rdy_n   : std_logic;
   signal output_tx_sop_n       : std_logic;
   signal output_tx_eop_n       : std_logic;
   signal output_tx_sof_n       : std_logic;
   signal output_tx_eof_n       : std_logic;


   signal mem_dob      : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+JUICE_WIDTH-1 downto 0);

   signal fl_com_juice          : std_logic_vector(JUICE_WIDTH-1 downto 0);
   signal fl_decom_juice        : std_logic_vector(JUICE_WIDTH-1 downto 0);

   signal mem_write_en          : std_logic;
   signal mem_write_addr        : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal mem_read_addr         : std_logic_vector(ADDRESS_WIDTH-1 downto 0);

   signal cnt_write_address     : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal cnt_read_address      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);

   signal cnt_write_rollback    : std_logic;
   signal reg_cnt_state         : std_logic_vector(cnt_write_address'range);
   signal reg_cnt_read          : std_logic_vector(cnt_read_address'range);

   signal write_en              : std_logic;
   signal read_en               : std_logic;
   signal reg_discard           : std_logic;
   signal cmp_full              : std_logic;
   signal cmp_empty             : std_logic;
   signal reg_write_address     : std_logic_vector(cnt_write_address'range);
   signal mem_di                : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+JUICE_WIDTH-1 downto 0);

begin
      -- write interface
   input_rx_data         <= RX_DATA;
   input_rx_rem          <= RX_REM;
   input_rx_src_rdy_n    <= RX_SRC_RDY_N;
   RX_DST_RDY_N          <= input_rx_dst_rdy_n;
   input_rx_sop_n        <= RX_SOP_N;
   input_rx_eop_n        <= RX_EOP_N;
   input_rx_sof_n        <= RX_SOF_N;
   input_rx_eof_n        <= RX_EOF_N;

      -- read interface
   TX_DATA             <= output_tx_data;
   TX_REM              <= output_tx_rem;
   TX_SRC_RDY_N        <= output_tx_src_rdy_n;
   output_tx_dst_rdy_n <= TX_DST_RDY_N;
   TX_SOP_N            <= output_tx_sop_n;
   TX_EOP_N            <= output_tx_eop_n;
   TX_SOF_N            <= output_tx_sof_n;
   TX_EOF_N            <= output_tx_eof_n;

      -- FIFO state signals
   sig_discard <= DISCARD;

   -- Memory connection -------------------------------------------------------
   U_DP_DISTMEM: entity work.DP_DISTMEM
      generic map (
         data_width     => mem_di'length,
         items          => ITEMS
      )
      port map (
         -- Write port
         WCLK        => CLK,
         ADDRA       => mem_write_addr,
         DI          => mem_di,
         WE          => mem_write_en,
         DOA         => open,

         -- Read port
         ADDRB       => mem_read_addr,
         DOB         => mem_dob
      );
   mem_di   <= fl_com_juice & input_rx_rem & input_rx_data;

   output_tx_data    <= mem_dob(DATA_WIDTH-1 downto 0);
   output_tx_rem     <= mem_dob(DATA_WIDTH+output_tx_rem'length-1 downto DATA_WIDTH);
   fl_decom_juice    <= mem_dob(mem_dob'left
                           downto mem_dob'left - fl_decom_juice'length + 1);


   mem_write_addr <= reg_write_address;
   mem_write_en <= write_en;
   mem_read_addr <= cnt_read_address;

   -- Compress FrameLink to juice
   fl_compress_inst : entity work.fl_compress
   generic map(
      WIRES       => JUICE_WIDTH
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,

      RX_SRC_RDY_N=> input_rx_src_rdy_n,
      RX_DST_RDY_N=> input_rx_dst_rdy_n,
      RX_SOP_N    => input_rx_sop_n,
      RX_EOP_N    => input_rx_eop_n,
      RX_SOF_N    => input_rx_sof_n,
      RX_EOF_N    => input_rx_eop_n,
      FL_JUICE    => fl_com_juice,
      FRAME_PART  => open
   );

   -- Decompress FrameLink signals from sig_juice_out
   fl_decompress_inst : entity work.fl_decompress_any
   generic map(
      WIRES       => JUICE_WIDTH,
      PARTS       => PARTS
   )
   port map(
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,

      TX_SRC_RDY_N=> output_tx_src_rdy_n,
      TX_DST_RDY_N=> output_tx_dst_rdy_n,
      TX_SOP_N    => output_tx_sop_n,
      TX_EOP_N    => output_tx_eop_n,
      TX_SOF_N    => output_tx_sof_n,
      TX_EOF_N    => output_tx_eof_n,
      FL_JUICE    => fl_decom_juice,
      DISCARD     => '0'
   );

   -- Read and Write allowed signals
   write_en <= not (input_rx_src_rdy_n or input_rx_dst_rdy_n);
   read_en  <= not (output_tx_src_rdy_n or output_tx_dst_rdy_n);

   -- FrameLink control signals
   input_rx_dst_rdy_n <= cmp_full;
   output_tx_src_rdy_n <= cmp_empty;
   -- register reg_write_address ----------------------------------------------
   reg_write_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_write_address <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (write_en = '1') then
            if (cnt_write_rollback = '0') then
               reg_write_address <= cnt_write_address;
            else
               reg_write_address <= reg_cnt_state;
            end if;
         end if;
      end if;
   end process;

   -- Write address counter ---------------------------------------------------
   cnt_write_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_write_address <= conv_std_logic_vector(1, cnt_write_address'length);
      elsif (CLK'event AND CLK = '1') then
         if (write_en = '1') then
            if (cnt_write_rollback = '1') then
               cnt_write_address <= reg_cnt_state + 1;
            elsif (cnt_write_address(ADDRESS_WIDTH-1 downto 0) = ITEMS-1) then
               cnt_write_address(ADDRESS_WIDTH-1 downto 0) <= (others => '0');
            else
               cnt_write_address <= cnt_write_address + 1;
            end if;
         end if;
      end if;
   end process;

--   cnt_write_rollback <= write_en and (not input_rx_eof_n) and (reg_discard or sig_discard);
   cnt_write_rollback <= write_en and ((reg_discard and input_rx_sof_n) or sig_discard);

   -- register reg_cnt_state ------------------------------------------------------
   reg_cnt_statep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_cnt_state <= conv_std_logic_vector(0, cnt_write_address'length);
         elsif (write_en = '1' and sig_discard = '0' and reg_discard = '0' and input_rx_eof_n = '0') then
            reg_cnt_state <= cnt_write_address;
         end if;
      end if;
   end process;

   -- Read counter ------------------------------------------------------------
   cnt_read_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_read_address <= conv_std_logic_vector(0, cnt_read_address'length);
         reg_cnt_read <= conv_std_logic_vector(ITEMS - 1, reg_cnt_read'length);
      elsif (CLK'event AND CLK = '1') then
         if (read_en = '1') then
            reg_cnt_read <= cnt_read_address;

            if (cnt_read_address(ADDRESS_WIDTH-1 downto 0) = ITEMS-1) then
               cnt_read_address(ADDRESS_WIDTH-1 downto 0) <= (others => '0');
            else
               cnt_read_address <= cnt_read_address + 1;
            end if;

         end if;
      end if;
   end process;

   -- register reg_discard ------------------------------------------------------
   reg_discardp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_discard <= '0';
         elsif write_en = '1' then
            reg_discard <= sig_discard or (reg_discard and input_rx_sof_n);
         end if;
      end if;
   end process;

   -- Comparator for EMPTY signal ---------------------------------------------
   sig_emptyp: process(cnt_read_address, reg_cnt_state)
   begin
      if ( cnt_read_address = reg_cnt_state) then
         cmp_empty <= '1';
      else
         cmp_empty <= '0';
      end if;
   end process;

   -- Comparator for FULL signal ----------------------------------------------
   cmp_fullp: process(reg_cnt_read, reg_write_address)
   begin
      if (reg_cnt_read(ADDRESS_WIDTH-1 downto 0) =
          reg_write_address(ADDRESS_WIDTH-1 downto 0)) then
         cmp_full <= '1';
      else
         cmp_full <= '0';
      end if;
   end process;
end architecture fl_dfifo_arch;
