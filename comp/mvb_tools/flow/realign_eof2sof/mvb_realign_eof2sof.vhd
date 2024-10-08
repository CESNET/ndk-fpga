-- mvb_realign_eof2sof.vhd:
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MVB_REALIGN_EOF2SOF is
   generic(
      ITEMS       : natural := 4;
      ITEM_WIDTH  : natural := 128;
      OUTPUT_REG  : boolean := True
   );
   port(
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      -- MFB SOF INTERFACE
      MFB_SOF     : in  std_logic_vector(ITEMS-1 downto 0);
      MFB_SRC_RDY : in  std_logic;
      MFB_DST_RDY : out std_logic;
      -- RX MVB INTERFACE (ALIGNED TO EOF)
      RX_DATA     : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
      RX_VLD      : in  std_logic_vector(ITEMS-1 downto 0);
      RX_SRC_RDY  : in  std_logic;
      RX_DST_RDY  : out std_logic;
      -- TX MVB INTERFACE (ALIGNED TO SOF)
      TX_DATA     : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
      TX_VLD      : out std_logic_vector(ITEMS-1 downto 0);
      TX_SRC_RDY  : out std_logic;
      TX_DST_RDY  : in  std_logic
   );
end MVB_REALIGN_EOF2SOF;

architecture FULL of MVB_REALIGN_EOF2SOF is

   constant LOG2_ITEMS : natural := log2(ITEMS);

   signal data_mux_out             : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
   signal data_reg                 : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
   signal data_reg_en              : std_logic_vector(ITEMS-1 downto 0);
   signal data_reg_bypass_en       : std_logic_vector(ITEMS-1 downto 0);
   signal tx_data_comb_arr         : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
   signal tx_data_comb             : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
   signal tx_vld_comb              : std_logic_vector(ITEMS-1 downto 0);

   signal eof_vld                  : std_logic_vector(ITEMS-1 downto 0);
   signal eof_vld_mask             : std_logic_vector(ITEMS-1 downto 0);
   signal eof_vld_vector           : slv_array_t(ITEMS downto 0)(ITEMS-1 downto 0);
   signal eof_vld_vector_first_one : slv_array_t(ITEMS-1 downto 0)(ITEMS-1 downto 0);
   signal mfb_sof_vld              : std_logic_vector(ITEMS-1 downto 0);
   signal mfb_sof_vld_mask         : std_logic_vector(ITEMS-1 downto 0);
   signal mux_sel_onehot           : slv_array_t(ITEMS-1 downto 0)(ITEMS-1 downto 0);
   signal mux_out_vld              : std_logic_vector(ITEMS-1 downto 0);
   signal mux_out_vld_reg          : std_logic_vector(ITEMS-1 downto 0);
   signal mux_out_vld_reg_en       : std_logic;
   signal mux_out_vld_reg_rst      : std_logic;
   signal accept_last_sof          : std_logic;
   signal accept_all_eof           : std_logic;
   signal accept_eof               : std_logic_vector(ITEMS-1 downto 0);
   signal accept_eof_reg           : std_logic_vector(ITEMS-1 downto 0);
   signal accept_eof_reg_en        : std_logic;
   signal accept_eof_reg_rst       : std_logic;

begin

fake_gen: if ITEMS <= 1 generate
  TX_DATA <= RX_DATA;
  TX_VLD <= RX_VLD;
  TX_SRC_RDY <= RX_SRC_RDY and MFB_SRC_RDY;
  RX_DST_RDY <= TX_DST_RDY and MFB_SRC_RDY;
  MFB_DST_RDY <= RX_SRC_RDY and TX_DST_RDY;
end generate;

real_gen: if ITEMS > 1 generate
   -- ==========================================================================
   --  DATA PATH
   -- ==========================================================================

   data_path_g : for i in 0 to ITEMS-1 generate
      -- input data multiplexor
      data_mux_i : entity work.GEN_MUX_ONEHOT
      generic map (
         DATA_WIDTH => ITEM_WIDTH,
         MUX_WIDTH  => ITEMS
      )
      port map (
         DATA_IN  => RX_DATA,
         SEL      => mux_sel_onehot(i),
         DATA_OUT => data_mux_out(i)
      );

      -- register for temporary storage of muxed data
      data_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (data_reg_en(i) = '1') then
               data_reg(i) <= data_mux_out(i);
            end if;
         end if;
      end process;

      -- multiplexor for bypassing data register
      tx_data_comb_arr(i) <= data_mux_out(i) when (data_reg_bypass_en(i) = '1') else data_reg(i);

      -- create output data vector
      tx_data_comb((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH) <= tx_data_comb_arr(i);
   end generate;

   -- ==========================================================================
   --  CONTROL LOGIC
   -- ==========================================================================

   -- EOF valid vector is vector of RX valid flags
   eof_vld <= RX_SRC_RDY and RX_VLD;

   -- processed valid flags of EOF valid vector are masked
   eof_vld_mask <= eof_vld and not accept_eof_reg;

   -- find each ones in masked EOF valid vector
   eof_vld_vector(0) <= eof_vld_mask;
   find_each_one_g : for i in 0 to ITEMS-1 generate
      -- logic for search first one
      first_one_i : entity work.FIRST_ONE
      generic map (
         DATA_WIDTH => ITEMS
      )
      port map (
         DI => eof_vld_vector(i),
         DO => eof_vld_vector_first_one(i)
      );
      -- found first one is masked and first one is searched again in masked vector
      eof_vld_vector(i+1) <= eof_vld_vector(i) and not eof_vld_vector_first_one(i);
   end generate;

   -- MFB_SOF is valid only when is assert MFB_SRC_RDY input
   mfb_sof_vld <= MFB_SOF and MFB_SRC_RDY;

   -- processed valid flags of MFB SOF vector are masked
   mfb_sof_vld_mask <= mfb_sof_vld and not mux_out_vld_reg;

   -- process of control logic
   mux_sel_logic_p : process (all)
      variable order_var      : natural range 0 to ITEMS;
      variable accept_eof_var : std_logic_vector(ITEMS-1 downto 0);
   begin
      order_var       := 0;
      accept_eof_var  := accept_eof_reg;
      mux_out_vld     <= (others => '0');
      accept_last_sof <= '0';
      for i in 0 to ITEMS-1 loop
         mux_sel_onehot(i) <= eof_vld_vector_first_one(order_var);
         if (mfb_sof_vld_mask(i) = '1') then
            mux_out_vld(i)  <= or eof_vld_vector_first_one(order_var);
            accept_last_sof <= or eof_vld_vector_first_one(order_var);
            accept_eof_var  := accept_eof_var or eof_vld_vector_first_one(order_var);
            order_var       := order_var + 1;
         end if;
      end loop;
      accept_eof <= accept_eof_var;
   end process;

   -- enable of data register is valid of multiplexor output
   data_reg_en <= mux_out_vld;

   -- register for store valid flags of multiplexor output
   mux_out_vld_reg_en  <= RX_DST_RDY and RX_SRC_RDY;
   mux_out_vld_reg_rst <= RESET or MFB_DST_RDY;

   mux_out_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (mux_out_vld_reg_rst = '1') then
            mux_out_vld_reg <= (others => '0');
         elsif (mux_out_vld_reg_en = '1') then
            mux_out_vld_reg <= mux_out_vld;
         end if;
      end if;
   end process;

   -- bypass of data register is enable when was not valid of multiplexor output
   -- in last valid cycle
   data_reg_bypass_en <= not mux_out_vld_reg;

   -- flag assert when was accepted (processed) all flags of EOF valid vector
   accept_all_eof <= nor (eof_vld_mask and not accept_eof);

   -- register for store accepted (processed) flags of EOF valid vector
   accept_eof_reg_en  <= TX_DST_RDY and not accept_all_eof;
   accept_eof_reg_rst <= RESET or RX_DST_RDY;

   accept_eof_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (accept_eof_reg_rst = '1') then
            accept_eof_reg <= (others => '0');
         elsif (accept_eof_reg_en = '1') then
            accept_eof_reg <= accept_eof;
         end if;
      end if;
   end process;

   -- output control signals of dataflow
   tx_vld_comb <= mfb_sof_vld and accept_last_sof;
   MFB_DST_RDY <= TX_DST_RDY and accept_last_sof;
   RX_DST_RDY  <= (accept_all_eof and not accept_last_sof and not RESET) or
                  (TX_DST_RDY and accept_last_sof and accept_all_eof and not RESET);

   -- ==========================================================================
   --  OUTPUT REGISTERS
   -- ==========================================================================

   out_reg_on_g : if OUTPUT_REG generate
      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               TX_SRC_RDY <= '0';
            elsif (TX_DST_RDY = '1') then
               TX_SRC_RDY <= or tx_vld_comb;
            end if;
         end if;
      end process;

      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
               TX_DATA <= tx_data_comb;
               TX_VLD  <= tx_vld_comb;
            end if;
         end if;
      end process;
   end generate;

   out_reg_off_g : if not OUTPUT_REG generate
      TX_SRC_RDY <= or tx_vld_comb;
      TX_DATA    <= tx_data_comb;
      TX_VLD     <= tx_vld_comb;
   end generate;
end generate;

end architecture;
