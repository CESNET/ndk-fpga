-- hins.vhd
--!
--! \file
--! \brief FLU header insert full architecture
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! \name  FLU header insert full architecture
architecture full of HINS is
  constant EOP_POS_WIDTH  : integer := log2(DATA_WIDTH/8);
  constant BLOCK_WIDTH    : integer := DATA_WIDTH/(2**SOP_POS_WIDTH);
  constant BLOCKS         : integer := 2**SOP_POS_WIDTH;
  constant HDR_BLOCKS     : integer := HDR_WIDTH/BLOCK_WIDTH;

  type block_array_t is array (integer range <>) of std_logic_vector(BLOCK_WIDTH-1 downto 0);
  signal in_data          : block_array_t(0 to BLOCKS-1);
  signal mux_data         : block_array_t(0 to BLOCKS-1);
  signal rx_mux           : std_logic_vector(BLOCKS-1 downto 0);
  signal reg_data         : block_array_t(0 to BLOCKS-1);
  signal reg_data_we      : std_logic;
  signal reg_data_re      : std_logic;
  signal hdr              : block_array_t(0 to HDR_BLOCKS-1);
  signal aligned_hdr      : block_array_t(0 to HDR_BLOCKS-1);
  signal out_data         : block_array_t(0 to BLOCKS-1);
  signal tx_mux           : std_logic_vector(BLOCKS-1 downto 0);
  signal hdr_sel          : std_logic_vector(max(1,log2(HDR_BLOCKS))-1 downto 0) := (others => '0');
  signal mux_vec          : std_logic_vector(2*BLOCKS-1 downto 0) := (others => '0');
  signal mux_vec_base     : std_logic_vector(3*BLOCKS-1 downto 0) := (others => '0');
  signal mux_en           : std_logic;

  signal sop_pos_sub      : std_logic_vector(SOP_POS_WIDTH downto 0);
  signal sop_pos_new      : std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0) := (others => '0');
  signal sop_pos_guard    : std_logic := '0';
  signal sop_pos_cmp      : std_logic := '0';
  signal sop_pos_cmp_base : std_logic := '0';
  signal eop_pos_mux      : std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0) := (others => '0');
  signal eop_mux          : std_logic;
  signal new_word         : std_logic;
  signal new_word_inside  : std_logic;
  signal new_word_outside : std_logic;
  signal sop_reg_skip     : std_logic;

  signal vld_reg          : std_logic;
  signal eop_reg          : std_logic;
  signal eop_pos_reg      : std_logic_vector(max(1,EOP_POS_WIDTH)-1 downto 0) := (others => '0');
  signal eop_pos_reg_full : std_logic := '1';
  signal sop_reg          : std_logic;
  signal sop_pos_reg      : std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0) := (others => '0');

  signal rx_in_packet     : std_logic;
  signal sig_rx_dst_rdy   : std_logic;
  signal sig_tx_src_rdy   : std_logic;
  signal rx_eop_sent      : std_logic;
  signal rx_sending       : std_logic;
  signal rx_src_rdy_strong: std_logic;
  signal sig_tx_sop       : std_logic;
  signal true_rx_eop      : std_logic;
  signal sig_hdr_next     : std_logic;
  signal wait_start       : std_logic;
begin
  -- asserts over generic parameters
  assert (2**log2(DATA_WIDTH)=DATA_WIDTH and DATA_WIDTH>4)
    report "FLU_HINS: DATA_WIDTH must be power of 2 and higher than 4."
    severity error;
  assert ((HDR_WIDTH/BLOCK_WIDTH)*BLOCK_WIDTH=HDR_WIDTH)
    report "FLU_HINS: HDR_WIDTH must multiple of SOP_POS block size."
    severity error;
  assert (SOP_POS_WIDTH<=log2(DATA_WIDTH/8))
    report "FLU_HINS: SOP_POS_WIDTH cannot exceed log2(DATA_WIDTH/8)."
    severity error;
  assert (HDR_WIDTH>=DATA_WIDTH/(2**(SOP_POS_WIDTH)))
    report "FLU_HINS: HDR_WIDTH must have at least the size of one block addressable by SOP_POS."
    severity error;
  assert (HDR_WIDTH<=DATA_WIDTH)
    report "FLU_HINS: HDR_WIDTH cannot be greater than DATA_WIDTH."
    severity error;

  -- interfaces data connections
  data_connection : for i in 0 to BLOCKS-1 generate
    in_data(i)  <= RX_DATA((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH);
    TX_DATA((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH) <= out_data(i);
  end generate;
  hdr_connection : for i in 0 to HDR_BLOCKS-1 generate
    hdr(i) <= HDR_DATA((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH);
  end generate;

  -- barrel shifter of header data
  hdr_shifter : for i in 0 to HDR_BLOCKS-1 generate
    aligned_hdr(i) <= hdr((HDR_BLOCKS-conv_integer(hdr_sel)+i) mod HDR_BLOCKS);
  end generate;

  -- RX interface data nad signals registers
  data_register : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if reg_data_we='1' then
        reg_data    <= mux_data;
        eop_pos_reg <= RX_EOP_POS;
        sop_pos_reg <= sop_pos_new;
      end if;
    end if;
  end process;
  eop_register : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or (reg_data_re='1' and reg_data_we='0') then
        eop_reg <= '0';
      elsif reg_data_we='1' then
        eop_reg <= true_rx_eop;
      end if;
    end if;
  end process;
  sop_register : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or (reg_data_re='1' and reg_data_we='0') then
        sop_reg <= '0';
      elsif reg_data_we='1' then
        sop_reg <= RX_SOP and not sop_reg_skip and not new_word_inside;
      end if;
    end if;
  end process;
  valid_data_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or (reg_data_re='1' and reg_data_we='0') then
        vld_reg <= '0';
      elsif (reg_data_we='1' and reg_data_re='0') then
        vld_reg <= '1';
      end if;
    end if;
  end process;

  -- auxilliary registers
  in_pckt_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        rx_in_packet <= '0';
      elsif rx_sending='1' then
        rx_in_packet <= rx_in_packet xor RX_SOP xor RX_EOP;
      end if;
    end if;
  end process;
  rx_eop_sent_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or rx_sending='1' then
        rx_eop_sent <= '0';
      elsif new_word_inside='1' and reg_data_we='1' then
        rx_eop_sent <= '1';
      end if;
    end if;
  end process;

  -- RX and TX partial data multiplexing
  need_rx_mux_gen : if BLOCKS>1 generate
    rx_mux_gen : for i in 0 to BLOCKS-2 generate
      mux_data(i) <= in_data(i) when rx_mux(i)='0' else aligned_hdr(i mod HDR_BLOCKS);
    end generate;
  end generate;
  mux_data(BLOCKS-1) <= in_data(BLOCKS-1);
  need_no_tx_mux_gen : if BLOCKS>HDR_BLOCKS generate
    no_tx_mux_gen : for i in 0 to BLOCKS-HDR_BLOCKS-1 generate
      out_data(i) <= reg_data(i);
    end generate;
  end generate;
  tx_mux_gen : for i in BLOCKS-HDR_BLOCKS to BLOCKS-1 generate
    out_data(i) <= reg_data(i) when tx_mux(i)='0' else aligned_hdr((HDR_BLOCKS+i-BLOCKS) mod HDR_BLOCKS);
  end generate;

  -- data multiplexing control
  rx_mux <= mux_vec(2*BLOCKS-1 downto BLOCKS);
  tx_mux <= mux_vec(BLOCKS-1   downto 0);
  mux_en <= RX_SOP and rx_sending;
  base_mux_control_decoder : entity work.dec1fn_enable
    generic map (2**SOP_POS_WIDTH)
    port map (RX_SOP_POS,mux_en,mux_vec_base(2*BLOCKS-1 downto BLOCKS));
  mux_vec_gen : for i in BLOCKS-HDR_BLOCKS to 2*BLOCKS-2 generate
    mux_vec_or : entity work.gen_or
      generic map (HDR_BLOCKS)
      port map (mux_vec_base(i+HDR_BLOCKS downto i+1),mux_vec(i));
  end generate;

  -- sop_pos and eop_pos processing
  real_sop_pos_proc_gen : if SOP_POS_WIDTH>0 generate
    sop_pos_sub   <= ('1'&RX_SOP_POS)-conv_std_logic_vector(HDR_BLOCKS,SOP_POS_WIDTH+1);
    sop_pos_new   <= sop_pos_sub(SOP_POS_WIDTH-1 downto 0);
    sop_pos_guard <= sop_pos_sub(SOP_POS_WIDTH);
    sop_pos_mod : entity work.gen_mod
      generic map (SOP_POS_WIDTH,HDR_BLOCKS)
      port map (RX_SOP_POS,hdr_sel);
    sop_pos_cmp      <= (sop_pos_cmp_base or not eop_mux) and (sop_pos_guard or not rx_in_packet);
    sop_pos_cmp_base <= '1' when sop_pos_new>eop_pos_mux else '0';
    eop_pos_mux      <= RX_EOP_POS(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH) when sop_pos_guard='1' else eop_pos_reg(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH);
    eop_mux          <= RX_EOP                                                         when sop_pos_guard='1' else eop_reg;
    eop_pos_reg_full <= '1' when eop_pos_reg(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH)=(SOP_POS_WIDTH-1 downto 0 => '1') else '0';
  end generate;

  -- other control signals
  sop_reg_skip      <= RX_SOP and not sop_pos_guard and not new_word;
  new_word          <= new_word_inside or new_word_outside;
  new_word_inside   <= RX_SOP and rx_in_packet     and not sop_pos_cmp and true_rx_eop;
  new_word_outside  <= RX_SOP and not rx_in_packet and (sop_reg or (not sop_pos_cmp and eop_reg));
  wait_start        <= ((RX_SRC_RDY and RX_SOP and not HDR_READY) or (HDR_READY and not (RX_SRC_RDY and RX_SOP))) and eop_reg and not sop_reg and not eop_pos_reg_full;
  true_rx_eop       <= RX_EOP and not rx_eop_sent;
  rx_sending        <= RX_SRC_RDY and sig_rx_dst_rdy;
  rx_src_rdy_strong <= RX_SRC_RDY and (not RX_SOP or HDR_READY);
  sig_tx_sop        <= sop_reg or (sop_reg_skip and RX_SRC_RDY);


  reg_data_we    <= RX_SRC_RDY and (not vld_reg or reg_data_re) and not new_word_outside and (sig_rx_dst_rdy or new_word_inside);
  reg_data_re    <= TX_DST_RDY and not wait_start and vld_reg;
  sig_rx_dst_rdy <= (not RX_SOP or HDR_READY) and not new_word and (TX_DST_RDY or (not sop_reg_skip and not vld_reg));
  sig_hdr_next   <= RX_SOP and rx_sending;
  sig_tx_src_rdy <= not wait_start and (vld_reg or (sop_reg_skip and RX_SRC_RDY and HDR_READY));




  -- interface signals connetions
  TX_EOP     <= eop_reg;
  TX_EOP_POS <= eop_pos_reg;
  TX_SOP     <= sig_tx_sop;
  TX_SOP_POS <= sop_pos_reg when sop_reg_skip='0' else sop_pos_new;
  TX_SRC_RDY <= sig_tx_src_rdy;
  RX_DST_RDY <= sig_rx_dst_rdy;
  HDR_NEXT   <= sig_hdr_next;

  -- some functional asserts for verification and debug only
-- pragma synthesis_off
  assert (vld_reg/='0' or sop_reg/='1')
    report "FLU_HINS: sop_reg active when vld_reg is not!"
    severity error;
  assert (vld_reg/='0' or eop_reg/='1')
    report "FLU_HINS: eop_reg active when vld_reg is not!"
    severity error;
-- pragma synthesis_on
end architecture;

