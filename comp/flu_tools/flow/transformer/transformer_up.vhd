-- transformer_up.vhd: Implementation of UP architecture of FrameLinkUnaligned Transformer component.
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- library containing log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FLU_TRANSFORMER_UP is
  generic(
    RX_DATA_WIDTH    : integer := 256;
    RX_SOP_POS_WIDTH : integer := 2;
    TX_DATA_WIDTH    : integer := 512;
    TX_SOP_POS_WIDTH : integer := 3
  );
  port(
    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- Frame Link Unaligned input interface
    RX_DATA       : in std_logic_vector(RX_DATA_WIDTH-1 downto 0);
    RX_SOP_POS    : in std_logic_vector(max(1,RX_SOP_POS_WIDTH)-1 downto 0);
    RX_EOP_POS    : in std_logic_vector(max(1,log2(RX_DATA_WIDTH/8))-1 downto 0);
    RX_SOP        : in std_logic;
    RX_EOP        : in std_logic;
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    -- Frame Link Unaligned output interface
    TX_DATA       : out std_logic_vector(TX_DATA_WIDTH-1 downto 0);
    TX_SOP_POS    : out std_logic_vector(max(1,TX_SOP_POS_WIDTH)-1 downto 0);
    TX_EOP_POS    : out std_logic_vector(max(1,log2(TX_DATA_WIDTH/8))-1 downto 0);
    TX_SOP        : out std_logic;
    TX_EOP        : out std_logic;
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic
  );
end entity;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of FLU_TRANSFORMER_UP is
  constant TX_BLOCKS            : integer := TX_DATA_WIDTH/RX_DATA_WIDTH;
  constant TX_SOP_POS_WIDTH_REAL: integer := RX_SOP_POS_WIDTH+log2(TX_BLOCKS);
  constant RX_EOP_POS_WIDTH     : integer := log2(RX_DATA_WIDTH/8);
  constant TX_EOP_POS_WIDTH     : integer := log2(TX_DATA_WIDTH/8);

  type rx_data_width_array_t is array (integer range <>) of std_logic_vector(RX_DATA_WIDTH-1 downto 0);
  signal tx_data_regs           : rx_data_width_array_t(0 to TX_BLOCKS-1);
  signal tx_data_regs_ce        : std_logic_vector(TX_BLOCKS-1 downto 0);
  signal tx_data_regs_cs1       : std_logic_vector(TX_BLOCKS-1 downto 0);
  signal tx_data_regs_cs2       : std_logic_vector(TX_BLOCKS-1 downto 0);
  signal tx_regs_wr             : std_logic;
  signal tx_eop_reg             : std_logic;
  signal tx_sop_reg             : std_logic;
  signal tx_eop_pos_reg         : std_logic_vector(TX_EOP_POS_WIDTH-1 downto 0);
  signal tx_sop_pos_reg         : std_logic_vector(TX_SOP_POS_WIDTH_REAL-1+max(1,RX_SOP_POS_WIDTH)-RX_SOP_POS_WIDTH downto 0);
  signal tx_vld                 : std_logic;
  signal tx_in_packet           : std_logic;
  signal shreg_pop              : std_logic;
  signal export_now             : std_logic;
  signal tx_eop_actual          : std_logic;
  signal tx_sop_actual          : std_logic;
  signal tx_last_word           : std_logic;
  signal tx_cnt                 : std_logic_vector(log2(TX_BLOCKS)-1 downto 0);
  signal tx_cnt_en              : std_logic;
  signal tx_addr                : std_logic_vector(log2(TX_BLOCKS)-1 downto 0);
  signal tx_sop_addr            : std_logic_vector(log2(TX_BLOCKS)-1 downto 0);

  signal aux_reg_vld_now        : std_logic;
  signal aux_reg_vld            : std_logic;
  signal aux_reg_data           : std_logic_vector(RX_DATA_WIDTH-1 downto 0);
  signal aux_reg_sop_pos        : std_logic_vector(max(1,RX_SOP_POS_WIDTH)-1 downto 0);

  signal rx_shift_en            : std_logic;
  signal rx_depth               : std_logic_vector(log2(TX_BLOCKS+1)-1 downto 0);
  signal rx_sop_vld             : std_logic;
  signal rx_eop_vld             : std_logic;
  signal rx_shreg_full          : std_logic;
  signal rx_shreg_empty         : std_logic;
  signal rx_in_packet           : std_logic;

  signal shift_data             : std_logic_vector(RX_DATA_WIDTH-1 downto 0);
  signal shift_sop_pos          : std_logic_vector(max(1,RX_SOP_POS_WIDTH)-1 downto 0);
  signal shift_eop_pos          : std_logic_vector(max(1,RX_EOP_POS_WIDTH)-1 downto 0);
  signal shift_sop              : std_logic;
  signal shift_eop              : std_logic;
  signal shift_flags            : std_logic_vector(1 downto 0);

  signal sop_array              : std_logic_vector(TX_BLOCKS downto 0);
  signal eop_array              : std_logic_vector(TX_BLOCKS downto 0);
  signal sop_array_fix          : std_logic_vector(TX_BLOCKS-1 downto 0);
  signal eop_array_fix          : std_logic_vector(TX_BLOCKS-1 downto 0);
  signal sop_in_array           : std_logic;
  signal eop_in_array           : std_logic;
  signal eop_in_array_addr      : std_logic_vector(log2(TX_BLOCKS)-1 downto 0);
begin
  -- basic shreg RX control
  RX_DST_RDY     <= not rx_shreg_full and not RESET;
  rx_shift_en    <= not rx_shreg_full and (RX_SRC_RDY or not rx_in_packet);
  rx_depth       <= conv_std_logic_vector(TX_BLOCKS-1,log2(TX_BLOCKS+1)) when rx_shreg_full='0' else conv_std_logic_vector(TX_BLOCKS,log2(TX_BLOCKS+1));
  rx_shreg_empty_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or (RX_SRC_RDY='1' or rx_in_packet='0') then
        rx_shreg_empty <= '0';
      elsif rx_shreg_full='0' and shreg_pop='1' and RX_SRC_RDY='0' then
        rx_shreg_empty <= '1';
      end if;
    end if;
  end process;
  rx_shreg_full_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' or (shreg_pop='1') then
        rx_shreg_full <= '0';
      elsif rx_shreg_empty='0' and shreg_pop='0' and (RX_SRC_RDY='1' or rx_in_packet='0') then
        rx_shreg_full <= '1';
      end if;
    end if;
  end process;
  rx_in_packet_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        rx_in_packet <= '0';
      elsif RX_SRC_RDY='1' and rx_shreg_full='0' then
        rx_in_packet <= rx_in_packet xor RX_SOP xor RX_EOP;
      end if;
    end if;
  end process;

  -- input shift registers (Serial-IN, Serial-OUT)
  data_shreg : entity work.SH_REG_BASE_DYNAMIC
    generic map (
      NUM_BITS   => TX_BLOCKS+1,
      DATA_WIDTH => RX_DATA_WIDTH
    ) port map (
      CLK        => CLK,
      DIN        => RX_DATA,
      CE         => rx_shift_en,
      ADDR       => rx_depth,
      DOUT       => shift_data
    );
  fake_sop_pos_shreg_gen : if RX_SOP_POS_WIDTH=0 generate
    shift_sop_pos <= "0";
  end generate;
  real_sop_pos_shreg_gen : if RX_SOP_POS_WIDTH>0 generate
    sop_pos_shreg : entity work.SH_REG_BASE_DYNAMIC
      generic map (
        NUM_BITS   => TX_BLOCKS+1,
        DATA_WIDTH => RX_SOP_POS_WIDTH
      ) port map (
        CLK        => CLK,
        DIN        => RX_SOP_POS,
        CE         => rx_shift_en,
        ADDR       => rx_depth,
        DOUT       => shift_sop_pos
      );
  end generate;
  fake_eop_pos_shreg_gen : if RX_EOP_POS_WIDTH=0 generate
    shift_eop_pos <= "0";
  end generate;
  real_eop_pos_shreg_gen : if RX_EOP_POS_WIDTH>0 generate
    eop_pos_shreg : entity work.SH_REG_BASE_DYNAMIC
      generic map (
        NUM_BITS   => TX_BLOCKS+1,
        DATA_WIDTH => RX_EOP_POS_WIDTH
      ) port map (
        CLK        => CLK,
        DIN        => RX_EOP_POS,
        CE         => rx_shift_en,
        ADDR       => rx_depth,
        DOUT       => shift_eop_pos
      );
  end generate;

  -- input shift registers (Serial-IN, Parallel-OUT)
  sop_shreg : entity work.sh_reg_sipo
    generic map (
      NUM_BITS    => TX_BLOCKS+1,
      INIT        => (TX_BLOCKS downto 0 => '0')
    ) port map (
      CLK      => CLK,
      RESET    => RESET,
      CE       => rx_shift_en,
      DI       => rx_sop_vld,
      PAR_DO   => sop_array
    );
  rx_sop_vld <= RX_SOP and RX_SRC_RDY;
  shift_sop  <= sop_array(TX_BLOCKS-1) when rx_shreg_full='0' else sop_array(TX_BLOCKS);
  eop_shreg : entity work.sh_reg_sipo
    generic map (
      NUM_BITS    => TX_BLOCKS+1,
      INIT        => (TX_BLOCKS downto 0 => '0')
    ) port map (
      CLK      => CLK,
      RESET    => RESET,
      CE       => rx_shift_en,
      DI       => rx_eop_vld,
      PAR_DO   => eop_array
    );
  rx_eop_vld <= RX_EOP and RX_SRC_RDY;
  shift_eop  <= eop_array(TX_BLOCKS-1) when rx_shreg_full='0' else eop_array(TX_BLOCKS);

-- -----------------------------------------------------------------------------

  -- cut out important data from sop and eop arrays
  sop_array_fix <= (sop_array(TX_BLOCKS-1) and rx_shreg_full) & sop_array(TX_BLOCKS-2 downto 0);
  eop_array_fix <= (eop_array(TX_BLOCKS-1) and rx_shreg_full) & eop_array(TX_BLOCKS-2 downto 0);
  tx_sop_addr   <= eop_in_array_addr when rx_shreg_full='1' else eop_in_array_addr+1;
  sop_array_proc : process(sop_array_fix,eop_array_fix)
    variable eo,so : std_logic;
  begin
    eo := '0';
    so := '0';
    for i in TX_BLOCKS-1 downto 0 loop
      eo := eo or eop_array_fix(i);
      so := so or (sop_array_fix(i) and not eo);
    end loop;
    sop_in_array <= so;
    eop_in_array <= eo;
  end process;
  last_eop_addr : entity work.GEN_ENC
    generic map (TX_BLOCKS)
    port map (eop_array_fix,eop_in_array_addr);

  -- output data registers
  tx_data_reg_gen : for i in 1 to TX_BLOCKS-1 generate
    tx_data_register : process (CLK)
    begin
      if CLK'event and CLK='1' then
        if tx_data_regs_ce(i)='1' then
          tx_data_regs(i) <= shift_data;
        end if;
      end if;
    end process;
  end generate;
  tx_data_register0 : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if tx_regs_wr='1' and aux_reg_vld='1' then
        tx_data_regs(0) <= aux_reg_data;
      elsif tx_data_regs_ce(0)='1' then
        tx_data_regs(0) <= shift_data;
      end if;
    end if;
  end process;
  tx_sop_register : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        tx_sop_reg <= '0';
      elsif tx_regs_wr='1' and (shift_sop='1' or aux_reg_vld='1') then
        tx_sop_reg <= '1';
      elsif tx_vld='1' and TX_DST_RDY='1' then
        tx_sop_reg <= '0';
      end if;
    end if;
  end process;
  tx_eop_register : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        tx_eop_reg <= '0';
      elsif tx_regs_wr='1' and shift_eop='1' then
        tx_eop_reg <= '1';
      elsif tx_vld='1' and TX_DST_RDY='1' then
        tx_eop_reg <= '0';
      end if;
    end if;
  end process;
  tx_sop_pos_register : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if tx_regs_wr='1' and aux_reg_vld='1' then
        tx_sop_pos_reg <= (tx_cnt'length-1 downto 0 => '0') & aux_reg_sop_pos;
      elsif tx_regs_wr='1' and shift_sop='1' and aux_reg_vld_now='0' then
        tx_sop_pos_reg <= tx_addr & shift_sop_pos;
      end if;
    end if;
  end process;
  tx_eop_pos_register : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if tx_regs_wr='1' and shift_eop='1' then
        tx_eop_pos_reg <= tx_cnt & shift_eop_pos;
      end if;
    end if;
  end process;
  tx_sop_actual <= (tx_sop_reg and not tx_vld) or aux_reg_vld;
  tx_eop_actual <= tx_eop_reg and not tx_vld;

  -- output interface connection
  tx_data_gen : for i in 0 to TX_BLOCKS-1 generate
    TX_DATA((i+1)*RX_DATA_WIDTH-1 downto RX_DATA_WIDTH*i) <= tx_data_regs(i);
  end generate;
  TX_EOP     <= tx_eop_reg;
  TX_SOP     <= tx_sop_reg;
  TX_EOP_POS <= tx_eop_pos_reg;
  TX_SOP_POS(TX_SOP_POS_WIDTH-1 downto TX_SOP_POS_WIDTH-TX_SOP_POS_WIDTH_REAL) <= tx_sop_pos_reg(tx_sop_pos_reg'length-1 downto tx_sop_pos_reg'length-TX_SOP_POS_WIDTH_REAL);
  tx_sop_pos_augment : if TX_SOP_POS_WIDTH>TX_SOP_POS_WIDTH_REAL generate
    TX_SOP_POS(TX_SOP_POS_WIDTH-TX_SOP_POS_WIDTH_REAL-1 downto 0) <= (others => '0');
  end generate;
  TX_SRC_RDY <= tx_vld;
  shreg_pop  <= (TX_DST_RDY or not tx_vld) and not rx_shreg_empty;

  -- Auxilliary registers
  aux_data_reg : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if tx_regs_wr='1' then
        aux_reg_data <= shift_data;
      end if;
    end if;
  end process;
  aux_sop_pos_reg : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if tx_regs_wr='1' then
        aux_reg_sop_pos <= shift_sop_pos;
      end if;
    end if;
  end process;
  aux_vld_reg : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if tx_regs_wr='1' then
        aux_reg_vld <= aux_reg_vld_now;
      end if;
    end if;
  end process;

  -- state registers and signals of tx
  tx_in_packet_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        tx_in_packet <= '0';
      elsif shreg_pop='1' then
        tx_in_packet <= tx_in_packet xor shift_sop xor shift_eop;
      end if;
    end if;
  end process;
  tx_vld_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        tx_vld <= '0';
      elsif shreg_pop='1' then
        tx_vld <= export_now;
      elsif TX_DST_RDY='1' then
        tx_vld <= '0';
      end if;
    end if;
  end process;
  tx_cnt_reg : process (CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        tx_cnt <= (others => '0');
      elsif shreg_pop='1' then
        if aux_reg_vld_now='1' then
          tx_cnt <= conv_std_logic_vector(1,tx_cnt'length);
        elsif export_now='1' then
          tx_cnt <= (others => '0');
        elsif tx_regs_wr='1' then
          tx_cnt <= tx_addr+1;
        end if;
      end if;
    end if;
  end process;
  tx_addr      <= tx_cnt when tx_cnt_en='1' or eop_in_array='0' or tx_cnt>tx_sop_addr else tx_sop_addr;
  tx_last_word <= '1' when tx_addr=conv_std_logic_vector(TX_BLOCKS-1,tx_addr'length) else '0';

  -- action select based on actual state and new word
  shift_flags <= shift_sop & shift_eop;
  action_select : process (shift_flags,tx_in_packet,sop_in_array,tx_sop_actual,tx_last_word,shreg_pop,tx_eop_actual)
  begin
    tx_regs_wr      <= '0';
    export_now      <= '0';
    aux_reg_vld_now <= '0';
    tx_cnt_en       <= '1';
    case shift_flags is
      when "00" =>
        -- nic (mimo paket) - ignorujem nic sa nedeje
        if tx_in_packet='1' then
          -- nic (v pakete)   - pridam do vystupu slovo a mozno exportujem
          tx_regs_wr <= shreg_pop;
          export_now <= tx_last_word;
        end if;
      when "01" =>
        if tx_sop_actual='1' then
          -- Eop (Sop uz je)  - vlozim a ukoncim aktualne slovo
          tx_regs_wr <= shreg_pop;
          export_now <= '1';
        else
          -- Eop (Sop nie je) - vlozim a ukoncim podla pritomnosti cisto Sop (OR v Sop and not Eop array)
          tx_regs_wr <= shreg_pop;
          export_now <= not sop_in_array or tx_last_word;
        end if;
      when "10" =>
        if tx_eop_actual='1' then
          -- Sop (Eop uz je)  - najdem Eop a zarovnam to vhodne (find first 1 v Eop array)
          tx_regs_wr <= shreg_pop;
          export_now <= tx_last_word;
          tx_cnt_en  <= '0';
        else
          -- Sop (Eop nie je) - zarovnam na zaciatok a vlozim
          tx_regs_wr <= shreg_pop;
        end if;
      when "11" =>
        if tx_in_packet='1' then
          if tx_sop_actual='1' then
            -- Eop Sop (Sop uz je)  - vlozim Eop a ukoncim aktualne slovo a zaroven vlozim Sop do noveho slova => rozdelit Sop a Eop cez hranicu slova
            tx_regs_wr      <= shreg_pop;
            export_now      <= '1';
            aux_reg_vld_now <= '1';
          else
            -- Eop Sop (Sop nie je) - najdem Eop a zarovnam Sop vhodne (find first 1 v Eop array) => mozno rozdelit Sop a Eop v ramci slova
            tx_regs_wr <= shreg_pop;
            tx_cnt_en  <= '0';
            export_now <= tx_last_word;
          end if;
        else
          -- Sop Eop (Eop uz je)  - NEMOZE NASTAT!!!
          -- Sop Eop (Eop nie je) - vlozim na zaciatok a ukoncim aktualne slovo
          tx_regs_wr <= shreg_pop;
          export_now <= '1';
        end if;
      when others => null;
    end case;
  end process;

  -- clock enable for tx registers
  chip_select1 : entity work.dec1fn
    generic map (TX_BLOCKS)
    port map (tx_addr,tx_data_regs_cs1);
  chip_select2 : entity work.dec1fn
    generic map (TX_BLOCKS)
    port map (tx_cnt,tx_data_regs_cs2);
  tx_data_regs_ce <= (tx_data_regs_cs1 or tx_data_regs_cs2) and (TX_BLOCKS-1 downto 0 => tx_regs_wr);
end architecture;
