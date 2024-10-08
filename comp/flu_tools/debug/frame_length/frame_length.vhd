-- frame_length.vhd: FrameLinkUnaligned frame length measurement
-- Copyright (C) 2018 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;



entity FLU_FRAME_LENGTH is
  generic(
    DATA_WIDTH     : integer:= 256;
    SOP_POS_WIDTH  : integer:= 2;
    USE_INREG      : boolean:= true;
    USE_OUTREG     : boolean:= false
  );
  port(
    CLK           : in std_logic;
    RESET         : in std_logic;

    RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    RX_EOP_POS    : in std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
    RX_SOP        : in std_logic;
    RX_EOP        : in std_logic;
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : in std_logic;

    LENGTH        : out std_logic_vector(16-1 downto 0);
    LENGTH_VLD    : out std_logic
  );
end entity;



architecture arch of FLU_FRAME_LENGTH is
  constant EOP_POS_WIDTH : integer := max(1,log2(DATA_WIDTH/8));
  signal spos, epos : std_logic_vector(EOP_POS_WIDTH-1 downto 0) := (others => '0');
  signal valid_word, sop, eop : std_logic;
  signal out_sel, out_len_vld : std_logic;
  signal out_len, reg_len : std_logic_vector(16-1 downto 0);
begin

  -- Input register
  inreg_gen: if USE_INREG generate
    inreg: process(CLK)
    begin
      if CLK'event and CLK='1' then
        if RESET='1' then
          valid_word <= '0';
        else
          valid_word <= RX_SRC_RDY and RX_DST_RDY;
        end if;
        spos(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH) <= RX_SOP_POS;
        epos <= RX_EOP_POS;
        sop <= RX_SOP;
        eop <= RX_EOP;
      end if;
    end process;
  end generate;

  no_inreg_gen: if not USE_INREG generate
    spos(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH) <= RX_SOP_POS;
    epos <= RX_EOP_POS;
    valid_word <= RX_SRC_RDY and RX_DST_RDY;
    sop <= RX_SOP;
    eop <= RX_EOP;
  end generate;


  -- Functional logic
  accumulation_reg: process(CLK)
  begin
    if CLK'event and CLK='1' then
      if valid_word='1' then
        if sop='1' then
          reg_len <= conv_std_logic_vector(DATA_WIDTH/8,16) - spos;
        else
          reg_len <= conv_std_logic_vector(DATA_WIDTH/8,16) + reg_len;
        end if;
      end if;
    end if;
  end process;

  out_sel <= '0' when sop='1' and eop='1' and spos <= epos else '1';
  out_len <= ((16-1 downto EOP_POS_WIDTH => '0')&epos)+1+reg_len when out_sel='1' else ((16-1 downto EOP_POS_WIDTH => '0')&epos)+1-((16-1 downto EOP_POS_WIDTH => '0')&spos);
  out_len_vld <= eop and valid_word;


  -- Output register
  outreg_gen: if USE_OUTREG generate
    outreg: process(CLK)
    begin
      if CLK'event and CLK='1' then
        if RESET='1' then
          LENGTH_VLD <= '0';
        else
          LENGTH_VLD <= out_len_vld;
        end if;
        LENGTH <= out_len;
      end if;
    end process;
  end generate;

  no_outreg_gen: if not USE_OUTREG generate
    LENGTH <= out_len;
    LENGTH_VLD <= out_len_vld;
  end generate;

end architecture;

