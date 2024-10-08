-- cmp_top.vhd: Top-level implementation of generic comparator
-- Copyright (C) 2016 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.std_logic_misc.all;

library work;
use work.math_pack.all;
-- use work.type_pack.all;


entity GEN_CMP is
  generic(
    DATA_WIDTH  : integer := 96;
    IS_DSP      : boolean := false;
    REG_IN      : boolean := false; -- strongly recommended to set true when IS_DSP is true
    REG_OUT     : boolean := false; -- strongly recommended to set true when IS_DSP is true
    COMPARE_EQ  : boolean := true; -- EQ output (A == B) will be computed (disable if not used to save resources)
    COMPARE_CMP : boolean := true; -- CMP output (A [CMP_TYPE] B) will be computed (disable if not used to save resources)
    CMP_TYPE    : string := "<" -- CMP operation: "<", ">", "<=", ">=", "=<", "=>"
  );
  port(
    CLK         : in  std_logic;
    RESET       : in  std_logic;
    CE_IN       : in  std_logic := '1';
    CE_OUT      : in  std_logic := '1';
    A           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    B           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    EQ          : out std_logic;
    CMP         : out std_logic
  );
end entity;



architecture full of GEN_CMP is
begin

  dsp_gen : if IS_DSP generate
    signal p : std_logic_vector(1 downto 0);
    signal as, bs : std_logic_vector(DATA_WIDTH-1 downto 0);
  begin

    cmp_core : entity work.CMP_DSP
    generic map (
      DATA_WIDTH  => DATA_WIDTH,
      REG_IN      => tsel(REG_IN, 1, 0),
      REG_OUT     => tsel(REG_OUT, 1, 0)
    ) port map (
      CLK         => CLK,
      RESET       => RESET,
      A           => as,
      B           => bs,
      CE_IN       => CE_IN,
      CE_OUT      => CE_OUT,
      P           => p
    );
    EQ <= p(0);

    lss_gen : if CMP_TYPE = "<" generate
      as <= B;
      bs <= A;
      CMP <= not p(1);
    end generate;
    leq_gen : if CMP_TYPE = "<=" or CMP_TYPE = "=<" generate
      as <= A;
      bs <= B;
      CMP <= p(1);
    end generate;
    gtr_gen : if CMP_TYPE = ">" generate
      as <= A;
      bs <= B;
      CMP <= not p(1);
    end generate;
    geq_gen : if CMP_TYPE = ">=" or CMP_TYPE = "=>" generate
      as <= B;
      bs <= A;
      CMP <= p(1);
    end generate;

  end generate;


  logic_gen : if not IS_DSP generate
    signal ar, br : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal eqr, cmpr : std_logic := '0';
  begin

    inreg_gen : if REG_IN generate
      reg : process(CLK)
      begin
        if CLK'event and CLK='1' then
          if CE_IN='1' then
            ar <= A;
            br <= B;
          end if;
        end if;
      end process;
    end generate;
    no_inreg_gen : if not REG_IN generate
      ar <= A;
      br <= B;
    end generate;

    eq_gen : if COMPARE_EQ generate
      eqr <= '1' when ar = br else '0';
    end generate;

    cmp_gen : if COMPARE_CMP generate
      lss_gen : if CMP_TYPE = "<" generate
        cmpr <= '1' when ar < br else '0';
      end generate;
      leq_gen : if CMP_TYPE = "<=" or CMP_TYPE = "=<" generate
        cmpr <= '1' when ar <= br else '0';
      end generate;
      gtr_gen : if CMP_TYPE = ">" generate
        cmpr <= '1' when ar > br else '0';
      end generate;
      geq_gen : if CMP_TYPE = ">=" or CMP_TYPE = "=>" generate
        cmpr <= '1' when ar >= br else '0';
      end generate;
    end generate;

    outreg_gen : if REG_OUT generate
      reg : process(CLK)
      begin
        if CLK'event and CLK='1' then
          if CE_OUT='1' then
            EQ <= eqr;
            CMP <= cmpr;
          end if;
        end if;
      end process;
    end generate;
    no_outreg_gen : if not REG_OUT generate
      EQ <= eqr;
      CMP <= cmpr;
    end generate;

  end generate;

end architecture;
