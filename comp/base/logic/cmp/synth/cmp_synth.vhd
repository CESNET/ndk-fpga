-- cmp_synth.vhd: Top-level for synthesis
-- Copyright (C) 2016 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;



entity CMP_SYNTH is
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
    A           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    B           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    EQ          : out std_logic;
    CMP         : out std_logic
  );
end entity;



architecture full of CMP_SYNTH is

  signal ar,br : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal eqr, cmpr, resetr : std_logic;

begin

  uut : entity work.GEN_CMP
  generic map (
    DATA_WIDTH  => DATA_WIDTH,
    IS_DSP      => IS_DSP,
    REG_IN      => REG_IN,
    REG_OUT     => REG_OUT,
    COMPARE_EQ  => COMPARE_EQ,
    COMPARE_CMP => COMPARE_CMP,
    CMP_TYPE    => CMP_TYPE
  ) port map (
    CLK         => CLK,
    RESET       => resetr,
    A           => ar,
    B           => br,
    EQ          => eqr,
    CMP         => cmpr
  );

  reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      resetr <= RESET;
      ar <= A;
      br <= B;
      EQ <= eqr;
      CMP <= cmpr;
    end if;
  end process;

end architecture;
