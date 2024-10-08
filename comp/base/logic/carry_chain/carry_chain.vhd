-- carry_chain.vhd: Generic structural implementation of carry chain
-- Copyright (C) 2017 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

entity CARRY_CHAIN is
  generic(
    CARRY_WIDTH    : integer := 12;
    DEVICE         : string := "7SERIES" --! "VIRTEX6", "7SERIES", "ULTRASCALE", "none" (behavioral)
  );
  port(
    -- Initial input carry
    CI : in std_logic;
    -- Data input (AX/BX/CX/DX or O5 from LUT)
    DI : in std_logic_vector(CARRY_WIDTH-1 downto 0);
    -- Carry selection input (O6 from LUT)
    S  : in std_logic_vector(CARRY_WIDTH-1 downto 0);
    -- Carry output
    --     CO(-1) = CI
    --     CO(i) = CO(i-1) when S(i) = '1' else DI(i);
    CO : out std_logic_vector(CARRY_WIDTH-1 downto 0);
    -- Data output
    --     DO(i) = CO(i-1) xor S(i)
    DO : out std_logic_vector(CARRY_WIDTH-1 downto 0)
  );
end entity;



architecture structural of CARRY_CHAIN is

   -- CARRY4 declaration as synthesis hack due to Quartus
   component CARRY4
   port (
      CO     : out std_logic_vector(4-1 downto 0);
      O      : out std_logic_vector(4-1 downto 0);
      CI     : in  std_logic;
      CYINIT : in  std_logic;
      DI     : in  std_logic_vector(4-1 downto 0);
      S      : in  std_logic_vector(4-1 downto 0)
   );
   end component;

begin

  behavioral_gen : if DEVICE /= "7SERIES" and DEVICE /= "VIRTEX6" and DEVICE /= "ULTRASCALE" generate
  begin
    carry_i : process(CI, DI, S)
      variable sig_co : std_logic_vector(CARRY_WIDTH downto 0) := (others => '0');
    begin
      sig_co(0) := CI;
      for i in 0 to CARRY_WIDTH-1 loop
        if S(i)='1' then
          sig_co(i+1) := sig_co(i);
        else
          sig_co(i+1) := DI(i);
        end if;
        DO(i) <= sig_co(i) xor S(i);
      end loop;
      CO <= sig_co(CARRY_WIDTH downto 1);
    end process;
  end generate;


  v6_v7_gen : if DEVICE = "7SERIES" or DEVICE = "VIRTEX6" or DEVICE = "ULTRASCALE" generate
    constant CARRY_COUNT : integer := (CARRY_WIDTH-1)/4 + 1;
    signal sig_do, sig_di, sig_s, sig_co : std_logic_vector(CARRY_COUNT*4-1 downto 0);
  begin
    first_carry_i : CARRY4
    port map(
      CO     => sig_co(4*(0+1)-1 downto 4*0),
      O      => sig_do(4*(0+1)-1 downto 4*0),
      CI     => '0',
      CYINIT => CI,
      DI     => sig_di(4*(0+1)-1 downto 4*0),
      S      => sig_s(4*(0+1)-1 downto 4*0)
    );
    carry_gen : for i in 1 to CARRY_COUNT-1 generate
      carry_i : CARRY4
      port map(
        CO     => sig_co(4*(i+1)-1 downto 4*i),
        O      => sig_do(4*(i+1)-1 downto 4*i),
        CI     => sig_co(4*i-1),
        CYINIT => '0',
        DI     => sig_di(4*(i+1)-1 downto 4*i),
        S      => sig_s(4*(i+1)-1 downto 4*i)
      );
    end generate;
    sig_di(CARRY_WIDTH-1 downto 0) <= DI;
    sig_s(CARRY_WIDTH-1 downto 0) <= S;
    CO <= sig_co(CARRY_WIDTH-1 downto 0);
    DO <= sig_do(CARRY_WIDTH-1 downto 0);
  end generate;

end architecture;

