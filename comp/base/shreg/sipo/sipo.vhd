-- sipo.vhd: Shift register with Serial Input and Parallel Output (SIPO)
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;

entity sh_reg_sipo is
  generic (
    NUM_BITS    : integer := 16;
    INIT        : std_logic_vector := X"0000"
  );
  port(
    CLK         : in std_logic;
    RESET       : in std_logic;
    CE          : in std_logic;
    DI          : in std_logic;
    PAR_DO      : out std_logic_vector(NUM_BITS-1 downto 0)
  );
end entity;

architecture arch of sh_reg_sipo is
  signal tmp: std_logic_vector(NUM_BITS-1 downto 0);
begin
  sipo_shreg : process(CLK)
  begin
    if (CLK'event and CLK='1') then
      if (RESET='1') then
        tmp <= INIT;
      elsif (CE='1') then
        tmp <= tmp(NUM_BITS-2 downto 0)& DI;
      end if;
    end if;
  end process;
  PAR_DO <= tmp;
end architecture;
