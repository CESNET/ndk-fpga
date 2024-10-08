-- slr_crossing_src.vhd: Special pipe component to cross between super logic regions (slow wire) - source part.
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity SLR_CROSSING_SRC is
  generic(
    DATA_WIDTH      : integer := 64
  );
  port(
    CLK              : in std_logic;
    RESET            : in std_logic;
    IN_DATA          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    IN_SRC_RDY       : in  std_logic;
    IN_DST_RDY       : out std_logic;
    CROSSING_DATA    : out std_logic_vector(DATA_WIDTH downto 0);
    CROSSING_DST_RDY : in  std_logic
  );
end entity;



library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

architecture full of SLR_CROSSING_SRC is
  signal data    : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal src_rdy : std_logic;
  signal dst_rdy : std_logic;
  attribute keep : string;
  attribute keep of dst_rdy : signal is "true";
begin
  data_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      data <= IN_DATA;
    end if;
  end process;

  src_rdy_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET = '1' then
        src_rdy <= '0';
      else
        src_rdy <= IN_SRC_RDY;
      end if;
    end if;
  end process;

  dst_rdy_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET = '1' then
        dst_rdy <= '0';
      else
        dst_rdy <= CROSSING_DST_RDY;
      end if;
    end if;
  end process;

  CROSSING_DATA <= data & src_rdy;
  IN_DST_RDY    <= dst_rdy;
end architecture;
