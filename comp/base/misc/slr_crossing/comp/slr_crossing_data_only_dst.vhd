-- slr_crossing_data_only_dst.vhd: Special pipe component to cross between super logic regions (slow wire) - destination part.
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity SLR_CROSSING_DATA_ONLY_DST is
  generic(
    DATA_WIDTH      : integer := 64
  );
  port(
    CLK              : in std_logic;
    RESET            : in std_logic;
    CROSSING_DATA    : in std_logic_vector(DATA_WIDTH downto 0);
    OUT_DATA         : out std_logic_vector(DATA_WIDTH-1 downto 0);
    OUT_SRC_RDY      : out std_logic
  );
end entity;



library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

architecture full of SLR_CROSSING_DATA_ONLY_DST is
  signal data       : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal src_rdy    : std_logic;
  attribute shreg_extract : string;
  attribute shreg_extract of data : signal is "no";
  attribute shreg_extract of src_rdy : signal is "no";
begin
  data_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      data <= CROSSING_DATA(DATA_WIDTH downto 1);
    end if;
  end process;

  src_rdy_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET = '1' then
        src_rdy <= '0';
      else
        src_rdy <= CROSSING_DATA(0);
      end if;
    end if;
  end process;

  OUT_DATA         <= data;
  OUT_SRC_RDY      <= src_rdy;
end architecture;
