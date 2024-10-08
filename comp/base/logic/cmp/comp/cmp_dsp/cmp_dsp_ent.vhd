-- cmp_dsp_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;

entity CMP_DSP is
    generic (
       DATA_WIDTH  : integer := 48;
       --! Input pipeline registers
       REG_IN      : integer := 0;
       --! Output pipeline register
       REG_OUT     : integer := 1
    );
    port (
       --! Clock input
       CLK         : in  std_logic;
       --! Reset input
       RESET       : in  std_logic;
       --! Data input
       A           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
       --! Data input
       B           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
       --! Clock enable for input pipeline registers
       CE_IN       : in  std_logic;
       --! Clock enable for output pipeline registers
       CE_OUT      : in  std_logic;
       --!
       --! Latency = REG_IN + REG_OUT
       --! Data output
       --! "00" when  A > B
       --! "10" when  A < B
       --! "11" when  A = B
       --! "01" undefined
       P           : out std_logic_vector(1 downto 0)
    );
 end CMP_DSP;
