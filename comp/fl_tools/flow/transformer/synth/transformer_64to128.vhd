-- transformer_64to128.vhd: Instance of FrameLink Transformer component.
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
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
entity FL_TRANSFORMER_64TO128 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- RX interface
      RX_DATA        : in  std_logic_vector(63 downto 0);
      RX_DREM        : in  std_logic_vector(2 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX interface
      TX_DATA        : out std_logic_vector(127 downto 0);
      TX_DREM        : out std_logic_vector(3 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end entity FL_TRANSFORMER_64TO128;

architecture FULL of FL_TRANSFORMER_64TO128 is

begin

   transformer_i : entity work.fl_transformer
   generic map(
      RX_DATA_WIDTH  => 64,
      TX_DATA_WIDTH  => 128
   )
   port map(
       CLK            => CLK,
       RESET          => RESET,
       --
       RX_DATA        => RX_DATA,
       RX_REM         => RX_DREM,
       RX_SOF_N       => RX_SOF_N,
       RX_EOF_N       => RX_EOF_N,
       RX_SOP_N       => RX_SOP_N,
       RX_EOP_N       => RX_EOP_N,
       RX_SRC_RDY_N   => RX_SRC_RDY_N,
       RX_DST_RDY_N   => RX_DST_RDY_N,
       --
       TX_DATA        => TX_DATA,
       TX_REM         => TX_DREM,
       TX_SOF_N       => TX_SOF_N,
       TX_EOF_N       => TX_EOF_N,
       TX_SOP_N       => TX_SOP_N,
       TX_EOP_N       => TX_EOP_N,
       TX_SRC_RDY_N   => TX_SRC_RDY_N,
       TX_DST_RDY_N   => TX_DST_RDY_N
   );

end architecture FULL;
