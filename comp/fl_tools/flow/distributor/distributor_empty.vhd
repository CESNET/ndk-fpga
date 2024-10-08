-- fl_distributor_empty.vhd: FrameLink 1-4 switch empty architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--


library IEEE;
use IEEE.std_logic_1164.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture empty of fl_distributor is

   constant REM_WIDTH : integer := log2(DATA_WIDTH/8);

   signal empty_sig :
      std_logic_vector(7 + DATA_WIDTH + REM_WIDTH - 1 downto 0);

   signal empty_tx :
      std_logic_vector(INTERFACES_COUNT-1 downto 0);

begin

   assert 2 ** log2(INTERFACES_COUNT) = INTERFACES_COUNT and INTERFACES_COUNT > 1
      report "Invalid INTERFACES_COUNT" severity failure;

   assert DEFAULT_INTERFACE >= 0 and DEFAULT_INTERFACE < INTERFACES_COUNT
      report "Invalid DEFAULT_INTERFACE - out of range" severity failure;

   empty_sig <=

      CLK               &        --    1
      RESET             &        --    1
      RX_DATA           &        --    DATA_WIDTH
      RX_REM            &        --    log2(DATA_WIDTH/8)
      RX_SRC_RDY_N      &        --    1
      RX_SOP_N          &        --    1
      RX_EOP_N          &        --    1
      RX_SOF_N          &        --    1
      RX_EOF_N;                  --    1
      -- ----------------------------------------------------
                                 --   7 + FL_DATA_WIDTH + log2(FL_DATA_WIDTH/8)


      gen_if_connections: for i in 0 to INTERFACES_COUNT-1 generate
         TX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
                           <= (others => 'Z');
         TX_REM((i+1)*REM_WIDTH-1 downto i*REM_WIDTH)
                           <= (others => 'Z');
         TX_SOP_N(i)       <= 'Z';
         TX_SOF_N(i)       <= 'Z';
         TX_EOP_N(i)       <= 'Z';
         TX_EOF_N(i)       <= 'Z';
         TX_SRC_RDY_N(i)   <= 'Z';
         empty_tx(i)       <= TX_DST_RDY_N(i);
      end generate;

end architecture empty;

