-- distributor_ifsel_word0.vhd: FrameLink distributor full architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture inum_in_word0 of fl_distributor_ifsel is

   constant INUM_WIDTH : integer := log2(INTERFACES_COUNT);
   constant WORD_INUM_OFFSET : integer := INUM_OFFSET mod DATA_WIDTH;

   -- width of the RX_REM signal
   constant REM_WIDTH : integer := log2(DATA_WIDTH/8);

   signal reg_inum         : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal reg_inum_ce      : std_logic;
   signal reg_inum_set     : std_logic_vector(INUM_WIDTH-1 downto 0);

begin

      inum_extract : entity work.inum_extract
      generic map (
         DATA_WIDTH => DATA_WIDTH,
         INUM_WIDTH => INUM_WIDTH,
         INUM_OFFSET => INUM_OFFSET,
         MASK       => MASK
      )
      port map (
         RX_DATA => RX_DATA,
         RX_REM => RX_REM,
         RX_EOP_N => RX_EOP_N,
         LAST_INUM => reg_inum,
         -- the INUM always must come, it is in the first incoming word
         INUM => reg_inum_set
      );

      -- save the INUM when the right offset was reached or RX_EOF comes
      reg_inum_ce <= not(RX_SOF_N) and not(RX_SRC_RDY_N);

      -- select tx interface
      TX_INTERFACE <= reg_inum_set when RX_SOF_N = '0' and RX_SRC_RDY_N = '0' else
                      reg_inum;

      -- enable the selected tx interface
      TX_SRC_RDY_N <= RX_SRC_RDY_N;
      RX_DST_RDY_N <= TX_DST_RDY_N;

      -- register to store the INUM
      register_inum : process(CLK, RESET, reg_inum_ce, reg_inum_set)
      begin
         if CLK = '1' and CLK'event then
            if RESET = '1' then
               reg_inum <= conv_std_logic_vector(DEFAULT_INTERFACE, reg_inum_set'length);

            elsif reg_inum_ce = '1' then
               reg_inum <= reg_inum_set;

            end if;
         end if;
      end process;

      TX_DATA <= RX_DATA;
      TX_REM  <= RX_REM;
      TX_SOP_N <= RX_SOP_N;
      TX_EOP_N <= RX_EOP_N;
      TX_SOF_N <= RX_SOF_N;
      TX_EOF_N <= RX_EOF_N;

end architecture;

