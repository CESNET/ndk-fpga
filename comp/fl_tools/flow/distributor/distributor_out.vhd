-- distributor_out.vhd: FrameLink switch full architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Entity declaration
-- ----------------------------------------------------------------------------
entity fl_distributor_out is
   generic (
      -- count of output interfaces, MUST be 2^n and greater than one
      INTERFACES_COUNT : integer := 2;
      DATA_WIDTH : integer := 1
   );
   port (
      CLK          : in std_logic;

      -- Write interface
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;

      -- Read interfaces
      TX_DATA     : out std_logic_vector(INTERFACES_COUNT*DATA_WIDTH-1 downto 0);
      TX_REM      : out std_logic_vector(INTERFACES_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_DST_RDY_N: in  std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_SOP_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_EOP_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_SOF_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_EOF_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);

      TX_INTERFACE : in std_logic_vector(log2(INTERFACES_COUNT)-1 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl_distributor_out is

   -- width of the RX_REM signal
   constant REM_WIDTH : integer := log2(DATA_WIDTH/8);

begin

   -- connections to TX interfaces:
   gen_tx_connections:
   for i in 0 to INTERFACES_COUNT-1 generate
      TX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH) <= RX_DATA;
      TX_REM((i+1)*REM_WIDTH-1 downto i*REM_WIDTH) <= RX_REM;
      TX_SOF_N(i) <= RX_SOF_N;
      TX_EOF_N(i) <= RX_EOF_N;
      TX_SOP_N(i) <= RX_SOP_N;
      TX_EOP_N(i) <= RX_EOP_N;

      TX_SRC_RDY_N(i) <= RX_SRC_RDY_N when i = conv_integer(unsigned(TX_INTERFACE)) else '1';

      process(CLK, TX_DST_RDY_N, TX_INTERFACE)
         variable tx_rdy_n : std_logic;
      begin
         tx_rdy_n := '0';

         for i in 0 to INTERFACES_COUNT - 1 loop
            if i = conv_integer(unsigned(TX_INTERFACE)) then
               tx_rdy_n := tx_rdy_n or TX_DST_RDY_N(i);
            end if;
         end loop;

         RX_DST_RDY_N <= tx_rdy_n;
      end process;
   end generate;

end architecture;


