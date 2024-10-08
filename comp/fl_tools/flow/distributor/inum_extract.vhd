-- inum_extract.vhd: Extracts interface number from RX_DATA.
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
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity inum_extract is
   generic (
      DATA_WIDTH : integer := 32;
      INUM_WIDTH : integer := 2;
      INUM_OFFSET : integer := 0;
      MASK       : boolean := false -- true -> frame contains mask, not number
   );
   port (
      signal RX_DATA : in std_logic_vector(DATA_WIDTH-1 downto 0);
      signal RX_REM : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      signal RX_EOP_N : in std_logic;
      signal LAST_INUM : in std_logic_vector(INUM_WIDTH-1 downto 0);
      signal INUM : out std_logic_vector(INUM_WIDTH-1 downto 0)
   );
end entity inum_extract;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of inum_extract is

   constant DATA_SIZE : integer := DATA_WIDTH / 8;
   constant INUM_LAST_BYTE : integer := (INUM_OFFSET / 8) mod DATA_SIZE;

   signal mask_decoded : std_logic_vector(INUM_WIDTH-1 downto 0);
   signal inum_int     : std_logic_vector(INUM_WIDTH-1 downto 0);

begin

   INUM <= inum_int when (INUM_LAST_BYTE <= RX_REM or RX_EOP_N = '1') else
           LAST_INUM;

   -- Assign decoded mask
   mask_gen : if MASK generate
      inum_int <= mask_decoded;
   end generate;
   -- Assign direct data
   nmask_gen : if not MASK generate
      inum_int <= RX_DATA((INUM_OFFSET mod DATA_WIDTH) + INUM_WIDTH - 1 downto (INUM_OFFSET mod DATA_WIDTH));
   end generate;

   -- Convert mask to interface number
   mask_decode : entity work.dec1fn2b
   generic map(
      ITEMS    => 2**INUM_WIDTH
   )
   port map(
      DI       => RX_DATA((INUM_OFFSET mod DATA_WIDTH) + 2**INUM_WIDTH - 1 downto (INUM_OFFSET mod DATA_WIDTH)),
      ENABLE   => '1',
      ADDR     => mask_decoded
   );

end architecture;

