--
-- lb_endpoint_read_shr.vhd: Internal Bus ADC Shift Register
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_READ_SHR is
   generic (
      DATA_WIDTH       : integer:=64
      );
   port(
      -- Common Interface
      CLK             : in  std_logic;
      RESET           : in  std_logic;
      -- Input Interface
      RD_DATA_IN      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SRC_RDY_IN   : in  std_logic;
      RD_DST_RDY_IN   : out std_logic;
      -- Output Interface
      RD_DATA_OUT     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SRC_RDY_OUT  : out std_logic;
      RD_DST_RDY_OUT  : in  std_logic
      );
end entity IB_ENDPOINT_READ_SHR;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_READ_SHR_ARCH of IB_ENDPOINT_READ_SHR is

-- Signal Declaration ---------------------------------------------------------
   signal full            : std_logic;
   signal empty           : std_logic;

begin
RD_DST_RDY_IN  <= not full;
RD_SRC_RDY_OUT <= not empty;

sh_fifo_u : entity work.sh_fifo
   generic map (
      FIFO_WIDTH  => 64,
      FIFO_DEPTH  => 16,
      USE_INREG   => false,
      USE_OUTREG  => true
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      -- write interface
      DIN         => RD_DATA_IN,
      WE          => RD_SRC_RDY_IN,
      FULL        => full,

      -- read interface
      DOUT       => RD_DATA_OUT,
      RE         => RD_DST_RDY_OUT,
      EMPTY      => empty
   );
end architecture IB_ENDPOINT_READ_SHR_ARCH;

