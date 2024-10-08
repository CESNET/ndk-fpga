-- lb_endpoint_norec.vhd: Local Bus End Point Component without records
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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

use work.lb_pkg.all; -- Local Bus package
use work.math_pack.all; -- Math Pack
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ENDPOINT_NOREC is
   generic(
      BASE_ADDR        : std_logic_vector(31 downto 0):= X"00000000"; -- Must be N*LIMIT
      LIMIT            : std_logic_vector(31 downto 0):= X"00000800";
      FREQUENCY        : integer:= 100;
      BUFFER_EN        : boolean:= false
   );
   port(
      -- Common Interface
      RESET         : in std_logic;

      -- Local Bus Interface
      LB_CLK        : in std_logic;
      LB_DWR        : in std_logic_vector(15 downto 0);
      LB_BE         : in std_logic_vector(1 downto 0);
      LB_ADS_N      : in std_logic;
      LB_RD_N       : in std_logic;
      LB_WR_N       : in std_logic;
      LB_DRD        : out std_logic_vector(15 downto 0);
      LB_RDY_N      : out std_logic;
      LB_ERR_N      : out std_logic;
      LB_ABORT_N    : in  std_logic;

      -- User Component Interface
      CLK           : in  std_logic;
      MI32_DWR      : out std_logic_vector(31 downto 0);           -- Input Data
      MI32_ADDR     : out std_logic_vector(31 downto 0);           -- Address
      MI32_RD       : out std_logic;                               -- Read Request
      MI32_WR       : out std_logic;                               -- Write Request
      MI32_BE       : out std_logic_vector(3  downto 0);           -- Byte Enable
      MI32_DRD      : in  std_logic_vector(31 downto 0);           -- Output Data
      MI32_ARDY     : in  std_logic;                               -- Address Ready
      MI32_DRDY     : in  std_logic                                -- Data Ready
  );
end entity LB_ENDPOINT_NOREC;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ENDPOINT_NOREC_ARCH of LB_ENDPOINT_NOREC is

   signal reset_pipe : std_logic;
   attribute equivalent_register_removal : string;
   attribute equivalent_register_removal of reset_pipe : signal is "no";

begin

assert (FREQUENCY = LOCAL_BUS_FREQUENCY) or (FREQUENCY = LOCAL_BUS_FREQUENCY/2)
report "lb_endpoint: Unsupported FREQUENCY" severity failure;

assert (to_integer(unsigned(BASE_ADDR)) rem to_integer(unsigned(LIMIT))) = 0
report "lb_endpoint BASE_ADDR must be N * LIMIT" severity failure;

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(RESET, LB_CLK)
   begin
      if LB_CLK'event and LB_CLK = '1' then
         reset_pipe  <= RESET;
      end if;
end process;

X50MHZ_U : if (FREQUENCY = (LOCAL_BUS_FREQUENCY/2)) generate

   LB_ENDPOINT_U : entity work.LB_ENDPOINT_50
   generic map(
      BASE_ADDR  => BASE_ADDR,
      LIMIT      => LIMIT,
      BUFFER_EN  => BUFFER_EN
   )
   port map(
      -- Common Interface
      RESET      => reset_pipe,

      -- Local Bus Interface
      LB_CLK      => LB_CLK,
      LB_DWR      => LB_DWR,
      LB_BE       => LB_BE,
      LB_ADS_N    => LB_ADS_N,
      LB_RD_N     => LB_RD_N,
      LB_WR_N     => LB_WR_N,
      LB_DRD      => LB_DRD,
      LB_RDY_N    => LB_RDY_N,
      LB_ERR_N    => LB_ERR_N,
      LB_ABORT_N  => LB_ABORT_N,

      -- User Component Interface
      CLK         => CLK,
      MI32_DWR    => MI32_DWR,
      MI32_ADDR   => MI32_ADDR,
      MI32_RD     => MI32_RD,
      MI32_WR     => MI32_WR,
      MI32_BE     => MI32_BE,
      MI32_DRD    => MI32_DRD,
      MI32_ARDY   => MI32_ARDY,
      MI32_DRDY   => MI32_DRDY
   );
end generate;


X100MHZ_U: if (FREQUENCY = LOCAL_BUS_FREQUENCY) generate

   LB_ENDPOINT_U : entity work.LB_ENDPOINT_100
   generic map(
      BASE_ADDR  => BASE_ADDR,
      LIMIT      => LIMIT,
      BUFFER_EN  => BUFFER_EN
   )
   port map(
      -- Common Interface
      RESET      => reset_pipe,

      -- Local Bus Interface
      LB_CLK      => LB_CLK,
      LB_DWR      => LB_DWR,
      LB_BE       => LB_BE,
      LB_ADS_N    => LB_ADS_N,
      LB_RD_N     => LB_RD_N,
      LB_WR_N     => LB_WR_N,
      LB_DRD      => LB_DRD,
      LB_RDY_N    => LB_RDY_N,
      LB_ERR_N    => LB_ERR_N,
      LB_ABORT_N  => LB_ABORT_N,

      -- User Component Interface
      CLK         => CLK,
      MI32_DWR    => MI32_DWR,
      MI32_ADDR   => MI32_ADDR,
      MI32_RD     => MI32_RD,
      MI32_WR     => MI32_WR,
      MI32_BE     => MI32_BE,
      MI32_DRD    => MI32_DRD,
      MI32_ARDY   => MI32_ARDY,
      MI32_DRDY   => MI32_DRDY
   );
end generate;


end architecture LB_ENDPOINT_NOREC_ARCH;

