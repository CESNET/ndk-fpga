--!
--! \file dp_bmem_V7_behav.vhd
--! \brief Dual port BRAM for Virtex 7 architecture, behavioral architecture
--! \author Jan Kučera <xkucer73@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! \brief Behavioral architecture of dual port Virtex7 BRAM declaration
architecture BEHAV of DP_BRAM_V7 is

begin

   --! \brief Instantion of behavioral BRAM
   BRAM_BEHAV_I:entity work.DP_BMEM(behavioral)
   generic map (
      DATA_WIDTH   => DATA_WIDTH,
      ITEMS        => 2**ADDRESS_WIDTH,
      WRITE_MODE_A => WRITE_MODE_A,
      WRITE_MODE_B => WRITE_MODE_B,
      OUTPUT_REG   => ENABLE_OUT_REG
   )
   port map(
      -- Interface A
      CLKA        => CLKA,       -- Clock A
      RSTA        => RSTA,       -- Clock A sync reset
      PIPE_ENA    => PIPE_ENA,   -- Pipe Enable
      REA         => REA,        -- Read Enable
      WEA         => WEA,        -- Write Enable
      ADDRA       => ADDRA,      -- Address A
      DIA         => DIA,        -- Data A In
      DOA_DV      => DOA_DV,     -- Data A Valid
      DOA         => DOA,        -- Data A Out

      -- Interface B
      CLKB        => CLKB,       -- Clock B
      RSTB        => RSTB,       -- Clock B sync reset
      PIPE_ENB    => PIPE_ENB,   -- Pipe Enable
      REB         => REB,        -- Read Enable
      WEB         => WEB,        -- Write Enable
      ADDRB       => ADDRB,      -- Address B
      DIB         => DIB,        -- Data B In
      DOB_DV      => DOB_DV,     -- Data B Valid
      DOB         => DOB         -- Data B Out
   );
end architecture BEHAV;
