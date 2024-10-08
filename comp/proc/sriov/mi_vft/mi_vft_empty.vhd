-- mi_vft.vhd: MI Virtual Function Translator - empty architecture
-- Copyright (C) 2017 CESNET
-- Author(s): Jan Remes
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ----------------------------------------------------------------------------

architecture mi_vft_arch of MI_VFT is

begin

   OUT_ADDR    <= IN_ADDR;
   OUT_DWR     <= IN_DWR;
   OUT_BE      <= IN_BE;
   OUT_WR      <= IN_WR;
   OUT_RD      <= IN_RD;
   OUT_MWR     <= IN_MWR;

   IN_DRD      <= OUT_DRD;
   IN_DRDY     <= OUT_DRDY;
   IN_ARDY     <= OUT_ARDY;

end mi_vft_arch;
