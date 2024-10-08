-- ib_bfm_rdy_pkg.vhd: Package for driving rdy signal
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Internal Bus BFM Package
-- ----------------------------------------------------------------------------
PACKAGE ib_bfm_rdy_pkg IS

  ----------------------------------------------------------------------------
  -- PKG FUNCTIONS
  ----------------------------------------------------------------------------

----------------------------------------------------------------------------
  --
  PROCEDURE DriveDstRdyN(signal CLK       : IN    std_logic;
                         signal DST_RDY_N : OUT std_logic);

END ib_bfm_rdy_pkg;



-- ----------------------------------------------------------------------------
--                      Internal Bus BFM Package BODY
-- ----------------------------------------------------------------------------
PACKAGE BODY ib_bfm_rdy_pkg IS

  -----------------------------------------------------------------------------
  --
  PROCEDURE DriveDstRdyN (signal CLK       : IN  std_logic;
                          signal DST_RDY_N : OUT std_logic) IS
  BEGIN
    DST_RDY_N <= '0';
    wait until (CLK'event and CLK='1');
    --DST_RDY_N <= '1';
    --wait until (CLK'event and CLK='1');
  END;

END ib_bfm_rdy_pkg;

