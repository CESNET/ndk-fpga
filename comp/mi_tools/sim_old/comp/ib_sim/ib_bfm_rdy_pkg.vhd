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
package ib_bfm_rdy_pkg is

    ----------------------------------------------------------------------------
    -- PKG FUNCTIONS
    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    --
    procedure drivedstrdyn (
        signal clk       : in    std_logic;
        signal dst_rdy_n : out std_logic
    );

end package;



-- ----------------------------------------------------------------------------
--                      Internal Bus BFM Package BODY
-- ----------------------------------------------------------------------------
package body ib_bfm_rdy_pkg is

    -----------------------------------------------------------------------------
    --
    procedure drivedstrdyn (
        signal clk       : in  std_logic;
        signal dst_rdy_n : out std_logic
    ) is
    begin
        dst_rdy_n <= '0';
        wait until (clk'event and clk = '1');
        -- DST_RDY_N <= '1';
        -- wait until (CLK'event and CLK='1');
    end procedure drivedstrdyn;

end package body;

