-- decoder_ent.vhd: FrameLink decoder entity
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_DEC is
   generic(
      -- Header data present
      HEADER      : boolean := true;
      -- Footer data present
      FOOTER      : boolean := true
   );
   port(
      CLK         : in  std_logic;
      RESET       : in  std_logic;

      -- ===================
      -- FrameLink interface
      -- ===================
      SOF_N       : in  std_logic;
      SOP_N       : in  std_logic;
      EOP_N       : in  std_logic;
      EOF_N       : in  std_logic;
      SRC_RDY_N   : in  std_logic;
      DST_RDY_N   : out std_logic;

      -- ===================
      -- decoder signals
      -- ===================

      -- start of frame
      SOF         : out std_logic;
      -- start of header
      SOHDR       : out std_logic;
      -- end of header
      EOHDR       : out std_logic;
      -- header part is transmitted
      HDR_FRAME   : out std_logic;
      -- start of payload
      SOPLD       : out std_logic;
      -- end of payload
      EOPLD       : out std_logic;
      -- payload part is transmitted
      PLD_FRAME   : out std_logic;
      -- start of footer
      SOFTR       : out std_logic;
      -- end of footer
      EOFTR       : out std_logic;
      -- footer part is transmitted
      FTR_FRAME   : out std_logic;
      -- end of frame
      EOF         : out std_logic;
      -- source ready
      SRC_RDY     : out std_logic;
      -- destination ready
      DST_RDY     : in  std_logic
   );
end entity FL_DEC;

