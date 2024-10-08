-- switch_impl_ent.vhd: Entity of a switch internal implementation.
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

--* Entity of a switch implementation. It can solve on of generic configurations.
--* Assumes that some external logic extracts the IFNUM from the frame. It
--* <b>doesn't solve</b> the output multiplexing.
--* The implementation <b>must</b> control signals TX_SRC_RDY_N and TX_DST_RDY_N.
--*
--* @author Jan Viktorin
entity fl_switch_impl is
generic (
   --* Number of TX interfaces
   TX_COUNT    : integer := 4;
   --* FrameLink data width
   DATA_WIDTH  : integer := 32;
   --* Offset of the IFNUM in every frame (in bits)
   INUM_OFFSET : integer := 0;
   --* Number of parts in the frame
   PARTS       : integer := 1
);
port (
   -- Common signals
   CLK            : in std_logic;
   RESET          : in std_logic;

   -- Read interface
   RX_DATA        : in std_logic_vector(DATA_WIDTH - 1 downto 0);
   RX_REM         : in std_logic_vector(log2(DATA_WIDTH / 8) - 1 downto 0);
   RX_SOF_N       : in std_logic;
   RX_EOF_N       : in std_logic;
   RX_SOP_N       : in std_logic;
   RX_EOP_N       : in std_logic;
   RX_SRC_RDY_N   : in  std_logic;
   RX_DST_RDY_N   : out std_logic;

   -- Write interface
   TX_DATA        : out std_logic_vector(DATA_WIDTH - 1 downto 0);
   TX_REM         : out std_logic_vector(log2(DATA_WIDTH / 8) - 1 downto 0);
   TX_SOF_N       : out std_logic;
   TX_EOF_N       : out std_logic;
   TX_SOP_N       : out std_logic;
   TX_EOP_N       : out std_logic;
   TX_SRC_RDY_N   : out std_logic_vector(TX_COUNT - 1 downto 0);
   TX_DST_RDY_N   : in  std_logic_vector(TX_COUNT - 1 downto 0);

   --* Extracted interface number
   IFNUM          : in  std_logic_vector(TX_COUNT - 1 downto 0)
);
end entity;


