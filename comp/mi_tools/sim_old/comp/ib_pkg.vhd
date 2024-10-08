-- ib_pkg.vhd: Internal Bus Package
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
--                        Internal Bus Package
-- ----------------------------------------------------------------------------
package ib_pkg is

   -- ========================
   -- Address
   -- ========================

   constant C_IB_TRANS_TYPE_WIDTH : integer := 3;
   constant C_IB_FLAG_WIDTH       : integer := 1;
   constant C_IB_LENGTH_WIDTH     : integer := 12;

   -- =============================================
   -- IB Transaction Type
   --
   -- ('NORMAL/COMPL' 'LOCAL/GLOBAL' 'WRITE/READ')
   -- =============================================

   constant C_IB_L2LW_TRANSACTION          : std_logic_vector(2 downto 0) := "000";
   constant C_IB_L2LR_TRANSACTION          : std_logic_vector(2 downto 0) := "001";
   constant C_IB_L2GW_TRANSACTION          : std_logic_vector(2 downto 0) := "010";
   constant C_IB_G2LR_TRANSACTION          : std_logic_vector(2 downto 0) := "011";
   constant C_IB_WR_COMPL_TRANSACTION      : std_logic_vector(2 downto 0) := "100";
   constant C_IB_RD_COMPL_TRANSACTION      : std_logic_vector(2 downto 0) := "101";

   -- Fourth bit of type (15 bit) is reserved for 1) Ack flag - for L2LW transaction
   --                                             2) Last fragment flag - for G2LR

   -- Internal 64 bit Bus Link
   type t_internal_bus_link64 is record
      DATA       : std_logic_vector(63 downto 0);
      SOP_N      : std_logic;
      EOP_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   -- Internal 64 bit Bus
   type t_internal_bus64 is record
      UP         : t_internal_bus_link64;
      DOWN       : t_internal_bus_link64;
   end record;


   -- Internal Bus Write Interface
   type t_ibmi_write64 is record
      -- Address
      ADDR      : std_logic_vector(31 downto 0);
      -- Data
      DATA      : std_logic_vector(63 downto 0);
      -- Byte Enable
      BE        : std_logic_vector(7 downto 0);
      -- Write Request
      REQ       : std_logic;
      -- Ready
      RDY       : std_logic;
      -- Length
      LENGTH    : std_logic_vector(11 downto 0);
      -- Start of Frame
      SOF       : std_logic;
      -- End of Frame
      EOF       : std_logic;
   end record;

   -- Internal Bus Read Interface (Simple)
   type t_ibmi_read64s is record
      -- Input interface

      -- Address
      ADDR      : std_logic_vector(31 downto 0);
      -- Byte Enable
      BE        : std_logic_vector(7 downto 0);
      -- Length
--       LENGTH    : std_logic_vector(11 downto 0);
      -- Read Request
      REQ       : std_logic;
      -- Address Ready
      ARDY      : std_logic;
      -- Start of Frame (Input)
      SOF_IN    : std_logic;
      -- End of Frame (Intput)
      EOF_IN    : std_logic;
      -- Output interface

      -- Read Data
      DATA      : std_logic_vector(63 downto 0);
      -- Data Ready
      SRC_RDY   : std_logic;
      -- Endpoint Ready
      DST_RDY   : std_logic;
   end record;


   -- Internal Bus Read Interface (Combined without Tags)
   type t_ibmi_read64c is record
      -- Input interface

      -- Address
      ADDR      : std_logic_vector(31 downto 0);
      -- Byte Enable
      BE        : std_logic_vector(7 downto 0);
      -- Length
      LENGTH    : std_logic_vector(11 downto 0);
      -- Read Request
      REQ       : std_logic;
      -- Address Ready
      ARDY      : std_logic;
      -- Accept
      ACCEPT    : std_logic;
      -- Start of Frame (Input)
      SOF_IN    : std_logic;
      -- End of Frame (Intput)
      EOF_IN    : std_logic;

      -- Output interface

      -- Read Data
      DATA      : std_logic_vector(63 downto 0);
      -- Data Ready
      SRC_RDY   : std_logic;
      -- Endpoint Ready
      DST_RDY   : std_logic;
      -- Start of Frame (Output)
      SOF_OUT   : std_logic;
      -- End of Frame (Output)
      EOF_OUT   : std_logic;
   end record;


   -- Internal Bus Read Interface (Combined with Tags)
   type t_ibmi_read64ct is record
      -- Input interface

      -- Address
      ADDR      : std_logic_vector(31 downto 0);
      -- Byte Enable
      BE        : std_logic_vector(7 downto 0);
      -- Length
      LENGTH    : std_logic_vector(11 downto 0);
      -- Read Transaction Tag (Input)
      TAG_IN    : std_logic_vector(7 downto 0);
      -- Read Request
      REQ       : std_logic;
      -- Address Ready
      ARDY      : std_logic;
      -- Accept
      ACCEPT    : std_logic;
      -- Start of Frame (Input)
      SOF_IN    : std_logic;
      -- End of Frame (Intput)
      EOF_IN    : std_logic;

      -- Output interface

      -- Read Transaction Tag (Output)
      TAG_OUT   : std_logic_vector(15 downto 0);
      -- Read Data
      DATA      : std_logic_vector(63 downto 0);
      -- Data Ready
      SRC_RDY   : std_logic;
      -- Endpoint Ready
      DST_RDY   : std_logic;
      -- Start of Frame (Output)
      SOF_OUT   : std_logic;
      -- End of Frame (Output)
      EOF_OUT   : std_logic;
   end record;


   -- Internal Bus BM Interface
   type t_ibbm_64 is record
      -- Master Interface Input

      -- Global Address
      GLOBAL_ADDR   : std_logic_vector(63 downto 0);
      -- Local Address
      LOCAL_ADDR    : std_logic_vector(31 downto 0);
      -- Length
      LENGTH        : std_logic_vector(11 downto 0);
      -- Operation TAG
      TAG           : std_logic_vector(15 downto 0);
      -- Type of transaction
      TRANS_TYPE    : std_logic_vector(1 downto 0);
      -- Request
      REQ           : std_logic;

      -- Master Output interface

      -- Ack
      ACK           : std_logic;
      -- Operation TAG
      OP_TAG        : std_logic_vector(15 downto 0);
      -- Acknowledge
      OP_DONE       : std_logic;
   end record;


end ib_pkg;


-- ----------------------------------------------------------------------------
--                        Internal Bus Package
-- ----------------------------------------------------------------------------
package body ib_pkg is

end ib_pkg;

