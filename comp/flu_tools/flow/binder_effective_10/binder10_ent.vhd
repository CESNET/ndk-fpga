--
-- binder_a10_ent.vhd: Binder 10 component for Frame Link Unaligned (ALIGNED)
-- Copyright (C) 2014 CESNET
-- Author: Tomas Zavodnik <zavodnik@cesnet.cz>
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

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLUA_BINDER_10_EFF is
   generic(
      --! FLU configuration
      DATA_WIDTH    : integer:= 512;
      SOP_POS_WIDTH : integer:= 3;

      --! Logarithm base
      --! \brief Number of inputs of one stage multiplexer. These multiplexers
      --! create a RR selection tree. Therefore, number of stages is computed as
      --! log2(16)/log2(DIVISION_RATIO)
      --! The result of this equation has to be an integer!
      --! Possible values are: 2,4,16
      --! Warning: We want to use all mux inputs at each stage!
      DIVISION_RATIO : integer := 2;

      --! Pipeline stages map - number of stages is 1 (header insert) + binder tree depth + 1
      --! (another pipeline stage).
      --!  '0' - pipeline won't be inserted
      --!  '1' - pipeline will be inserted
      PIPELINE_MAP   : std_logic_vector(5 downto 0) := "111110";

      --! DSP multiplexer map, it tells to RR element if to choose a DSP based multiplexor
      --! in the RR stage. Width of this signal is computed with usage of the DIVISION_RATIO formula.
      --! The usage is as same asin the pipeline PIPELINE_MAP generic.
      --!   '0' - don't use the DSP multiplexor
      --!   '1' - use the DSP multiplexor
      DSP_MAP        : std_logic_vector(3 downto 0) := "0000";

      --! Enable/Disable header (which can be assigned to input FLU frame)
      --!   false - Disable Header function
      --!   true  - Enable Header function
      HDR_ENABLE     : boolean := true;
      --! Enable/Disable header insertion in the beginning of packets
      --!   false - use parallel (independent) path
      --!   true  - insert header directly into packet
      HDR_INSERT     : boolean := true;
      --! Widht of the header
      HDR_WIDTH      : integer := 128;
      --! FIFO configuration in header parallel path
      HDR_FIFO_ITEMS : integer := 32;

      --! Enable/disable the reservation of 128 bit gap
      --! NOTICE: If you enable this functionality, you should be sure
      --! that the minimal packet length is of the frame is 60 bytes.
      --! This generic is tightly bounded with usage in network module and
      --! the FSM needs to be optimized for that usage. This generic can
      --! be used with DATA_WIDTH equals to 256 and 512 bits, because the
      --! author wants to keep the solution as simple as possible.
      --!   false - Disable insertion of the 128 bit gap between FLU frames
      --!   true  - Enable insertion of the 128 bit gap between FLU frames
      RESERVE_GAP_EN : boolean := false;

      --! Enable/disable the debug interface (enabled by default)
      --! When disabled, output is not connected and some resources can be saved.
      --! Affected outputs are DISTRIBUTED_TO and SELECTED_FROM
      --!   0 - Disable debug
      --!   1 - Enable debug
      ENABLE_DEBUG   : integer := 1
   );
   port(
       --! \name  Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      --! \name Frame Link Unaligned (ALIGNED) input interface
      RX_DATA        : in std_logic_vector(10*DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in std_logic_vector(10*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS     : in std_logic_vector(10*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP         : in std_logic_vector(10-1 downto 0);
      RX_EOP         : in std_logic_vector(10-1 downto 0);
      RX_SRC_RDY     : in std_logic_vector(10-1 downto 0);
      RX_DST_RDY     : out std_logic_vector(10-1 downto 0);

      --! \name Header input interface
      RX_HDR_DATA    : in std_logic_vector(10*HDR_WIDTH-1 downto 0);
      RX_HDR_SRC_RDY : in std_logic_vector(10-1 downto 0);
      RX_HDR_DST_RDY : out std_logic_vector(10-1 downto 0);

      --! \name Frame Link Unaligned concentrated interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic;

      --! \name Header output interface
      TX_HDR_DATA    : out std_logic_vector(HDR_WIDTH-1 downto 0);
      TX_HDR_SRC_RDY : out std_logic;
      TX_HDR_DST_RDY : in std_logic;

      --! \name Debug
      --! Information about source Interface (valid when TX_SOP = '1')
      --! 10 MSB bits contains the port, last bit contains information about
      --! used line in internal infrastructure
      SELECTED_FROM  : out std_logic_vector(10 downto 0);
      --! Information abou internal distribution interface (one bit on interface)
      DISTRIBUTED_TO : out std_logic_vector(9 downto 0)
   );
end entity;
