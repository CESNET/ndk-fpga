--
-- binder_ent.vhd: Binder N-1 component for Frame Link Unaligned
-- Copyright (C) 2012 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
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
entity FLU_BINDER_EFF is
   generic(
      --! FLU configuration (DATA_WIDTH and SOP_POS_WIDTH bus)
      DATA_WIDTH    : integer:= 512;
      SOP_POS_WIDTH : integer:= 3;

      --! Number of input ports
      --! \brief Warning, only powers of two are allowed as
      --! input port count. Minimal input ports are 2.
      INPUT_PORTS   : integer:= 8;

      --! Logarithm base
      --! \brief Number of inputs of one stage multiplexer. These multiplexers
      --! create a RR selection tree. Therefore, number of stages is computed as
      --! RR_TREE_DEPTH = log2(INPUT_PORTS)/log2(DIVISION_RATIO)
      --! The result of this equation has to be an integer!
      --! Default value is 2
      DIVISION_RATIO : integer := 2;

      --! Pipeline stages map (number of stages can be computed as RR tree dept + 1 (input pipeline)
      --!  '0' - pipeline won't be inserted
      --!  '1' - pipeline will be inserted
      PIPELINE_MAP   : integer := 15; --1111

      --! DSP multiplexer map, it tells to RR element if to choose a DSP based multiplexor
      --! in the RR stage. Width of this signal is computed with usage of the DIVISION_RATIO formula.
      --! The usage is as same asin the pipeline PIPELINE_MAP generic.
      --!   '0' - don't use the DSP multiplexor
      --!   '1' - use the DSP multiplexor
      DSP_MAP        : integer := 0; --0000

      --! Type of pipes used inside
      --! You can select type of pipe implementation:
      --!    "SHREG" - pipe implemented as shift register
      --!    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --!              on wide buses and on Intel/Altera devices
      PIPE_TYPE      : string := "SHREG";

      --! Input Align map (It tells if input flow is aligned - can be computed as INPUT_PORTS)
      --!   '0' - input flow is alligned
      --!   '1' - input FLU flow is not alligned
      ALIGN_MAP      : integer := 255; --11111111

      --! Enable/Disable header (which can be assigned to input FLU frame)
      --!   0 - Disable Header function
      --!   1 - Enable Header function
      HDR_ENABLE     : integer := 1;
      --! Widht of the header
      HDR_WIDTH      : integer := 128;
      --! FIFO configuration
      HDR_FIFO_ITEMS    : integer := 32;

      --! Enable/disable the reservation of 128 bit gap
      --! NOTICE: If you enable this functionality, you should be sure
      --! that the minimal packet length is of the frame is 60 bytes.
      --! This generic is tightly bounded with usage in network module and
      --! the FSM needs to be optimized for that usage. This generic can
      --! be used with DATA_WIDTH equals to 256 and 512 bits, because the
      --! author wants to keep the solution as simple as possible.
      --!   0 - Disable insertion of the 128 bit gap between FLU frames
      --!   1 - Enable insertion of the 128 bit gap between FLU frames
      RESERVE_GAP_EN : boolean := true;

      -- Enable pipe on both header and data output interface due to possible
      -- deadlock state: the binder core awaits that header will be pulled in
      -- the same cycle as SOP data. If HDR_ENABLE is 0, pipe is not instanced.
      -- Disable, if you handle this behavior in your application correctly.
      -- This can be also probably somehow fixed in binder internal logic.
      OUTPUT_PIPE_EN : boolean := true;

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

      --! \name Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_EOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);

      --! \name Header input interface
      RX_HDR_DATA       : in std_logic_vector(INPUT_PORTS*HDR_WIDTH-1 downto 0);
      RX_HDR_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_HDR_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);

      --! \name Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic;

      --! \name Header output interface
      TX_HDR_DATA       : out std_logic_vector(HDR_WIDTH-1 downto 0);
      TX_HDR_SRC_RDY    : out std_logic;
      TX_HDR_DST_RDY    : in std_logic;

      --! \name Debug
      --! Information about source Interface (valid when TX_SOP = '1')
      --! log2(INPUT_PORTS) MSB bits contains the port, last bit contains information about
      --! used line in internal infrastructure
      SELECTED_FROM  : out std_logic_vector(log2(INPUT_PORTS) downto 0);
      --! Information abou internal distribution interface (one bit on interface)
      DISTRIBUTED_TO : out std_logic_vector(INPUT_PORTS-1 downto 0)
   );
end entity;
