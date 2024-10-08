--
-- flu2flua_arch.vhd: Component for conversion of FLU to Aligned FLU
-- Copyright (C) 2014 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU2FLUA_CORE is
   generic(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH    : integer:= 256;
      SOP_POS_WIDTH : integer:= 2;

      -- Pipeline Config ------------------------
      -- Use input pipe
      IN_PIPE_EN           : boolean := false;
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      IN_PIPE_TYPE         : string := "SHREG";
      -- Use output register of input pipe
      IN_PIPE_OUTREG       : boolean := false;
      -- Use output pipe
      OUT_PIPE_EN          : boolean := false;
      -- same as IN_PIPE_TYPE
      OUT_PIPE_TYPE        : string := "SHREG";
      -- Use output register of input pipe
      OUT_PIPE_OUTREG      : boolean := false;
      -- Select PIPE component implementation
      -- Use "REG" for Intel devices
      -- Use "SHREG" for Xilinx devices
      PIPE_TYPE            : string  := "REG";
      -- Base ID - if ID not enabled, ID output is not connected
      ENABLE_DEBUG         : integer := 1;
      ID_WIDTH             : integer := 1;
      ID0_VAL              : integer := 0;
      ID1_VAL              : integer := 1;

      -- Align input flow
      ALIGN                : boolean := true
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Distributed to output (active when SOP = 1)
      DISTRIBUTED_TO : out std_logic;

      -- Frame Link Unaligned output lane 0
      TX_DATA0      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS0   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS0   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP0       : out std_logic;
      TX_EOP0       : out std_logic;
      TX_SRC_RDY0   : out std_logic;
      TX_DST_RDY0   : in std_logic;
      ID0           : out std_logic_vector(ID_WIDTH-1 downto 0);

      -- Frame Link Unaligned output lane 1
      TX_DATA1      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS1   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS1   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP1       : out std_logic;
      TX_EOP1       : out std_logic;
      TX_SRC_RDY1   : out std_logic;
      TX_DST_RDY1   : in std_logic;
      ID1           : out std_logic_vector(ID_WIDTH-1 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLU2FLUA_CORE is
   --! FLU Input signals
   signal in_rx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_rx_sop_pos       : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_rx_eop_pos       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_rx_sop           : std_logic;
   signal in_rx_eop           : std_logic;
   signal in_rx_src_rdy       : std_logic;
   signal in_rx_dst_rdy       : std_logic;

   --! Signal for distribute information
   signal distributed_to_out : std_logic;

   --! FLU Distrib -> FLU2FLUA signals (lane 0)
   signal flu2flua_rx_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flu2flua_rx_sop_pos0   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flu2flua_rx_eop_pos0   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal flu2flua_rx_sop0       : std_logic;
   signal flu2flua_rx_eop0       : std_logic;
   signal flu2flua_rx_src_rdy0   : std_logic;
   signal flu2flua_rx_dst_rdy0   : std_logic;

   --! FLU Distrib -> FLU2FLUA signals (lane 1)
   signal flu2flua_rx_data1      : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
   signal flu2flua_rx_sop_pos1   : std_logic_vector(SOP_POS_WIDTH-1 downto 0) := (others => '0');
   signal flu2flua_rx_eop_pos1   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0) := (others => '0');
   signal flu2flua_rx_sop1       : std_logic;
   signal flu2flua_rx_eop1       : std_logic;
   signal flu2flua_rx_src_rdy1   : std_logic;
   signal flu2flua_rx_dst_rdy1   : std_logic;

begin
   -- -------------------------------------------------------------------------
   -- Input signal map
   -- -------------------------------------------------------------------------
   --! FLU RX signal map
   in_rx_data     <= RX_DATA;
   in_rx_sop_pos  <= RX_SOP_POS;
   in_rx_eop_pos  <= RX_EOP_POS;
   in_rx_sop      <= RX_SOP;
   in_rx_eop      <= RX_EOP;
   in_rx_src_rdy  <= RX_SRC_RDY;
   RX_DST_RDY     <= in_rx_dst_rdy;

   --! Information about frame distribution
   DISTRIBUTED_TO <= distributed_to_out;

   -- -------------------------------------------------------------------------
   -- FLU -> FLU Align logic
   -- -------------------------------------------------------------------------

   RR_DISTRIB_GEN:if(ALIGN = true)generate
      --! FLU RR distribution
      DISTRIB_I:entity work.DISTRIB
         generic map(
             --! FLU protocol generics
             DATA_WIDTH       => DATA_WIDTH,
             SOP_POS_WIDTH    => SOP_POS_WIDTH
         )
         port map(
             -- -------------------------------------------------
             -- \name Common interface
             -- -------------------------------------------------
            RESET          => RESET,
            CLK            => CLK,

            -- --------------------------------------------------
            -- \name Frame Link Unaligned input interface
            -- --------------------------------------------------
            RX_DATA        => in_rx_data,
            RX_SOP_POS     => in_rx_sop_pos,
            RX_EOP_POS     => in_rx_eop_pos,
            RX_SOP         => in_rx_sop,
            RX_EOP         => in_rx_eop,
            RX_SRC_RDY     => in_rx_src_rdy,
            RX_DST_RDY     => in_rx_dst_rdy,

            -- Distributed to output (active when SOP = 1)
            DISTRIBUTED_TO => distributed_to_out,

            -- --------------------------------------------------
            -- \name Frame Link Unaligned output interface (lane 0)
            -- --------------------------------------------------
            TX_DATA0       => flu2flua_rx_data0,
            TX_SOP_POS0    => flu2flua_rx_sop_pos0,
            TX_EOP_POS0    => flu2flua_rx_eop_pos0,
            TX_SOP0        => flu2flua_rx_sop0,
            TX_EOP0        => flu2flua_rx_eop0,
            TX_SRC_RDY0    => flu2flua_rx_src_rdy0,
            TX_DST_RDY0    => flu2flua_rx_dst_rdy0,

            -- --------------------------------------------------
            -- \name Frame Link Unaligned output interface (lane 1)
            -- --------------------------------------------------
            TX_DATA1       => flu2flua_rx_data1,
            TX_SOP_POS1    => flu2flua_rx_sop_pos1,
            TX_EOP_POS1    => flu2flua_rx_eop_pos1,
            TX_SOP1        => flu2flua_rx_sop1,
            TX_EOP1        => flu2flua_rx_eop1,
            TX_SRC_RDY1    => flu2flua_rx_src_rdy1,
            TX_DST_RDY1    => flu2flua_rx_dst_rdy1
         );
   end generate;

   NO_RR_DISTRIB_GEN:if(ALIGN =  false)generate
      -- Put data on LANE0, LANE1 will be disabled
      flu2flua_rx_data0 <= in_rx_data;
      flu2flua_rx_sop_pos0 <= in_rx_sop_pos;
      flu2flua_rx_eop_pos0 <= in_rx_eop_pos;
      flu2flua_rx_sop0 <= in_rx_sop;
      flu2flua_rx_eop0 <= in_rx_eop;
      flu2flua_rx_src_rdy0 <= in_rx_src_rdy;
      in_rx_dst_rdy <= flu2flua_rx_dst_rdy0;

      -- Everything is distributed to lane 0
      distributed_to_out <= '0';

      -- Disable lane 1
      flu2flua_rx_src_rdy1 <= '0';
      flu2flua_rx_sop1 <= '0';
      flu2flua_rx_eop1 <= '0';
   end generate;

   --! FLU Aligning unit for lane 0
   ALIGN_LANE0_I:entity work.FLU_ALIGN
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH        => DATA_WIDTH,
         SOP_POS_WIDTH     => SOP_POS_WIDTH,

         -- Pipeline Config ------------------------
         -- Use input pipe
         IN_PIPE_EN           => IN_PIPE_EN,
         -- Input pipe type (SHREG or REG)
         IN_PIPE_TYPE         => IN_PIPE_TYPE,
         -- Use output register of input pipe
         IN_PIPE_OUTREG       => IN_PIPE_OUTREG,
         -- Use output pipe
         OUT_PIPE_EN          => OUT_PIPE_EN,
         -- Output pipe type (SHREG or REG)
         OUT_PIPE_TYPE        => OUT_PIPE_TYPE,
         -- Use output register of input pipe
         OUT_PIPE_OUTREG      => OUT_PIPE_OUTREG,
         -- Align output flow
         ALIGN                => ALIGN
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => RESET,
         CLK            => CLK,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         RX_DATA        => flu2flua_rx_data0,
         RX_SOP_POS     => flu2flua_rx_sop_pos0,
         RX_EOP_POS     => flu2flua_rx_eop_pos0,
         RX_SOP         => flu2flua_rx_sop0,
         RX_EOP         => flu2flua_rx_eop0,
         RX_SRC_RDY     => flu2flua_rx_src_rdy0,
         RX_DST_RDY     => flu2flua_rx_dst_rdy0,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface
         -- --------------------------------------------------
         TX_DATA        => TX_DATA0,
         TX_SOP_POS     => TX_SOP_POS0,
         TX_EOP_POS     => TX_EOP_POS0,
         TX_SOP         => TX_SOP0,
         TX_EOP         => TX_EOP0,
         TX_SRC_RDY     => TX_SRC_RDY0,
         TX_DST_RDY     => TX_DST_RDY0
      );

   --! Assign the channel ID
   ID0_OUT_GENP:if(ENABLE_DEBUG = 1)generate
      ID0 <= conv_std_logic_vector(ID0_VAL,ID_WIDTH);
   end generate;

   --! FLU Aligning unit for lane 1
   ALIGN_LANE1_I:entity work.FLU_ALIGN
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH        => DATA_WIDTH,
         SOP_POS_WIDTH     => SOP_POS_WIDTH,

         -- Pipeline Config ------------------------
         -- Use input pipe
         IN_PIPE_EN           => IN_PIPE_EN,
         -- Input pipe type (SHREG or REG)
         IN_PIPE_TYPE         => IN_PIPE_TYPE,
         -- Use output register of input pipe
         IN_PIPE_OUTREG       => IN_PIPE_OUTREG,
         -- Use output pipe
         OUT_PIPE_EN          => OUT_PIPE_EN,
         -- Output pipe type (SHREG or REG)
         OUT_PIPE_TYPE        => OUT_PIPE_TYPE,
         -- Use output register of input pipe
         OUT_PIPE_OUTREG      => OUT_PIPE_OUTREG,
         -- Align
         ALIGN                => ALIGN
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => RESET,
         CLK            => CLK,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         RX_DATA       => flu2flua_rx_data1,
         RX_SOP_POS    => flu2flua_rx_sop_pos1,
         RX_EOP_POS    => flu2flua_rx_eop_pos1,
         RX_SOP        => flu2flua_rx_sop1,
         RX_EOP        => flu2flua_rx_eop1,
         RX_SRC_RDY    => flu2flua_rx_src_rdy1,
         RX_DST_RDY    => flu2flua_rx_dst_rdy1,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface
         -- --------------------------------------------------
         TX_DATA        => TX_DATA1,
         TX_SOP_POS     => TX_SOP_POS1,
         TX_EOP_POS     => TX_EOP_POS1,
         TX_SOP         => TX_SOP1,
         TX_EOP         => TX_EOP1,
         TX_SRC_RDY     => TX_SRC_RDY1,
         TX_DST_RDY     => TX_DST_RDY1
      );

      --! Assign ID
   ID1_OUT_GENP:if(ENABLE_DEBUG = 1)generate
         ID1 <= conv_std_logic_vector(ID1_VAL,ID_WIDTH);
   end generate;

end architecture FULL;
