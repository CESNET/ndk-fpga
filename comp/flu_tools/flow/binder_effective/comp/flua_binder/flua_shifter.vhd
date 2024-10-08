--
-- align_ent.vhd: FLU align component
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
entity FLUA_SHIFTER is
   generic(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH    : integer:= 256;
      SOP_POS_WIDTH : integer:= 2;
      ID_WIDTH      : integer:= 1;
      ENABLE_ID     : integer:= 1;

      --! Header configuratoin
      HDR_ENABLE    : integer := 1;
      HDR_WIDTH     : integer := 128;

      --! Changes for binding with FLU gap,
      --! if short frame with non zero shift is detected,
      --! ignore first EOP because it is not valid, this signal
      --! not masked to reach better frequency.
      FLU_GAP_EN    : boolean := false
   );
   port(
       -- -------------------------------------------------
       -- \name Common interface
       -- -------------------------------------------------
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- --------------------------------------------------
      -- \name Control interface
      -- --------------------------------------------------
      -- Shifting value of SOP_POS; this signal is valid
      -- when RX_SOP is asserted.
      SHIFT_VAL      : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);

      -- --------------------------------------------------
      -- \name Frame Link Unaligned input interface
      -- --------------------------------------------------
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;
      ID_IN         : in std_logic_vector(ID_WIDTH-1 downto 0);
      HDR_IN        : in std_logic_vector(HDR_WIDTH-1 downto 0);

      -- --------------------------------------------------
      -- \name Frame Link Unaligned output interface
      -- --------------------------------------------------
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic;
      ID_OUT         : out std_logic_vector(ID_WIDTH-1 downto 0);
      HDR_OUT        : out std_logic_vector(HDR_WIDTH-1 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLUA_SHIFTER is

   -- Signals declaration -----------------------------------------------------
   signal masked_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal masked_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal masked_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal masked_sop        : std_logic;
   signal masked_eop        : std_logic;
   signal masked_src_rdy    : std_logic;
   signal masked_dst_rdy    : std_logic;

begin

   --! Aligning core entity
   CORE_I:entity work.FLUA_SHIFTER_CORE
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,
         FLU_GAP_EN     => FLU_GAP_EN
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => RESET,
         CLK            => CLK,

         -- --------------------------------------------------
         -- \name Control interface
         -- --------------------------------------------------
         -- Shifting value of SOP_POS; this signal is valid
         -- when RX_SOP is asserted.
         SHIFT_VAL      => SHIFT_VAL,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         RX_DATA        => RX_DATA,
         RX_SOP_POS     => RX_SOP_POS,
         RX_EOP_POS     => RX_EOP_POS,
         RX_SOP         => RX_SOP,
         RX_EOP         => RX_EOP,
         RX_SRC_RDY     => RX_SRC_RDY,
         RX_DST_RDY     => RX_DST_RDY,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface
         -- --------------------------------------------------
         TX_DATA        => masked_data,
         TX_SOP_POS     => masked_sop_pos,
         TX_EOP_POS     => masked_eop_pos,
         TX_SOP         => masked_sop,
         TX_EOP         => masked_eop,
         TX_SRC_RDY     => masked_src_rdy,
         TX_DST_RDY     => masked_dst_rdy
      );


      -- Copy the rest of signals without any change
      TX_DATA        <= masked_data;
      TX_SOP_POS     <= masked_sop_pos;
      TX_EOP_POS     <= masked_eop_pos;
      TX_SOP         <= masked_sop;
      TX_EOP         <= masked_eop;
      TX_SRC_RDY     <= masked_src_rdy;
      masked_dst_rdy <= TX_DST_RDY;

      -- Transfer the ID_IN value
   ID_OUT_GEN:if(ENABLE_ID = 1)generate
      ID_OUT <= ID_IN;
   end generate;

      -- Transfer the header value
      NO_HDR_GEN:if(HDR_ENABLE = 0)generate
         HDR_OUT <= (others=>'0');
      end generate;

      HDR_GEN:if(HDR_ENABLE = 1)generate
         HDR_OUT <= HDR_IN;
      end generate;
end architecture;
