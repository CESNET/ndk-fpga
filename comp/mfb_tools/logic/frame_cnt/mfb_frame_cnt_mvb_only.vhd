-- mfb_frame_cnt_mvb_only.vhd: Wrapper of MFB frame counter with MVB only on the output
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MFB_FRAME_CNT_MVB_ONLY is
   generic(
      -- =================
      -- MFB configuration
      -- =================

      REGIONS         : natural := 1;
      REGION_SIZE     : natural := 8;
      BLOCK_SIZE      : natural := 8;
      ITEM_WIDTH      : natural := 8;
      OUTPUT_REG      : boolean := true;

      -- =====================
      -- Counter configuration
      -- =====================

      CNT_WIDTH       : natural := 64;
      AUTO_RESET      : boolean := true;
      -- "serial", "parallel"
      IMPLEMENTATION  : string  := "serial"
   );
      port(
      -- =================
      -- CLOCK AND RESET
      -- =================

      CLK           : in  std_logic;
      RST           : in  std_logic;

      -- =================
      -- RX MFB INTERFACE
      -- =================

      RX_DATA       : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_SOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF        : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF        : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY    : in  std_logic;
      RX_DST_RDY    : out std_logic;

      -- =================
      -- TX MFB INTERFACE
      -- =================

      -- alligned with original SOF, one cycle delayed when OUTPUT_REG is true
      TX_DATA       : out std_logic_vector(REGIONS*CNT_WIDTH-1 downto 0);
      TX_VLD        : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in  std_logic;

      -- =================
      -- TOTAL FRAME COUNTER
      -- =================

      FRAME_CNT     : out std_logic_vector(CNT_WIDTH-1 downto 0);
      FRAME_CNT_RST : in  std_logic
   );
end MFB_FRAME_CNT_MVB_ONLY;

architecture FULL of MFB_FRAME_CNT_MVB_ONLY is

  signal vld : std_logic_vector(REGIONS-1 downto 0);
  signal src_rdy, dst_rdy, vld_any : std_logic;

begin

  core: entity work.MFB_FRAME_CNT
  generic map (
    REGIONS         => REGIONS,
    REGION_SIZE     => REGION_SIZE,
    BLOCK_SIZE      => BLOCK_SIZE,
    ITEM_WIDTH      => ITEM_WIDTH,
    OUTPUT_REG      => OUTPUT_REG,
    CNT_WIDTH       => CNT_WIDTH,
    AUTO_RESET      => AUTO_RESET,
    IMPLEMENTATION  => IMPLEMENTATION
  ) port map (
    CLK           => CLK,
    RST           => RST,
    RX_DATA       => RX_DATA,
    RX_SOF_POS    => RX_SOF_POS,
    RX_EOF_POS    => RX_EOF_POS,
    RX_SOF        => RX_SOF,
    RX_EOF        => RX_EOF,
    RX_SRC_RDY    => RX_SRC_RDY,
    RX_DST_RDY    => RX_DST_RDY,
    TX_DATA       => open,
    TX_FRAME_NUM  => TX_DATA,
    TX_SOF_POS    => open,
    TX_EOF_POS    => open,
    TX_SOF        => vld,
    TX_EOF        => open,
    TX_SRC_RDY    => src_rdy,
    TX_DST_RDY    => dst_rdy,
    FRAME_CNT     => FRAME_CNT,
    FRAME_CNT_RST => FRAME_CNT_RST
  );
  vld_any <= OR vld;
  TX_VLD <= vld;
  TX_SRC_RDY <= src_rdy and vld_any;
  dst_rdy <= TX_DST_RDY or not vld_any;

end architecture;
