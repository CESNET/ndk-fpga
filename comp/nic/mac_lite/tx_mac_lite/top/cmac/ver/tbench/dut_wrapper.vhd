-- dut_wrapper.vhd: Wrapper of DUT
-- Copyright (C) 2017 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity DUT_WRAPPER is
   port(
      -- FRAME LINK UNALIGNED INTERFACE (FLU_CLK) ------------------------------
      FLU_CLK           : in  std_logic;
      FLU_RESET         : in  std_logic;
      RX_DATA           : in  std_logic_vector(511 downto 0);
      RX_SOP_POS        : in  std_logic_vector(2 downto 0);
      RX_EOP_POS        : in  std_logic_vector(5 downto 0);
      RX_SOP            : in  std_logic;
      RX_EOP            : in  std_logic;
      RX_SRC_RDY        : in  std_logic;
      RX_DST_RDY        : out std_logic;

      -- MI32 INTERFACE (MI_CLK) -----------------------------------------------
      MI_CLK            : in  std_logic;
      MI_RESET          : in  std_logic;
      MI_DWR            : in  std_logic_vector(31 downto 0);
      MI_ADDR           : in  std_logic_vector(31 downto 0);
      MI_RD             : in  std_logic;
      MI_WR             : in  std_logic;
      MI_BE             : in  std_logic_vector(3 downto 0);
      MI_DRD            : out std_logic_vector(31 downto 0);
      MI_ARDY           : out std_logic;
      MI_DRDY           : out std_logic;

      -- LBUS INTERFACE (CMAC_CLK) ---------------------------------------------
      CMAC_CLK          : in  std_logic;
      CMAC_RESET        : in  std_logic;
      TX_DATA           : out slv_array_t(4-1 downto 0)(128-1 downto 0);
      TX_SOP            : out std_logic_vector(4-1 downto 0);
      TX_EOP            : out std_logic_vector(4-1 downto 0);
      TX_MTY            : out slv_array_t(4-1 downto 0)(4-1 downto 0);
      TX_ENA            : out std_logic_vector(4-1 downto 0);
      TX_RDY            : in  std_logic
   );
end DUT_WRAPPER;

architecture FULL of DUT_WRAPPER is

   signal obuf_data    : std_logic_vector(511 downto 0);
   signal obuf_sof_pos : std_logic_vector(1 downto 0);
   signal obuf_eof_pos : std_logic_vector(5 downto 0);
   signal obuf_sof     : std_logic;
   signal obuf_eof     : std_logic;
   signal obuf_src_rdy : std_logic;
   signal obuf_dst_rdy : std_logic;

begin

   -- --------------------------------------------------------------------------
   --  OBUF
   -- --------------------------------------------------------------------------

   obuf_i: entity work.TX_MAC_LITE_CMAC
   port map (
      MI_CLK          => MI_CLK,
      MI_RESET        => MI_RESET,
      MI_DWR          => MI_DWR,
      MI_ADDR         => MI_ADDR,
      MI_BE           => MI_BE,
      MI_RD           => MI_RD,
      MI_WR           => MI_WR,
      MI_DRD          => MI_DRD,
      MI_ARDY         => MI_ARDY,
      MI_DRDY         => MI_DRDY,

      RX_CLK          => FLU_CLK,
      RX_CLK_X2       => FLU_CLK,
      RX_RESET        => FLU_RESET,
      RX_MFB_DATA     => RX_DATA,
      RX_MFB_SOF_POS  => RX_SOP_POS,
      RX_MFB_EOF_POS  => RX_EOP_POS,
      RX_MFB_SOF(0)   => RX_SOP,
      RX_MFB_EOF(0)   => RX_EOP,
      RX_MFB_SRC_RDY  => RX_SRC_RDY,
      RX_MFB_DST_RDY  => RX_DST_RDY,

      TX_CLK          => CMAC_CLK,
      TX_RESET        => CMAC_RESET,
      TX_MFB_DATA     => obuf_data,
      TX_MFB_SOF_POS  => obuf_sof_pos,
      TX_MFB_EOF_POS  => obuf_eof_pos,
      TX_MFB_SOF      => obuf_sof,
      TX_MFB_EOF      => obuf_eof,
      TX_MFB_SRC_RDY  => obuf_src_rdy,
      TX_MFB_DST_RDY  => obuf_dst_rdy,

      OUTGOING_FRAME  => open
   );

   -- --------------------------------------------------------------------------
   --  MFB TO LBUS
   -- --------------------------------------------------------------------------

   mfb2lbus_i : entity work.MFB2LBUS
   port map (
      CLK            => CMAC_CLK,
      RST            => CMAC_RESET,
      -- MFB RX INTERFACE
      RX_DATA        => obuf_data,
      RX_SOF_POS     => obuf_sof_pos,
      RX_EOF_POS     => obuf_eof_pos,
      RX_SOF         => obuf_sof,
      RX_EOF         => obuf_eof,
      RX_SRC_RDY     => obuf_src_rdy,
      RX_DST_RDY     => obuf_dst_rdy,
      -- MFB HEADER AND OTHERS RX SIGNALS
      RX_H_ERROR     => '0',
      RX_O_OVF       => open,
      RX_O_UNF       => open,
      -- LBUS TX INTERFACE
      TX_RDY         => TX_RDY,
      TX_OVF         => '0',
      TX_UNF         => '0',
      TX_DATA0       => TX_DATA(0),
      TX_DATA1       => TX_DATA(1),
      TX_DATA2       => TX_DATA(2),
      TX_DATA3       => TX_DATA(3),
      TX_MTY0        => TX_MTY(0),
      TX_MTY1        => TX_MTY(1),
      TX_MTY2        => TX_MTY(2),
      TX_MTY3        => TX_MTY(3),
      TX_ENA         => TX_ENA,
      TX_SOP         => TX_SOP,
      TX_EOP         => TX_EOP,
      TX_ERR         => open
   );

end architecture;
