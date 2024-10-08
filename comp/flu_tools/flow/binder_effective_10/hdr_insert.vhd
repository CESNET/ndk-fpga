--
-- flua_header_insert.vhd: Header insert component for Frame Link Unaligned (ALIGNED)
-- Copyright (C) 2014 CESNET
-- Author: Tomas Zavodnik <zavodnik@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
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
entity FLUA_HEADER_INSERT is
   generic(
      --! FLU configuration
      DATA_WIDTH    : integer:= 512;
      SOP_POS_WIDTH : integer:= 3;

      --! Enable/Disable header insertion
      --!   false - Disable Header insertion
      --!   true  - Enable Header insertion
      HDR_ENABLE    : boolean := true;
      --! Widht of the header (multiple of 8)
      HDR_WIDTH     : integer := 128;

      -- Pipeline Config ------------------------
      -- Use input pipe
      OUT_PIPE_EN   : boolean := false
   );
   port(
       --! \name  Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      --! \name Frame Link Unaligned (ALIGNED) input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      --! \name Header input interface
      RX_HDR_DATA       : in std_logic_vector(HDR_WIDTH-1 downto 0);
      RX_HDR_SRC_RDY    : in std_logic;
      RX_HDR_DST_RDY    : out std_logic;

      --! \name Frame Link Unaligned (ALIGNED) output interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity;

architecture FULL of FLUA_HEADER_INSERT is

   constant OUT_PIPE_DISABLE : boolean := not(OUT_PIPE_EN);

   signal rx_src_rdy_in   : std_logic;

   signal rx_data_pipe    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_sop_pos_pipe : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal rx_eop_pos_pipe : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal rx_sop_pipe     : std_logic;
   signal rx_eop_pipe     : std_logic;
   signal rx_src_rdy_pipe : std_logic;
   signal rx_dst_rdy_pipe : std_logic;

   signal rx_dst_rdy_out  : std_logic;

   signal rx_data_hw_r    : std_logic_vector(HDR_WIDTH-1 downto 0);
   signal rx_eop_overflow : std_logic;
   signal rx_eop_insert_r : std_logic := '0';
   signal rx_eop_pos_r    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

begin

   HEAD_INS_T_GEN: if (HDR_ENABLE = true) generate
      rx_src_rdy_in <= RX_SRC_RDY and (not(RX_SOP) or RX_HDR_SRC_RDY);

      RX_DATA_LW_R_P: process(CLK)
      begin
         if (CLK'event) and (CLK = '1') then
            if (rx_src_rdy_in = '1') and (rx_dst_rdy_out = '1') then
               rx_data_hw_r <= RX_DATA(DATA_WIDTH-1 downto DATA_WIDTH-HDR_WIDTH);
            end if;
         end if;
      end process;

      rx_eop_overflow <= '1' when (RX_EOP_POS >= (DATA_WIDTH/8 - HDR_WIDTH/8)) else '0';

      RX_EOP_INSERT_R_P: process(CLK)
      begin
         if (CLK'event) and (CLK = '1') then
            if (RESET = '1') then
               rx_eop_insert_r <= '0';
            elsif (rx_src_rdy_pipe = '1') and (rx_dst_rdy_pipe = '1') then
               rx_eop_insert_r <= RX_EOP and rx_eop_overflow and not(rx_eop_insert_r);
            end if;
         end if;
      end process;

      RX_EOP_POS_R_P: process(CLK)
      begin
         if (CLK'event) and (CLK = '1') then
            if (rx_src_rdy_pipe = '1') and (rx_dst_rdy_pipe = '1') then
               rx_eop_pos_r <= RX_EOP_POS;
            end if;
         end if;
      end process;

      rx_data_pipe(DATA_WIDTH-1 downto HDR_WIDTH) <= RX_DATA(DATA_WIDTH-HDR_WIDTH-1 downto 0);
      rx_data_pipe(HDR_WIDTH-1 downto 0) <= RX_HDR_DATA when ((RX_SOP = '1') and (rx_eop_insert_r = '0')) else rx_data_hw_r;

      rx_sop_pos_pipe <= RX_SOP_POS;
      rx_eop_pos_pipe <= (RX_EOP_POS + HDR_WIDTH/8) when (rx_eop_insert_r = '0') else (rx_eop_pos_r - (DATA_WIDTH/8 - HDR_WIDTH/8));

      rx_sop_pipe <= RX_SOP and not(rx_eop_insert_r);
      rx_eop_pipe <= (RX_EOP and not(rx_eop_overflow)) or rx_eop_insert_r;

      rx_src_rdy_pipe <= rx_src_rdy_in or rx_eop_insert_r;
      rx_dst_rdy_out  <= rx_dst_rdy_pipe and rx_src_rdy_in and not(rx_eop_insert_r);

      RX_DST_RDY      <= rx_dst_rdy_out;
      RX_HDR_DST_RDY  <= rx_dst_rdy_out and RX_SOP;
   end generate;

   HEAD_INS_F_GEN: if (HDR_ENABLE = false) generate
      rx_data_pipe <= RX_DATA;

      rx_sop_pos_pipe <= RX_SOP_POS;
      rx_eop_pos_pipe <= RX_EOP_POS;

      rx_sop_pipe <= RX_SOP;
      rx_eop_pipe <= RX_EOP;

      rx_src_rdy_pipe <= RX_SRC_RDY;
      RX_DST_RDY      <= rx_dst_rdy_pipe;

      RX_HDR_DST_RDY <= '1';
   end generate;

   --! \brief Output data pipeline
   OUT_DATA_PIPE_I:entity work.FLU_PIPE
   generic map(
      -- FrameLinkUnaligned Data Width
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      USE_OUTREG     => true,
      FAKE_PIPE      => OUT_PIPE_DISABLE
   )
   port map(
      -- Common interface
      CLK            => CLK,
      RESET          => RESET,

      -- Input interface
      RX_DATA       => rx_data_pipe,
      RX_SOP_POS    => rx_sop_pos_pipe,
      RX_EOP_POS    => rx_eop_pos_pipe,
      RX_SOP        => rx_sop_pipe,
      RX_EOP        => rx_eop_pipe,
      RX_SRC_RDY    => rx_src_rdy_pipe,
      RX_DST_RDY    => rx_dst_rdy_pipe,

      -- Output interface
      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY,

      -- Debuging interface ---------------------------------------------------
      DEBUG_BLOCK     => open,
      DEBUG_DROP      => open,
      DEBUG_SRC_RDY   => open,
      DEBUG_DST_RDY   => open,
      DEBUG_SOP       => open,
      DEBUG_EOP       => open
   );

end architecture;

