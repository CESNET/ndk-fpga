-- mfb_enabler.vhd: Enabler for MFB without destination ready
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--  Description
-- =========================================================================

-- This component enables sending of MFB frames to the output.
-- For this purpose, it uses the :vhdl:portsignal:`TX_ENABLE <enabler.tx_enable>` port.
-- Enabling starts from the first SOF.
-- Disabling starts from the last EOF in the current word.
-- If this happens in the middle of a frame then all following words are sent until the EOF is found.
-- If in this word is/are other complete frame/s then it/they are sent as well.
-- If this happens when outside of a frame then at least the next frame (can be more) in the first following valid word is still sent to the output.
-- The following packets are discarded.
-- For indication of the region in which discarded frame ends, there is a flag :vhdl:portsignal:`STAT_DISCARDED <enabler.stat_discarded>`.
--
entity MFB_ENABLER is
   generic(
      -- =======================================================================
      -- MFB CONFIGURATION:
      -- =======================================================================

      REGIONS     : natural := 4;   -- any possitive value
      REGION_SIZE : natural := 8;   -- any possitive value
      BLOCK_SIZE  : natural := 8;   -- any possitive value
      ITEM_WIDTH  : natural := 8;   -- any possitive value
      META_WIDTH  : natural := 8;   -- any possitive value
      OUTPUT_REG  : boolean := true -- only for TX MFB interface, not for STAT
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================

      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- =======================================================================
      -- INPUT INTERFACE OF MFB PLUS
      -- =======================================================================

      RX_DATA        : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META        : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      RX_SOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF         : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF         : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY     : in  std_logic;

      -- =======================================================================
      -- TX MFB PLUS INTERFACE WITH ENABLE
      -- =======================================================================

      TX_DATA        : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META        : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF         : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF         : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY     : out std_logic;
      -- Enable the MFB stream starting with the next frame.
      -- Disable the MFB stream after the last complete frame.
      TX_ENABLE      : in  std_logic;

      -- =======================================================================
      -- OUTPUT INTERFACE OF STATISTICS
      -- =======================================================================

      -- Flag of discarded frame for each region.
      -- Valid with EOF.
      STAT_DISCARDED : out std_logic_vector(REGIONS-1 downto 0)
   );
end MFB_ENABLER;

architecture FULL of MFB_ENABLER is

   constant SOF_POS_LOW_GND : std_logic_vector(log2(BLOCK_SIZE)-1 downto 0) := (others=>'0');
   constant SOF_POS_SIZE    : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_SIZE    : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

   type fsm_states is (st_stop, st_run);

   signal s_some_sof             : std_logic;
   signal s_some_eof             : std_logic;

   signal s_sof_pos_wid          : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_eof_pos              : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_sof_before_eof       : std_logic_vector(REGIONS-1 downto 0);

   signal s_sof_mask_after_leof  : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_mask_before_fsof : std_logic_vector(REGIONS-1 downto 0);

   signal s_sof_masked           : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_masked           : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_fsm              : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_fsm              : std_logic_vector(REGIONS-1 downto 0);
   signal s_valid                : std_logic;

   signal s_discarded_frame      : std_logic_vector(REGIONS-1 downto 0);

   signal s_curr_state           : fsm_states;
   signal s_next_state           : fsm_states;

begin

   s_some_sof <= (or RX_SOF) and RX_SRC_RDY;
   s_some_eof <= (or RX_EOF) and RX_SRC_RDY;

   -- SOF is before EOF, position of SOF is smaller than of EOF
   sof_before_eof_g : if REGION_SIZE > 1 generate
      sof_befor_eof_g : for r in 0 to REGIONS-1 generate
         s_sof_pos_wid(r)    <= RX_SOF_POS((r+1)*SOF_POS_SIZE-1 downto r*SOF_POS_SIZE) & SOF_POS_LOW_GND;
         s_eof_pos(r)        <= RX_EOF_POS((r+1)*EOF_POS_SIZE-1 downto r*EOF_POS_SIZE);
         s_sof_before_eof(r) <= '1' when (unsigned(s_sof_pos_wid(r)) < unsigned(s_eof_pos(r))) else '0';
      end generate;
   end generate;

   sof_before_eof_rs1_g : if REGION_SIZE = 1 generate
      s_sof_before_eof <= (others=>'1');
   end generate;

   -- Mask of SOF after last EOF
   sof_mask_after_leof_p : process (RX_EOF, s_sof_before_eof)
   begin
      s_sof_mask_after_leof <= (others => '1');
      for r in REGIONS-1 downto 0 loop
         if (RX_EOF(r) = '1') then
            if (s_sof_before_eof(r) = '0') then
               s_sof_mask_after_leof(r) <= '0';
            end if;
            exit;
         else
            s_sof_mask_after_leof(r) <= '0';
         end if;
      end loop;
   end process;

   -- Mask of EOF before first SOF
   eof_mask_before_fsof_p : process (RX_SOF, s_sof_before_eof)
   begin
      s_eof_mask_before_fsof <= (others => '1');
      for r in 0 to REGIONS-1 loop
         if (RX_SOF(r) = '1') then
            if (s_sof_before_eof(r) = '0') then
               s_eof_mask_before_fsof(r) <= '0';
            end if;
            exit;
         else
            s_eof_mask_before_fsof(r) <= '0';
         end if;
      end loop;
   end process;

   -- Masking SOF and EOF
   s_sof_masked <= RX_SOF and s_sof_mask_after_leof;
   s_eof_masked <= RX_EOF and s_eof_mask_before_fsof;

   -- ==========================================================================
   -- FSM CURRENT STATE REGISTER
   -- ==========================================================================

   current_state_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_curr_state <= st_stop;
         else
            s_curr_state <= s_next_state;
         end if;
      end if;
   end process;

   -- ==========================================================================
   -- FSM NEXT STATE LOGIC
   -- ==========================================================================

   next_state_logic_p : process (s_curr_state, TX_ENABLE, s_some_sof, s_some_eof)
   begin
      case (s_curr_state) is
         -- st_stop
         when st_stop =>
            if (TX_ENABLE = '1' and s_some_sof = '1') then
               s_next_state <= st_run;
            else
               s_next_state <= st_stop;
            end if;

         -- st_run
         when st_run =>
            if (TX_ENABLE = '0' and s_some_eof = '1') then
               s_next_state <= st_stop;
            else
               s_next_state <= st_run;
            end if;

         -- other states
         when others =>
            s_next_state <= st_stop;

      end case;
   end process;

   -- ==========================================================================
   -- FSM OUTPUT LOGIC
   -- ==========================================================================

   output_logic_p : process (s_curr_state, TX_ENABLE, RX_SOF, RX_EOF,
      RX_SRC_RDY, s_some_sof, s_some_eof, s_sof_masked, s_eof_masked)
   begin
      case (s_curr_state) is
         -- st_stop
         when st_stop =>
            s_sof_fsm <= RX_SOF;
            s_eof_fsm <= s_eof_masked;
            s_valid   <= '0';
            if (TX_ENABLE = '1' and s_some_sof = '1') then
               s_valid <= RX_SRC_RDY;
            end if;

         -- st_run
         when st_run =>
            s_sof_fsm <= RX_SOF;
            s_eof_fsm <= RX_EOF;
            s_valid   <= RX_SRC_RDY;
            if (TX_ENABLE = '0' and s_some_eof = '1') then
               s_sof_fsm <= s_sof_masked;
            end if;

         -- other states
         when others =>
            s_sof_fsm <= RX_SOF;
            s_eof_fsm <= RX_EOF;
            s_valid   <= '0';
      end case;
   end process;

   -- ==========================================================================
   -- DISCARDED FRAME FOR STATISTIC ONLY
   -- ==========================================================================

   -- Discarded frame
    process(all)
    begin
        for r in 0 to REGIONS-1 loop
          s_discarded_frame(r) <= (RX_EOF(r) and not s_eof_fsm(r) and s_valid and not RESET) or
                              (RX_EOF(r) and RX_SRC_RDY and not s_valid and not RESET);
        end loop;
    end process;

   -- ==========================================================================
   -- OUTPUT REGISTERS
   -- ==========================================================================

   -- statistics register is not optional due to better timming
   stat_discarded_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         STAT_DISCARDED <= s_discarded_frame;
      end if;
   end process;

   -- output mfb register is optional
   tx_reg_g : if OUTPUT_REG generate
      tx_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            TX_DATA    <= RX_DATA;
            TX_META    <= RX_META;
            TX_SOF_POS <= RX_SOF_POS;
            TX_EOF_POS <= RX_EOF_POS;
            TX_SOF     <= s_sof_fsm;
            TX_EOF     <= s_eof_fsm;
         end if;
      end process;

      tx_vld_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               TX_SRC_RDY <= '0';
            else
               TX_SRC_RDY <= s_valid;
            end if;
         end if;
      end process;
   end generate;

   no_tx_reg_g : if not OUTPUT_REG generate
      TX_DATA    <= RX_DATA;
      TX_META    <= RX_META;
      TX_SOF_POS <= RX_SOF_POS;
      TX_EOF_POS <= RX_EOF_POS;
      TX_SOF     <= s_sof_fsm;
      TX_EOF     <= s_eof_fsm;
      TX_SRC_RDY <= s_valid;
   end generate;

end architecture;
