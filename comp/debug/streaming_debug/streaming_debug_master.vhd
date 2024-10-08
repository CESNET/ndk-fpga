-- streaming_debug_master.vhd: MI32 accesible collector and statistical unit for streaming data probes.
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity STREAMING_DEBUG_MASTER is
  generic (
    --! \brief Number of connected probes.
    CONNECTED_PROBES   : integer := 4;
    -- Number of MFB regions.
    REGIONS            : natural := 1;
    --! \brief Master debuging enable switch.
    --! \description True means full architecture implementation, false means empty architecture implementation.
    DEBUG_ENABLED      : boolean := false;
    --! \brief Selective enabling of monitoring of connected probes when master enable is true.
    --! \details Character 'E' or 'e' means enabled, each other character means disabled.
    --! String is red from left to right, one character for each interface numbered from 0.
    PROBE_ENABLED      : string := "EEEE";
    --! \brief Should counter of data words be available?
    COUNTER_WORD       : string := "EEEE";
    --! \brief Should counter of waiting cycles (not source nor destination ready) be available?
    COUNTER_WAIT       : string := "EEEE";
    --! \brief Should counter of cycles when source is ready and destination is not be available?
    COUNTER_DST_HOLD   : string := "EEEE";
    --! \brief Should counter of cycles when destination is ready and source is not be available?
    COUNTER_SRC_HOLD   : string := "EEEE";
    --! \brief Should counter of started transactions be available?
    COUNTER_SOP        : string := "EEEE";
    --! \brief Should counter of ended transactions be available?
    COUNTER_EOP        : string := "EEEE";
    --! \brief Should bus controll functionality be available?
    BUS_CONTROL        : string := "EEEE";
    --! \brief Text identificators for connected probes.
    --! \details Each probe name has precisely 4 characters.
    PROBE_NAMES        : string := "Int1Int2Int3Int4";
    --! \brief Use internal register on all DEBUG interface signals.
    DEBUG_REG          : boolean := false
  );
  port (
    --! \name CLOCK and RESET
    CLK         : in std_logic;
    RESET       : in std_logic;

    --! \name Input controll MI32 interface
    MI_DWR             : in  std_logic_vector(31 downto 0);
    MI_ADDR            : in  std_logic_vector(31 downto 0);
    MI_RD              : in  std_logic;
    MI_WR              : in  std_logic;
    MI_BE              : in  std_logic_vector(3 downto 0);
    MI_DRD             : out std_logic_vector(31 downto 0) := X"00000000";
    MI_ARDY            : out std_logic := '0';
    MI_DRDY            : out std_logic := '0';

    --! \name Multi-interface for connected streaming interfaces
    DEBUG_BLOCK        : out std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
    DEBUG_DROP         : out std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
    DEBUG_SRC_RDY      : in  std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
    DEBUG_DST_RDY      : in  std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
    DEBUG_SOP          : in  std_logic_vector(CONNECTED_PROBES*REGIONS-1 downto 0) := (others => '0');
    DEBUG_EOP          : in  std_logic_vector(CONNECTED_PROBES*REGIONS-1 downto 0) := (others => '0')
  );
end entity;

architecture full of STREAMING_DEBUG_MASTER is
  -- Functions converting enable character to reasonable types
  function enableChar2logic (c : character) return std_logic is
  begin
    if (c = 'E' or c = 'e') then
      return '1';
    end if;
    return '0';
  end function;
  function enableChar2bool (c : character) return boolean is
  begin
    if (c = 'E' or c = 'e') then
      return true;
    end if;
    return false;
  end function;

  -- Signals and types
  signal word_cnt          : u_array_t(CONNECTED_PROBES-1 downto 0)(64-1 downto 0);
  signal wait_cnt          : u_array_t(CONNECTED_PROBES-1 downto 0)(64-1 downto 0);
  signal dst_hold_cnt      : u_array_t(CONNECTED_PROBES-1 downto 0)(64-1 downto 0);
  signal src_hold_cnt      : u_array_t(CONNECTED_PROBES-1 downto 0)(64-1 downto 0);
  signal sop_cnt           : u_array_t(CONNECTED_PROBES-1 downto 0)(64-1 downto 0);
  signal eop_cnt           : u_array_t(CONNECTED_PROBES-1 downto 0)(64-1 downto 0);

  type d32_array_t is array(integer range <>) of std_logic_vector(31 downto 0);
  signal mi_drds           : d32_array_t(0 to CONNECTED_PROBES*16-1):=(others => (others => '0'));
  signal mi_wes            : std_logic_vector(CONNECTED_PROBES*16-1 downto 0);

  signal cnt_start         : std_logic_vector(CONNECTED_PROBES-1 downto 0);
  signal cnt_stop          : std_logic_vector(CONNECTED_PROBES-1 downto 0);
  signal cnt_running       : std_logic_vector(CONNECTED_PROBES-1 downto 0);

  signal line_block        : std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
  signal line_drop         : std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
  signal line_blocked      : std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
  signal line_droped       : std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');
  signal line_req          : std_logic_vector(CONNECTED_PROBES-1 downto 0) := (others => '0');

  signal reg_debug_block   : std_logic_vector(CONNECTED_PROBES-1 downto 0);
  signal reg_debug_drop    : std_logic_vector(CONNECTED_PROBES-1 downto 0);
  signal reg_debug_src_rdy : std_logic_vector(CONNECTED_PROBES-1 downto 0);
  signal reg_debug_dst_rdy : std_logic_vector(CONNECTED_PROBES-1 downto 0);
  signal reg_debug_sop     : slv_array_t(CONNECTED_PROBES-1 downto 0)(REGIONS-1 downto 0);
  signal reg_debug_eop     : slv_array_t(CONNECTED_PROBES-1 downto 0)(REGIONS-1 downto 0);

begin
  full_architecture_gen : if DEBUG_ENABLED generate

    -- Debug interface registers
    debug_reg_gen : if DEBUG_REG generate
      debug_reg : process(CLK)
      begin
        if rising_edge(CLK) then
          DEBUG_BLOCK <= reg_debug_block;
          DEBUG_DROP <= reg_debug_drop;
          reg_debug_src_rdy <= DEBUG_SRC_RDY;
          reg_debug_dst_rdy <= DEBUG_DST_RDY;
          reg_debug_sop <= slv_array_deser(DEBUG_SOP, CONNECTED_PROBES, REGIONS);
          reg_debug_eop <= slv_array_deser(DEBUG_EOP, CONNECTED_PROBES, REGIONS);
        end if;
      end process;
    end generate;
    debug_noreg_gen : if not DEBUG_REG generate
      DEBUG_BLOCK <= reg_debug_block;
      DEBUG_DROP <= reg_debug_drop;
      reg_debug_src_rdy <= DEBUG_SRC_RDY;
      reg_debug_dst_rdy <= DEBUG_DST_RDY;
      reg_debug_sop <= slv_array_deser(DEBUG_SOP, CONNECTED_PROBES, REGIONS);
      reg_debug_eop <= slv_array_deser(DEBUG_EOP, CONNECTED_PROBES, REGIONS);
    end generate;

    -- Address Decorder on MI interface
    MI_ARDY       <= MI_RD or MI_WR;
    read_data_reg : process (CLK)
    begin
      if rising_edge(CLK) then
        MI_DRD        <= mi_drds(to_integer(unsigned(MI_ADDR(log2(CONNECTED_PROBES)+5 downto 2))));
        MI_DRDY       <= MI_RD;
      end if;
    end process;
    mi_wr_dec : entity work.dec1fn_enable
      generic map (CONNECTED_PROBES*16)
      port map (MI_ADDR(log2(CONNECTED_PROBES)+5 downto 2), MI_WR, mi_wes);

    probes_stats_gen : for i in 0 to CONNECTED_PROBES-1 generate
      probe_enabled_gen : if enableChar2bool(PROBE_ENABLED(i+1)) generate
        -- Write data mapping for single probe
        cnt_start(i)  <= mi_wes(i*16+14) and MI_DWR(0);
        cnt_stop(i)   <= mi_wes(i*16+14) and not MI_DWR(0);
        line_block(i) <= MI_DWR(0) and not MI_DWR(1);
        line_drop(i)  <= MI_DWR(1) and not MI_DWR(0);
        line_req(i)   <= mi_wes(i*16+15);

        -- Read data mapping for single probe
        mi_drds(i*16+ 0) <= std_logic_vector(word_cnt(i)(31 downto 0));
        mi_drds(i*16+ 1) <= std_logic_vector(word_cnt(i)(63 downto 32));
        mi_drds(i*16+ 2) <= std_logic_vector(wait_cnt(i)(31 downto 0));
        mi_drds(i*16+ 3) <= std_logic_vector(wait_cnt(i)(63 downto 32));
        mi_drds(i*16+ 4) <= std_logic_vector(dst_hold_cnt(i)(31 downto 0));
        mi_drds(i*16+ 5) <= std_logic_vector(dst_hold_cnt(i)(63 downto 32));
        mi_drds(i*16+ 6) <= std_logic_vector(src_hold_cnt(i)(31 downto 0));
        mi_drds(i*16+ 7) <= std_logic_vector(src_hold_cnt(i)(63 downto 32));
        mi_drds(i*16+ 8) <= std_logic_vector(sop_cnt(i)(31 downto 0));
        mi_drds(i*16+ 9) <= std_logic_vector(sop_cnt(i)(63 downto 32));
        mi_drds(i*16+10) <= std_logic_vector(eop_cnt(i)(31 downto 0));
        mi_drds(i*16+11) <= std_logic_vector(eop_cnt(i)(63 downto 32));
        mi_drds(i*16+12) <= std_logic_vector(to_unsigned(character'pos(PROBE_NAMES(i*4+4)),8)) &
                            std_logic_vector(to_unsigned(character'pos(PROBE_NAMES(i*4+3)),8)) &
                            std_logic_vector(to_unsigned(character'pos(PROBE_NAMES(i*4+2)),8)) &
                            std_logic_vector(to_unsigned(character'pos(PROBE_NAMES(i*4+1)),8));
        mi_drds(i*16+13) <= X"000000" &
                            '1' &                              -- probe enabled
                            'X' &                              -- reserved
                            enableChar2logic(COUNTER_EOP(i+1)) &
                            enableChar2logic(COUNTER_SOP(i+1)) &
                            enableChar2logic(COUNTER_SRC_HOLD(i+1)) &
                            enableChar2logic(COUNTER_DST_HOLD(i+1)) &
                            enableChar2logic(COUNTER_WAIT(i+1)) &
                            enableChar2logic(COUNTER_WORD(i+1));
        mi_drds(i*16+14) <= X"0000000" & "000" & cnt_running(i);
        mi_drds(i*16+15) <= X"0000000" & "00"  & line_droped(i) & line_blocked(i);

        -- Counters enabled (running) register
        cnt_en_reg : process (CLK)
        begin
          if rising_edge(CLK) then
            if RESET='1' or cnt_start(i)='1' then
              cnt_running(i) <= '1';
            elsif cnt_stop(i)='1' then
              cnt_running(i) <= '0';
            end if;
          end if;
        end process;

        -- Line controlling registers
        bus_control_gen : if enableChar2bool(BUS_CONTROL(i+1)) generate
          line_ctrl_reg : process (CLK)
          begin
            if rising_edge(CLK) then
              if RESET='1' then
                line_blocked(i) <= '0';
                line_droped(i)  <= '0';
              elsif line_req(i)='1' then
                line_blocked(i) <= line_block(i);
                line_droped(i)  <= line_drop(i);
              end if;
            end if;
          end process;
        end generate;
        reg_debug_block(i) <= line_blocked(i);
        reg_debug_drop(i)  <= line_droped(i);

        -- Word counter
        word_cnt_gen : if enableChar2bool(COUNTER_WORD(i+1)) generate
          word_cnt_reg : process (CLK)
          begin
            if rising_edge(CLK) then
              if RESET='1' or cnt_start(i)='1' then
                word_cnt(i) <= (others => '0');
              elsif cnt_running(i)='1' and reg_debug_src_rdy(i)='1' and reg_debug_dst_rdy(i)='1' then
                word_cnt(i) <= word_cnt(i)+1;
              end if;
            end if;
          end process;
        end generate;
        -- Wait counter
        wait_cnt_gen : if enableChar2bool(COUNTER_WAIT(i+1)) generate
          wait_cnt_reg : process (CLK)
          begin
            if rising_edge(CLK) then
              if RESET='1' or cnt_start(i)='1' then
                wait_cnt(i) <= (others => '0');
              elsif cnt_running(i)='1' and reg_debug_src_rdy(i)='0' and reg_debug_dst_rdy(i)='0' then
                wait_cnt(i) <= wait_cnt(i)+1;
              end if;
            end if;
          end process;
        end generate;
        -- Destination hold counter
        dst_hold_cnt_gen : if enableChar2bool(COUNTER_DST_HOLD(i+1)) generate
          dst_hold_cnt_reg : process (CLK)
          begin
            if rising_edge(CLK) then
              if RESET='1' or cnt_start(i)='1' then
                dst_hold_cnt(i) <= (others => '0');
              elsif cnt_running(i)='1' and reg_debug_src_rdy(i)='1' and reg_debug_dst_rdy(i)='0' then
                dst_hold_cnt(i) <= dst_hold_cnt(i)+1;
              end if;
            end if;
          end process;
        end generate;
        -- Source hold counter
        src_hold_cnt_gen : if enableChar2bool(COUNTER_SRC_HOLD(i+1)) generate
          dst_hold_cnt_reg : process (CLK)
          begin
            if rising_edge(CLK) then
              if RESET='1' or cnt_start(i)='1' then
                src_hold_cnt(i) <= (others => '0');
              elsif cnt_running(i)='1' and reg_debug_src_rdy(i)='0' and reg_debug_dst_rdy(i)='1' then
                src_hold_cnt(i) <= src_hold_cnt(i)+1;
              end if;
            end if;
          end process;
        end generate;
        -- Start of transaction counter
        sop_cnt_gen : if enableChar2bool(COUNTER_SOP(i+1)) generate
          sop_cnt_reg : process (CLK)
            variable v_tmp_cnt : unsigned(log2(REGIONS+1)-1 downto 0);
          begin
            if rising_edge(CLK) then
              if RESET='1' or cnt_start(i)='1' then
                sop_cnt(i) <= (others => '0');
              elsif cnt_running(i)='1' and reg_debug_src_rdy(i)='1' and reg_debug_dst_rdy(i)='1' then
                v_tmp_cnt := (others => '0');
                for r in 0 to REGIONS-1 loop
                  v_tmp_cnt := v_tmp_cnt + reg_debug_sop(i)(r);
                end loop;
                sop_cnt(i) <= sop_cnt(i) + v_tmp_cnt;
              end if;
            end if;
          end process;
        end generate;
        -- End of transaction counter
        eop_cnt_gen : if enableChar2bool(COUNTER_EOP(i+1)) generate
          eop_cnt_reg : process (CLK)
            variable v_tmp_cnt : unsigned(log2(REGIONS+1)-1 downto 0);
          begin
            if rising_edge(CLK) then
              if RESET='1' or cnt_start(i)='1' then
                eop_cnt(i) <= (others => '0');
              elsif cnt_running(i)='1' and reg_debug_src_rdy(i)='1' and reg_debug_dst_rdy(i)='1' then
                v_tmp_cnt := (others => '0');
                for r in 0 to REGIONS-1 loop
                  v_tmp_cnt := v_tmp_cnt + reg_debug_eop(i)(r);
                end loop;
                eop_cnt(i) <= eop_cnt(i) + v_tmp_cnt;
              end if;
            end if;
          end process;
        end generate;
      end generate;
    end generate;

  end generate;

  empty_architecture_gen : if not DEBUG_ENABLED generate
    MI_DRD      <= X"00000000";
    MI_DRDY     <= '0';
    MI_ARDY     <= '0';
    DEBUG_BLOCK <= (others => '0');
    DEBUG_DROP  <= (others => '0');
  end generate;
end architecture;
