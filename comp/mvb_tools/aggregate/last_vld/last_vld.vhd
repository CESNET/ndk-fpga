-- last_vld.vhd: Last valid item aggregation of Multi-Value Bus
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;

use work.math_pack.all;



entity MVB_AGGREGATE_LAST_VLD is
  generic(
    ITEMS          : integer := 4; -- any possitive value
    ITEM_WIDTH     : integer := 8; -- any possitive value
    IMPLEMENTATION : string := "serial"; -- "serial", "parallel", "prefixsum"
    INTERNAL_REG   : boolean := true; -- when true, REG_* ports are unused and word register is internally implemented
    RESET_DATA     : boolean := false -- when true, the RESET signal also resets data, not just valid (only when INTERNAL_REG=true)
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_VLD        : in std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    REG_IN_DATA   : in std_logic_vector(ITEM_WIDTH-1 downto 0);
    REG_IN_VLD    : in std_logic;
    REG_OUT_DATA  : out std_logic_vector(ITEM_WIDTH-1 downto 0);
    REG_OUT_VLD   : out std_logic;
    REG_OUT_WR    : out std_logic;

    TX_DATA         : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0); -- starting from: REG_IN + RX_DATA[0]
    TX_VLD          : out std_logic_vector(ITEMS-1 downto 0);
    TX_PRESCAN_DATA : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0); -- starting from: REG_IN
    TX_PRESCAN_VLD  : out std_logic_vector(ITEMS-1 downto 0);
    TX_SRC_RDY      : out std_logic;
    TX_DST_RDY      : in std_logic
  );
end entity;



architecture arch of MVB_AGGREGATE_LAST_VLD is

  type item_t is record
    value : std_logic_vector(ITEM_WIDTH-1 downto 0);
    valid : std_logic;
  end record;
  type item_array_t is array (natural range <>) of item_t;
  type item_matrix_t is array (natural range<>, natural range<>) of item_t;

  -- Select last valid from 2
  function "+"(A, B: item_t) return item_t is
  begin
    if B.valid = '1' then
      return B;
    else
      return A;
    end if;
  end function;

  signal rx, tx : item_array_t(0 to ITEMS);

begin

  -- Timing signaling connections
  TX_SRC_RDY <= RX_SRC_RDY;
  RX_DST_RDY <= TX_DST_RDY;

  -- Inter Word Register
  internal_reg_gen: if INTERNAL_REG generate
    signal reg : item_t;
    signal ce : std_logic;
  begin
    reset_data_gen : if RESET_DATA generate
      word_reg : process(CLK)
      begin
        if CLK'event and CLK='1' then
          if RESET='1' then
            reg.valid <= '0';
            reg.value <= (others => '0');
          elsif ce='1' then
            reg.valid <= tx(ITEMS).valid;
            reg.value <= tx(ITEMS).value;
          end if;
        end if;
      end process;
    else generate
      word_reg : process(CLK)
      begin
        if CLK'event and CLK='1' then
          if RESET='1' then
            reg.valid <= '0';
          elsif ce='1' then
            reg.valid <= tx(ITEMS).valid;
          end if;
          if ce='1' then
            reg.value <= tx(ITEMS).value;
          end if;
        end if;
      end process;
    end generate;
    rx(0) <= reg;
    REG_OUT_DATA <= (others => '0');
    REG_OUT_VLD <= '0';
    REG_OUT_WR <= '0';
    ce <= RX_SRC_RDY and TX_DST_RDY;
  end generate;
  external_reg_gen : if not INTERNAL_REG generate
    rx(0).value <= REG_IN_DATA;
    rx(0).valid <= REG_IN_VLD;
    REG_OUT_DATA <= tx(ITEMS).value;
    REG_OUT_VLD <= tx(ITEMS).valid;
    REG_OUT_WR <= RX_SRC_RDY and TX_DST_RDY;
  end generate;

  -- Data connections
  data_connect_gen : for i in 0 to ITEMS-1 generate
    rx(i+1).value <= RX_DATA((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH);
    rx(i+1).valid <= RX_VLD(i);
    TX_DATA((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH) <= tx(i+1).value;
    TX_VLD(i) <= tx(i+1).valid;
    TX_PRESCAN_DATA((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH) <= tx(i).value;
    TX_PRESCAN_VLD(i) <= tx(i).valid;
  end generate;


  -- CORE IMPLEMENTATION -------------------------------------------------------

  serial_gen : if IMPLEMENTATION = "serial" generate
    tx(0) <= rx(0);
    pipeline_gen : for i in 1 to ITEMS generate
      tx(i) <= tx(i-1) + rx(i);
    end generate;
  end generate;

  parallel_gen : if IMPLEMENTATION = "parallel" generate
    signal data : std_logic_vector((ITEMS+1)*ITEM_WIDTH-1 downto 0);
    signal vld : std_logic_vector(ITEMS downto 0);
  begin
    data <= RX_DATA & rx(0).value;
    vld <= RX_VLD & rx(0).valid;
    units_gen : for i in 0 to ITEMS generate
      sum : entity work.GEN_MUX_ONEHOT
        generic map(ITEM_WIDTH, i+1)
        port map(data((i+1)*ITEM_WIDTH-1 downto 0), vld(i downto 0), tx(i).value);
      tx(i).valid <= or_reduce(vld(i downto 0));
    end generate;
  end generate;

  prefixsum_gen : if IMPLEMENTATION = "prefixsum" generate
    constant UP_STEPS : integer := log2(ITEMS+2)-1;
    constant DOWN_STEPS : integer := log2((ITEMS+4)/3);
    constant STEPS : integer := UP_STEPS + DOWN_STEPS;
    signal st : item_matrix_t(0 to STEPS, 0 to ITEMS);
  begin
    input_gen : for i in 0 to ITEMS generate
      st(0,i) <= rx(i);
    end generate;
    up_gen : for s in 1 to UP_STEPS generate
      constant LEFT_INDEX : integer := 2**(s-1);
      constant PLUS_INTERVAL : integer := 2**s;
    begin
      step_gen : for i in 0 to ITEMS generate
        constant USE_PLUS : boolean := ((i+1) mod PLUS_INTERVAL) = 0;
      begin
        wire_gen : if not USE_PLUS generate
          st(s,i) <= st(s-1,i);
        end generate;
        plus_gen : if USE_PLUS generate
          st(s,i) <= st(s-1,i-LEFT_INDEX) + st(s-1,i);
        end generate;
      end generate;
    end generate;
    down_gen : for s in UP_STEPS+1 to STEPS generate
      constant LEFT_INDEX : integer := 2**(STEPS-s);
      constant PLUS_INTERVAL : integer := 2**(STEPS-s+1);
    begin
      step_gen : for i in 0 to ITEMS generate
        constant USE_PLUS : boolean := ((i mod PLUS_INTERVAL) = LEFT_INDEX-1) and (i >= PLUS_INTERVAL);
      begin
        wire_gen : if not USE_PLUS generate
          st(s,i) <= st(s-1,i);
        end generate;
        plus_gen : if USE_PLUS generate
          st(s,i) <= st(s-1,i-LEFT_INDEX) + st(s-1,i);
        end generate;
      end generate;
    end generate;
    output_gen : for i in 0 to ITEMS generate
      tx(i) <= st(STEPS,i);
    end generate;
  end generate;

end architecture;
