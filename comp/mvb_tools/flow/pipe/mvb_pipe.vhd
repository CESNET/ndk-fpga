-- pipe.vhd: Multi-Value Bus pipeline
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;



entity MVB_PIPE is
  generic(
    ITEMS          : integer := 4; -- any possitive value
    ITEM_WIDTH     : integer := 8; -- any possitive value
    -- OPT of SHREG (SRL, VIVADO or REG)
    OPT            : string := "SRL";
    FAKE_PIPE      : boolean := false;
    USE_DST_RDY    : boolean := true;
    DEVICE         : string  := "7SERIES"
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_VLD        : in std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    TX_DATA       : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX_VLD        : out std_logic_vector(ITEMS-1 downto 0);
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic
  );
end entity;



architecture arch of MVB_PIPE is

  constant WORD_WIDTH        : integer := ITEMS * ITEM_WIDTH;
  constant PIPE_WIDTH        : integer := WORD_WIDTH + ITEMS;

  subtype PIPE_DATA          is natural range WORD_WIDTH+ITEMS-1 downto ITEMS;
  subtype PIPE_VLD           is natural range ITEMS-1 downto 0;

  signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
  signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);

begin

  -- RX/TX signals aggregations
  pipe_in_data(PIPE_DATA) <= RX_DATA;
  TX_DATA <= pipe_out_data(PIPE_DATA);
  pipe_in_data(PIPE_VLD) <= RX_VLD;
  TX_VLD <= pipe_out_data(PIPE_VLD);

  -- Real pipe implementation
  true_pipe_gen : if USE_DST_RDY generate
    pipe_core : entity work.PIPE
    generic map(
      DATA_WIDTH      => PIPE_WIDTH,
      USE_OUTREG      => not FAKE_PIPE,
      FAKE_PIPE       => FAKE_PIPE,
      OPT             => OPT,
      RESET_BY_INIT   => false,
      DEVICE          => DEVICE
    ) port map(
      CLK         => CLK,
      RESET       => RESET,
      IN_DATA      => pipe_in_data,
      IN_SRC_RDY   => RX_SRC_RDY,
      IN_DST_RDY   => RX_DST_RDY,
      OUT_DATA     => pipe_out_data,
      OUT_SRC_RDY  => TX_SRC_RDY,
      OUT_DST_RDY  => TX_DST_RDY
    );
  end generate;

  -- Register only implementation
  simple_pipe_gen : if not USE_DST_RDY generate
    RX_DST_RDY <= '1';
    fake_gen : if FAKE_PIPE generate
      TX_SRC_RDY <= RX_SRC_RDY;
      pipe_out_data <= pipe_in_data;
    end generate;
    full_gen : if not FAKE_PIPE generate
      pipe_core : process(CLK)
      begin
        if CLK'event and CLK='1' then
          if RESET='1' then
            TX_SRC_RDY <= '0';
          else
            TX_SRC_RDY <= RX_SRC_RDY;
          end if;
          pipe_out_data <= pipe_in_data;
        end if;
      end process;
    end generate;
  end generate;

end architecture;
