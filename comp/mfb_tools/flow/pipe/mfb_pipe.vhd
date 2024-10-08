-- pipe.vhd: Multi-Frame Bus pipeline
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

-- Component for pipelining MFB data paths with source and destination ready signals.
-- Compatible with Xilinx and Intel FPGAs.
entity MFB_PIPE is
  generic(
    -- =============================
    -- Bus parameters
    --
    -- Frame size restrictions: none
    -- =============================

    -- any possitive value
    REGIONS        : integer := 4;
    -- any possitive value
    REGION_SIZE    : integer := 8;
    -- any possitive value
    BLOCK_SIZE     : integer := 8;
    -- any possitive value
    ITEM_WIDTH     : integer := 8;
    -- any possitive value
    META_WIDTH     : integer := 0;

    -- =============================
    -- Others
    -- =============================

    FAKE_PIPE      : boolean := false;
    USE_DST_RDY    : boolean := true;
    -- "SHREG" or "REG"
    PIPE_TYPE      : string  := "SHREG";
    DEVICE         : string  := "7SERIES"
  );
  port(
      -- =============================
      -- Clock and Reset
      -- =============================

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- =============================
      -- MFB input interface
      -- =============================

      RX_DATA       : in std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META       : in std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
      RX_SOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF        : in std_logic_vector(REGIONS-1 downto 0);
      RX_EOF        : in std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- =============================
      -- MFB output interface
      -- =============================

      TX_DATA       : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META       : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF        : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF        : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity;



architecture arch of MFB_PIPE is

  constant WORD_WIDTH        : integer := REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
  constant SOF_POS_WIDTH     : integer := REGIONS * log2(REGION_SIZE);
  constant EOF_POS_WIDTH     : integer := REGIONS * log2(REGION_SIZE * BLOCK_SIZE);
  constant META_WORD_WIDTH   : integer := REGIONS * META_WIDTH;
  constant PIPE_WIDTH        : integer := WORD_WIDTH + META_WORD_WIDTH + SOF_POS_WIDTH + EOF_POS_WIDTH + REGIONS + REGIONS;

  subtype PIPE_DATA          is natural range WORD_WIDTH+META_WORD_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS-1 downto META_WORD_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS;
  subtype PIPE_META          is natural range META_WORD_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS-1 downto SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS;
  subtype PIPE_SOF_POS       is natural range SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS-1 downto EOF_POS_WIDTH+REGIONS+REGIONS;
  subtype PIPE_EOF_POS       is natural range EOF_POS_WIDTH+REGIONS+REGIONS-1 downto REGIONS+REGIONS;
  subtype PIPE_SOF           is natural range REGIONS+REGIONS-1 downto REGIONS;
  subtype PIPE_EOF           is natural range REGIONS-1 downto 0;

  signal pipe_in_data        : std_logic_vector(PIPE_WIDTH-1 downto 0);
  signal pipe_out_data       : std_logic_vector(PIPE_WIDTH-1 downto 0);

begin

  -- RX/TX signals aggregations
  pipe_in_data(PIPE_DATA) <= RX_DATA;
  TX_DATA <= pipe_out_data(PIPE_DATA);
  sof_gen : if SOF_POS_WIDTH > 0 generate
    pipe_in_data(PIPE_SOF_POS) <= RX_SOF_POS;
    TX_SOF_POS <= pipe_out_data(PIPE_SOF_POS);
  end generate;
  empty_sof_gen : if SOF_POS_WIDTH = 0 generate
    TX_SOF_POS <= (others => '0');
  end generate;
  eof_gen : if EOF_POS_WIDTH > 0 generate
    pipe_in_data(PIPE_EOF_POS) <= RX_EOF_POS;
    TX_EOF_POS <= pipe_out_data(PIPE_EOF_POS);
  end generate;
  empty_eof_gen : if EOF_POS_WIDTH = 0 generate
    TX_EOF_POS <= (others => '0');
  end generate;
  meta_gen : if META_WIDTH > 0 generate
    pipe_in_data(PIPE_META) <= RX_META;
    TX_META <= pipe_out_data(PIPE_META);
  end generate;
  empty_meta_gen : if META_WIDTH = 0 generate
    TX_META <= (others => '0');
  end generate;
  pipe_in_data(PIPE_SOF) <= RX_SOF;
  TX_SOF <= pipe_out_data(PIPE_SOF);
  pipe_in_data(PIPE_EOF) <= RX_EOF;
  TX_EOF <= pipe_out_data(PIPE_EOF);

  -- Real pipe implementation
  true_pipe_gen : if USE_DST_RDY generate
    pipe_core : entity work.PIPE
    generic map(
      DATA_WIDTH      => PIPE_WIDTH,
      USE_OUTREG      => not FAKE_PIPE,
      FAKE_PIPE       => FAKE_PIPE,
      PIPE_TYPE       => PIPE_TYPE,
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
