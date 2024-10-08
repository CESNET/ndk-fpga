-- data_transformer.vhd: Data transformation block for FrameLink Binder
-- Copyright (C) 2008 CESNET
-- Author(s):  Martin Kosek   <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
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
entity FLB_DATA_TRANSFORMER is
   generic(
      INPUT_WIDTH    : integer := 32;
      INPUT_COUNT    : integer := 2;  -- total count of input interfaces
      OUTPUT_WIDTH   : integer := 64;
      STATUS_WIDTH   : integer := 4;
      BLOCK_SIZE     : integer := 256;
      FRAME_PARTS    : integer := 2   -- number of parts in 1 frame
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- NFIFO2FIFO interface
      DATA_OUT       : in  std_logic_vector(INPUT_COUNT*(INPUT_WIDTH+(INPUT_WIDTH/8))-1 downto 0);
      DATA_VLD       : in  std_logic;
      BLOCK_ADDR     : out std_logic_vector(abs(log2(INPUT_COUNT)-1) downto 0);
      READ           : out std_logic;
      EMPTY          : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      STATUS         : in  std_logic_vector(log2(BLOCK_SIZE+1)*INPUT_COUNT-1 downto 0);

      -- Output data
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);

      -- Output block interface
      TX_STATUS      : out std_logic_vector(INPUT_COUNT*STATUS_WIDTH-1 downto 0);
      TX_EMPTY       : out std_logic_vector(INPUT_COUNT-1 downto 0);
      TX_IFC         : in  std_logic_vector(abs(log2(INPUT_COUNT))-1 downto 0);

      -- Other
      FRAME_DONE     : out std_logic_vector(INPUT_COUNT-1 downto 0)
   );
end entity FLB_DATA_TRANSFORMER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_DATA_TRANSFORMER is

   -- ------------------ Constants declaration --------------------------------
   constant WORD_COUNT        : integer := INPUT_COUNT;
   constant JUICE_WIDTH       : integer := minimum(INPUT_WIDTH/16, 4);
   -- memory word width
   constant IWORD_WIDTH       : integer := INPUT_WIDTH + (INPUT_WIDTH/8);
   constant FL_MEM_WIDTH      : integer := INPUT_COUNT * INPUT_WIDTH;

   -- ------------------ Types declaration ------------------------------------
   type t_juice_in         is array (0 to (WORD_COUNT-1)) of
                              std_logic_vector(JUICE_WIDTH-1 downto 0);

   -- ------------------ Signals declaration ----------------------------------

   -- decompressor signals
   signal decomp_sof_n     : std_logic;
   signal decomp_sop_n     : std_logic;
   signal decomp_eop_n     : std_logic;
   signal decomp_eof_n     : std_logic;
   signal decomp_src_rdy_n : std_logic;
   signal decomp_dst_rdy_n : std_logic;
   signal decomp_data      : std_logic_vector(FL_MEM_WIDTH-1 downto 0);
   signal decomp_rem       : std_logic_vector(log2(FL_MEM_WIDTH/8)-1 downto 0);
   signal fl_juice_in      : t_juice_in;
   signal fl_juice         : std_logic_vector(JUICE_WIDTH-1 downto 0);

   -- REM computer signals
   signal rem_sel          : std_logic_vector(WORD_COUNT-1 downto 0);
   signal rem_in           : std_logic_vector(WORD_COUNT*log2(INPUT_WIDTH/8)-1 downto 0);

   signal reg_data_invalid   : std_logic;
   signal reg_data_invalid_set : std_logic;
   signal reg_data_invalid_clr : std_logic;
   signal reg_first_word   : std_logic;
   signal reg_first_word_clr : std_logic;

   -- others
   signal sig_frame_done   : std_logic;
   signal data_valid_n     : std_logic;
   signal read_i           : std_logic;

begin
   -- directly mapped signals -------------------------------------------------
   data_valid_n      <= decomp_src_rdy_n or decomp_dst_rdy_n;
   sig_frame_done    <= not (decomp_eof_n or data_valid_n);

   reg_data_invalid_set <= not (decomp_eof_n or decomp_src_rdy_n or decomp_dst_rdy_n);
   reg_data_invalid_clr <= read_i;

   reg_first_word_clr <= read_i;

   -- decompress control
   decomp_src_rdy_n  <= not (DATA_VLD and not reg_data_invalid);

   -- Output interface signals mapping
   BLOCK_ADDR        <= TX_IFC;
   read_i            <= not decomp_dst_rdy_n and ((decomp_eof_n or reg_data_invalid or not DATA_VLD) or reg_first_word);
   READ              <= read_i;
   TX_EMPTY          <= EMPTY;

   GEN_STATUS_SIGNAL : for i in 0 to INPUT_COUNT-1 generate
      TX_STATUS((i+1)*STATUS_WIDTH-1 downto i*STATUS_WIDTH) <=
         STATUS((i+1)*log2(BLOCK_SIZE+1)-1 downto (i+1)*log2(BLOCK_SIZE+1)-STATUS_WIDTH);
   end generate;

   -- -------------------------------------------------------------------------
   --                         JUICE DECOMPRESSION
   -- -------------------------------------------------------------------------
   -- map decompressing unit
   OUTPUT_DECOMPRESSOR : entity work.fl_decompress
      generic map(
         WIRES          => JUICE_WIDTH,
         PARTS          => FRAME_PARTS
      )
      port map(
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- Transmit interface
         TX_SRC_RDY_N   => decomp_src_rdy_n,
         TX_DST_RDY_N   => decomp_dst_rdy_n,
         TX_SOP_N       => decomp_sop_n,
         TX_EOP_N       => decomp_eop_n,
         TX_SOF_N       => decomp_sof_n,
         TX_EOF_N       => decomp_eof_n,
         -- Compressed FL control signals
         FL_JUICE       => fl_juice,
         DISCARD        => '0',
         FRAME_PART     => '0'
      );

   -- map REM computing unit
   REM_COMPUTER : entity work.FLB_REM_CMP
      generic map(
         INPUT_WIDTH    => INPUT_WIDTH,
         OUTPUT_WIDTH   => FL_MEM_WIDTH,
         COUNT          => WORD_COUNT
      )
      port map(
         -- which REM is valid
         SEL            => rem_sel,
         INPUT_REMS     => rem_in,
         -- computed REM
         TX_REM         => decomp_rem
      );

   GEN_REM_CMP_IN : for i in 0 to WORD_COUNT-1 generate
      rem_sel(i) <= not DATA_OUT(i*IWORD_WIDTH +
         INPUT_WIDTH + log2(INPUT_WIDTH/8));
      rem_in((i+1)*log2(INPUT_WIDTH/8)-1 downto i*log2(INPUT_WIDTH/8))
         <= DATA_OUT(
         i*IWORD_WIDTH + INPUT_WIDTH + log2(INPUT_WIDTH/8)-1
         downto
         i*IWORD_WIDTH + INPUT_WIDTH);
   end generate;

   GEN_JUICE_IN : for i in 0 to WORD_COUNT-1 generate

      fl_juice_in(i) <=
         DATA_OUT(i*IWORD_WIDTH + INPUT_WIDTH + log2(INPUT_WIDTH/8) +
         JUICE_WIDTH - 1
         downto
         i*IWORD_WIDTH + INPUT_WIDTH + log2(INPUT_WIDTH/8));

   end generate;

   GEN_JUICE : for i in 0 to JUICE_WIDTH-1 generate

      juice_andp : process(fl_juice_in)
         variable and_int : std_logic;
      begin
         and_int := '1';

         for j in 0 to WORD_COUNT - 1 loop
            and_int := and_int and fl_juice_in(j)(i);
         end loop;
         fl_juice(i) <= and_int;
      end process;

   end generate;

   -- generate decompressed data ----------------------------------------------
   GEN_DATA : for i in 0 to WORD_COUNT-1 generate
      decomp_data((i+1)*INPUT_WIDTH-1 downto i*INPUT_WIDTH)
         <= DATA_OUT(i*IWORD_WIDTH + INPUT_WIDTH - 1 downto i*IWORD_WIDTH);
   end generate;

   -- mapping demultiplexer for FrameDone signal ------------------------------
   FRAME_DONE_DEMUX : entity work.GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => INPUT_COUNT
      )
      port map(
         DATA_IN(0)  => sig_frame_done,
         SEL         => TX_IFC,
         DATA_OUT    => FRAME_DONE
      );

   -- register reg_data_invalid
   reg_data_invalidp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_data_invalid <= '0';
         else
            if (reg_data_invalid_set = '1') then
               reg_data_invalid <= '1';
            elsif (reg_data_invalid_clr = '1') then
               reg_data_invalid <= '0';
            end if;
         end if;
      end if;
   end process;

   -- register reg_first_word
   reg_first_wordp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_first_word <= '1';
         else
            if (reg_first_word_clr = '1') then
               reg_first_word <= '0';
            end if;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                         OUTPUT TRANSFORMER
   -- -------------------------------------------------------------------------
   OUTPUT_TRANSFORMER : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH  => FL_MEM_WIDTH,
         TX_DATA_WIDTH  => OUTPUT_WIDTH
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- RX interface
         RX_SOF_N       => decomp_sof_n,
         RX_SOP_N       => decomp_sop_n,
         RX_EOP_N       => decomp_eop_n,
         RX_EOF_N       => decomp_eof_n,
         RX_SRC_RDY_N   => decomp_src_rdy_n,
         RX_DST_RDY_N   => decomp_dst_rdy_n,
         RX_DATA        => decomp_data,
         RX_REM         => decomp_rem,
         -- TX interface
         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM,
         TX_SOF_N       => TX_SOF_N,
         TX_EOF_N       => TX_EOF_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOP_N       => TX_EOP_N,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_DST_RDY_N   => TX_DST_RDY_N
      );

end architecture full;
