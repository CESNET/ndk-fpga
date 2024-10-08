-- flu_multiplexer_dsp.vhd
--!
--! \brief FLU light-weight multiplexer which is made out of DSP multiplexers
--! \author Pavel Benacek <benacek@cesnet.cz>
--! \date 2015
--!
--! \section License
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU_MULTIPLEXER_DSP is
   generic(
      --! \brief Data width of the Multiplexer
      DATA_WIDTH    : integer := 512;
      --! \brief Width of the SOP_POS bus
      SOP_POS_WIDTH : integer := 3;
      --! \brief Number of input ports
      INPUT_PORTS   : integer := 8;

      --! Input pipeline registers (0, 1)
      REG_IN      : integer := 1;
      --! Output pipeline registers (0, 1)
      REG_OUT     : integer := 1;
      --! Pipeline between muxs levels (0, 1)
      REG_LVL     : integer := 1
   );
   port(
      -- --------------------------------------------------
      --! \name Common interface
      -- --------------------------------------------------
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- --------------------------------------------------
      --! \name Selection interface
      -- --------------------------------------------------
      --! Select input
      SEL            : in std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
      --! Confirmation of selected input
      SEL_RDY        : in std_logic;
      --! Ready to get new request
      SEL_NEXT       : out std_logic;

      -- --------------------------------------------------
      --! \name Frame Link Unaligned input interfaces
      -- --------------------------------------------------
      RX_DATA       : in std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_EOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);

      -- --------------------------------------------------
      --! \name Frame Link Unaligned concentrated interface
      -- --------------------------------------------------
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLU_MULTIPLEXER_DSP is
   --! Width of the input MUX word
   constant SOP_WIDTH      : integer := 1;
   constant EOP_WIDTH      : integer := 1;
   constant SRC_RDY_WIDTH  : integer := 1;
   constant EOP_POS_WIDTH  : integer := log2(DATA_WIDTH/8);
   constant MUX_DATA_WIDTH : integer := DATA_WIDTH + SOP_POS_WIDTH + EOP_POS_WIDTH +
                                        SOP_WIDTH + EOP_WIDTH + SRC_RDY_WIDTH;
   --! Helping ranges (to accomodate data to "juice" vector)
   constant SRC_RDY_RANGE     : integer := 0;
   constant EOP_RANGE         : integer := SRC_RDY_RANGE + 1;
   constant SOP_RANGE         : integer := EOP_RANGE + 1;
      -- Definition of EOP_POS range
   constant EOP_POS_START     : integer := SOP_RANGE + 1;
   constant EOP_POS_END       : integer := EOP_POS_START + EOP_POS_WIDTH - 1;
      -- Definition of SOP_POS range
   constant SOP_POS_START     : integer := EOP_POS_END + 1;
   constant SOP_POS_END       : integer := SOP_POS_START + SOP_POS_WIDTH - 1;
      -- Definition of DATA range
   constant DATA_START        : integer := SOP_POS_END + 1;
   constant DATA_END          : integer := DATA_START + DATA_WIDTH - 1;

   --! Multiplexer input, output and selection signals
   signal mux_data_in      : std_logic_vector(INPUT_PORTS*MUX_DATA_WIDTH-1 downto 0);
   signal mux_data_out     : std_logic_vector(MUX_DATA_WIDTH-1 downto 0);
   signal mux_sel          : std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
   signal mux_ce_en        : std_logic;

   --! Input related signals
      -- Selected input is active
   signal input_active        : std_logic_vector(INPUT_PORTS-1 downto 0);
      -- Transaction is running
   signal transaction_active  : std_logic_vector(INPUT_PORTS-1 downto 0);
      -- Repaired SOP_POS signal
   type t_sop_pos_rep is array(0 to INPUT_PORTS-1) of std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal sop_pos_rep         : t_sop_pos_rep;
   signal eop_pos_sig         : t_sop_pos_rep;

   --! Block is ready to process new request
   signal next_rdy_gen        : std_logic;

   --! Output FLU data
   signal flu_data_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flu_sop_pos_out  : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flu_eop_pos_out  : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal flu_sop_out      : std_logic;
   signal flu_eop_out      : std_logic;
   signal flu_src_rdy_out  : std_logic;
   signal flu_dst_rdy_out  : std_logic;

begin

   --! \brief Create the "juice" input for DSP based multiplexer.
   DSP_MUX_INPUT_GENP:for i in 0 to INPUT_PORTS-1 generate
      --! Map input data, *_POS data and {SOP,EOP} data
      mux_data_in(EOP_RANGE + i*MUX_DATA_WIDTH)       <= RX_EOP(i);
      mux_data_in(SOP_RANGE + i*MUX_DATA_WIDTH)       <= RX_SOP(i);

      mux_data_in(EOP_POS_END + i*MUX_DATA_WIDTH downto i*MUX_DATA_WIDTH + EOP_POS_START)
         <= RX_EOP_POS((i+1)*EOP_POS_WIDTH-1 downto i*EOP_POS_WIDTH);

      mux_data_in(SOP_POS_END + i*MUX_DATA_WIDTH downto i*MUX_DATA_WIDTH + SOP_POS_START)
         <= RX_SOP_POS((i+1)*SOP_POS_WIDTH-1 downto i*SOP_POS_WIDTH);

      mux_data_in(DATA_END + i*MUX_DATA_WIDTH downto DATA_START + i*MUX_DATA_WIDTH)
         <= RX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH);

      --! Generate the src rdy validity detector
      mux_data_in(SRC_RDY_RANGE + i*MUX_DATA_WIDTH)   <= RX_SRC_RDY(i);

      --! Enable input when:
      --! * Port is selected
      --! * Transaction is running
      input_active(i) <= '1' when ((SEL = i and SEL_RDY = '1' and next_rdy_gen = '1') or
                                    transaction_active(i) = '1')
                        else '0';

      --! Genration of the RX_DST_RDY output -> this signal is active when multiplexer is ready
      --! and input is selected.
      RX_DST_RDY(i) <=  input_active(i) and mux_ce_en;

      --! \brief Generate repaired SOP_POS signal and map eop_pos signal withou any
      --! change
      process(RX_SOP_POS,RX_EOP_POS)
      begin
         -- Deal with SOP
         sop_pos_rep(i) <= (others=>'0');
         sop_pos_rep(i)(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH) <=
            RX_SOP_POS((i+1)*SOP_POS_WIDTH-1 downto i*SOP_POS_WIDTH);

         -- Deal with EOP
         eop_pos_sig(i) <= RX_EOP_POS((i+1)*EOP_POS_WIDTH-1 downto i*EOP_POS_WIDTH);
      end process;


      --! \brief Transaction detector for the input. This process detects transaction
      --! which takes more than two clock cycles
      trans_detp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(RESET = '1')then
               -- Input is not active by default
               transaction_active(i) <= '0';
            else
               -- If, input is selected, short packet is not detected and
               -- not active transaction, word is not shared
               if(mux_ce_en = '1' and RX_SRC_RDY(i) = '1' and RX_SOP(i) = '1' and
                  RX_EOP(i) = '0' and input_active(i) = '1')then

                  transaction_active(i) <= '1';

               -- If, input is selected, short packet is not detected and
               -- not active transaction, word is shared
               elsif(mux_ce_en = '1' and RX_SRC_RDY(i) = '1' and RX_SOP(i) = '1' and
                     RX_EOP(i) = '1' and sop_pos_rep(i) > eop_pos_sig(i) and input_active(i) = '1')then

                  transaction_active(i) <= '1';

               -- If input is not selected and eop is detected .. disable the
               -- transaction
               elsif(mux_ce_en = '1' and RX_SRC_RDY(i) = '1' and RX_SOP(i) = '0' and
                  RX_EOP(i) = '1' and transaction_active(i) = '1')then

                  transaction_active(i) <= '0';
               end if;
            end if;
         end if;
      end process;

   end generate;

   --! Map "next redy" signal
   SEL_NEXT <= next_rdy_gen;

   --!  Write next_rdy_gen logic - we are ready to receive the packet if mux is ready and long transaction is not running
   next_rdy_gen <= '0' when (transaction_active /= 0 or (transaction_active = 0 and mux_ce_en = '0'))
                   else '1';

   --! \brief Generation of selected input
   mux_sel_genp:process(SEL,transaction_active)
      variable index : integer;
   begin
      if(transaction_active = 0)then
         -- Transaction is not active, select the SEL value from input
         mux_sel <= SEL;
      else
         -- Transaction is active, retrieve it from the bit vector
         index := 0;
         for i in 0 to INPUT_PORTS-1 loop
            if(transaction_active(i) = '1')then
               index := i;
            end if;
         end loop;
         -- Setup the value
         mux_sel <= conv_std_logic_vector(index,log2(INPUT_PORTS));
      end if;

   end process;


   --! \brief DSP based multiplexer
   DSP_MUX_I:entity work.MUX_DSP_GEN
   generic map(
      --! Data width and number of inputs
      DATA_WIDTH     => MUX_DATA_WIDTH,
      MUX_WIDTH      => INPUT_PORTS,
      --! Input pipeline registers (0, 1)
      REG_IN         => REG_IN,
      --! Output pipeline registers (0, 1)
      REG_OUT        => REG_OUT,
      --! Pipeline between muxs levels (0, 1)
      REG_LVL        => REG_LVL
   )
   port map(
      --! Clock input
      CLK         => CLK,
      --! Reset input
      RESET       => RESET,
      --! Data input
      DATA_IN     => mux_data_in,
      --! Clock enable for input pipeline registers
      CE_IN       => mux_ce_en,
      --! Clock enable for output pipeline registers
      CE_OUT      => mux_ce_en,
      --! Clock enable for lvls
      CE_LVL      => mux_ce_en,
      --! Select input data
      SEL         => mux_sel,
      --! output
      DATA_OUT    => mux_data_out
   );

   --! Deal CE EN generation, in general .. we want to move data if and only iff, destination
   --! is ready
   mux_ce_en <= TX_DST_RDY;

   --! "de-juice" the data from multiplexer output and deal with the output data
   flu_data_out      <= mux_data_out(DATA_END downto DATA_START);
   flu_sop_pos_out   <= mux_data_out(SOP_POS_END downto SOP_POS_START);
   flu_eop_pos_out   <= mux_data_out(EOP_POS_END downto EOP_POS_START);
   flu_sop_out       <= mux_data_out(SOP_RANGE);
   flu_eop_out       <= mux_data_out(EOP_RANGE);
   flu_src_rdy_out   <= mux_data_out(SRC_RDY_RANGE);

   -- -----------------------------------------------------
   -- TX Connection
   -- -----------------------------------------------------
   TX_DATA           <= flu_data_out;
   TX_SOP_POS        <= flu_sop_pos_out;
   TX_EOP_POS        <= flu_eop_pos_out;
   TX_SOP            <= flu_sop_out;
   TX_EOP            <= flu_eop_out;
   TX_SRC_RDY        <= flu_src_rdy_out;
   flu_dst_rdy_out   <= TX_DST_RDY;

end architecture;
