-- binder.vhd: FrameLink Binder top architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity packet_binder is
   generic(
      -- width of one input interface. Should be multiple of 8
      FL_WIDTH        : integer := 32;
      -- specifies the primary interface - 0 or 1
      PRIMARY         : integer := 0;
      -- size of buffer for interface 0
      IF0_BUFFER_SIZE : integer := 512;
      -- size of buffer for interface 1
      IF1_BUFFER_SIZE : integer := 512;
      -- number of parts in frame
      IF0_PARTS       : integer := 1;
      -- number of parts in frame
      IF1_PARTS       : integer := 3;
      -- if true, register will be placed before data output
      OUTPUT_REG      : boolean := true
   );
   port(
      CLK             : in  std_logic;
      RESET           : in  std_logic;

      -- input FrameLink interface0
      RX_SOF_N_0      : in  std_logic;
      RX_SOP_N_0      : in  std_logic;
      RX_EOP_N_0      : in  std_logic;
      RX_EOF_N_0      : in  std_logic;
      RX_SRC_RDY_N_0  : in  std_logic;
      RX_DST_RDY_N_0  : out std_logic;
      RX_DATA_0       : in  std_logic_vector(FL_WIDTH-1 downto 0);
      RX_REM_0        : in  std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);

      -- input FrameLink interface1
      RX_SOF_N_1      : in  std_logic;
      RX_SOP_N_1      : in  std_logic;
      RX_EOP_N_1      : in  std_logic;
      RX_EOF_N_1      : in  std_logic;
      RX_SRC_RDY_N_1  : in  std_logic;
      RX_DST_RDY_N_1  : out std_logic;
      RX_DATA_1       : in  std_logic_vector(FL_WIDTH-1 downto 0);
      RX_REM_1        : in  std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);


      -- output FrameLink interface
      TX_SOF          : out std_logic;
      TX_SOP          : out std_logic;
      TX_EOP          : out std_logic;
      TX_EOF          : out std_logic;
      TX_SRC_RDY      : out std_logic;
      TX_DST_RDY      : in  std_logic;
      TX_DATA         : out std_logic_vector(FL_WIDTH-1 downto 0);
      TX_REM          : out std_logic_vector(log2(FL_WIDTH/8)-1 downto 0)
   );
end entity packet_binder;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture arc_packet_binder of packet_binder is

   type fsm_state is (if0, if1);

   signal pstate                : fsm_state;
   signal nstate                : fsm_state;



   -- FIFO_0 output signals
   signal flfifo_tx_data_0      : std_logic_vector(FL_WIDTH-1 downto 0);
   signal flfifo_tx_rem_0       : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal flfifo_tx_src_rdy_n_0 : std_logic;
   signal flfifo_tx_dst_rdy_n_0 : std_logic;
   signal flfifo_tx_sop_n_0     : std_logic;
   signal flfifo_tx_eop_n_0     : std_logic;
   signal flfifo_tx_sof_n_0     : std_logic;
   signal flfifo_tx_eof_n_0     : std_logic;
   -- FIFO_1 output signals
   signal flfifo_tx_data_1      : std_logic_vector(FL_WIDTH-1 downto 0);
   signal flfifo_tx_rem_1       : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal flfifo_tx_src_rdy_n_1 : std_logic;
   signal flfifo_tx_dst_rdy_n_1 : std_logic;
   signal flfifo_tx_sop_n_1     : std_logic;
   signal flfifo_tx_eop_n_1     : std_logic;
   signal flfifo_tx_sof_n_1     : std_logic;
   signal flfifo_tx_eof_n_1     : std_logic;

   signal pb_output_data        : std_logic_vector(FL_WIDTH-1 downto 0);
   signal pb_output_rem         : std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
   signal pb_output_src_rdy_n   : std_logic;
   signal pb_output_sop_n       : std_logic;
   signal pb_output_eop_n       : std_logic;
   signal pb_output_sof_n       : std_logic;
   signal pb_output_eof_n       : std_logic;

   signal src_rdy_n   : std_logic;


   signal muxsel		: std_logic;
   signal cstate0		: std_logic;
   signal cstate1		: std_logic;
begin

FL_FIFO_0 : entity work.FL_FIFO
         generic map(
            DATA_WIDTH     => FL_WIDTH,
            USE_BRAMS      => true,
            ITEMS          => IF0_BUFFER_SIZE,
            BLOCK_SIZE     => 1,
            STATUS_WIDTH   => 1,
            PARTS          => IF0_PARTS
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- write interface
            RX_DATA        => RX_DATA_0,
            RX_REM         => RX_REM_0,
            RX_SRC_RDY_N   => RX_SRC_RDY_N_0,
            RX_DST_RDY_N   => RX_DST_RDY_N_0,
            RX_SOP_N       => RX_SOP_N_0,
            RX_EOP_N       => RX_EOP_N_0,
            RX_SOF_N       => RX_SOF_N_0,
            RX_EOF_N       => RX_EOF_N_0,
            -- read interface
            TX_DATA        => flfifo_tx_data_0,
            TX_REM         => flfifo_tx_rem_0,
            TX_SRC_RDY_N   => flfifo_tx_src_rdy_n_0,
            TX_DST_RDY_N   => flfifo_tx_dst_rdy_n_0,
            TX_SOP_N       => flfifo_tx_sop_n_0,
            TX_EOP_N       => flfifo_tx_eop_n_0,
            TX_SOF_N       => flfifo_tx_sof_n_0,
            TX_EOF_N       => flfifo_tx_eof_n_0,
            -- FIFO state signals
            LSTBLK         => open,
            FULL           => open,
            EMPTY          => open,
            STATUS         => open
         );


FL_FIFO_1 : entity work.FL_FIFO
         generic map(
            DATA_WIDTH     => FL_WIDTH,
            USE_BRAMS      => true,
            ITEMS          => IF1_BUFFER_SIZE,
            BLOCK_SIZE     => 1,
            STATUS_WIDTH   => 1,
            PARTS          => IF1_PARTS
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- write interface
            RX_DATA        => RX_DATA_1,
            RX_REM         => RX_REM_1,
            RX_SRC_RDY_N   => RX_SRC_RDY_N_1,
            RX_DST_RDY_N   => RX_DST_RDY_N_1,
            RX_SOP_N       => RX_SOP_N_1,
            RX_EOP_N       => RX_EOP_N_1,
            RX_SOF_N       => RX_SOF_N_1,
            RX_EOF_N       => RX_EOF_N_1,
            -- read interface
            TX_DATA        => flfifo_tx_data_1,
            TX_REM         => flfifo_tx_rem_1,
            TX_SRC_RDY_N   => flfifo_tx_src_rdy_n_1,
            TX_DST_RDY_N   => flfifo_tx_dst_rdy_n_1,
            TX_SOP_N       => flfifo_tx_sop_n_1,
            TX_EOP_N       => flfifo_tx_eop_n_1,
            TX_SOF_N       => flfifo_tx_sof_n_1,
            TX_EOF_N       => flfifo_tx_eof_n_1,
            -- FIFO state signals
            LSTBLK         => open,
            FULL           => open,
            EMPTY          => open,
            STATUS         => open
         );



cstate0 <= not (flfifo_tx_eof_n_0) and not (flfifo_tx_src_rdy_n_0) and not (flfifo_tx_dst_rdy_n_0); --and(flfifo_tx_sof_n_0);
cstate1 <= not (flfifo_tx_eof_n_1) and not (flfifo_tx_src_rdy_n_1) and not (flfifo_tx_dst_rdy_n_1);
-- and (flfifo_tx_sof_n_1);

--FSM present state
fsm_pstate: process(CLK, RESET)
   begin
      if (RESET='1') then if (PRIMARY=0) then pstate <= if0;
                                         else pstate <= if1;
                          end if;
      else if (CLK'event) and (CLK='1') then
             pstate <= nstate;
           end if;
      end if;
   end process;




--FSM next state logic
nsl: process(pstate,cstate0,cstate1,reset)
   begin
      case pstate is
         when if0 =>
            if (cstate0='1') then nstate <= if1;
            else nstate <= if0;
            end if;
         when if1 =>
            if (cstate1='1') then nstate <= if0;
            else nstate <= if1;
            end if;
      end case;
   end process;


--FSM output logic
outputlogic: process(pstate,reset)
   begin
      case pstate is
         when if0 =>
            muxsel <= '0';
         when if1 =>
            muxsel <= '1';
      end case;
   end process;



sofeof0:   if PRIMARY=0 generate
            pb_output_sof_n  <= '1' when (muxsel = '1')
	                   else flfifo_tx_sof_n_0;
            pb_output_eof_n  <= '1' when (muxsel = '0')
	                   else flfifo_tx_eof_n_1;
   end generate;

sofeof1:   if PRIMARY=1 generate
            pb_output_sof_n  <= '1' when (muxsel = '0')
	                   else flfifo_tx_sof_n_1;
            pb_output_eof_n  <= '1' when (muxsel = '1')
	                   else flfifo_tx_eof_n_0;

   end generate;


            pb_output_sop_n  <= flfifo_tx_sop_n_1 when (muxsel = '1')
	                                 else flfifo_tx_sop_n_0;
            pb_output_eop_n  <= flfifo_tx_eop_n_1 when (muxsel = '1')
	                                 else flfifo_tx_eop_n_0;
            pb_output_data <= flfifo_tx_data_1 when (muxsel = '1')
		                        else flfifo_tx_data_0;
            pb_output_rem  <= flfifo_tx_rem_1 when (muxsel = '1')
		                       else flfifo_tx_rem_0;

            pb_output_src_rdy_n <= flfifo_tx_src_rdy_n_1 when (muxsel = '1')
		                                else flfifo_tx_src_rdy_n_0;

            flfifo_tx_dst_rdy_n_0 <= '1' when (muxsel = '1')
      	                                 else TX_DST_RDY;

            flfifo_tx_dst_rdy_n_1 <= '1' when (muxsel = '0')
			                 else TX_DST_RDY;


reg_output: if OUTPUT_REG = true generate
   sof_reg: process(CLK, RESET)
      begin
         if (RESET='1') then  TX_SOF <= '1';
                              TX_EOF <= '1';
                              TX_SOP <= '1';
                              TX_EOP <= '1';
                              src_rdy_n <= '1';
                              TX_DATA <= (others => '0');
                              TX_REM <= (others => '0');
           else if (CLK'event) and (CLK='1') and (TX_DST_RDY='0') and ((src_rdy_n='0') or (pb_output_src_rdy_n='0')) then
              TX_SOF <= pb_output_sof_n;
              TX_EOF <= pb_output_eof_n;
              TX_SOP <= pb_output_sop_n;
              TX_EOP <= pb_output_eop_n;
              src_rdy_n <= pb_output_src_rdy_n;
              TX_DATA <= pb_output_data;
              TX_REM <= pb_output_rem;
           end if;
         end if;
      end process;

    TX_SRC_RDY <= src_rdy_n;

  end generate;

output_without_reg: if OUTPUT_REG = false generate

              TX_SOF <= pb_output_sof_n;
              TX_EOF <= pb_output_eof_n;
              TX_SOP <= pb_output_sop_n;
              TX_EOP <= pb_output_eop_n;
              TX_SRC_RDY <= pb_output_src_rdy_n;
              TX_DATA <= pb_output_data;
              TX_REM <= pb_output_rem;
  end generate;

end architecture arc_packet_binder;
