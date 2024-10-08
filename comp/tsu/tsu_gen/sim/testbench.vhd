-- testbench.vhd: Testbench of timestamp unit entity
-- Copyright (C) 2014 CESNET
-- Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--library unisim;
--use unisim.vcomponents.all;

--! Package containing max function.
use work.math_pack.all;

use work.mi32_pkg.all;
use work.ib_sim_oper.all;  -- Internal bus simulation pkg

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- ============================
   -- Global Constant Declaration
   -- ============================

   -- 125MHz
   constant mi32_period         : time := 8 ns;
   -- 200MHz
   constant clk_period          : time := 5 ns;
   -- 1Hz
   constant pps_period 	        : time := 1 us;
   constant reset_delay	        : time := 100 ns;
   constant PPS_SEL_WIDTH       : integer := 8;
   constant CLK_SEL_WIDTH       : integer := 8;

   -- ===============
   -- Address offsets
   -- ===============

   constant MICOM_LOW  	        : std_logic_vector(31 downto 0) := X"00000000";
   constant MICOM_MIDDLE        : std_logic_vector(31 downto 0) := X"00000004";
   constant MICOM_HIGH 	        : std_logic_vector(31 downto 0) := X"00000008";
   constant CNTRL  	           : std_logic_vector(31 downto 0) := X"0000000C";
   constant STATE_REG           : std_logic_vector(31 downto 0) := X"00000010";
   constant INTA	              : std_logic_vector(31 downto 0) := X"00000014";
   constant SEL_PPS_N	        : std_logic_vector(31 downto 0) := X"00000018";
   constant FREQ_REG            : std_logic_vector(31 downto 0) := X"0000001C";
   constant SEL_CLK	           : std_logic_vector(31 downto 0) := X"00000020";
   constant NUM_CLK_PPS	        : std_logic_vector(31 downto 0) := X"00000024";

   -- Signal declaration
   signal mi32_clk              : std_logic := '0';
   signal mi32_reset            : std_logic;
   signal clk                   : std_logic := '0';
   signal reset                 : std_logic;
   signal reg_reset             : std_logic;
   signal clk_freq              : std_logic_vector(31 downto 0);
   signal clk_src               : std_logic_vector(15 downto 0);
   signal clk_sel               : std_logic_vector(max(CLK_SEL_WIDTH-1,0) downto 0);

   -- mi32 bus interface
   signal mi32		              : t_mi32;

   -- mi32 simulation signals
   signal mi32_sim_ctrl         : t_ib_ctrl;
   signal mi32_sim_strobe       : std_logic := '0';
   signal mi32_sim_busy         : std_logic;

   -- Output interface
   signal ts	   	           : std_logic_vector(63 downto 0);
   signal ts_dv     	           : std_logic;
   signal ts_ns                 : std_logic_vector(63 downto 0);

   -- Input GPS signal
   signal pps_n	              : std_logic;
   signal pps_src	              : std_logic_vector(15 downto 0);
   signal pps_sel	              : std_logic_vector(max(PPS_SEL_WIDTH-1,0) downto 0);

signal TS_ERR	              : std_logic;
   signal last_ts	   	           : std_logic_vector(63 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   clk_freq <= conv_std_logic_vector(200000000-1,32);

   -- -------------------------------------------------------------------------
   --                         TIMESTAMP UNIT
   -- -------------------------------------------------------------------------
   uut : entity work.tsu_gen
      generic map(
         --! \brief Selects smarter DSPs arrangement for timestamp format conversion
         --! \details Meanings of supported values: \n
         --! true = use multiplication in DSPs composed of adds and shifts \n
         --! false = look at TS_MULT_USE_DSP
         TS_MULT_SMART_DSP => true,
         --! \brief Selects whether to use DSPs for timestamp format conversion
         --! \details Meanings of supported values: \n
         --! true = use multipliers in DSPs \n
         --! false = disable DSPs, use logic
         TS_MULT_USE_DSP   => true,
         --! \brief Width of PPS select signal
         --! \details Used value must be in range from 1 to 16.
         --! Should be greater or equal to base 2 logarithm from number of available PPS sources.
         PPS_SEL_WIDTH     => PPS_SEL_WIDTH,
         --! \brief Width of main CLK select signal
         --! \details Used value must be in range from 1 to 16.
         --! Should be greater or equal to base 2 logarithm from number of available CLK sources.
         CLK_SEL_WIDTH     => CLK_SEL_WIDTH
      )
      port map(
         --! \name Signals for MI_32 interface

         --! Interface clock.
         MI_CLK        => mi32_clk,
         --! Interface reset.
         MI_RESET      => mi32_reset,
         --! Data to write.
         MI_DWR        => mi32.dwr,
         --! Read/write address.
         MI_ADDR       => mi32.addr,
         --! Read valid.
         MI_RD         => mi32.rd,
         --! Write valid.
         MI_WR         => mi32.wr,
         --! Write data byte enable (not supported).
         MI_BE         => mi32.be,
         --! Read data.
         MI_DRD        => mi32.drd,
         --! Read/write address ready.
         MI_ARDY       => mi32.ardy,
         --! Read data ready.
         MI_DRDY       => mi32.drdy,

         --! \name PPS signal interface

         --! Input PPS_N signal
         PPS_N         => pps_n,
         --! \brief Number of different PPS sources (on MI_CLK)
         PPS_SRC       => X"0002",
         --! \brief Select PPS source (on MI_CLK)
         PPS_SEL       => pps_sel,

         --! \name Main CLK signal interface

         --! Input CLK signal
         CLK           => clk,
         --! Synchronious reset with main clock
         RESET         => reset,
         --! Frequency of input CLK signal (on MI_CLK)
         CLK_FREQ      => clk_freq,
         --! \brief Number of different CLK sources (on MI_CLK)
         CLK_SRC       => X"0001",
         --! \brief Select CLK source (on MI_CLK)
         CLK_SEL       => open,


         --! \name Output timestamp interface (on main CLK)

         --! \brief Timestamp in fractional (old) format
         --! \details Fractional part of timestamp represents number of xanoseconds (one xanosecond is 2^(-32) seconds).
         TS  	 	    => ts,
         --! \brief Timestamp in nanosecond (new) format
         --! \details Fractional part of timestamp represents number of nanoseconds (one nanosecond is 10^(-9) seconds).
         --! Maximum number of nanoseconds is 999 999 999, therefor highest 2 bits of fractional part are unused.
         TS_NS 	    => ts_ns, -- timestamp with fractinal part with base 10^-9 (ns)
         --! Timestamp is valid in this cycle
         TS_DV	       => ts_dv
      );


   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim_u: entity work.mi32_sim
      generic map(
         UPSTREAM_LOG_FILE   => "", --"./data/mi32upstream",
         DOWNSTREAM_LOG_FILE => "", --"./data/mi32downstream",
         BASE_ADDR           => X"00000000",
         LIMIT               => X"00000300",  --01048576
         BUFFER_EN           => true
	)

      port map(
         -- Common interface
         IB_RESET       => mi32_reset,
         IB_CLK         => mi32_clk,

         -- User Component Interface
         CLK		      => mi32_clk,
	      MI32.DWR  	   => mi32.dwr,
	      MI32.ADDR 	   => mi32.addr,
	      MI32.RD 	      => mi32.rd,
	      MI32.WR        => mi32.wr,
	      MI32.BE    	   => mi32.be,
	      MI32.DRD       => mi32.drd,
	      MI32.ARDY  	   => mi32.ardy,
	      MI32.DRDY  	   => mi32.drdy,

         -- IB SIM interface
         STATUS         => open,
         CTRL           => mi32_sim_ctrl,
         STROBE         => mi32_sim_strobe,
         BUSY           => mi32_sim_busy
     );

   -- ----------------------------------------------------
   -- MI32 CLK generator
   mi32_clk_gen : process
   begin
      mi32_clk <= '1';
      wait for mi32_period/2;
      mi32_clk <= '0';
      wait for mi32_period/2;
   end process;

   -- ----------------------------------------------------
   -- CLK generator
   clk_gen : process
   begin
      clk <= '1';
      wait for clk_period/2;
      clk <= '0';
      wait for clk_period/2;
   end process;

   -- ----------------------------------------------------
   -- MI32 Reset generation
   proc_mi32_reset : process
   begin
      mi32_reset <= '1';
      wait for reset_delay;
      mi32_reset <= '0';
      wait;
   end process;

   -- ----------------------------------------------------
   -- Reset generation
   proc_reset : process(clk)
   begin
      if rising_edge(clk) then
         reset <= reg_reset;
         reg_reset <= mi32_reset;
      end if;
   end process;

   -- ----------------------------------------------------
   -- PPS_N pulse generator
   pps_gen : process
   begin
      pps_n <= '1';
      wait for 9*pps_period/10;
      pps_n <= '0';
      wait for pps_period/10;
   end process;

   -- ----------------------------------------------------
   -- TS CONTROL
   TS_ERR_gen : process(clk)
   begin
      if (rising_edge(CLK)) then
       --  if (TS_DV = '1') then
            last_ts <= TS;
            if (last_ts > TS) then
               TS_ERR <= '1';
            else
               TS_ERR <= '0';
            end if;
        -- end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------
   --                         Main testbench process
   -- ----------------------------------------------------------------------------
   tsu_sw_test : process
      -- ----------------------------------------------------------------
      --                    Procedures declaration
      -- ----------------------------------------------------------------

      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessary for correct function of MI32_SIM
      procedure ib_op(ctrl : in t_ib_ctrl) is
	 begin
	    wait until (mi32_clk'event and mi32_clk='1' and mi32_sim_busy = '0');
	    mi32_sim_ctrl <= ctrl;
	    mi32_sim_strobe <= '1';
	    wait until (mi32_clk'event and mi32_clk='1');
	    mi32_sim_strobe <= '0';
	 end ib_op;

       -- ----------------------------------------------------------------
       --                        Testbench Body
       -- ----------------------------------------------------------------
   begin
      wait for reset_delay;

      -- write into register INCR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FF"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 1, 16#ABAD#, '0', X"11223344556677EE"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000000"));

      -- write into register RTR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FA"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EB"));
      ib_op(ib_local_write(MICOM_HIGH, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EC"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000001"));

      -- write into register INTA
      ib_op(ib_local_write(INTA, X"11111111", 1, 16#ABAA#, '0', X"0000000000000001"));

      -- read from register RTR
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000005"));
      ib_op(ib_local_read(MICOM_LOW, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_MIDDLE, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_HIGH, X"11111111", 4, 16#ABAB#));

      -- read from register PPS
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000007"));
      ib_op(ib_local_read(MICOM_LOW, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_MIDDLE, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_HIGH, X"11111111", 4, 16#ABAB#));

      -- read from register INCR
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000004"));
      ib_op(ib_local_read(MICOM_LOW, X"11111111", 4, 16#ABAB#, true));
      ib_op(ib_local_read(MICOM_MIDDLE, X"11111111", 4, 16#ABAB#));

      -- write into register INCR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FC"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 1, 16#ABAD#, '0', X"11223344556677DE"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000000"));

      --wait for 4000*mi32_period;

      -- write into register INTA
      ib_op(ib_local_write(INTA, X"11111111", 1, 16#ABAA#, '0', X"0000000000000000"));

      -- read from register FREQ_REG
      ib_op(ib_local_read(FREQ_REG, X"11111111", 4, 16#ABAB#));

      -- read from register DETECT_PPS_N
      ib_op(ib_local_read(STATE_REG, X"11111111", 4, 16#ABAB#));

      -- write into register SEL_PPS_N
      ib_op(ib_local_write(SEL_PPS_N, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF0001"));

      wait for 30*mi32_period;

   end process;

end architecture behavioral;
