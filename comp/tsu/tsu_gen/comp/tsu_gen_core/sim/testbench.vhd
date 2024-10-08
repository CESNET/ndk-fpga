-- testbench.vhd: Testbench of timestamp unit entity
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
   -- ===========================
   -- Global Constant Declaration
   -- ===========================

   -- 125MHz
   constant mi32_period    : time := 8  ns;
   -- 200MHz
   constant tsu_core_period : time := 6.25 ns;
   --  1Hz
   constant pps_period 	   : time := 1  us;
   constant reset_delay	   : time := 100 ns;

   -- ================
   -- Address offsets
   -- ================
   constant MICOM_LOW  	   : std_logic_vector(31 downto 0) := X"00000000";
   constant MICOM_MIDDLE   : std_logic_vector(31 downto 0) := X"00000004";
   constant MICOM_HIGH 	   : std_logic_vector(31 downto 0) := X"00000008";
   constant CNTRL  	   : std_logic_vector(31 downto 0) := X"0000000C";
   constant DETECT_PPS_N   : std_logic_vector(31 downto 0) := X"00000010";
   constant INTA	   : std_logic_vector(31 downto 0) := X"00000014";
   constant SEL_PPS_N	   : std_logic_vector(31 downto 0) := X"00000018";
   constant FREQ_REG       : std_logic_vector(31 downto 0) := X"0000001C";

   -- Signal declaration
   signal mi32_clk          : std_logic := '0';
   signal mi32_reset        : std_logic;
   signal tsu_core_reset    : std_logic;
   signal tsu_core_clk      : std_logic := '0';

   -- mi32 bus interface
   signal mi32		   : t_mi32;

   -- mi32 simulation signals
   signal mi32_sim_ctrl    : t_ib_ctrl;
   signal mi32_sim_strobe  : std_logic := '0';
   signal mi32_sim_busy    : std_logic;

   -- Output interface
   signal ts	   	   : std_logic_vector(63 downto 0) := X"0000000000000000";
   signal ts_dv     	   : std_logic;

   -- Input GPS signal
   signal pps_n	           : std_logic;

signal TS_ERR	              : std_logic;
   signal last_ts	   	           : std_logic_vector(63 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         TIMESTAMP UNIT
   -- -------------------------------------------------------------------------
   uut : entity work.tsu_cv2_core
      port map(
          -- Combo clock and reset signals for MI_32 interface
          MI32_CLK       => mi32_clk,
          MI32_RESET     => mi32_reset,

          -- In / Out SW interface via MI_32
	  DWR          => mi32.dwr,
	  ADDR         => mi32.addr,
	  RD           => mi32.rd,
	  WR           => mi32.wr,
	  BE           => mi32.be,
	  DRD          => mi32.drd,
	  ARDY         => mi32.ardy,
	  DRDY	       => mi32.drdy,

          -- Input PPS_N signal
          PPS_N    => pps_n,

          -- TSU core clock ----------------------------
          TSU_CORE_CLK   => tsu_core_clk,
          TSU_CORE_RESET => tsu_core_reset,

          -- Output pacodag interface
          TS           => ts,
          TS_DV        => ts_dv
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
         IB_RESET          => mi32_reset,
         IB_CLK            => mi32_clk,

         -- User Component Interface
         CLK		   => mi32_clk,
	 MI32.DWR  	   => mi32.dwr,
	 MI32.ADDR 	   => mi32.addr,
	 MI32.RD 	   => mi32.rd,
	 MI32.WR     	   => mi32.wr,
	 MI32.BE    	   => mi32.be,
	 MI32.DRD     	   => mi32.drd,
	 MI32.ARDY  	   => mi32.ardy,
	 MI32.DRDY  	   => mi32.drdy,

         -- IB SIM interface
         STATUS            => open,
         CTRL              => mi32_sim_ctrl,
         STROBE            => mi32_sim_strobe,
         BUSY              => mi32_sim_busy
     );


   -- ----------------------------------------------------
   -- CLK generator - 125 MHz
   mi32_clk_gen : process
   begin
      mi32_clk <= '1';
      wait for mi32_period/2;
      mi32_clk <= '0';
      wait for mi32_period/2;
   end process;

   -- ----------------------------------------------------
   -- TSU_CORE_CLK generator - 160 MHz
   ptm_precise_clk_gen : process
   begin
      tsu_core_clk <= '1';
      wait for tsu_core_period/2;
      tsu_core_clk <= '0';
      wait for tsu_core_period/2;
   end process;

   -- ----------------------------------------------------
   -- MI32 Reset generation
   proc_mi32_reset : process
   begin
      mi32_reset <= '1';
      tsu_core_reset <= '1';
      wait for reset_delay;
      mi32_reset <= '0';
      tsu_core_reset <= '0';
      wait;
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
   TS_ERR_gen : process(tsu_core_clk)
   begin
      if (rising_edge(tsu_core_clk)) then
       --  if (TS_DV = '1') then
            last_ts <= ts;
            if (last_ts > ts) then
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
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 4, 16#ABAD#, '0', X"A1223344556677EB"));
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

      -- write into register INTA
      ib_op(ib_local_write(INTA, X"11111111", 1, 16#ABAA#, '0', X"0000000000000000"));

      -- read from register FREQ_REG - incorrect address
      ib_op(ib_local_read(FREQ_REG, X"11111111", 4, 16#ABAB#));

      -- read from register DETECT_PPS_N - incorrect address
      ib_op(ib_local_read(DETECT_PPS_N, X"11111111", 4, 16#ABAB#));

      -- write into register SEL_PPS_N - incorrect address
      ib_op(ib_local_write(SEL_PPS_N, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF0001"));

      wait for 30*mi32_period;

   end process;

end architecture behavioral;
