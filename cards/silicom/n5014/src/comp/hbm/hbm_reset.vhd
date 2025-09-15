-- hbm_reset.vhd: HBM reset controller
-- Copyright (C) BrnoLogic, Ltd. - All Rights Reserved
-- Author: Tomas Fukac <fukac@brnologic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;


entity HBM_RESET is
	port(
		CORE_CLK        : in  std_logic;

		PLL_LOCKED      : in  std_logic;
		HBM_CAL_SUCCESS : in  std_logic;

		HBM_RST_REQ     : out std_logic;
		HBM_WMCRST_N    : out std_logic;
		CORE_CLK_LOCKED : out std_logic
	);

end entity;

architecture FULL of HBM_RESET is

	type state_t is (CAL_INIT_ST, CAL_REQ_ST, CAL_ONGOING_ST, CAL_DONE_ST);
	signal cstate                 : state_t := CAL_INIT_ST;
	signal nstate                 : state_t := CAL_INIT_ST;

	signal core_clk_locked_resync : std_logic;
	signal cal_cnt                : std_logic_vector(16 downto 0);
	signal cal_cnt_en             : std_logic;

begin

	locked_resync : entity work.fim_resync
	generic map (
		SYNC_CHAIN_LENGTH      => 3,
		WIDTH                  => 1,
		INIT_VALUE             => 0,
		NO_CUT                 => 0,
		TURN_OFF_METASTABILITY => 1,
		TURN_OFF_ADD_PIPELINE  => 1
	)
	port map(
		clk               => CORE_CLK,
		reset             => '0',
		d                 => PLL_LOCKED,
		q                 => core_clk_locked_resync
	);

	CORE_CLK_LOCKED <= core_clk_locked_resync;

	cnt : process(CORE_CLK)
	  begin
		 if rising_edge(CORE_CLK) then
			if core_clk_locked_resync = '0' then
				cal_cnt <= (others=>'1');
			elsif cal_cnt_en = '1' then
				cal_cnt <= std_logic_vector( unsigned(cal_cnt) - 1 );
			end if;
		 end if;
	  end process;

	-----------------------------------------------
	------------------- FSM -----------------------
	-----------------------------------------------

	fsm_state: process(CORE_CLK)
	begin
		if rising_edge(CORE_CLK) then
			if core_clk_locked_resync = '0' then
				cstate <= CAL_INIT_ST;
			else
				cstate <= nstate;
			end if;
		end if;
	end process;

	fsm_next: process(cstate, HBM_CAL_SUCCESS, core_clk_locked_resync, cal_cnt)
	begin
		nstate  <= cstate;

		case cstate is
			when CAL_INIT_ST =>
				if HBM_CAL_SUCCESS = '1' and core_clk_locked_resync = '1' then
					nstate <= CAL_REQ_ST;
				else
					nstate <= CAL_INIT_ST;
				end if;

			when CAL_REQ_ST =>
				nstate <= CAL_ONGOING_ST;

			when CAL_ONGOING_ST =>
				-- wait for last word
				if cal_cnt = (16 downto 0 => '0') and HBM_CAL_SUCCESS = '1' then
					nstate <= CAL_DONE_ST;
				else
					nstate <= CAL_ONGOING_ST;
				end if;

			when CAL_DONE_ST =>
				nstate <= CAL_DONE_ST;

		end case;
	end process;

	fsm_output: process(cstate, cal_cnt)
	begin
		HBM_RST_REQ  <= '0';
		HBM_WMCRST_N <= '1';
		cal_cnt_en   <= '0';

		case cstate is
			when CAL_INIT_ST =>

			when CAL_REQ_ST =>
				HBM_RST_REQ  <= '1';
				HBM_WMCRST_N <= '0';

			when CAL_ONGOING_ST =>
				cal_cnt_en <= '1';

			when CAL_DONE_ST =>

		end case;
	end process;

end architecture;
