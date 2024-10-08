-- async.vhd: Unit gets write or read requests at input frequency and creates
--            write enables for an register as output on another frequency.
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO: resets
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- Async is unit for assynchrounous requests. When RQST is set to high, then
-- it must keep state until RDY signal also gets high else request may be lost.
-- After RDY is set, then RQST may be unset. Next RQST can be generated
-- after RQST was set to low.
entity async is
  port (
    -- input clk
    IN_CLK     : in std_logic;
    IN_RESET   : in std_logic;
    -- data write request
    -- request
    RQST       : in std_logic;
    -- address ready signal - when we are ready for another transaction
    -- data are ready
    RDY        : out std_logic;

    -- output clk and write enable
    OUT_CLK    : in std_logic;
    OUT_RESET  : in std_logic;
    -- output write enable
    OUT_RQST   : out std_logic
  );
end async;

architecture behavioral of async is
  signal rqst_toogle   : std_logic;
  signal rqst_tg_reg0  : std_logic;
  signal rqst_tg_reg1  : std_logic;
  signal rqst_tg_out   : std_logic;

  signal rdy_toogle    : std_logic;
  signal rdy_tg_reg0   : std_logic;
  signal rdy_tg_reg1   : std_logic;
  signal rdy_tg_out    : std_logic;

  signal sig_out_rqst  : std_logic;
  signal sig_rdy       : std_logic;
  signal sig_rqst      : std_logic;
  signal busy          : std_logic;

begin
  -- Block all incomming requests while there is a request in process
  sig_rqst <= RQST and (not busy or sig_rdy);

  --! Request in process (busy register)
  busy_reg : process(IN_CLK)
  begin
    if IN_CLK'event and IN_CLK='1' then
      if IN_RESET='1' then
        busy <= '0';
      elsif sig_rqst='1' then
        busy <= '1';
      elsif sig_rdy='1' then
        busy <= '0';
      end if;
    end if;
  end process;

  --! Request pulse to toogle
  rqst_toogle_reg : process(IN_CLK)
  begin
    if IN_CLK'event and IN_CLK='1' then
      if IN_RESET='1' then
        rqst_toogle <= '0';
      elsif sig_rqst='1' then
        rqst_toogle <= not rqst_toogle;
      end if;
    end if;
  end process;

  --! Request toogle synchronizer
  rqst_sync : process(OUT_CLK)
  begin
    if OUT_CLK'event and OUT_CLK='1' then
      if OUT_RESET='1' then
        rqst_tg_reg0 <= '0';
        rqst_tg_reg1 <= '0';
        rqst_tg_out  <= '0';
      else
        rqst_tg_reg0 <= rqst_toogle;
        rqst_tg_reg1 <= rqst_tg_reg0;
        rqst_tg_out  <= rqst_tg_reg1;
      end if;
    end if;
  end process;

  -- Request toogle back to pulse
  sig_out_rqst <= rqst_tg_out xor rqst_tg_reg1;
  OUT_RQST     <= sig_out_rqst;


  --! Ready pulse to toogle
  rdy_toogle_reg : process(OUT_CLK)
  begin
    if OUT_CLK'event and OUT_CLK='1' then
      if OUT_RESET='1' then
        rdy_toogle <= '0';
      elsif sig_out_rqst='1' then
        rdy_toogle <= not rdy_toogle;
      end if;
    end if;
  end process;

  --! Ready toogle synchronizer
  rdy_sync : process(IN_CLK)
  begin
    if IN_CLK'event and IN_CLK='1' then
      if IN_RESET='1' then
        rdy_tg_reg0 <= '0';
        rdy_tg_reg1 <= '0';
        rdy_tg_out  <= '0';
      else
        rdy_tg_reg0 <= rdy_toogle;
        rdy_tg_reg1 <= rdy_tg_reg0;
        rdy_tg_out  <= rdy_tg_reg1;
      end if;
    end if;
  end process;

  -- Ready toogle back to pulse
  sig_rdy <= rdy_tg_out xor rdy_tg_reg1;
  RDY     <= sig_rdy;

end architecture behavioral;
