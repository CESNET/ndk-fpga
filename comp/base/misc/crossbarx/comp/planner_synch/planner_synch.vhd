-- planner_synch.vhd: Crossbar data transfer planner synchronisator
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_PLANNER_SYNCHRONISATOR is
generic(
    -- Number of independent Transaction Streams with independent Color Conformation mechanism
    TRANS_STREAMS       : integer := 1;

    -- Create asynch transfer (CLK_PLAN is different from CLK_OTHER)
    ASYNC_EN            : boolean := false;

    -- Color confirmation delay
    COLOR_CONF_DELAY    : integer := 16;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE              : string := "STRATIX10"
);
port(
    -- Clock and Reset
    CLK_PLAN            : in  std_logic;
    RESET_PLAN          : in  std_logic;
    CLK_OTHER           : in  std_logic;
    RESET_OTHER         : in  std_logic;

    -- ========================
    -- Planner-side interface
    -- ========================

    -- Color Conformation Timeout cancel signal
    P_NEW_RX_TRANS      : out std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- Color Conformation signal
    P_CONF_COLOR        : in  std_logic_vector(TRANS_STREAMS-1 downto 0);
    P_CONF_VLD          : in  std_logic_vector(TRANS_STREAMS-1 downto 0);
    P_CONF_PROPAGATED   : out std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- ========================
    -- Other-CLK-side interface
    -- ========================

    -- Color Conformation Timeout cancel signal
    O_NEW_RX_TRANS      : in  std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- Color Conformation signal
    O_CONF_COLOR        : out std_logic_vector(TRANS_STREAMS-1 downto 0);
    O_CONF_VLD          : out std_logic_vector(TRANS_STREAMS-1 downto 0);
    O_CONF_PROPAGATED   : in  std_logic_vector(TRANS_STREAMS-1 downto 0)

    -- -----------------------------------------------------------------
);
end entity;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------

architecture FULL of CROSSBARX_PLANNER_SYNCHRONISATOR is

    -- -----------------------------------------------------------------
    -- Signals
    -- -----------------------------------------------------------------

    signal plan_conf_color      : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal plan_conf_vld        : std_logic_vector(TRANS_STREAMS-1 downto 0);

    signal plan_conf_color_delayed   : slv_array_t(COLOR_CONF_DELAY+1-1 downto 0)(TRANS_STREAMS-1 downto 0);
    signal plan_conf_vld_delayed     : slv_array_t(COLOR_CONF_DELAY+1-1 downto 0)(TRANS_STREAMS-1 downto 0);

    signal p_in_reg         : std_logic_vector(2*TRANS_STREAMS-1 downto 0);
    signal p2o_asfifo_full  : std_logic;
    signal p2o_asfifo_do    : std_logic_vector(2*TRANS_STREAMS-1 downto 0);
    signal p2o_asfifo_empty : std_logic;

    signal o_in_reg         : std_logic_vector(2*TRANS_STREAMS-1 downto 0);
    signal o2p_asfifo_full  : std_logic;
    signal o2p_asfifo_do    : std_logic_vector(2*TRANS_STREAMS-1 downto 0);
    signal o2p_asfifo_empty : std_logic;

    -- -----------------------------------------------------------------

begin

    sync_gen : if (ASYNC_EN) generate

        -- -----------------------------------------------------------------
        -- Planner to Others Asynch connection
        -- -----------------------------------------------------------------
        -- These registers save signal when it cannot be propagated because
        -- ASFIFOX is full (should not happen very often).

        p_in_reg_pr : process (CLK_PLAN)
            variable reg_tmp : std_logic_vector(2*TRANS_STREAMS-1 downto 0);
        begin
            if (rising_edge(CLK_PLAN)) then

                reg_tmp := p_in_reg;

                if (p2o_asfifo_full='0') then
                    reg_tmp := (others => '0');
                end if;

                for i in 0 to TRANS_STREAMS-1 loop
                    if (P_CONF_VLD(i)='1') then
                        -- Add new propagation
                        reg_tmp(i) := '1';
                        -- Override old color (should only happen for previously non-valid items)
                        reg_tmp(TRANS_STREAMS+i) := P_CONF_COLOR(i);
                    end if;
                end loop;

                p_in_reg <= reg_tmp;

                if (RESET_PLAN='1') then
                    p_in_reg <= (others => '0');
                end if;
            end if;
        end process;

        p_to_o_asfifox_i : entity work.ASFIFOX
        generic map(
            DATA_WIDTH          => 2*TRANS_STREAMS,
            ITEMS               => 64             ,
            RAM_TYPE            => "LUT"          ,
            FWFT_MODE           => true           ,
            OUTPUT_REG          => true           ,
            DEVICE              => DEVICE         ,
            ALMOST_FULL_OFFSET  => 0              ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            WR_CLK    => CLK_PLAN       ,
            WR_RST    => RESET_PLAN     ,
            WR_DATA   => p_in_reg       ,
            WR_EN     => (or p_in_reg(TRANS_STREAMS-1 downto 0)), -- Write when at least one signal is valid
            WR_FULL   => p2o_asfifo_full,
            WR_AFULL  => open           ,
            WR_STATUS => open           ,

            RD_CLK    => CLK_OTHER       ,
            RD_RST    => RESET_OTHER     ,
            RD_DATA   => p2o_asfifo_do   ,
            RD_EN     => '1'             ,
            RD_EMPTY  => p2o_asfifo_empty,
            RD_AEMPTY => open            ,
            RD_STATUS => open
        );

        plan_conf_color <= p2o_asfifo_do(TRANS_STREAMS*2-1 downto TRANS_STREAMS);
        plan_conf_vld   <= p2o_asfifo_do(TRANS_STREAMS-1 downto 0) and (not p2o_asfifo_empty);

        -- -----------------------------------------------------------------

        -- -----------------------------------------------------------------
        -- Others to Planner Asynch connection
        -- -----------------------------------------------------------------
        -- These registers save signal when it cannot be propagated because
        -- ASFIFOX is full (should not happen very often).

        o_in_reg_pr : process (CLK_OTHER)
            variable reg_tmp : std_logic_vector(2*TRANS_STREAMS-1 downto 0);
        begin
            if (rising_edge(CLK_OTHER)) then

                reg_tmp := o_in_reg;

                if (o2p_asfifo_full='0') then
                    reg_tmp := (others => '0');
                end if;

                for i in 0 to TRANS_STREAMS-1 loop
                    if (O_NEW_RX_TRANS(i)='1') then
                        -- Add new propagation
                        reg_tmp(i) := '1';
                    end if;
                    if (O_CONF_PROPAGATED(i)='1') then
                        -- Add new propagation
                        reg_tmp(TRANS_STREAMS+i) := '1';
                    end if;
                end loop;

                o_in_reg <= reg_tmp;

                if (RESET_OTHER='1') then
                    o_in_reg <= (others => '0');
                end if;
            end if;
        end process;

        o_to_p_asfifox_i : entity work.ASFIFOX
        generic map(
            DATA_WIDTH          => 2*TRANS_STREAMS,
            ITEMS               => 64             ,
            RAM_TYPE            => "LUT"          ,
            FWFT_MODE           => true           ,
            OUTPUT_REG          => true           ,
            DEVICE              => DEVICE         ,
            ALMOST_FULL_OFFSET  => 0              ,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            WR_CLK    => CLK_OTHER      ,
            WR_RST    => RESET_OTHER    ,
            WR_DATA   => o_in_reg       ,
            WR_EN     => (or o_in_reg)  , -- Write when at least one signal is valid
            WR_FULL   => o2p_asfifo_full,
            WR_AFULL  => open           ,
            WR_STATUS => open           ,

            RD_CLK    => CLK_PLAN        ,
            RD_RST    => RESET_PLAN      ,
            RD_DATA   => o2p_asfifo_do   ,
            RD_EN     => '1'             ,
            RD_EMPTY  => o2p_asfifo_empty,
            RD_AEMPTY => open            ,
            RD_STATUS => open
        );

        P_CONF_PROPAGATED <= o2p_asfifo_do(TRANS_STREAMS*2-1 downto TRANS_STREAMS) and (not o2p_asfifo_empty);
        P_NEW_RX_TRANS    <= o2p_asfifo_do(TRANS_STREAMS-1 downto 0) and (not o2p_asfifo_empty);

        -- -----------------------------------------------------------------

    else generate

        -- -----------------------------------------------------------------
        -- Direct connection
        -- -----------------------------------------------------------------

        P_NEW_RX_TRANS    <= O_NEW_RX_TRANS;
        plan_conf_color   <= P_CONF_COLOR;
        plan_conf_vld     <= P_CONF_VLD;
        P_CONF_PROPAGATED <= O_CONF_PROPAGATED;

        -- -----------------------------------------------------------------

    end generate;

    -- -----------------------------------------------------------------
    -- Color confirmation delay
    -- -----------------------------------------------------------------

    -- Delaying Color confirmation signal for Color change
    plan_conf_delay_pr : process (CLK_OTHER)
    begin
        if (rising_edge(CLK_OTHER)) then

            plan_conf_color_delayed(COLOR_CONF_DELAY) <= plan_conf_color;
            plan_conf_vld_delayed  (COLOR_CONF_DELAY) <= plan_conf_vld;
            for i in 0 to COLOR_CONF_DELAY-1 loop
                plan_conf_color_delayed(i) <= plan_conf_color_delayed(i+1);
                plan_conf_vld_delayed  (i) <= plan_conf_vld_delayed  (i+1);
            end loop;

            if (RESET_OTHER='1') then
                plan_conf_vld_delayed(COLOR_CONF_DELAY-1 downto 0) <= (others => (others => '0'));
            end if;
        end if;
    end process;

    O_CONF_COLOR <= plan_conf_color_delayed(0);
    O_CONF_VLD   <= plan_conf_vld_delayed  (0);

    -- -----------------------------------------------------------------

end architecture;
