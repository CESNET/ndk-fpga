-- planner.vhd: Crossbar data transfer planner
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
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

entity CROSSBARX_PLANNER is
generic (
    -- Data transfer direction
    -- false -> from A to B
    -- true  -> from B to A
    DATA_DIR            : boolean := false;

    -- Transfer data on double frequency Clock
    USE_CLK2            : boolean := true;

    -- Number of independent Transaction Streams with independent Color Conformation mechanism
    TRANS_STREAMS       : integer := 1;

    -- Buffer A size
    BUF_A_COLS          : integer := 512;
    -- max(BUF_A_TRUE_ROWS)
    BUF_A_ROWS          : integer := 8*4;
    -- Buffer B size
    BUF_B_COLS          : integer := 2048;
    -- max(BUF_B_TRUE_ROWS)
    BUF_B_ROWS          : integer := 8*4;
    -- Number of items in one bufer row
    ROW_ITEMS           : integer := 1;
    -- Width of one item
    ITEM_WIDTH          : integer := 8*8;

    -- Width of Color Conformation Timeout counter
    -- The resulting timeout takes 2**COLOR_TIMEOUT_WIDTH cycles to expire.
    -- This affects the maximum latency of CrossbarX Transactions.
    -- WARNING:
    --     When set too low, the Timeout might expire between the arrival
    --     of NEW_RX_TRANS signal and the arrival of the corresponding RX_UINSTR_SRC_RDY.
    --     This could break the entire Color Conformation mechanism!
    COLOR_TIMEOUT_WIDTH : integer := 6;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE              : string := "STRATIX10"
);
port (
    -- ========================
    -- Clock and Reset
    -- ========================

    CLK                : in  std_logic;
    RESET              : in  std_logic;

    -- ========================
    -- Input uInstructions
    -- ========================

    RX_UINSTR_A_COL    : in  slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    RX_UINSTR_B_COL    : in  slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    RX_UINSTR_B_ROW    : in  slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_B_ROWS)-1 downto 0);
    -- row rotation
    RX_UINSTR_ROW_ROT  : in  slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    -- item enable
    RX_UINSTR_IE       : in  slv_array_t     (BUF_A_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    RX_UINSTR_COLOR    : in  std_logic_vector(BUF_A_ROWS-1 downto 0);
    RX_UINSTR_SRC_RDY  : in  std_logic_vector(BUF_A_ROWS-1 downto 0);
    RX_UINSTR_DST_RDY  : out std_logic_vector(BUF_A_ROWS-1 downto 0);

    -- ========================
    -- Output uInstructions
    -- ========================

    -- per src row
    TX_UINSTR_SRC_COL  : out slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_A_ROWS,BUF_B_ROWS)-1 downto 0)(tsel(DATA_DIR,log2(BUF_A_COLS),log2(BUF_B_COLS))-1 downto 0);
    -- per dst row
    TX_UINSTR_SRC_ROW  : out slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(tsel(DATA_DIR,log2(BUF_A_ROWS),log2(BUF_B_ROWS))-1 downto 0);
    TX_UINSTR_DST_COL  : out slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(tsel(DATA_DIR,log2(BUF_B_COLS),log2(BUF_A_COLS))-1 downto 0);
    -- row rotation
    TX_UINSTR_ROW_ROT  : out slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    -- item enable
    TX_UINSTR_IE       : out slv_array_2d_t(2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0)(ROW_ITEMS-1 downto 0);
    TX_UINSTR_SRC_RDY  : out slv_array_t   (2-1 downto 0)(tsel(DATA_DIR,BUF_B_ROWS,BUF_A_ROWS)-1 downto 0);

    -- Color Conformation Timeout cancel signal
    NEW_RX_TRANS       : in  std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- Color Conformation signal
    CONF_COLOR         : out std_logic_vector(TRANS_STREAMS-1 downto 0);
    CONF_VLD           : out std_logic_vector(TRANS_STREAMS-1 downto 0);
    CONF_PROPAGATED    : in  std_logic_vector(TRANS_STREAMS-1 downto 0)
);
end entity;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------

architecture FULL of CROSSBARX_PLANNER is

    -- -----------------------------------------------------------------
    -- Color Conformation logic
    -- -----------------------------------------------------------------

    constant BUF_A_STREAM_ROWS : integer := BUF_A_ROWS/TRANS_STREAMS;

    signal rx_uinstr_curr_color_vld : slv_array_t     (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal rx_uinstr_new_color_vld  : slv_array_t     (TRANS_STREAMS-1 downto 0)(BUF_A_STREAM_ROWS-1 downto 0);
    signal rx_uinstr_curr_color_any : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal rx_uinstr_new_color_any  : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal rx_uinstr_new_color_only : std_logic_vector(TRANS_STREAMS-1 downto 0);

    signal curr_color_reg    : std_logic_vector(TRANS_STREAMS-1 downto 0);
    signal color_timeout_reg : u_array_t       (TRANS_STREAMS-1 downto 0)(COLOR_TIMEOUT_WIDTH+1-1 downto 0);
    signal color_timeout_en  : std_logic_vector(TRANS_STREAMS-1 downto 0);

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- RX uInstruction consumption
    -- -----------------------------------------------------------------

    signal rx_uinstr_color_invld  : std_logic_vector(BUF_A_ROWS-1 downto 0);
    signal rx_uinstr_b_row_eq_vld : slv_array_t(BUF_A_ROWS-1 downto 0)(BUF_A_ROWS-1 downto 0);

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- uInstruction register 0
    -- -----------------------------------------------------------------

    signal reg0_uinstr_a_col   : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal reg0_uinstr_b_col   : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg0_uinstr_b_row   : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(BUF_B_ROWS)-1 downto 0);
    signal reg0_uinstr_row_rot : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal reg0_uinstr_ie      : slv_array_t(BUF_A_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal reg0_uinstr_src_rdy : std_logic_vector(BUF_A_ROWS-1 downto 0);

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- uInstruction register 1
    -- -----------------------------------------------------------------

    signal reg1_lr_first_oneI : i_array_t(BUF_B_ROWS-1 downto 0) := (others => 0);
    signal reg1_lr_uinstr_vld : std_logic_vector(BUF_B_ROWS-1 downto 0);
    signal reg1_rl_first_oneI : i_array_t(BUF_B_ROWS-1 downto 0) := (others => 0);
    signal reg1_rl_uinstr_vld : std_logic_vector(BUF_B_ROWS-1 downto 0);

    signal reg1_uinstr_a_col   : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    signal reg1_uinstr_b_col   : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg1_uinstr_b_row   : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(BUF_B_ROWS)-1 downto 0);
    signal reg1_uinstr_row_rot : slv_array_t(BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal reg1_uinstr_ie      : slv_array_t(BUF_A_ROWS-1 downto 0)(ROW_ITEMS-1 downto 0);
    signal reg1_uinstr_src_rdy : std_logic_vector(BUF_A_ROWS-1 downto 0);

    -- -----------------------------------------------------------------

begin

    -- -----------------------------------------------------------------
    -- Color Conformation logic
    -- -----------------------------------------------------------------

    -- Check if RX uInstructions is divisible by number of Transaction Streams
    assert (BUF_A_STREAM_ROWS*TRANS_STREAMS=BUF_A_ROWS)
        report "CrossbarX: Planner: Number of RX uInstructions (" & to_string(BUF_A_ROWS) & ")" &
               " is not divisible by number of Transaction Streams (" & to_string(TRANS_STREAMS) & ")!"
        severity failure;

    -- Preprocess RX uInstruction Colors
    rx_uinstr_curr_color_gen : for i in 0 to TRANS_STREAMS-1 generate
        rx_uinstr_curr_color_str_gen : for e in 0 to BUF_A_STREAM_ROWS-1 generate
            rx_uinstr_curr_color_vld(i)(e) <= '1' when RX_UINSTR_COLOR(i*BUF_A_STREAM_ROWS+e) =curr_color_reg(i) and RX_UINSTR_SRC_RDY(i*BUF_A_STREAM_ROWS+e)='1' else '0';
            rx_uinstr_new_color_vld (i)(e) <= '1' when RX_UINSTR_COLOR(i*BUF_A_STREAM_ROWS+e)/=curr_color_reg(i) and RX_UINSTR_SRC_RDY(i*BUF_A_STREAM_ROWS+e)='1' else '0';
        end generate;
        rx_uinstr_curr_color_any(i) <= (or rx_uinstr_curr_color_vld(i));
        rx_uinstr_new_color_any (i) <= (or rx_uinstr_new_color_vld (i));

        rx_uinstr_new_color_only(i) <= '1' when rx_uinstr_new_color_any(i)='1' and rx_uinstr_curr_color_any(i)='0' else '0';

        color_conf_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then

                CONF_COLOR(i) <= curr_color_reg(i);
                CONF_VLD  (i) <= '0';

                -- Re-enable Timeout when Confirmation has been successfully propagated
                if (CONF_PROPAGATED(i)='1') then
                    color_timeout_en(i) <= '1';
                end if;

                -- Change Color when only uInstructions with the new Color are present
                if (rx_uinstr_new_color_only(i)='1') then
                    curr_color_reg  (i) <= not curr_color_reg(i);
                    CONF_VLD        (i) <= '1';
                    color_timeout_en(i) <= '0';
                end if;

                -- Change Color when Timeout has expired
                if (color_timeout_reg(i)(COLOR_TIMEOUT_WIDTH)='1') then
                    curr_color_reg  (i) <= not curr_color_reg(i);
                    CONF_VLD        (i) <= '1';
                    color_timeout_en(i) <= '0';
                end if;

                if (RESET='1') then
                    -- Must be initialized to different Color than the Color of first expected RX uInstruction.
                    curr_color_reg  (i) <= '1';
                    color_timeout_en(i) <= '1';
                end if;
            end if;
        end process;

        color_timeout_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then

                color_timeout_reg(i) <= color_timeout_reg(i)+1;

                -- Reset Timeout after it has expired.
                if (color_timeout_reg(i)(COLOR_TIMEOUT_WIDTH)='1') then
                    color_timeout_reg(i) <= (others => '0');
                end if;

                -- Reset Timeout when new uInstructions are to be expected (bearing new Color).
                if (NEW_RX_TRANS(i)='1') then
                    color_timeout_reg(i) <= (others => '0');
                end if;

                -- Reset Timeout when new uInstructions are currently incoming.
                -- (NEW_RX_TRANS might not be active for a long time in case of very long Transactions.)
                if ((or reg0_uinstr_src_rdy((i+1)*BUF_A_STREAM_ROWS-1 downto i*BUF_A_STREAM_ROWS))='1') then
                    color_timeout_reg(i) <= (others => '0');
                end if;

                -- Reset Timeout when the previous Confirmation has not been propagated yet
                if (color_timeout_en(i)='0') then
                    color_timeout_reg(i) <= (others => '0');
                end if;

                if (RESET='1') then
                    color_timeout_reg(i) <= (others => '0');
                end if;
            end if;
        end process;

    end generate;

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- RX uInstruction consumption
    -- -----------------------------------------------------------------

    -- uInstruction invalidation based on Color
    rx_uinstr_color_invld_gen : for i in 0 to BUF_A_ROWS-1 generate
        rx_uinstr_color_invld(i) <= '1' when rx_uinstr_curr_color_any(i/BUF_A_STREAM_ROWS)='1' and RX_UINSTR_COLOR(i)/=curr_color_reg(i/BUF_A_STREAM_ROWS) else '0';
    end generate;

    -- uInstruction Buffer B row address comparisson
    rx_uinstr_b_row_eq_gen : for i in 0 to BUF_A_ROWS-1 generate
        rx_uinstr_b_row_eq_i_gen : for e in 0 to BUF_A_ROWS-1 generate
            --                              '1' when (      uInstructions collide          ) and (   the other is valid   ) and (the other is not invalidated based on its Color) else '0'
            rx_uinstr_b_row_eq_vld(i)(e) <= '1' when (RX_UINSTR_B_ROW(i)=RX_UINSTR_B_ROW(e)) and (RX_UINSTR_SRC_RDY(e)='1') and (          rx_uinstr_color_invld(e)='0'         ) else '0';
        end generate;
    end generate;

    -- uInstruction consumption decision
    double_clk_consum_gen : if (USE_CLK2) generate -- allow one collision
        rx_uinstr_consum_gen : for i in 0 to BUF_A_ROWS-1 generate
            --                      '1' when ((   there is no colliding uInstruction before    ) or (         there is no colliding uInstruction after          )) and (this uInstructions is not invalidated based on its Color) else '0';
            RX_UINSTR_DST_RDY(i) <= '1' when (((or rx_uinstr_b_row_eq_vld(i)(i-1 downto 0))='0') or ((or rx_uinstr_b_row_eq_vld(i)(BUF_A_ROWS-1 downto i+1))='0')) and (            rx_uinstr_color_invld(i)='0'                ) else '0';
        end generate;
    end generate;
    no_double_clk_consum_gen : if (not USE_CLK2) generate -- don't allow any collisions
        rx_uinstr_consum_gen : for i in 0 to BUF_A_ROWS-1 generate
            --                      '1' when ((   there is no colliding uInstruction before    )) and (this uInstructions is not invalidated based on its Color) else '0';
            RX_UINSTR_DST_RDY(i) <= '1' when (((or rx_uinstr_b_row_eq_vld(i)(i-1 downto 0))='0')) and (            rx_uinstr_color_invld(i)='0'                ) else '0';
        end generate;
    end generate;

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- uInstruction register 0
    -- -----------------------------------------------------------------
    -- Save uInstructions, that can be actually planned.

    reg0_uinstr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            reg0_uinstr_a_col   <= RX_UINSTR_A_COL;
            reg0_uinstr_b_col   <= RX_UINSTR_B_COL;
            reg0_uinstr_b_row   <= RX_UINSTR_B_ROW;
            reg0_uinstr_row_rot <= RX_UINSTR_ROW_ROT;
            reg0_uinstr_ie      <= RX_UINSTR_IE;
            reg0_uinstr_src_rdy <= RX_UINSTR_SRC_RDY and RX_UINSTR_DST_RDY;

            if (RESET='1') then
                reg0_uinstr_src_rdy <= (others => '0');
            end if;
        end if;
    end process;

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- uInstruction register 1
    -- -----------------------------------------------------------------
    -- Save uInstrctions as they were.
    -- Precompute Buffer B comparissons and first one detections.

    -- left->right first one detection for all buffer B rows
    reg1_lr_first_one_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            reg1_lr_uinstr_vld <= (others => '0');
            reg1_lr_first_oneI <= (others => 0);
            for i in 0 to BUF_B_ROWS-1 loop
                for e in BUF_A_ROWS-1 downto 0 loop
                    reg1_lr_first_oneI(i) <= e;
                    if (reg0_uinstr_src_rdy(e)='1' and (unsigned(reg0_uinstr_b_row(e))=i or BUF_B_ROWS<2)) then
                        reg1_lr_uinstr_vld(i) <= '1';
                        exit;
                    end if;
                end loop;
            end loop;

            if (RESET='1') then
                reg1_lr_uinstr_vld <= (others => '0');
            end if;
        end if;
    end process;

    -- right->left first one detection for all buffer B rows
    reg1_rl_first_one_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            reg1_rl_uinstr_vld <= (others => '0');
            reg1_rl_first_oneI <= (others => 0);
            for i in 0 to BUF_B_ROWS-1 loop
                for e in 0 to BUF_A_ROWS-1 loop
                    reg1_rl_first_oneI(i) <= e;
                    if (reg0_uinstr_src_rdy(e)='1' and (unsigned(reg0_uinstr_b_row(e))=i or BUF_B_ROWS<2)) then
                        reg1_rl_uinstr_vld(i) <= '1';
                        exit;
                    end if;
                end loop;
            end loop;

            if (RESET='1') then
                reg1_rl_uinstr_vld <= (others => '0');
            end if;
        end if;
    end process;

    reg1_uinstr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            reg1_uinstr_a_col   <= reg0_uinstr_a_col;
            reg1_uinstr_b_col   <= reg0_uinstr_b_col;
            reg1_uinstr_b_row   <= reg0_uinstr_b_row;
            reg1_uinstr_row_rot <= reg0_uinstr_row_rot;
            reg1_uinstr_ie      <= reg0_uinstr_ie;
            reg1_uinstr_src_rdy <= reg0_uinstr_src_rdy;

            if (RESET='1') then
                reg1_uinstr_src_rdy <= (others => '0');
            end if;
        end if;
    end process;

    -- -----------------------------------------------------------------

    -- -----------------------------------------------------------------
    -- uInstruction register 2
    -- -----------------------------------------------------------------
    -- Split uInstructions to 2 plans (if USE_CLK2==true).
    -- Each plan has 1 uInstruction per destination buffer (depends on DATA_DIR).

    reg2_uinstr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (DATA_DIR) then -- A -> B
                TX_UINSTR_SRC_COL <= (others => reg1_uinstr_a_col);

                for i in 0 to BUF_B_ROWS-1 loop
                    TX_UINSTR_SRC_ROW(0)(i) <= std_logic_vector(to_unsigned(reg1_rl_first_oneI(i),log2(BUF_A_ROWS)));
                    TX_UINSTR_DST_COL(0)(i) <= reg1_uinstr_b_col           (reg1_rl_first_oneI(i));
                    TX_UINSTR_ROW_ROT(0)(i) <= reg1_uinstr_row_rot         (reg1_rl_first_oneI(i));
                    TX_UINSTR_IE     (0)(i) <= reg1_uinstr_ie              (reg1_rl_first_oneI(i));
                    TX_UINSTR_SRC_RDY(0)(i) <= reg1_uinstr_src_rdy         (reg1_rl_first_oneI(i)) and reg1_rl_uinstr_vld(i);

                    TX_UINSTR_SRC_ROW(1)(i) <= std_logic_vector(to_unsigned(reg1_lr_first_oneI(i),log2(BUF_A_ROWS)));
                    TX_UINSTR_DST_COL(1)(i) <= reg1_uinstr_b_col           (reg1_lr_first_oneI(i));
                    TX_UINSTR_ROW_ROT(1)(i) <= reg1_uinstr_row_rot         (reg1_lr_first_oneI(i));
                    TX_UINSTR_IE     (1)(i) <= reg1_uinstr_ie              (reg1_lr_first_oneI(i));
                    TX_UINSTR_SRC_RDY(1)(i) <= reg1_uinstr_src_rdy         (reg1_lr_first_oneI(i)) and reg1_lr_uinstr_vld(i);
                end loop;
            else -- B -> A
                for i in 0 to BUF_B_ROWS-1 loop
                    TX_UINSTR_SRC_COL(0)(i) <= reg1_uinstr_b_col(reg1_rl_first_oneI(i));
                    TX_UINSTR_SRC_COL(1)(i) <= reg1_uinstr_b_col(reg1_lr_first_oneI(i));
                end loop;
                TX_UINSTR_SRC_ROW <= (others => reg1_uinstr_b_row);
                TX_UINSTR_DST_COL <= (others => reg1_uinstr_a_col);
                TX_UINSTR_ROW_ROT <= (others => reg1_uinstr_row_rot);
                TX_UINSTR_IE      <= (others => reg1_uinstr_ie);

                TX_UINSTR_SRC_RDY <= (others => (others => '0'));
                for i in 0 to BUF_B_ROWS-1 loop -- OR
                    if (reg1_rl_uinstr_vld(i)='1') then
                        TX_UINSTR_SRC_RDY(0)(reg1_rl_first_oneI(i)) <= '1';
                    end if;
                    if (reg1_lr_uinstr_vld(i)='1') then
                        TX_UINSTR_SRC_RDY(1)(reg1_lr_first_oneI(i)) <= '1';
                    end if;
                end loop;
            end if;

            -- Eliminate plan1 when USE_CLK2==false
            -- This should lead to removal of all reg1_lr_* signals as optimalization
            if (not USE_CLK2) then
                TX_UINSTR_SRC_COL(1) <= (others => (others => '0'));
                TX_UINSTR_SRC_ROW(1) <= (others => (others => '0'));
                TX_UINSTR_DST_COL(1) <= (others => (others => '0'));
                TX_UINSTR_ROW_ROT(1) <= (others => (others => '0'));
                TX_UINSTR_IE     (1) <= (others => (others => '0'));
                TX_UINSTR_SRC_RDY(1) <= (others => '0');
            end if;

            if (RESET='1') then
                TX_UINSTR_SRC_RDY <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- -----------------------------------------------------------------

end architecture;
