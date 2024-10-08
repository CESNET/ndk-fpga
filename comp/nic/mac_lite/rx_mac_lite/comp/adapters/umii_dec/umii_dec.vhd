-- umii_dec.vhd: Universal MII decoder (XGMII, XLGMII, CGMII, CDMII)
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity UMII_DEC is
    generic(
        -- =====================================================================
        -- UNIVERSAL MII DECODER CONFIGURATION:
        -- =====================================================================
        -- Data width of MII data signal, must be power of two, minimum is 64
        MII_DW           : natural := 2048;
        -- Length of link error timeout counter (number of counter bits)
        CNT_ERROR_LENGTH : natural := 5;
        -- Turns on the start aligner (to 8 bytes), only for XGMII interface,
        -- when is enabled MII_VLD must be set to VCC.
        XGMII_ALIGN_EN   : boolean := (MII_DW=64);
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        -- WARNING: The MFB parameters are calculated automatically, they cannot
        -- be changed manually!!!
        REGIONS          : natural := max(MII_DW/512,1);
        BLOCK_SIZE       : natural := 8; -- SOF must be aligned by 8 bytes
        ITEM_WIDTH       : natural := 8; -- one item = one byte
        REGION_SIZE      : natural := (MII_DW/REGIONS)/(BLOCK_SIZE*ITEM_WIDTH)
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK            : in  std_logic;
        RESET          : in  std_logic;
        -- =====================================================================
        -- INPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
        -- =====================================================================
        -- MII signal with data bits
        MII_RXD        : in  std_logic_vector(MII_DW-1 downto 0);
        -- MII signal with control flags
        MII_RXC        : in  std_logic_vector(MII_DW/8-1 downto 0);
        -- Valid signal of MII word, set to VCC if this signal is not needed.
        MII_VLD        : in  std_logic;
        -- =====================================================================
        -- OUTPUT MFB LIKE INTERFACE
        -- =====================================================================
        TX_DATA        : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_SOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_ERR         : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY     : out std_logic;
        -- =====================================================================
        -- OUTPUT LINK STATE INTERFACE
        -- =====================================================================
        -- Active when link is up
        LINK_UP        : out std_logic;
        -- Active while receiving a frame
        INCOMING_FRAME : out std_logic
   );
end entity;

architecture FULL of UMII_DEC is

    constant MII_CW       : natural := MII_DW/8;
    constant REGION_ITEMS : natural := REGION_SIZE*BLOCK_SIZE;
    constant REGION_WIDTH : natural := REGION_ITEMS*ITEM_WIDTH;
    constant DATA_WIDTH   : natural := REGIONS*REGION_WIDTH;
    constant SOF_POS_SIZE : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_SIZE : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

    signal mii_rxd_in                       : std_logic_vector(MII_DW-1 downto 0);
    signal mii_rxc_in                       : std_logic_vector(MII_CW-1 downto 0);
    signal mii_vld_in                       : std_logic;

   -- logic stage 1
   signal s_is_locfault                     : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_preamble                     : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_terminate                    : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_error                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_start                       : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_pos_terminate                   : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);

   -- register stage 1
   signal s_mii_rxd_reg1                    : std_logic_vector(MII_DW-1 downto 0);
   signal s_mii_rxc_reg1                    : std_logic_vector(MII_CW-1 downto 0);
   signal s_is_locfault_reg1                : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_preamble_reg1                : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_terminate_reg1               : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_error_reg1                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_start_reg1                  : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_pos_terminate_reg1              : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_valid_reg1                      : std_logic;

   -- logic stage 2
   signal s_link_error                      : std_logic;
   signal s_pos_first_terminate             : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_pos_last_terminate              : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_pos_last_terminate_after64      : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_pos_last_terminate_after        : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);

   -- register stage 2
   signal s_mii_rxd_reg2                    : std_logic_vector(MII_DW-1 downto 0);
   signal s_mii_rxc_reg2                    : std_logic_vector(MII_CW-1 downto 0);
   signal s_is_preamble_reg2                : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_terminate_reg2               : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_start_reg2                  : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_link_error_reg2                 : std_logic;
   signal s_pos_first_terminate_reg2        : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_pos_last_terminate_after_reg2   : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_valid_reg2                      : std_logic;

   -- logic stage 3
   signal s_pos_first_terminate_before      : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_is_some_terminate               : std_logic;
   signal s_cnt_let_en                      : std_logic;
   signal s_cnt_let_nxt_uns                 : unsigned(CNT_ERROR_LENGTH-1 downto 0);
   signal s_pos_start_masked                : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_pos_start_selected              : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_is_first_start                  : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_first_start                 : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_pos_first_start_wider           : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_pos_first_start_after           : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);

   signal s_eof_temp                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_prev                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_pos_temp                    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);

   -- register stage 3
   signal s_cnt_let_uns_reg3                : unsigned(CNT_ERROR_LENGTH-1 downto 0);
   signal s_link_up_reg3                    : std_logic;
   signal s_mii_rxd_reg3                    : std_logic_vector(MII_DW-1 downto 0);
   signal s_mii_rxc_reg3                    : std_logic_vector(MII_CW-1 downto 0);
   signal s_is_preamble_reg3                : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_first_terminate_before_reg3 : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_is_first_start_reg3             : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_first_start_reg3            : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_pos_first_start_after_reg3      : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_valid_reg3                      : std_logic;

   signal s_eof_reg3                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_prev_reg3                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_pos_reg3                    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);

   -- logic stage 4
   signal s_mii_rxc_reg3_arr                : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_sof_temp                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_next                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_ctrl                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_ctrl_after_start            : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_pos_ctrl_before_terminate       : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_is_ctrl_after_start_n           : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_ctrl_before_terminate_n      : std_logic_vector(REGIONS-1 downto 0);
   signal s_pos_first_start_rol             : slv_array_t(REGIONS-1 downto 0)(REGION_SIZE-1 downto 0);
   signal s_pos_first_terminate_ror         : slv_array_t(REGIONS-1 downto 0)(REGION_ITEMS-1 downto 0);
   signal s_sof_pos_temp                    : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal s_sof_ok                          : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_ok                          : std_logic_vector(REGIONS-1 downto 0);

   -- register stage 4
   signal s_mii_rxd_reg4                    : std_logic_vector(MII_DW-1 downto 0);
   signal s_sof_reg4                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_reg4                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_next_reg4                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_prev_reg4                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_pos_reg4                    : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal s_eof_pos_reg4                    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_sof_ok_reg4                     : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_ok_reg4                     : std_logic_vector(REGIONS-1 downto 0);
   signal s_is_ctrl_reg4                    : std_logic_vector(REGIONS-1 downto 0);
   signal s_valid_reg4                      : std_logic;

   -- logic stage 5
   signal s_sof_mx                          : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_ok_mx                       : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_pos_mx                      : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal s_eof_sel_old                     : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_mx                          : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_ok_mx                       : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_pos_mx                      : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_data_err                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_err                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_err                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_ctrl_err                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_before_eof                  : std_logic_vector(REGIONS-1 downto 0);
   signal s_whole_frame                     : std_logic_vector(REGIONS-1 downto 0);

   -- register stage 5
   signal s_sof_last_reg5                   : std_logic;
   signal s_sof_pos_last_reg5               : std_logic_vector(SOF_POS_SIZE-1 downto 0);
   signal s_sof_ok_last_reg5                : std_logic;
   signal s_sof_next_last_reg5              : std_logic;
   signal s_mii_rxd_reg5                    : std_logic_vector(MII_DW-1 downto 0);
   signal s_wf_reg5                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_reg5                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_reg5                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_pos_reg5                    : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal s_eof_pos_reg5                    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_sof_err_reg5                    : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_err_reg5                    : std_logic_vector(REGIONS-1 downto 0);
   signal s_ctrl_err_reg5                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_data_err_reg5                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_valid_reg5                      : std_logic;

   -- logic stage 6
   signal s_sof_fsm                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_fsm                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_err_fsm                         : std_logic_vector(REGIONS-1 downto 0);
   signal s_inc_frame                       : std_logic_vector(REGIONS downto 0);
   signal s_valid_region                    : std_logic_vector(REGIONS-1 downto 0);
   signal s_valid_word                      : std_logic;

   -- register stage 6
   signal s_is_frame_reg6                   : std_logic;
   signal s_data_reg6                       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal s_sof_reg6                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_eof_reg6                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_sof_pos_reg6                    : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal s_eof_pos_reg6                    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_err_reg6                        : std_logic_vector(REGIONS-1 downto 0);
   signal s_valid_reg6                      : std_logic;

begin

    -- asserts
    assert (BLOCK_SIZE = 8 and ITEM_WIDTH = 8)
        report "UMII_DEC: BLOCK_SIZE and ITEM_WIDTH must be 8, other values are not supported!!!"
        severity failure;

    -- XGMII aligner
    xgmii_align_on_g : if XGMII_ALIGN_EN generate
        xgmii_align_i : entity work.RX_MAC_LITE_XGMII_ALIGN
        port map(
            CLK           => CLK,
            RESET         => RESET,
            IN_XGMII_RXD  => MII_RXD,
            IN_XGMII_RXC  => MII_RXC,
            OUT_XGMII_RXD => mii_rxd_in,
            OUT_XGMII_RXC => mii_rxc_in
        );
        --
        mii_vld_in <= '1';
    end generate;

    xgmii_align_off_g : if not XGMII_ALIGN_EN generate
        mii_rxd_in <= MII_RXD;
        mii_rxc_in <= MII_RXC;
        mii_vld_in <= MII_VLD;
    end generate;

    -- =========================================================================
    -- 1. LOGIC STAGE
    -- =========================================================================

    umii_ctrl_dec_g : for r in 0 to REGIONS-1 generate
        -- Decoder of controls and sequences positions
        umii_ctrl_dec_i : entity work.UMII_CTRL_DEC
        generic map(
            MII_DW => REGION_WIDTH
        )
        port map(
            MII_RXD       => mii_rxd_in((r+1)*REGION_WIDTH-1 downto r*REGION_WIDTH),
            MII_RXC       => mii_rxc_in((r+1)*REGION_ITEMS-1 downto r*REGION_ITEMS),

            IS_LOCFAULT   => s_is_locfault(r),
            IS_PREAMBLE   => s_is_preamble(r),
            IS_START      => open,
            IS_TERMINATE  => s_is_terminate(r),
            IS_ERROR      => s_is_error(r),

            POS_LOCFAULT  => open,
            POS_PREAMBLE  => open,
            POS_START     => s_pos_start(r),
            POS_TERMINATE => s_pos_terminate(r),
            POS_ERROR     => open
        );
    end generate;

    -- =========================================================================
    -- 1. REGISTERS STAGE
    -- =========================================================================

    reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_mii_rxd_reg1       <= mii_rxd_in;
            s_mii_rxc_reg1       <= mii_rxc_in;
            s_is_locfault_reg1   <= s_is_locfault;
            s_is_preamble_reg1   <= s_is_preamble;
            s_is_terminate_reg1  <= s_is_terminate;
            s_is_error_reg1      <= s_is_error;
            s_pos_start_reg1     <= s_pos_start;
            s_pos_terminate_reg1 <= s_pos_terminate;
        end if;
    end process;

    vld_reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg1 <= '0';
            else
                s_valid_reg1 <= mii_vld_in;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 2. LOGIC STAGE
    -- =========================================================================

    -- On link is error
    s_link_error <= (or s_is_error_reg1) or (or s_is_locfault_reg1);

    -- First and last Terminate position
    terminate_first_last_g : for r in 0 to REGIONS-1 generate
        first_terminate_i : entity work.FIRST_ONE
        generic map (
            DATA_WIDTH => REGION_ITEMS
        )
        port map (
            DI => s_pos_terminate_reg1(r),
            DO => s_pos_first_terminate(r)
        );

        last_terminate_i : entity work.LAST_ONE
        generic map (
            DATA_WIDTH => REGION_ITEMS
        )
        port map (
            DI => s_pos_terminate_reg1(r),
            DO => s_pos_last_terminate(r)
        );
    end generate;

    after_terminate_g : for r in 0 to REGIONS-1 generate
        -- after last terminate
        pos_last_terminate_after64_i : entity work.AFTER_ONE
        generic map (
            DATA_WIDTH     => REGION_ITEMS,
            IMPLEMENTATION => "P-OR"
        )
        port map (
            DI => s_pos_last_terminate(r),
            DO => s_pos_last_terminate_after64(r)
        );

        pos_last_terminate_after_g : for i in 0 to REGION_SIZE-1 generate
            s_pos_last_terminate_after(r)(i) <= s_pos_last_terminate_after64(r)(i*BLOCK_SIZE);
        end generate;
    end generate;

    -- =========================================================================
    -- 2. REGISTERS STAGE
    -- =========================================================================

    reg2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_mii_rxd_reg2                  <= s_mii_rxd_reg1;
            s_mii_rxc_reg2                  <= s_mii_rxc_reg1;
            s_is_preamble_reg2              <= s_is_preamble_reg1;
            s_is_terminate_reg2             <= s_is_terminate_reg1;
            s_pos_start_reg2                <= s_pos_start_reg1;
            s_pos_first_terminate_reg2      <= s_pos_first_terminate;
            s_pos_last_terminate_after_reg2 <= s_pos_last_terminate_after;
            s_link_error_reg2               <= s_link_error;
        end if;
    end process;

    vld_reg2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg2 <= '0';
            else
                s_valid_reg2 <= s_valid_reg1;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 3. LOGIC STAGE
    -- =========================================================================

    -- terminate in any region
    s_is_some_terminate <= or s_is_terminate_reg2;

    -- link error timeout counter enable
    s_cnt_let_en <= s_valid_reg2 and (or s_cnt_let_uns_reg3);

    -- link error timeout counter logic
    s_cnt_let_nxt_uns_p : process (all)
    begin
        if (s_link_error_reg2 = '1') then
            s_cnt_let_nxt_uns <= (others => '1');
        elsif (s_is_some_terminate = '1') then
            s_cnt_let_nxt_uns <= (others => '0');
        else
            s_cnt_let_nxt_uns <= s_cnt_let_uns_reg3 - 1;
        end if;
    end process;

    before_terminate_g : for r in 0 to REGIONS-1 generate
        -- before first terminate
        pos_first_terminate_before_i : entity work.BEFORE_ONE
        generic map (
            DATA_WIDTH     => REGION_ITEMS,
            IMPLEMENTATION => "P-OR"
        )
        port map (
            DI => s_pos_first_terminate_reg2(r),
            DO => s_pos_first_terminate_before(r)
        );
    end generate;

    -- Decoding start position
    start_position_dec_g : for r in 0 to REGIONS-1 generate
        -- Masked start position before last terminate
        s_pos_start_masked(r) <= s_pos_start_reg2(r) and s_pos_last_terminate_after_reg2(r);

        -- Selected start position after last terminate
        s_pos_start_selected(r) <= s_pos_start_reg2(r) when (s_is_terminate_reg2(r) = '0') else
                                    s_pos_start_masked(r);

        -- Is selected start position?
        s_is_first_start(r) <= or s_pos_start_selected(r);

        first_start_i : entity work.FIRST_ONE
        generic map (
            DATA_WIDTH => REGION_SIZE
        )
        port map (
            DI => s_pos_start_selected(r),
            DO => s_pos_first_start(r)
        );

        -- Wider start position
        first_start_wider_g : for i in 0 to REGION_SIZE-1 generate
            s_pos_first_start_wider(r)((i+1)*BLOCK_SIZE-1 downto i*BLOCK_SIZE+1) <= (others => '0');
            s_pos_first_start_wider(r)(i*BLOCK_SIZE) <= s_pos_first_start(r)(i);
        end generate;

        pos_first_start_after_i : entity work.AFTER_ONE
        generic map (
            DATA_WIDTH     => REGION_ITEMS,
            IMPLEMENTATION => "P-OR"
        )
        port map (
            DI => s_pos_first_start_wider(r),
            DO => s_pos_first_start_after(r)
        );
    end generate;

    eof_pos_temp_g : for r in 0 to REGIONS-1 generate
        -- Active when at least one Terminate control character occurs
        s_eof_temp(r) <= s_is_terminate_reg2(r);

        -- Indication that EOF will be asserted in the previous MFB region
        s_eof_prev(r) <= s_pos_first_terminate_reg2(r)(0);

        -- Rotate Terminate position to the right by 1 (truncate the Terminate)
        s_pos_first_terminate_ror(r) <= s_pos_first_terminate_reg2(r)(0) &
                                        s_pos_first_terminate_reg2(r)(REGION_ITEMS-1 downto 1);

        -- EOP position encoder (REGION_ITEMS possible values)
        eop_pos_enc_i : entity work.gen_enc
        generic map (
            ITEMS => REGION_ITEMS
        )
        port map (
            DI    => s_pos_first_terminate_ror(r),
            ADDR  => s_eof_pos_temp(r)
        );
    end generate;

    -- =========================================================================
    -- 3. REGISTERS STAGE
    -- =========================================================================

    -- link error timeout counter
    cnt_let_uns_reg3_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_cnt_let_uns_reg3 <= (others => '0');
            elsif (s_cnt_let_en = '1') then
                s_cnt_let_uns_reg3 <= s_cnt_let_nxt_uns;
            end if;
        end if;
    end process;

    -- link_up register
    link_up_reg3_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_link_up_reg3 <= '0';
            else
                s_link_up_reg3 <= nor s_cnt_let_uns_reg3;
            end if;
        end if;
    end process;

    reg3_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_mii_rxd_reg3                    <= s_mii_rxd_reg2;
            s_mii_rxc_reg3                    <= s_mii_rxc_reg2;
            s_is_preamble_reg3                <= s_is_preamble_reg2;
            s_pos_first_terminate_before_reg3 <= s_pos_first_terminate_before;
            s_is_first_start_reg3             <= s_is_first_start;
            s_pos_first_start_reg3            <= s_pos_first_start;
            s_pos_first_start_after_reg3      <= s_pos_first_start_after;
            s_eof_reg3                        <= s_eof_temp;
            s_eof_prev_reg3                   <= s_eof_prev;
            s_eof_pos_reg3                    <= s_eof_pos_temp;
        end if;
    end process;

    vld_reg3_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg3 <= '0';
            else
                s_valid_reg3 <= s_valid_reg2;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 4. LOGIC STAGE
    -- =========================================================================

    -- Deriving SOP, SOP_POS, EOP, EOP_POS and related signals
    deriving_signals_g : for r in 0 to REGIONS-1 generate
        s_mii_rxc_reg3_arr(r) <= s_mii_rxc_reg3((r+1)*REGION_ITEMS-1 downto r*REGION_ITEMS);

        -- Active when at least one Start control character occurs
        s_sof_temp(r) <= s_is_first_start_reg3(r);

        -- Indication that SOF will be asserted in the next MFB region
        s_sof_next(r) <= s_pos_first_start_reg3(r)(REGION_SIZE-1);

        -- Rotate Start position to the left by 1 (jump over the Preamble)
        s_pos_first_start_rol(r) <= s_pos_first_start_reg3(r)(REGION_SIZE-2 downto 0) &
        s_pos_first_start_reg3(r)(REGION_SIZE-1);

        -- SOP position encoder (REGION_SIZE possible values)
        sop_pos_enc_i : entity work.gen_enc
        generic map (
            ITEMS => REGION_SIZE
        )
        port map (
            DI    => s_pos_first_start_rol(r),
            ADDR  => s_sof_pos_temp(r)
        );

        -- Active when at least one control character occurs
        s_is_ctrl(r) <= or s_mii_rxc_reg3_arr(r);

        -- Is control after Start character?
        s_pos_ctrl_after_start(r) <= s_pos_first_start_after_reg3(r) and s_mii_rxc_reg3_arr(r);
        -- Is control before Terminate character?
        s_pos_ctrl_before_terminate(r) <= s_pos_first_terminate_before_reg3(r) and s_mii_rxc_reg3_arr(r);

        -- Detection whether there are some control characters after Start
        s_is_ctrl_after_start_n(r) <= nor s_pos_ctrl_after_start(r);

        -- Detection whether there are some control characters before Terminate
        s_is_ctrl_before_terminate_n(r) <= nor s_pos_ctrl_before_terminate(r);

        -- Active when there are no control characters in the range given by
        -- Start and Terminate or Start and the end of the word and least one
        -- Preamble pattern occurs
        s_sof_ok(r) <= s_is_ctrl_after_start_n(r) and s_is_preamble_reg3(r);

        -- Active when there are no control characters in the range given by
        -- Start and Terminate or Start of the word and Terminate
        s_eof_ok(r) <= s_is_ctrl_before_terminate_n(r);
    end generate;

    -- =========================================================================
    -- 4. REGISTERS STAGE
    -- =========================================================================

    reg4_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_mii_rxd_reg4  <= s_mii_rxd_reg3;
            s_sof_reg4      <= s_sof_temp;
            s_eof_reg4      <= s_eof_reg3;
            s_sof_next_reg4 <= s_sof_next;
            s_eof_prev_reg4 <= s_eof_prev_reg3;
            s_sof_pos_reg4  <= s_sof_pos_temp;
            s_eof_pos_reg4  <= s_eof_pos_reg3;
            s_sof_ok_reg4   <= s_sof_ok;
            s_eof_ok_reg4   <= s_eof_ok;
            s_is_ctrl_reg4  <= s_is_ctrl;
        end if;
    end process;

    vld_reg4_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg4 <= '0';
            else
                s_valid_reg4 <= s_valid_reg3;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 5. LOGIC STAGE
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- Multiplexors of SOFs signals
    -- -------------------------------------------------------------------------

    s_sof_mx(0) <= '0' when (s_sof_next_reg4(0) = '1') else
        s_sof_last_reg5 when (s_sof_next_last_reg5 = '1' and s_sof_reg4(0) = '0') else
        s_sof_reg4(0); -- when (eop_prev = '0' or reg4_eop = '0') else '0'; --?????

    s_sof_ok_mx(0) <= '0' when (s_sof_next_reg4(0) = '1') else
        s_sof_ok_last_reg5 when (s_sof_next_last_reg5 = '1' and s_sof_reg4(0) = '0') else
        s_sof_ok_reg4(0);

    s_sof_pos_mx(0) <= (others => '0') when (s_sof_next_reg4(0) = '1') else
        s_sof_pos_last_reg5 when (s_sof_next_last_reg5 = '1' and s_sof_reg4(0) = '0') else
        s_sof_pos_reg4(0);

    sof_mx_g : for r in 1 to REGIONS-1 generate
        s_sof_mx(r) <= '0' when (s_sof_next_reg4(r) = '1') else
            s_sof_reg4(r-1) when (s_sof_next_reg4(r-1) = '1' and s_sof_reg4(r) = '0') else
            s_sof_reg4(r); -- when (eop_prev = '0' or reg4_eop = '0') else '0'; --?????

        s_sof_ok_mx(r) <= '0' when (s_sof_next_reg4(r) = '1') else
            s_sof_ok_reg4(r-1) when (s_sof_next_reg4(r-1) = '1' and s_sof_reg4(r) = '0') else
            s_sof_ok_reg4(r);

        s_sof_pos_mx(r) <= (others => '0') when (s_sof_next_reg4(r) = '1') else
            s_sof_pos_reg4(r-1) when (s_sof_next_reg4(r-1) = '1' and s_sof_reg4(r) = '0') else
            s_sof_pos_reg4(r);
    end generate;

    -- -------------------------------------------------------------------------
    -- Multiplexors of EOFs signals
    -- -------------------------------------------------------------------------

    eof_mx_g : for r in 0 to REGIONS-2 generate
        s_eof_sel_old(r) <= s_eof_prev_reg4(r+1) and not s_eof_reg4(r);

        s_eof_mx(r) <= '0' when (s_eof_prev_reg4(r) = '1') else
            s_eof_reg4(r+1) when (s_eof_sel_old(r) = '1') else
            s_eof_reg4(r);

        s_eof_ok_mx(r) <= '0' when (s_eof_prev_reg4(r) = '1') else
            s_eof_ok_reg4(r+1) when (s_eof_sel_old(r) = '1') else
            s_eof_ok_reg4(r);

        s_eof_pos_mx(r) <= (others => '0') when (s_eof_prev_reg4(r) = '1') else
            s_eof_pos_reg4(r+1) when (s_eof_sel_old(r) = '1') else
            s_eof_pos_reg4(r);
    end generate;

    s_eof_sel_old(REGIONS-1) <= s_eof_prev_reg3(0) and s_valid_reg3 and not s_eof_reg4(REGIONS-1);

    s_eof_mx(REGIONS-1) <= '0' when (s_eof_prev_reg4(REGIONS-1) = '1') else s_eof_reg3(0) when (s_eof_sel_old(REGIONS-1) = '1') else s_eof_reg4(REGIONS-1);

    s_eof_ok_mx(REGIONS-1) <= '0' when (s_eof_prev_reg4(REGIONS-1) = '1') else s_eof_ok(0) when (s_eof_sel_old(REGIONS-1) = '1') else s_eof_ok_reg4(REGIONS-1);

    s_eof_pos_mx(REGIONS-1) <= (others => '0') when (s_eof_prev_reg4(REGIONS-1) = '1') else s_eof_pos_reg3(0) when (s_eof_sel_old(REGIONS-1) = '1') else s_eof_pos_reg4(REGIONS-1);

    -- -------------------------------------------------------------------------
    -- Data error: Active when there are no data between Start and Terminate
    -- -------------------------------------------------------------------------

    data_err_r1_g : if REGIONS = 1 generate
        s_data_err(0) <= (s_sof_next_last_reg5 and s_eof_prev_reg4(0)) or (s_sof_next_reg4(0) and (s_eof_prev_reg3(0) and s_valid_reg3));
    end generate;

    data_err_r1p_g : if REGIONS > 1 generate
        s_data_err(0) <= (s_sof_next_last_reg5 and s_eof_prev_reg4(0)) or (s_sof_next_reg4(0) and s_eof_prev_reg4(1));
        data_err_g : for r in 1 to REGIONS-2 generate
            s_data_err(r) <= (s_sof_next_reg4(r-1) and s_eof_prev_reg4(r)) or (s_sof_next_reg4(r) and s_eof_prev_reg4(r+1));
        end generate;
        s_data_err(REGIONS-1) <= (s_sof_next_reg4(REGIONS-2) and s_eof_prev_reg4(REGIONS-1)) or (s_sof_next_reg4(REGIONS-1) and (s_eof_prev_reg3(0) and s_valid_reg3));
    end generate;

    ----------------------------------------------------------------------------
    -- Others error signals derivation
    ----------------------------------------------------------------------------

    error_derivation_g : for r in 0 to REGIONS-1 generate
        -- Erroneous SOF
        s_sof_err(r) <= s_sof_mx(r) and (not s_sof_ok_mx(r));
        -- Erroneous EOF
        s_eof_err(r) <= s_eof_mx(r) and (not s_eof_ok_mx(r));

        -- Control characters other than Start or Terminate occured
        s_ctrl_err(r) <= (not s_sof_reg4(r)) and (not s_eof_reg4(r)) and (s_is_ctrl_reg4(r));

        -- SOF is before EOF, position of SOF is smaller than of EOF
        s_sof_before_eof(r) <= '1' when ((unsigned(s_sof_pos_mx(r)) & "000") < unsigned(s_eof_pos_mx(r))) else '0';

        -- Active when there is a whole frame in one word
        s_whole_frame(r) <= s_sof_mx(r) and s_eof_mx(r) and s_sof_before_eof(r);
    end generate;

    -- =========================================================================
    -- 5. REGISTERS STAGE
    -- =========================================================================

    sof_last_reg5_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_valid_reg4 = '1') then
                s_sof_last_reg5     <= s_sof_reg4(REGIONS-1);
                s_sof_pos_last_reg5 <= s_sof_pos_reg4(REGIONS-1);
                s_sof_ok_last_reg5  <= s_sof_ok_reg4(REGIONS-1);
            end if;
        end if;
    end process;

    sof_next_last_reg5_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_sof_next_last_reg5 <= '0';
            elsif (s_valid_reg4 = '1') then
                s_sof_next_last_reg5 <= s_sof_next_reg4(REGIONS-1);
            end if;
        end if;
    end process;

    reg5_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_mii_rxd_reg5  <= s_mii_rxd_reg4;
            s_wf_reg5       <= s_whole_frame;
            s_sof_reg5      <= s_sof_mx;
            s_eof_reg5      <= s_eof_mx;
            s_sof_pos_reg5  <= s_sof_pos_mx;
            s_eof_pos_reg5  <= s_eof_pos_mx;
            s_sof_err_reg5  <= s_sof_err;
            s_eof_err_reg5  <= s_eof_err;
            s_ctrl_err_reg5 <= s_ctrl_err;
            s_data_err_reg5 <= s_data_err;
        end if;
    end process;

    vld_reg5_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg5 <= '0';
            else
                s_valid_reg5 <= s_valid_reg4;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 6. LOGIC STAGE
    -- =========================================================================

    -- FSM instantiation
    umii_dec_fsm_i : entity work.UMII_DEC_FSM
    generic map (
        REGIONS => REGIONS
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,
        ENABLE      => s_valid_reg5,
        IN_WF       => s_wf_reg5,
        IN_SOF      => s_sof_reg5,
        IN_EOF      => s_eof_reg5,
        IN_SOF_ERR  => s_sof_err_reg5,
        IN_EOF_ERR  => s_eof_err_reg5,
        IN_CTRL_ERR => s_ctrl_err_reg5,
        IN_DATA_ERR => s_data_err_reg5,
        OUT_SOF     => s_sof_fsm,
        OUT_EOF     => s_eof_fsm,
        OUT_ERR     => s_err_fsm
    );

    -- -------------------------------------------------------------------------
    --  FRAME STATE LOGIC
    -- -------------------------------------------------------------------------

    inc_frame_g : for r in 0 to REGIONS-1 generate
        s_inc_frame(r+1) <= (s_sof_fsm(r) and not s_eof_fsm(r) and not s_inc_frame(r)) or
                            (s_sof_fsm(r) and s_eof_fsm(r) and s_inc_frame(r)) or
                            (not s_sof_fsm(r) and not s_eof_fsm(r) and s_inc_frame(r));
    end generate;

    inc_frame_last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_inc_frame(0) <= '0';
            elsif (s_valid_reg5 = '1') then
                s_inc_frame(0) <= s_inc_frame(REGIONS);
            end if;
        end if;
    end process;

    valid_region_g : for r in 0 to REGIONS-1 generate
        s_valid_region(r) <= s_sof_fsm(r) or s_eof_fsm(r) or s_inc_frame(r);
    end generate;
    s_valid_word <= (or s_valid_region) and s_valid_reg5;

    -- =========================================================================
    -- 6. REGISTERS STAGE
    -- =========================================================================

    reg6_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_data_reg6     <= s_mii_rxd_reg5;
            s_sof_reg6      <= s_sof_fsm;
            s_eof_reg6      <= s_eof_fsm;
            s_sof_pos_reg6  <= s_sof_pos_reg5;
            s_eof_pos_reg6  <= s_eof_pos_reg5;
            s_err_reg6      <= s_err_fsm;
        end if;
    end process;

    vld_reg6_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg6 <= '0';
            else
                s_valid_reg6 <= s_valid_word;
            end if;
        end if;
    end process;

    is_frame_reg6_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_is_frame_reg6 <= '0';
            else
                s_is_frame_reg6 <= s_inc_frame(REGIONS) or (or s_sof_fsm);
            end if;
        end if;
    end process;

    -- =========================================================================
    -- OUTPUT PORTS
    -- =========================================================================

    LINK_UP        <= s_link_up_reg3;
    INCOMING_FRAME <= s_is_frame_reg6;

    -- MFB LIKE OUTPUT
    TX_DATA    <= s_data_reg6;
    TX_SOF     <= s_sof_reg6;
    TX_EOF     <= s_eof_reg6;
    TX_SOF_POS <= slv_array_ser(s_sof_pos_reg6,REGIONS,SOF_POS_SIZE);
    TX_EOF_POS <= slv_array_ser(s_eof_pos_reg6,REGIONS,EOF_POS_SIZE);
    TX_ERR     <= s_err_reg6;
    TX_SRC_RDY <= s_valid_reg6;

end architecture;
