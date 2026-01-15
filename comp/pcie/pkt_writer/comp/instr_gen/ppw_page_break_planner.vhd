-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


entity PPW_PAGE_BREAK_PLANNER is
    generic (
        -- Number of MVB Items in a word, can't handle more than 1.
        MVB_ITEMS      : natural := 1;
        -- Maximum packet size (in bytes).
        PKT_MTU        : integer := 2**12;
        ADDRESS_WIDTH  : natural := 64;
        -- Size of a RAM page (in bytes).
        PAGE_SIZE      : natural := 4096;
        DEVICE         : string := "AGILEX"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_MVB_ADDRESS : in  std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_VALID   : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        -- ========================================================
        -- TX Interface
        -- ========================================================

        TX_MVB_ADDRESS : out std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
        TX_MVB_LENGTH  : out std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
        -- Indicates final MVB Item for a packet.
        TX_MVB_LAST    : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VALID   : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of PPW_PAGE_BREAK_PLANNER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant WANTED_BIT        : natural := log2(PAGE_SIZE);

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    type fsm_t is (ST_IDLE, ST_BREAK);

    signal addr_page_init      : unsigned(ADDRESS_WIDTH-log2(PAGE_SIZE)-1 downto 0);
    signal addr_subpage_init   : unsigned(log2(PAGE_SIZE)-1 downto 0);
    signal len2endpage_init    : unsigned(log2(PAGE_SIZE+1)-1 downto 0);
    signal end_address_init    : unsigned(ADDRESS_WIDTH-1 downto 0);
    signal len_over_page_init  : std_logic;
    signal len_over_page_cont  : std_logic;

    signal fsm_pstate          : fsm_t;
    signal fsm_nstate          : fsm_t;

    signal nextpage_addr       : unsigned(ADDRESS_WIDTH-log2(PAGE_SIZE)-1 downto 0);
    signal len2end             : unsigned(log2(PKT_MTU+1)-1 downto 0);
    signal breaking            : std_logic;

    signal nextpage_addr_reg   : unsigned(ADDRESS_WIDTH-log2(PAGE_SIZE)-1 downto 0);
    signal len2end_reg         : unsigned(log2(PKT_MTU+1)-1 downto 0);

    signal s_tx_mvb_address    : std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
    signal s_tx_mvb_length     : std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
    signal s_tx_mvb_last       : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_tx_mvb_valid      : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_tx_mvb_src_rdy    : std_logic;

begin

    RX_MVB_DST_RDY <= TX_MVB_DST_RDY and not (breaking and RX_MVB_SRC_RDY);

    -- =====================================================================
    --  Initial calculations from input data
    -- =====================================================================

    -- Page address (top bits)
    addr_page_init    <= unsigned(RX_MVB_ADDRESS(ADDRESS_WIDTH-1 downto WANTED_BIT));
    -- Address within the page (bottom bits)
    addr_subpage_init <= unsigned(RX_MVB_ADDRESS(WANTED_BIT-1 downto 0));

    -- The length (number of bytes) to the end of the page
    len2endpage_init <= to_unsigned(PAGE_SIZE, log2(PAGE_SIZE+1)) - addr_subpage_init;
    -- Address of the packet's last byte
    end_address_init <= unsigned(RX_MVB_ADDRESS) + unsigned(RX_MVB_LENGTH) - 1;

    -- Packet goes over page and needs at leas one breaking
    len_over_page_init <= '1' when (addr_page_init /= end_address_init(ADDRESS_WIDTH-1 downto WANTED_BIT)) else '0';
    -- Packet needs further braking
    len_over_page_cont <= '1' when (len2end_reg > PAGE_SIZE) else '0';

    -- =====================================================================
    --  FSM
    -- =====================================================================

    fsm_state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MVB_DST_RDY = '1') then
                fsm_pstate <= fsm_nstate;
            end if;
            if (RESET = '1') then
                fsm_pstate <= ST_IDLE;
            end if;
        end if;
    end process;

    fsm_state_transitions_p : process (all)
    begin
        case (fsm_pstate) is
            when ST_IDLE =>
                if ((RX_MVB_SRC_RDY = '1') and (RX_MVB_VALID(0) = '1') and (len_over_page_init = '1')) then
                    fsm_nstate <= ST_BREAK;
                else
                    fsm_nstate <= ST_IDLE;
                end if;
            when ST_BREAK =>
                if (len_over_page_cont = '1') then
                    fsm_nstate <= ST_BREAK;
                else
                    fsm_nstate <= ST_IDLE;
                end if;
        end case;
    end process;

    fsm_state_logic_p : process (all)
    begin
        case (fsm_pstate) is

            when ST_IDLE =>
                s_tx_mvb_address <= RX_MVB_ADDRESS;
                s_tx_mvb_length  <= std_logic_vector(resize(len2endpage_init, log2(PKT_MTU+1))) when (len_over_page_init = '1') else RX_MVB_LENGTH;
                s_tx_mvb_last    <= "0" when (len_over_page_init = '1') else "1";
                s_tx_mvb_valid   <= RX_MVB_VALID;
                s_tx_mvb_src_rdy <= RX_MVB_SRC_RDY;

                nextpage_addr <= addr_page_init + 1;
                len2end       <= unsigned(RX_MVB_LENGTH) - len2endpage_init;
                breaking      <= '0';

            when ST_BREAK =>
                s_tx_mvb_address <= std_logic_vector(resize_right(nextpage_addr_reg, ADDRESS_WIDTH));
                s_tx_mvb_length  <= std_logic_vector(to_unsigned(PAGE_SIZE, log2(PKT_MTU+1))) when (len_over_page_cont = '1') else std_logic_vector(len2end_reg);
                s_tx_mvb_last    <= "0" when (len_over_page_cont = '1') else "1";
                s_tx_mvb_valid   <= (others => '1');
                s_tx_mvb_src_rdy <= '1';

                nextpage_addr <= nextpage_addr_reg + 1;
                len2end       <= len2end_reg - PAGE_SIZE;
                breaking      <= '1';

        end case;
    end process;

    fsm_misc_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((TX_MVB_DST_RDY = '1') and (fsm_nstate = ST_BREAK)) then
                len2end_reg       <= len2end;
                nextpage_addr_reg <= nextpage_addr;
            end if;
        end if;
    end process;

    -- =====================================================================
    --  OUTPUT REGISTER
    -- =====================================================================

    output_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MVB_DST_RDY = '1') then
                TX_MVB_ADDRESS <= s_tx_mvb_address;
                TX_MVB_LENGTH  <= s_tx_mvb_length;
                TX_MVB_LAST    <= s_tx_mvb_last;
                TX_MVB_VALID   <= s_tx_mvb_valid;
                TX_MVB_SRC_RDY <= s_tx_mvb_src_rdy;
            end if;
            if (RESET = '1') then
                TX_MVB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
