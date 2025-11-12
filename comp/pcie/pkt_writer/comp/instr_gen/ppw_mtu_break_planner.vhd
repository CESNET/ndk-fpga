-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


entity PPW_MTU_BREAK_PLANNER is
    generic (
        -- Number of MVB Items in a word, can't handle more than 1.
        MVB_ITEMS      : natural := 1;
        -- Maximum packet size (in bytes).
        PKT_MTU        : integer := 2**12;
        ADDRESS_WIDTH  : natural := 64;
        PCIE_MPS_WIDTH : integer := 15;
        DEVICE         : string := "AGILEX"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- Specifies the currently configured PCIe Maximum Packet Size (in bytes).
        -- PCIe specification allows at least 128.
        PCIE_MPS       : in  std_logic_vector(PCIE_MPS_WIDTH-1 downto 0);

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_MVB_ADDRESS : in  std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
        -- Indicates final MVB Item for a packet.
        RX_MVB_LAST    : in  std_logic_vector(MVB_ITEMS-1 downto 0);
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

architecture FULL of PPW_MTU_BREAK_PLANNER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant LEN_WIDTH_EXT   : natural := log2(PKT_MTU+1) + 1;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    type fsm_t is (ST_IDLE, ST_BREAK);

    signal last_reg          : std_logic_vector(MVB_ITEMS-1 downto 0);

    signal fsm_pstate        : fsm_t;
    signal fsm_nstate        : fsm_t;

    signal len_over_mps      : std_logic;

    signal s_tx_mvb_address  : std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
    signal s_tx_mvb_length   : std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
    signal s_tx_mvb_last     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_tx_mvb_valid    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_tx_mvb_src_rdy  : std_logic;

    signal len2end           : unsigned(LEN_WIDTH_EXT-1 downto 0);
    signal breaking          : std_logic;

    signal len2end_reg       : unsigned(log2(PKT_MTU+1)-1 downto 0);
    signal next_address_reg  : std_logic_vector(ADDRESS_WIDTH-1 downto 0);

begin

    RX_MVB_DST_RDY <= TX_MVB_DST_RDY and not (breaking and RX_MVB_SRC_RDY);

    last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((RX_MVB_SRC_RDY = '1') and (RX_MVB_DST_RDY = '1')) then
                last_reg <= RX_MVB_LAST;
            end if;
        end if;
    end process;

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
                if ((RX_MVB_SRC_RDY = '1') and (RX_MVB_VALID(0) = '1') and (len_over_mps = '1')) then
                    fsm_nstate <= ST_BREAK;
                else
                    fsm_nstate <= ST_IDLE;
                end if;
            when ST_BREAK =>
                if (len_over_mps = '1') then
                    fsm_nstate <= ST_BREAK;
                else
                    fsm_nstate <= ST_IDLE;
                end if;
        end case;
    end process;

    len_over_mps <= not len2end(len2end'high) when (len2end /= 0) else '0';

    fsm_state_logic_p : process (all)
    begin
        case (fsm_pstate) is

            when ST_IDLE =>
                s_tx_mvb_address <= RX_MVB_ADDRESS;
                s_tx_mvb_length  <= std_logic_vector(resize(unsigned(PCIE_MPS), log2(PKT_MTU+1))) when (len_over_mps = '1') else RX_MVB_LENGTH;
                s_tx_mvb_last    <= "0" when (len_over_mps = '1') else RX_MVB_LAST;
                s_tx_mvb_valid   <= RX_MVB_VALID;
                s_tx_mvb_src_rdy <= RX_MVB_SRC_RDY;

                len2end  <= resize(unsigned(RX_MVB_LENGTH), LEN_WIDTH_EXT) - resize(unsigned(PCIE_MPS), LEN_WIDTH_EXT);
                breaking <= '0';

            when ST_BREAK =>
                s_tx_mvb_address <= next_address_reg;
                s_tx_mvb_length  <= std_logic_vector(resize(unsigned(PCIE_MPS), log2(PKT_MTU+1))) when (len_over_mps = '1') else std_logic_vector(len2end_reg);
                s_tx_mvb_last    <= "0" when (len_over_mps = '1') else last_reg;
                s_tx_mvb_valid   <= (others => '1');
                s_tx_mvb_src_rdy <= '1';

                len2end  <= resize(len2end_reg, LEN_WIDTH_EXT) - resize(unsigned(PCIE_MPS), LEN_WIDTH_EXT);
                breaking <= '1';

        end case;
    end process;

    fsm_misc_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MVB_DST_RDY = '1') then
                if (fsm_nstate = ST_BREAK) then
                    len2end_reg      <= len2end(log2(PKT_MTU+1)-1 downto 0);
                    next_address_reg <= std_logic_vector(unsigned(s_tx_mvb_address) + unsigned(PCIE_MPS));
                end if;
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
