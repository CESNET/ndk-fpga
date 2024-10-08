-- transformer_down.vhd: Implementation of DOWN architecture of MFB transformer component
-- Copyright (C) 2020 CESNET
-- Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity MFB_TRANSFORMER_DOWN is
    generic (
        RX_REGIONS  : integer := 2;
        TX_REGIONS  : integer := 1;
        REGION_SIZE : integer := 1;
        BLOCK_SIZE  : integer := 8;
        ITEM_WIDTH  : integer := 32;
        META_WIDTH  : integer := 0
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- MFB input interface
        RX_DATA    : in  std_logic_vector(RX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META    : in  std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOP     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_EOP     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_SOP_POS : in  std_logic_vector(RX_REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        RX_EOP_POS : in  std_logic_vector(RX_REGIONS*max(1, log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- MFB output interface
        TX_DATA    : out std_logic_vector(TX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META    : out std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
        TX_SOP     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_EOP     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_SOP_POS : out std_logic_vector(TX_REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        TX_EOP_POS : out std_logic_vector(TX_REGIONS*max(1, log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of MFB_TRANSFORMER_DOWN is

    -- input/output ratio
    constant RX_BLOCKS : integer := RX_REGIONS/TX_REGIONS;

    -- extreme values of sel signal
    constant IDLE : std_logic_vector(log2(RX_BLOCKS) downto 0) := ('1', others => '0');
    constant MAX  : std_logic_vector(log2(RX_BLOCKS) downto 0) := ('0', others => '1');

    -- input registers
    signal rx_data_reg    : std_logic_vector(RX_DATA'range);
    signal rx_meta_reg    : std_logic_vector(RX_META'range);
    signal rx_sop_reg     : std_logic_vector(RX_SOP'range);
    signal rx_eop_reg     : std_logic_vector(RX_EOP'range);
    signal rx_sop_pos_reg : std_logic_vector(RX_SOP_POS'range);
    signal rx_eop_pos_reg : std_logic_vector(RX_EOP_POS'range);

    -- select signal
    signal sel : std_logic_vector(log2(RX_BLOCKS) downto 0) := IDLE;

    -- packet logic signals
    signal tx_sop_sel        : std_logic_vector(TX_SOP'range);
    signal tx_eop_sel        : std_logic_vector(TX_EOP'range);
    signal inside_packet_reg : std_logic := '0';

    type t_state is (S_IDLE, S_MAX, S_OTHERS);
    signal state : t_state;

begin

    -- data, sop, eop, sop_pos and eop_pos multiplexers
    data_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => TX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH,
        MUX_WIDTH  => RX_BLOCKS)
    port map (
        DATA_IN    => rx_data_reg,
        SEL        => sel(sel'high-1 downto 0),
        DATA_OUT   => TX_DATA
    );

    meta_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => TX_REGIONS*META_WIDTH,
        MUX_WIDTH  => RX_BLOCKS)
    port map (
        DATA_IN    => rx_meta_reg,
        SEL        => sel(sel'high-1 downto 0),
        DATA_OUT   => TX_META
    );

    sop_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => TX_REGIONS,
        MUX_WIDTH  => RX_BLOCKS)
    port map (
        DATA_IN    => rx_sop_reg,
        SEL        => sel(sel'high-1 downto 0),
        DATA_OUT   => tx_sop_sel
    );

    eop_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => TX_REGIONS,
        MUX_WIDTH  => RX_BLOCKS)
    port map (
        DATA_IN    => rx_eop_reg,
        SEL        => sel(sel'high-1 downto 0),
        DATA_OUT   => tx_eop_sel
    );

    -- sop_pos has significance only when REGION_SIZE > 1
    gen_sop_pos_mux_g : if REGION_SIZE > 1 generate
        sop_pos_mux_i : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => TX_REGIONS*log2(REGION_SIZE),
            MUX_WIDTH  => RX_BLOCKS)
        port map (
            DATA_IN    => rx_sop_pos_reg,
            SEL        => sel(sel'high-1 downto 0),
            DATA_OUT   => TX_SOP_POS
        );
    end generate;

    gen_sop_pos_mux_fake_g : if REGION_SIZE = 1 generate
        TX_SOP_POS <= (others => '0');
    end generate;

    eop_pos_mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => TX_REGIONS*log2(REGION_SIZE*BLOCK_SIZE),
        MUX_WIDTH  => RX_BLOCKS)
    port map (
        DATA_IN    => rx_eop_pos_reg,
        SEL        => sel(sel'high-1 downto 0),
        DATA_OUT   => TX_EOP_POS
    );

    state <= S_IDLE when sel = IDLE else
             S_MAX  when sel = MAX  else
             S_OTHERS;

    -- counter handles the select signal for multiplexers
    -- sel signal is one bit wider (for IDLE state)
    cnt_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if RESET = '1' then
                sel <= IDLE;
            else
                case state is
                    when S_IDLE =>
                        if RX_SRC_RDY = '1' then
                            sel <= (others => '0');
                        end if;
                    when S_MAX =>
                        if TX_DST_RDY = '1' then
                            if RX_SRC_RDY = '1' then
                                sel <= (others => '0');
                            else
                                sel <= IDLE;
                            end if;
                        end if;
                    when S_OTHERS =>
                        if TX_DST_RDY = '1' then
                            sel <= std_logic_vector(unsigned(sel)+1);
                        end if;
                end case;
            end if;
        end if;
    end process;

    -- logic defining RX_DST_RDY, TX_SRC_RDY
    communication_logic_p : process(RESET, state, sel, TX_DST_RDY, tx_sop_sel, tx_eop_sel, inside_packet_reg)
    begin
            RX_DST_RDY <= '0';
            TX_SRC_RDY <= '0';
            case state is
                when S_IDLE =>
                    RX_DST_RDY <= '1';
                when S_MAX =>
                    if TX_DST_RDY = '1' then
                        RX_DST_RDY <= '1';
                    end if;
                    TX_SRC_RDY <= '0' when inside_packet_reg = '0' and unsigned(tx_sop_sel) = 0 and unsigned(tx_eop_sel) = 0 else '1';
                when S_OTHERS =>
                    TX_SRC_RDY <= '0' when inside_packet_reg = '0' and unsigned(tx_sop_sel) = 0 and unsigned(tx_eop_sel) = 0 else '1';
            end case;
    end process;

    -- process controlling whether we're inside a packet or not
    -- tmp and for loop handle the logic for TX_REGIONS > 1
    packet_logic_p : process(CLK)
        variable tmp : std_logic;
    begin
        if rising_edge(CLK) then
            if RESET = '1' then
                inside_packet_reg <= '0';
            elsif sel /= IDLE then
                tmp := inside_packet_reg;
                for i in 0 to TX_REGIONS-1 loop
                    tmp := '1' when (tx_eop_sel(i) = '0' and (tmp = '1' or tx_sop_sel(i) = '1')) or (tx_sop_sel(i) = '1' and tmp = '1') else '0';
                end loop;
                inside_packet_reg <= tmp;
            end if;
        end if;
    end process;

    -- input registers
    regs_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if RX_DST_RDY = '1' then
                rx_data_reg <= RX_DATA;
                rx_meta_reg <= RX_META;
                rx_sop_reg <= RX_SOP;
                rx_eop_reg <= RX_EOP;
                rx_sop_pos_reg <= RX_SOP_POS;
                rx_eop_pos_reg <= RX_EOP_POS;
            end if;
        end if;
    end process;

    TX_SOP <= tx_sop_sel;
    TX_EOP <= tx_eop_sel;

end architecture;
