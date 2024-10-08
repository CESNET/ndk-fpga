-- fp_data_sel.vhd: Unit to handle overflow and set correct SOF/EOF and SOF_POS/EOF_POS of Packets
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- TODO: If the sequence where 16 384 B and 64 B packets arrive, it is possible
-- to generate packets of size greater than MTU.

-- Note: 4 region of this component is not able to send packet by packet
-- For simplicity, the lowest resolution is MFB word
entity FP_DATA_SEL is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        RX_PKT_SIZE_MAX     : natural := 2**10
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        -- Data from temporary register and pre-register
        RX_TMP_REG_DATA : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_CURRENT_DATA : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Points to the free block cell
        RX_TMP_PTR      : in  unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))-1 downto 0);
        -- External timeout indicating that there is a last part of packet in the Temporary register
        RX_SRC_RDY      : in  std_logic;
        RX_TIMEOUT_EXT  : in  std_logic;
        RX_PKT_LNG      : in  slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
        -- EOF_POS
        RX_SOF          : in  std_logic_vector(MFB_REGIONS - 1 downto 0);
        RX_EOF          : in  std_logic_vector(MFB_REGIONS - 1 downto 0);
        RX_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);

        -- TX
        TX_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_PKT_LNG      : out slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(RX_PKT_SIZE_MAX + 1 )) - 1 downto 0);
        TX_META         : out std_logic;
        TX_TIMEOUT_EXT  : out std_logic;
        TX_SOF          : out std_logic_vector(MFB_REGIONS - 1 downto 0);
        TX_EOF          : out std_logic_vector(MFB_REGIONS - 1 downto 0);
        TX_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_SRC_RDY      : out std_logic
    );
end entity;

architecture FULL of FP_DATA_SEL is
    ------------------------------------------------------------
    --                   SIGNAL DECLARATION                   --
    ------------------------------------------------------------
    -- OUT_SELECT
    signal sel_out      : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal sel_out_n    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal sel_one_hot  : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    -- OUT_MUX
    signal tmp_data_arr : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal cur_data_arr : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mux_out_arr  : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mux_select   : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(0 downto 0);

begin

    --------------------------------------------------------------------------------
    ---                                OUT_SELECT                                ---
    --------------------------------------------------------------------------------
    -- MUX select based on pointer value
    sel_one_hot_p: process(all)
    begin
        sel_one_hot                         <= (others => '0');
        sel_one_hot(to_integer(RX_TMP_PTR)) <= '1';
    end process;

    sel_before_one_i : entity work.BEFORE_ONE
        generic map(
            DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE
        )
        port map(
            DI  => sel_one_hot,
            DO  => sel_out_n
        );

    sel_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            sel_out <= not sel_out_n;
        end if;
    end process;

    --------------------------------------------------------------------------------
    ---                                  OUT_MUX                                 ---
    --------------------------------------------------------------------------------
    tmp_data_arr <= slv_array_deser(RX_TMP_REG_DATA, MFB_REGIONS*MFB_REGION_SIZE);
    cur_data_arr <= slv_array_deser(RX_CURRENT_DATA, MFB_REGIONS*MFB_REGION_SIZE);

    mux_select   <= slv_array_deser(sel_out, MFB_REGIONS*MFB_REGION_SIZE);

    out_mux_g: for i in MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0 generate
        mux_i: entity work.GEN_MUX
            generic map(
                DATA_WIDTH  => MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,
                MUX_WIDTH   => 2
            )
            port map(
                DATA_IN     => cur_data_arr(i) & tmp_data_arr(i),
                SEL         => mux_select(i),
                DATA_OUT    => mux_out_arr(i)
            );
    end generate;

    --------------------------------------------------------------------------------
    ---                                  OUTPUT                                  ---
    --------------------------------------------------------------------------------

    TX_DATA         <= slv_array_ser(mux_out_arr);
    TX_TIMEOUT_EXT  <= RX_TIMEOUT_EXT;
    TX_SOF          <= RX_SOF;
    TX_EOF          <= RX_EOF;
    TX_SOF_POS      <= RX_SOF_POS;
    TX_EOF_POS      <= RX_EOF_POS;
    TX_SRC_RDY      <= RX_SRC_RDY;

    -- Length per region - Valid with SOF
    lng_per_region_g: for r in 0 to MFB_REGIONS - 1 generate
        TX_PKT_LNG(r)      <= RX_PKT_LNG(r) when TX_SOF(r) = '1' else (others => '0');
    end generate;
end architecture;
