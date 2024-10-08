-- fp_tmp_reg.vhd: Temporary register with it's logic
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FP_TMP_REG is
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

        RX_TMP_OVERFLOW     : in  std_logic;
        RX_TMP_PTR_UNS      : in  unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))-1 downto 0);
        RX_TMP_DATA_ARR     : in  slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1  downto 0);
        RX_TMP_SOF_ONE_HOT  : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_TMP_EOF_ONE_HOT  : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_PKT_LNG          : in  slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

        TX_TMP_DATA         : out slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1  downto 0);
        TX_TMP_SOF_ONE_HOT  : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        TX_TMP_EOF_ONE_HOT  : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        TX_PKT_LNG          : out slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0)

    );
end entity;

architecture FULL of FP_TMP_REG is
    -- TMP_ENABLE
    signal en_one_hot       : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal en_tmp_n         : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal en_tmp_reg       : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tmp_enable       : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    --[SOF_OH] [EOF_OH]
    signal xof_reg          : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(1 + 1 - 1 downto 0);
    signal xof_reg_input    : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(1 + 1 - 1 downto 0);

begin
    --------------------------------------------------------------------------------
    ---                                TMP_ENABLE                                ---
    --------------------------------------------------------------------------------
    -- This part decides which blocks to store, based on the value of the pointer
    en_one_hot_p: process(all)
    begin
        en_one_hot                              <= (others => '0');
        en_one_hot(to_integer(RX_TMP_PTR_UNS))  <= '1';
    end process;

    en_before_one_i : entity work.BEFORE_ONE
    generic map(
        DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE
    )
    port map(
        DI  => en_one_hot,
        DO  => en_tmp_n
    );

    en_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            en_tmp_reg  <= not en_tmp_n;
        end if;
    end process;

    enable_p: process(all)
    begin
        if RX_TMP_OVERFLOW = '1' then
            tmp_enable  <= (others => '1');
        else
            tmp_enable  <= en_tmp_reg;
        end if;
    end process;

    --------------------------------------------------------------------------------
    ---                            TMP_REG - DATA                                ---
    --------------------------------------------------------------------------------
    -- Temporary register stores overflow data
    tmp_reg_g: for i in MFB_REGIONS*MFB_REGION_SIZE -1 downto 0 generate
        tmp_reg_data_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if RST = '1' then
                    TX_TMP_DATA(i) <= (others => '0');
                elsif tmp_enable(i) = '1' then
                    TX_TMP_DATA(i) <= RX_TMP_DATA_ARR(i);
                end if;
            end if;
        end process;
    end generate;

    --------------------------------------------------------------------------------
    ---                            TMP_REG - XOF                                 ---
    --------------------------------------------------------------------------------
    eof_oncatenation_g: for i in MFB_REGIONS*MFB_REGION_SIZE -1 downto 0 generate
        xof_reg_input(i)  <= RX_TMP_SOF_ONE_HOT(i) & RX_TMP_EOF_ONE_HOT(i);
    end generate;

    xof_reg_g: for i in MFB_REGIONS*MFB_REGION_SIZE -1 downto 0 generate
        tmp_reg_xof_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if RST = '1' then
                    xof_reg(i) <= (others => '0');
                elsif tmp_enable(i) = '1' then
                    xof_reg(i) <= xof_reg_input(i);
                end if;
            end if;
        end process;
    end generate;

    eof_extraction_g: for i in MFB_REGIONS*MFB_REGION_SIZE -1 downto 0 generate
        TX_TMP_SOF_ONE_HOT(i)   <= xof_reg(i)(1);
        TX_TMP_EOF_ONE_HOT(i)   <= xof_reg(i)(0);
    end generate;

    --------------------------------------------------------------------------------
    ---                           TMP_REG - PKT_LNG                              ---
    --------------------------------------------------------------------------------
    pkt_lng_reg_g: for i in MFB_REGIONS*MFB_REGION_SIZE -1 downto 0 generate
        tmp_reg_lng_p: process(CLK)
        begin
            if rising_edge(CLK) then
                if RST = '1' then
                    TX_PKT_LNG(i)   <= (others => '0');
                elsif tmp_enable(i) = '1' then
                    TX_PKT_LNG(i)   <= RX_PKT_LNG(i);
                end if;
            end if;
        end process;
    end generate;

end architecture;
