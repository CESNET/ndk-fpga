-- pcie_cii2cfg_ext.vhd: PCIe CII to CFG_EXT interface convertor
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PCIE_CII2CFG_EXT is
    port (
        CLK                    : in  std_logic;
        RESET                  : in  std_logic;

        PCIE_CII_HDR_POISONED  : in  std_logic;
        PCIE_CII_OVERRIDE_EN   : out std_logic;
        PCIE_CII_HDR_FIRST_BE  : in  std_logic_vector(3 downto 0);
        PCIE_CII_DOUT          : in  std_logic_vector(31 downto 0);
        PCIE_CII_HALT          : out std_logic;
        PCIE_CII_REQ           : in  std_logic;
        PCIE_CII_ADDR          : in  std_logic_vector(9 downto 0);
        PCIE_CII_WR            : in  std_logic;
        PCIE_CII_OVERRIDE_DIN  : out std_logic_vector(31 downto 0);

        CFG_EXT_READ           : out std_logic;
        CFG_EXT_WRITE          : out std_logic;
        CFG_EXT_REGISTER       : out std_logic_vector(9 downto 0);
        CFG_EXT_FUNCTION       : out std_logic_vector(7 downto 0);
        CFG_EXT_WRITE_DATA     : out std_logic_vector(31 downto 0);
        CFG_EXT_WRITE_BE       : out std_logic_vector(3 downto 0);
        CFG_EXT_READ_DATA      : in  std_logic_vector(31 downto 0);
        CFG_EXT_READ_DV        : in  std_logic
    );
end entity;

architecture FULL of PCIE_CII2CFG_EXT is

    signal pcie_cii_req_reg          : std_logic;
    signal pcie_cii_wr_reg           : std_logic;
    signal pcie_cii_addr_reg         : std_logic_vector(9 downto 0);
    signal pcie_cii_dout_reg         : std_logic_vector(31 downto 0);
    signal pcie_cii_hdr_first_be_reg : std_logic_vector(3 downto 0);

    signal pcie_cii_req_edge         : std_logic;
    signal pcie_cii_addr_ok          : std_logic;

    type   cii_fsm_st_t is (ST_IDLE, ST_MEM_ACCESS, ST_MEM_WRITE, ST_MEM_READ, ST_MEM_READ2);
    signal cii_fsm_pst            : cii_fsm_st_t;
    signal cii_fsm_nst            : cii_fsm_st_t;

    signal cii_vld_pulse          : std_logic;
    signal cfg_ext_write_reg      : std_logic;
    signal cfg_ext_write_reg2     : std_logic;
    signal cfg_ext_read_dv_reg    : std_logic;
    signal cfg_ext_read_data_reg  : std_logic_vector(31 downto 0);

begin

    cii_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            pcie_cii_req_reg          <= PCIE_CII_REQ;
            pcie_cii_wr_reg           <= PCIE_CII_WR;
            pcie_cii_addr_reg         <= PCIE_CII_ADDR;
            pcie_cii_dout_reg         <= PCIE_CII_DOUT;
            pcie_cii_hdr_first_be_reg <= PCIE_CII_HDR_FIRST_BE;
        end if;
    end process;

    pcie_cii_req_edge     <= PCIE_CII_REQ and not pcie_cii_req_reg;
    PCIE_CII_OVERRIDE_DIN <= cfg_ext_read_data_reg;

    -- Intel CII FSM STATE REGISTER
    cii_fsm_pst_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                cii_fsm_pst <= ST_IDLE;
            else
                cii_fsm_pst <= cii_fsm_nst;
            end if;
        end if;
    end process;

    --  Intel CII FSM LOGIC
    cii_fsm_logic_p : process (all)
    begin
        cii_fsm_nst          <= cii_fsm_pst;
        PCIE_CII_HALT        <= '1';
        PCIE_CII_OVERRIDE_EN <= '0';
        CFG_EXT_WRITE        <= '0';
        CFG_EXT_READ         <= '0';

        case (cii_fsm_pst) is
            when ST_IDLE =>
                if (pcie_cii_req_edge = '1') then
                    cii_fsm_nst <= ST_MEM_ACCESS;
                end if;

            when ST_MEM_ACCESS =>
                CFG_EXT_WRITE <= pcie_cii_wr_reg;
                CFG_EXT_READ  <= not pcie_cii_wr_reg;
                if (pcie_cii_wr_reg = '1') then
                    cii_fsm_nst <= ST_MEM_WRITE;
                else
                    cii_fsm_nst <= ST_MEM_READ;
                end if;

            when ST_MEM_WRITE =>
                PCIE_CII_HALT <= '0';
                cii_fsm_nst   <= ST_IDLE;

            when ST_MEM_READ =>
                cii_fsm_nst <= ST_MEM_READ2;

            when ST_MEM_READ2 =>
                PCIE_CII_HALT        <= '0';
                PCIE_CII_OVERRIDE_EN <= cfg_ext_read_dv_reg;
                cii_fsm_nst          <= ST_IDLE;
        end case;
    end process;

    cfg_ext_read_data_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            cfg_ext_read_data_reg <= CFG_EXT_READ_DATA;
            cfg_ext_read_dv_reg   <= CFG_EXT_READ_DV;
        end if;
    end process;

    CFG_EXT_REGISTER   <= pcie_cii_addr_reg;
    CFG_EXT_WRITE_DATA <= pcie_cii_dout_reg;
    CFG_EXT_WRITE_BE   <= pcie_cii_hdr_first_be_reg;
    CFG_EXT_FUNCTION   <= (others => '0'); -- TODO

end architecture;
