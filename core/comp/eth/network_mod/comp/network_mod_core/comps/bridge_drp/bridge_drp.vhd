-- bridge_drp.vhd: submodule which is used to change MI interface to interface used or submodules.
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Záhora <xzahor06@vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity BRIDGE_DRP is
    generic(
        MI_DATA_WIDTH_PHY : natural := 32;
        MI_ADDR_WIDTH_PHY : natural := 18;
        MI_SEL_RANGE      : natural := 16;
        MI_EN_MAP         : std_logic_vector(MI_SEL_RANGE-1 downto 0) := (others => '0')
    );
    port(
        -- MGMT_DRP interface
        DRPCLK                  : in  std_logic;
        DRPDO                   : out std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
        DRP_DRDY                : out std_logic;
        DRPEN                   : in  std_logic;
        DRPWE                   : in  std_logic;
        DRPADDR                 : in  std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0);
        DRPARDY                 : out std_logic;
        DRPDI                   : in  std_logic_vector(MI_DATA_WIDTH_PHY-1 downto 0);
        DRPSEL                  : in  std_logic_vector(4-1 downto 0);

        -- IP core interface for Eth and XCVR and DR_Cntrl if is used multirate
        RECONFIG_ADDR           : out slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
        RECONFIG_READDATA_VALID : in  std_logic_vector(MI_SEL_RANGE-1 downto 0);
        RECONFIG_READ           : out std_logic_vector(MI_SEL_RANGE-1 downto 0);
        RECONFIG_WRITE          : out std_logic_vector(MI_SEL_RANGE-1 downto 0);
        RECONFIG_READDATA       : in  slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
        RECONFIG_WRITEDATA      : out slv_array_t     (MI_SEL_RANGE-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
        RECONFIG_WAITREQUEST    : in  std_logic_vector(MI_SEL_RANGE-1 downto 0)
    );
end entity;

architecture FULL of BRIDGE_DRP is 
    signal drp_sel   : std_logic_vector (DRPSEL'range);
    signal drpardy_vld : std_logic;
    signal drp_rd_sig  : std_logic;

begin
    -- Store mi_ia_sel for read operations
    sel_reg_p: process(DRPCLK)
    begin
        if rising_edge(DRPCLK) then
            if DRPEN = '1' then
                drp_sel <= DRPSEL;
            end if;
            -- DRPARDY is valid one clock cycle after DRPEN at the earliest
            drpardy_vld <= DRPEN;
            if (DRP_DRDY = '1') then 
                drp_rd_sig <= '0';
            elsif (DRPEN = '1') and (DRPWE = '0') then
                drp_rd_sig <= '1';
            end if;
        end if;
    end process;

    -- Assign WR/RD signals for Eth blocks
    drd_mux_p: process(all)
    begin
        for j in 0 to MI_SEL_RANGE-1 loop 
            if (MI_EN_MAP(j) = '1') then
                RECONFIG_ADDR     (j) <= DRPADDR(RECONFIG_ADDR(j)'range);
                RECONFIG_WRITEDATA(j) <= DRPDI;
                RECONFIG_WRITE    (j) <= DRPEN and     DRPWE when DRPSEL = std_logic_vector(to_unsigned((j),DRPSEL'length)) else '0';
                RECONFIG_READ     (j) <= DRPEN and not DRPWE when DRPSEL = std_logic_vector(to_unsigned((j),DRPSEL'length)) else '0';
            end if;
        end loop;
    end process;

    DRPDO    <= RECONFIG_READDATA       (to_integer(unsigned(drp_sel)));
    DRP_DRDY <= RECONFIG_READDATA_VALID (to_integer(unsigned(drp_sel))) and drp_rd_sig;
    DRPARDY  <= RECONFIG_WAITREQUEST    (to_integer(unsigned(drp_sel))) and drpardy_vld;

end architecture;
