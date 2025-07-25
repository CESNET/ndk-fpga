--
-- mi_sim.vhd : MI32 simulation component
-- Copyright (C) 2008 CESNET
-- Author(s): Jakub Sochor <xsocho06@stud.fit.vutbr.cz>
--            Adam Piecek <xpiece00@stud.fit.vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.mi_sim_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

entity MI_SIM is
    generic (
        MI_SIM_ID : integer := 0
    );
    port (
        -- Common interface -----------------------------------------------------
        CLK         : in std_logic;
        RESET       : in std_logic;

        -- Output MI interfaces -------------------------------------------------
        MI32_DWR     : out std_logic_vector(31 downto 0);
        MI32_ADDR    : out std_logic_vector(31 downto 0);
        MI32_BE      : out std_logic_vector(3 downto 0);
        MI32_DRD     : in  std_logic_vector(31 downto 0);
        MI32_RD      : out std_logic;
        MI32_WR      : out std_logic;
        MI32_ARDY    : in  std_logic;
        MI32_DRDY    : in  std_logic

    );
end entity;


architecture MI_SIM_ARCH of MI_SIM is

    signal commandstatus : TCommandStatus := ('0', '0', 'Z');

    procedure sendtransaction (
        variable trans   : inout TTransaction;
        signal clk       : in std_logic;
        signal mi32_dwr  : out std_logic_vector(31 downto 0);
        signal mi32_addr : out std_logic_vector(31 downto 0);
        signal mi32_be   : out std_logic_vector(3 downto 0);
        signal mi32_wr   : out std_logic;
        signal mi32_rd   : out std_logic;
        signal mi32_drd  : in std_logic_vector(31 downto 0);
        signal mi32_drdy : in std_logic;
        signal mi32_ardy : in std_logic
    ) is

    begin
        if (trans.DIRECTION = READ) then
            mi32_addr <= trans.ADDR;
            mi32_be   <= trans.BE;
            mi32_rd   <= '1';
            wait until (clk'event and clk = '0');
            -- while (not((MI32_DRDY = '1' and MI32_ARDY = '1'))) loop
            --    wait until (MI32_DRDY = '1' and MI32_ARDY = '1');
            -- end loop;
            while (not(mi32_ardy = '1')) loop
                wait until mi32_ardy = '1';
            end loop;

            if (mi32_drdy = '0') then
                wait until (clk'event and clk = '1');
                mi32_rd <= '0';
                while (not(mi32_drdy = '1')) loop
                    wait until mi32_drdy = '1';
                end loop;
            end if;

            trans.DATA := mi32_drd;
            wait until (clk'event and clk = '1');
            mi32_rd    <= '0';
        else
            mi32_addr <= trans.ADDR;
            mi32_be   <= trans.BE;
            mi32_dwr  <= trans.DATA;
            mi32_wr   <= '1';
            wait until (clk'event and clk = '0');
            while (mi32_ardy = '0') loop
                wait until mi32_ardy = '1';
            end loop;
            wait until (clk'event and clk = '1');
            mi32_wr <= '0';
        end if;
    end procedure sendtransaction;


begin
    sim : process
        variable transaction : TTransaction;
    begin
        MI32_DWR  <= (others => '0');
        MI32_ADDR <= (others => '0');
        MI32_RD   <= '0';
        MI32_WR   <= '0';

        -- Wait here till the reset
        wait until RESET = '0';

        loop
            commandStatus.BUSY <= '0';
            while (commandStatus.REQ = '0') loop
                wait until commandStatus.REQ = '1';
            end loop;
            commandStatus.BUSY <= '1';

            commandStatus.REQ_ACK <= (not(commandStatus.REQ_ACK));
            ReadTransaction(transaction, MI_SIM_ID);
            sendtransaction(transaction, CLK, MI32_DWR, MI32_ADDR, MI32_BE, MI32_WR, MI32_RD, MI32_DRD, MI32_DRDY, MI32_ARDY);
            WriteTransaction(transaction, MI_SIM_ID);
            commandStatus.BUSY    <= '0';
        end loop;
    end process;

    status(MI_SIM_ID).REQ_ACK <= commandStatus.REQ_ACK;
    status(MI_SIM_ID).BUSY    <= commandStatus.BUSY;
    commandStatus.REQ         <= status(MI_SIM_ID).REQ;


end architecture;
