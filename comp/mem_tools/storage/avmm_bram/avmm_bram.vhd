-- avmm_bram.vhd
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity AVMM_BRAM is
    generic (
        ADDR_WIDTH  : natural := 16;
        BURST_WIDTH : natural := 6;
        DATA_WIDTH  : natural := 256;
        DEVICE      : string := "AGILEX"
    );
    port (
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        AVMM_READY         : out std_logic;
        AVMM_READ          : in  std_logic;
        AVMM_WRITE         : in  std_logic;
        AVMM_ADDRESS       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        AVMM_BURSTCOUNT    : in  std_logic_vector(BURST_WIDTH-1 downto 0);
        AVMM_WRITEDATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);

        AVMM_READDATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        AVMM_READDATAVALID : out std_logic
    );
end entity;

architecture FULL of AVMM_BRAM is

    type fsm_st is (ST_IDLE, ST_WRITE, ST_READ);
    signal fsm_pst            : fsm_st;
    signal fsm_nst            : fsm_st;
    signal fsm_addr_sig       : unsigned(ADDR_WIDTH-1 downto 0);
    signal fsm_addr_reg       : unsigned(ADDR_WIDTH-1 downto 0);
    signal fsm_burst_sig      : unsigned(BURST_WIDTH-1 downto 0);
    signal fsm_burst_reg      : unsigned(BURST_WIDTH-1 downto 0);
    signal fsm_cnt_sig        : unsigned(BURST_WIDTH-1 downto 0);
    signal fsm_cnt_reg        : unsigned(BURST_WIDTH-1 downto 0);
    signal fsm_bram_addr      : unsigned(ADDR_WIDTH-1 downto 0);
    signal fsm_bram_wr        : std_logic;
    signal fsm_bram_rd        : std_logic;

begin

    -- =========================================================================
    -- MAIN FSM
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                fsm_pst <= ST_IDLE;
            else
                fsm_pst <= fsm_nst;
            end if;
            fsm_cnt_reg   <= fsm_cnt_sig;
            fsm_addr_reg  <= fsm_addr_sig;
            fsm_burst_reg <= fsm_burst_sig;
        end if;
    end process;

    process (all)
    begin
        fsm_nst       <= fsm_pst;
        fsm_addr_sig  <= fsm_addr_reg;
        fsm_burst_sig <= fsm_burst_reg;
        fsm_cnt_sig   <= fsm_cnt_reg;
        fsm_bram_addr <= unsigned(AVMM_ADDRESS);
        fsm_bram_wr   <= '0';
        fsm_bram_rd   <= '0';
        AVMM_READY    <= '0';

        case fsm_pst is
            when ST_IDLE =>
                fsm_addr_sig  <= unsigned(AVMM_ADDRESS);
                fsm_burst_sig <= unsigned(AVMM_BURSTCOUNT);
                fsm_cnt_sig   <= to_unsigned(1, BURST_WIDTH);
                fsm_bram_wr   <= AVMM_WRITE;
                fsm_bram_rd   <= AVMM_READ;
                AVMM_READY    <= '1';
                if (unsigned(AVMM_BURSTCOUNT) > 1) then
                    if (AVMM_WRITE = '1') then
                        fsm_nst <= ST_WRITE;
                    elsif (AVMM_READ = '1') then
                        fsm_nst <= ST_READ;
                    end if;
                end if;

            when ST_WRITE =>
                fsm_bram_addr <= fsm_addr_reg + fsm_cnt_reg;
                fsm_bram_wr   <= AVMM_WRITE;
                AVMM_READY    <= '1';
                if (AVMM_WRITE = '1') then
                    fsm_cnt_sig <= fsm_cnt_reg + 1;
                    if (fsm_burst_reg = fsm_cnt_sig) then
                        fsm_nst <= ST_IDLE;
                    end if;
                end if;

            when ST_READ =>
                fsm_cnt_sig   <= fsm_cnt_reg + 1;
                fsm_bram_addr <= fsm_addr_reg + fsm_cnt_reg;
                fsm_bram_rd   <= '1';
                AVMM_READY    <= '0';
                if (fsm_burst_reg = fsm_cnt_sig) then
                    fsm_nst <= ST_IDLE;
                end if;

            when others =>
                fsm_nst <= ST_IDLE;
        end case;
    end process;

    bram_i : entity work.SDP_BRAM_BEHAV
    generic map(
       DATA_WIDTH  => DATA_WIDTH,
       ITEMS       => 2**ADDR_WIDTH,
       OUTPUT_REG  => True
    )
    port map(
       --WRITE INTERFACE
       WR_CLK      => CLK,
       WR_ADDR     => std_logic_vector(fsm_bram_addr),
       WR_EN       => fsm_bram_wr,
       WR_DIN      => AVMM_WRITEDATA,
       --READ INTERFACE
       RD_CLK      => CLK,
       RD_RST      => RESET,
       RD_CE       => '1',
       RD_REG_CE   => '1',
       RD_ADDR     => std_logic_vector(fsm_bram_addr),
       RD_EN       => fsm_bram_rd,
       RD_DOUT     => AVMM_READDATA,
       RD_DOUT_VLD => AVMM_READDATAVALID
    );

end architecture;
