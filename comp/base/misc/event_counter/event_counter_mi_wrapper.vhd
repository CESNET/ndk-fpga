-- event_counter_mi_wrapper.vhd: Event Counter Statistics unit MI32 Wrapper
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =========================================================================
--                                 Description
-- =========================================================================
-- A wrapper with MI32 interface for component Event Counter.
-- =========================================================================

entity EVENT_COUNTER_MI_WRAPPER is
generic(
    -- Maximum number of CLK cycles in one counting interval
    -- Automatically rounded to the closes higher (2**N-1).
    MAX_INTERVAL_CYCLES     : natural := 2**12-1;
    -- Maximum number of event occurences in one CLK cycle
    -- Automatically rounded to the closes higher (2**N-1).
    MAX_CONCURRENT_EVENTS   : natural := 4;

    -- Enable FIFO for capturing sequence of event intervals
    CAPTURE_EN              : boolean := false;
    -- Size of capturing FIFO
    CAPTURE_FIFO_ITEMS      : natural := 1024;

    -- MI interface width
    MI_WIDTH                : natural := 32;
    -- MI address for Interval settings
    MI_INTERVAL_ADDR        : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(0,MI_WIDTH));
    -- MI address for Events Counter register
    MI_EVENTS_ADDR          : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(1,MI_WIDTH));
    -- MI address for Events Capture enable register
    MI_CPT_EN_ADDR          : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(2,MI_WIDTH));
    -- MI address for Events Capture FIFO output read
    MI_CPT_RD_ADDR          : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(3,MI_WIDTH));
    -- MI address mask
    -- (has '1' on bits, which are relevant in MI addresses)
    MI_ADDR_MASK            : std_logic_vector(MI_WIDTH-1 downto 0) := (others => '1');

    -- Target device
    DEVICE                  : string := "ULTRASCALE"
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================

    CLK       : in  std_logic;
    RESET     : in  std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Other interfaces
    -- =====================================================================

    --  MI interface
    MI_DWR    : in  std_logic_vector(MI_WIDTH-1 downto 0);
    MI_ADDR   : in  std_logic_vector(MI_WIDTH-1 downto 0);
  --MI_BE     : in  std_logic_vector(MI_WIDTH/8-1 downto 0); NOT SUPPORTED
    MI_RD     : in  std_logic;
    MI_WR     : in  std_logic;
    MI_ARDY   : out std_logic;
    MI_DRD    : out std_logic_vector(MI_WIDTH-1 downto 0);
    MI_DRDY   : out std_logic;

    -- Event occurence propagation
    EVENT_CNT : in  std_logic_vector(log2(MAX_CONCURRENT_EVENTS+1)-1 downto 0);
    EVENT_VLD : in  std_logic

    -- =====================================================================
);
end entity;

architecture FULL of EVENT_COUNTER_MI_WRAPPER is

    signal interval_cycles : std_logic_vector(log2(MAX_INTERVAL_CYCLES+1)-1 downto 0);
    signal interval_set    : std_logic;
    signal total_events    : std_logic_vector(log2((MAX_INTERVAL_CYCLES+1)*(MAX_CONCURRENT_EVENTS+1))-1 downto 0);
    signal total_cycles    : std_logic_vector(log2(MAX_INTERVAL_CYCLES+1)-1 downto 0);
    signal total_update    : std_logic;

    signal cpt_en_reg       : std_logic;
    signal cpt_fifox_do    : std_logic_vector(log2((MAX_INTERVAL_CYCLES+1)*(MAX_CONCURRENT_EVENTS+1))-1 downto 0);
    signal cpt_fifox_rd    : std_logic;
    signal cpt_fifox_empty : std_logic;

begin

    -- =====================================================================
    --  Event Counter unit
    -- =====================================================================

    eve_cnt_i : entity work.EVENT_COUNTER
    generic map(
        MAX_INTERVAL_CYCLES   => MAX_INTERVAL_CYCLES,
        MAX_CONCURRENT_EVENTS => MAX_CONCURRENT_EVENTS
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        INTERVAL_CYCLES => interval_cycles,
        INTERVAL_SET    => interval_set   ,

        EVENT_CNT       => EVENT_CNT      ,
        EVENT_VLD       => EVENT_VLD      ,

        TOTAL_EVENTS    => total_events   ,
        TOTAL_CYCLES    => total_cycles   ,
        TOTAL_UPDATE    => total_update
    );

    -- =====================================================================

    cpt_gen : if (CAPTURE_EN) generate

        -- =====================================================================
        --  Capture register
        -- =====================================================================

        cpt_en_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then

                if (MI_WR='1' and (MI_ADDR and MI_ADDR_MASK)=(MI_CPT_EN_ADDR and MI_ADDR_MASK)) then
                    cpt_en_reg <= MI_DWR(0);
                end if;

                if (RESET='1') then
                    cpt_en_reg <= '0';
                end if;
            end if;
        end process;

        -- =====================================================================

        -- =====================================================================
        --  Capture FIFO
        -- =====================================================================

        capt_fifo_i : entity work.FIFOX
        generic map(
            DATA_WIDTH          => log2((MAX_INTERVAL_CYCLES+1)*(MAX_CONCURRENT_EVENTS+1)),
            ITEMS               => CAPTURE_FIFO_ITEMS,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 1     ,
            ALMOST_EMPTY_OFFSET => 1     ,
            FAKE_FIFO           => false
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => total_events,
            WR     => total_update and cpt_en_reg,
            FULL   => open,
            AFULL  => open,
            STATUS => open,

            DO     => cpt_fifox_do   ,
            RD     => cpt_fifox_rd   ,
            EMPTY  => cpt_fifox_empty,
            AEMPTY => open
        );

        -- Remove item from FIFO by writing on the output address
        cpt_fifox_rd <= '1' when MI_WR='1' and (MI_ADDR and MI_ADDR_MASK)=(MI_CPT_RD_ADDR and MI_ADDR_MASK) else '0';

        -- =====================================================================

    end generate;

    -- =====================================================================
    --  MI connection
    -- =====================================================================

    MI_ARDY <= MI_WR or MI_RD;
    MI_DRDY <= MI_RD;

    assert (total_events'length+1<=MI_WIDTH) -- Must fit Empty flag for capture FIFO read
        report "WARNING: EVENT COUNTER MI WRAPPER: The width of register for counting number of events ("&to_string(total_events'length)&") is higher or equal to the total width of the connected MI interface ("&to_string(MI_WIDTH)&")! This might cause overflow of the value read from this register!"
        severity warning;

    MI_DRD <= std_logic_vector(resize_left(unsigned(total_events),MI_WIDTH))
         when (MI_ADDR and MI_ADDR_MASK)=(MI_EVENTS_ADDR and MI_ADDR_MASK) else
              std_logic_vector(resize_left(unsigned(total_cycles),MI_WIDTH))
         when (MI_ADDR and MI_ADDR_MASK)=(MI_INTERVAL_ADDR and MI_ADDR_MASK) else
              (0 => cpt_en_reg, others => '0')
         when (MI_ADDR and MI_ADDR_MASK)=(MI_CPT_EN_ADDR and MI_ADDR_MASK) and CAPTURE_EN else
              (not cpt_fifox_empty) & std_logic_vector(resize_left(unsigned(cpt_fifox_do),MI_WIDTH-1)) -- MSB is VLD bit
         when (MI_ADDR and MI_ADDR_MASK)=(MI_CPT_RD_ADDR and MI_ADDR_MASK) and CAPTURE_EN else
              (others => '0');

    interval_cycles <= std_logic_vector(resize_left(unsigned(MI_DWR),interval_cycles'length));
    interval_set    <= '1' when MI_WR='1' and (MI_ADDR and MI_ADDR_MASK)=(MI_INTERVAL_ADDR and MI_ADDR_MASK) else '0';

    -- =====================================================================

end architecture;
