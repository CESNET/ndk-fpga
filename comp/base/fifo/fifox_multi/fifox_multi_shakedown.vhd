-- fifox_multi_shakedown.vhd: FIFOX MULTI architecture
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             Description
-- ----------------------------------------------------------------------------
-- This architecture consists of a simple FIFOX and a MVB SHAKEDOWN at the end.
-- PROS:
--     - Less resources thanks to only one FIFOX being present.
--     - Output propagated directly from a register.
-- CONS:
--     - Output register is connected in a self-loop through a MVB SHAKEDOWN.
--       This SHAKEDOWN has MUXes twice as wide as would be needed
--       in architecture FULL.
--     - Worse buffering capabilities. (The data words FIFOX contain non-valid
--       items)
--     - Worse throughput (approximately 87% compared to architecture FULL
--       according to tests in simulation).

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture SHAKEDOWN of FIFOX_MULTI is

    -- Number of data words in SHAKEDOWN register
    -- Changes the width of MUXes in SHAKEDOWN and the throughput.
    -- Higher values -> higher width and higher throughput
    -- throughputs compared to architecture FULL:
    --   1 REG  -> ~50%
    --   2 REGS -> ~87%
    --   3 REGS -> ~94%
    --   4 REGS -> ~96%
    constant SHAKEDOWN_REGS      : integer := 2;

    constant FIFOX_AFULL_OFFSET  : integer := (ALMOST_FULL_OFFSET+WRITE_PORTS-1)/WRITE_PORTS; -- divide and round up
    constant FIFOX_AEMPTY_OFFSET : integer := max(0,(ALMOST_EMPTY_OFFSET-SHAKEDOWN_REGS+WRITE_PORTS-1)/WRITE_PORTS);

    -- -------------------------------------------------------------------------
    -- FIFOX
    -- -------------------------------------------------------------------------

    constant FIFOX_DATA_WIDTH : integer := DATA_WIDTH*WRITE_PORTS+WRITE_PORTS; -- data + valid bits
    signal fifox_rd      : std_logic;
    signal fifox_empty   : std_logic;
    signal fifox_do      : std_logic_vector(FIFOX_DATA_WIDTH-1 downto 0);
    signal fifox_do_data : std_logic_vector(WRITE_PORTS*DATA_WIDTH-1 downto 0);
    signal fifox_do_vld  : std_logic_vector(WRITE_PORTS-1 downto 0);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB SHAKEDOWN
    -- -------------------------------------------------------------------------

    signal sh_data : std_logic_vector(READ_PORTS*DATA_WIDTH-1 downto 0);
    signal sh_vld  : std_logic_vector(READ_PORTS-1 downto 0);
    signal sh_next : std_logic_vector(READ_PORTS-1 downto 0);

    -- -------------------------------------------------------------------------
    function rd_check(rd : std_logic_vector; empty : std_logic_vector) return boolean is
        variable read_stop : boolean;
    begin
        read_stop := false;
        for IT in rd'low to rd'high loop
            if (rd(IT) = '1' and empty(IT) = '0' and read_stop = true) then
                return false;
            end if;

            if (rd(IT) = '0' and empty(IT) = '0') then
                read_stop := true;
            end if;
        end loop;

        return true;
    end function;

begin

    -- -------------------------------------------------------------------------
    -- Assert checking
    -- -------------------------------------------------------------------------

    -- psl assert_safe_read :
    --      assert always (SAFE_READ_MODE=true or (RD and EMPTY) = (READ_PORTS-1 downto 0 => '0')) abort (RESET) @rising_edge(CLK)
    --      report "ERROR: FIFOX Multi: Non-safe Read Mode condition violated! Reading from port is forbidden when is EMPTY!";

    -- psl assert_read_condition :
    --      assert always (rd_check(RD, EMPTY)) abort (RESET) @rising_edge(CLK)
    --      report "ERROR: FIFOX Multi: Aligned read condition viloated! Reading from non-empty port which and dont read from lower nonempty port is forbidden!";


    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- FIFOX
    -- -------------------------------------------------------------------------

    fifox_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => FIFOX_DATA_WIDTH   ,
        ITEMS               => ITEMS/WRITE_PORTS  ,
        RAM_TYPE            => RAM_TYPE           ,
        DEVICE              => DEVICE             ,
        ALMOST_FULL_OFFSET  => FIFOX_AFULL_OFFSET ,
        ALMOST_EMPTY_OFFSET => FIFOX_AEMPTY_OFFSET,
        FAKE_FIFO           => false
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => DI & WR,
        WR     => (or WR),
        FULL   => FULL   ,
        AFULL  => AFULL  ,

        DO     => fifox_do   ,
        RD     => fifox_rd   ,
        EMPTY  => fifox_empty,
        AEMPTY => AEMPTY
    );

    fifox_do_data <= fifox_do(fifox_do'high downto WRITE_PORTS);
    fifox_do_vld  <= fifox_do(WRITE_PORTS-1 downto 0);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB SHAKEDOWN
    -- -------------------------------------------------------------------------

    shakedown_i : entity work.MVB_SHAKEDOWN
    generic map(
        RX_ITEMS    => WRITE_PORTS   ,
        TX_ITEMS    => READ_PORTS    ,
        ITEM_WIDTH  => DATA_WIDTH    ,
        SHAKE_PORTS => SHAKEDOWN_REGS
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DATA    => fifox_do_data  ,
        RX_VLD     => fifox_do_vld   ,
        RX_SRC_RDY => not fifox_empty,
        RX_DST_RDY => fifox_rd       ,

        TX_DATA    => sh_data,
        TX_VLD     => sh_vld ,
        TX_NEXT    => sh_next
    );

    DO      <= sh_data;
    EMPTY   <= not sh_vld;
    sh_next <= RD;

    -- -------------------------------------------------------------------------

end architecture;
