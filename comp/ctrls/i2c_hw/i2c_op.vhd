-- i2c_op.vhd : I2C device read/write operation controller
--              Controller accesses I2C device and reads/writes data byte
-- Copyright (C) 2019 CESNET
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

entity i2c_op is
    generic (
        -- I2C clock dividier
        CLK_CNT : ieee.numeric_std.unsigned(15 downto 0) := X"007D"
    );
    port (
    -- =============
    -- CLK and RST
    -- =============

    -- sync reset
    RESET   : in   std_logic;
    -- clock
    CLK     : in   std_logic;

    -- =============
    -- I2C interface
    -- =============

    SCL_I    : in  std_logic;
    SCL_O    : out std_logic;
    SCL_OEN  : out std_logic;
    SDA_I    : in  std_logic;
    SDA_O    : out std_logic;
    SDA_OEN  : out std_logic;
    --
    -- Start the read operation
    START   : in  std_logic;
    -- '0' = read, '1' = write
    WR      : in  std_logic;
    -- Address Only flag. When set, terminate the bus operation after address phase ()
    AO      : in  std_logic := '0';
    -- I2C bus device address
    DEV     : in  std_logic_vector( 6 downto 0);
    -- I2C register address
    REG     : in  std_logic_vector( 7 downto 0);
    -- Do a 16 bit read
    DRD16   : in  std_logic := '0';
    -- I2C read data (Slave -> master)
    DRD     : out std_logic_vector(15 downto 0);
    -- I2C write data (master -> slave)
    DWD     : in  std_logic_vector( 7 downto 0);
    -- Operation acknowledge
    ACK     : out std_logic;
    -- Error during I2C operation (arbitration lost, destination not available)
    ERROR   : out std_logic;
    BUSY    : out std_logic;
    DONE    : out std_logic
    );
end i2c_op;

architecture behavioral of i2c_op is

type t_i2c_state is (IDLE, DA, DR,
                     RB_DA, RB_D, RB_D2, -- (Multiple) read byte states
                     WB_D,               -- Write byte
                     ERR
                    );

signal i2c_state : t_i2c_state;

signal reset_n   : std_logic;

signal i2c_start : std_logic;
signal i2c_stop  : std_logic;
signal i2c_rd    : std_logic;
signal i2c_wr    : std_logic;
signal i2c_ack   : std_logic;
signal i2c_din   : std_logic_vector(7 downto 0);
signal i2c_drd   : std_logic_vector(7 downto 0);
signal i2c_done  : std_logic;
signal i2c_busy  : std_logic;
signal i2c_rxack : std_logic;
signal i2c_al    : std_logic;

signal i2c_scl_o   : std_logic;
signal i2c_scl_i   : std_logic;
signal i2c_scl_oen : std_logic;
signal i2c_sda_o   : std_logic;
signal i2c_sda_i   : std_logic;
signal i2c_sda_oen : std_logic;

begin

    -- FSM performs sequence of I2C bus operations to read or write single byte
    -- to/from device DEV register REG
    fsm: process(CLK)
    begin
        if rising_edge(CLK) then
            i2c_start <= '0';
            i2c_stop  <= '0';
            i2c_rd    <= '0';
            i2c_wr    <= '0';
            i2c_ack   <= '0';
            DONE      <= '0';
            ACK       <= '0';
            ERROR     <= '0';

            case i2c_state is
                -- Bus IDLE, waiting for start
                when IDLE   =>
                    BUSY      <= '0';
                    if (START = '1') then
                        i2c_state <= DA;
                        BUSY      <= '1';
                        ACK       <= '1';
                    end if;

                -- Read-byte - device address
                when DA  =>
                    i2c_start <= '1';
                    i2c_wr    <= '1';
                    i2c_din   <= DEV & '0';
                    if (i2c_done = '1') then
                        i2c_start <= '0';
                        i2c_wr    <= '0';
                        if (i2c_rxack = '0') then
                           i2c_state <= DR;
                        else
                           i2c_state <= ERR; -- not acknowledged (no such device on bus)
                        end if;
                    end if;
                    if (i2c_al = '1') then
                        i2c_state <= ERR; -- arbitration lost
                    end if;

                -- Read-byte - write register number
                when DR =>
                    i2c_wr    <= '1';
                    i2c_stop  <= (not WR) or AO;
                    i2c_din   <= REG;
                    if (i2c_done = '1') then
                        i2c_wr   <= '0';
                        i2c_stop <= '0';
                        if (i2c_rxack = '0') then
                            if AO = '1' then -- Requested to execute addressing phase only
                                i2c_state <= IDLE;
                                DONE      <= '1';
                                BUSY      <= '0';
                            elsif WR = '1' then
                                i2c_state <= WB_D;
                            else
                                i2c_state <= RB_DA;
                            end if;
                        else
                            i2c_state <= ERR; -- not acknowledged
                        end if;
                    end if;
                    if (i2c_al = '1') then
                        i2c_state <= ERR; -- arbitration lost
                    end if;

                -- Read byte - write device address & read bit
                when RB_DA  =>
                    i2c_start <= '1';
                    i2c_wr    <= '1';
                    i2c_rd    <= '0';
                    i2c_din   <= DEV & '1';
                    i2c_ack   <= '0';
                    if (i2c_done = '1') then
                        i2c_start <= '0';
                        i2c_rd    <= '0';
                        i2c_wr    <= '0';
                        if (i2c_rxack = '0') then
                           i2c_state <= RB_D;
                        else
                           i2c_state <= ERR; -- not acknowledged (no such device on bus)
                        end if;
                    end if;
                    if (i2c_al = '1') then
                        i2c_state <= ERR; -- arbitration lost
                    end if;

                -- Read byte - read data
                when RB_D  =>
                    i2c_rd <= '1';
                    if DRD16 = '0' then
                        DRD(7 downto 0)  <= i2c_drd;
                        DRD(15 downto 8) <= X"00";
                        i2c_ack   <= '1'; -- NACK
                        i2c_stop  <= '1';
                    else
                        DRD(15 downto 8) <= i2c_drd;
                        i2c_ack   <= '0'; -- ACK
                        i2c_stop  <= '0';
                    end if;
                    if (i2c_done = '1') then -- byte is read
                        i2c_rd    <= '0';
                        i2c_stop  <= '0';
                        if DRD16 = '0' then -- All done
                            DONE      <= '1';
                            BUSY      <= '0';
                            i2c_state <= IDLE;
                        else                -- Read next byte
                            i2c_state <= RB_D2;
                        end if;
                    end if;
                    if (i2c_al = '1') then
                        i2c_state <= ERR; -- arbitration lost
                    end if;

                -- Read second data byte
                when RB_D2 =>
                    i2c_rd   <= '1';
                    i2c_ack  <= '1'; -- NACK
                    i2c_stop <= '1';
                    DRD(7 downto 0)  <= i2c_drd;
                    if (i2c_done = '1') then -- byte is read
                        i2c_rd    <= '0';
                        i2c_stop  <= '0';
                        DONE      <= '1';
                        BUSY      <= '0';
                        i2c_state <= IDLE;
                    end if;
                    if (i2c_al = '1') then
                        i2c_state <= ERR; -- arbitration lost
                    end if;

                -- write data byte
                when WB_D   =>
                    i2c_wr    <= '1';
                    i2c_stop  <= '1';
                    i2c_din   <= DWD;
                    if (i2c_done = '1') then -- all done, byte is written
                        i2c_wr    <= '0';
                        i2c_stop  <= '0';
                        DONE      <= '1';
                        BUSY      <= '0';
                        if (i2c_rxack = '0') then
                            i2c_state <= IDLE;
                        else
                            i2c_state <= ERR;
                        end if;
                    end if;
                    if (i2c_al = '1') then
                        i2c_state <= ERR; -- arbitration lost
                    end if;
                --
                when ERR  =>
                    i2c_stop <= '1';
                    --if (i2c_busy_i = '0') then --
                    if (i2c_done = '1') or (i2c_al = '1') then --
                        i2c_state <= IDLE;
                        BUSY     <= '0';
                        ERROR    <= '1';
                        i2c_stop <= '0';
                    end if;
            end case;

            if RESET = '1' then
                i2c_state <= IDLE;
            end if;
        end if;
    end process;

    reset_n <= not RESET;

    i2c_ctrl: entity work.i2c_master_byte_ctrl
    port map (
        clk     => CLK,
        rst     => RESET,
        nReset  => reset_n,
        ena     => '1',
        clk_cnt => ieee.std_logic_arith.unsigned(CLK_CNT), -- Clock dividier
        -- input signals
        start   => i2c_start,
        stop    => i2c_stop,
        read    => i2c_rd,
        write   => i2c_wr,
        ack_in  => i2c_ack,
        din     => i2c_din,
        -- output signals
        cmd_ack  => i2c_done,
        ack_out  => i2c_rxack,
        i2c_busy => i2c_busy,
        i2c_al   => i2c_al,
        dout     => i2c_drd,
        -- i2c lines
        scl_i    => scl_i,
        scl_o    => scl_o,
        scl_oen  => scl_oen,
        sda_i    => SDA_i,
        sda_o    => sda_o,
        sda_oen  => sda_oen
    );

end behavioral;
