-- io_exp.vhd : "Device driver" for the i2C IO expander (like TCA6408A)
--              DIR, I and O ports are propagated to the expander ports
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity i2c_io_exp is
    generic (
        -- I2C clock divider
        IIC_CLK_CNT : unsigned(15 downto 0) := X"007D";
        -- IO expander device I2C address
        -- 0x20
        IIC_DEV_ADDR  : std_logic_vector( 6 downto 0) := "0100000";
        -- Configure the IO ports direction upon releasing reset
        PWR_UP_CONFIG : boolean := true;
        -- Address of port direction register. Predefined for the TCA6408A chip
        IIC_REG_DIR   : std_logic_vector( 7 downto 0) := X"03";
        -- Address of input port register
        IIC_REG_I     : std_logic_vector( 7 downto 0) := X"00";
        -- Address of output port register
        IIC_REG_O     : std_logic_vector( 7 downto 0) := X"01";
        -- Enable auto refresh of the remote inputs (I port)
        AUTO_REFRESH : boolean := true;
        -- Number of clock cycles for refreshing I input. Range 0 to 2^24-1, 0 = refresh as fast as possible
        REFRESH_CYCLES: natural := 16#0010000#
    );
    port (
        -- =====================
        -- CLK and RST
        -- =====================

        RESET      : in  std_logic;
        CLK        : in  std_logic;

        -- =====================
        -- Remote I/O interface
        -- =====================

        -- '1' = Input, '0' = output
        DIR        : in  std_logic_vector(7 downto 0);
        -- Remote input
        I          : out std_logic_vector(7 downto 0);
        -- Remote output
        O          : in  std_logic_vector(7 downto 0);

        -- =====================
        -- Control
        -- =====================

        -- Force manual refresh of the I port
        REFRESH    : in  std_logic := '0';
        -- Force manual settings of DIR and O ports
        CONFIG     : in  std_logic := '0';
        -- operation failed (i2c error)
        ERROR      : out std_logic;

        -- =====================
        -- I2C bus arbitration
        -- =====================

        -- IIC bus request
        I2C_REQ    : out std_logic;
        -- IIC bus grant
        I2C_GNT    : in  std_logic := '1';
        -- IIC bus busy
        I2C_BUSY   : out std_logic;
        -- IIC bus operation done
        I2C_DONE   : out std_logic;

        -- =====================
        -- I2C interface
        -- =====================

        SCL_I      : in  std_logic;
        SCL_O      : out std_logic;
        SCL_OEN    : out std_logic;
        SDA_I      : in  std_logic;
        SDA_O      : out std_logic;
        SDA_OEN    : out std_logic
    );
end i2c_io_exp;

architecture behavioral of i2c_io_exp is

type t_pool_state is (S_IDLE,
                      S_WR_BUSY,
                      S_RD_BUSY,
                      S_DONE
                     );

signal state         : t_pool_state;

signal o_sync        : std_logic_vector(O'range);
signal dir_sync      : std_logic_vector(DIR'range);
signal o_set         : std_logic;
signal dir_set       : std_logic;
signal i_get         : std_logic;
signal o_r           : std_logic_vector(O'range);
signal dir_r         : std_logic_vector(DIR'range);
signal d_ack         : std_logic;
signal i_ack         : std_logic;
signal o_ack         : std_logic;

signal iic_start     : std_logic;
signal iic_wr        : std_logic;
signal iic_dev       : std_logic_vector(6 downto 0);
signal iic_reg       : std_logic_vector(7 downto 0);
signal iic_drd       : std_logic_vector(15 downto 0);
signal iic_dwr       : std_logic_vector(7 downto 0);
signal iic_error     : std_logic;
signal iic_busy      : std_logic;
signal iic_done      : std_logic;
signal busy          : std_logic;
signal done          : std_logic;

signal o_change      : std_logic;
signal dir_change    : std_logic;
signal refr_timer    : unsigned(27 downto 0);
signal refr_timer_done : std_logic := '0';
signal i_refresh       : std_logic;

begin

cdc_g: for i in DIR'range generate
    sync_dir: entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG   => false,
        TWO_REG  => true
    )
    port map (
        ADATAIN  => DIR(i),
        BCLK     => CLK,
        BDATAOUT => dir_sync(i)
    );
    sync_o: entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG   => false,
        TWO_REG  => true
    )
    port map (
        ADATAIN  => O(i),
        BCLK     => CLK,
        BDATAOUT => o_sync(i)
    );
end generate;

o_change   <= '1' when  o_sync /= o_r     else CONFIG;
dir_change <= '1' when  dir_sync /= dir_r else CONFIG;

refresh_cntr_g: if AUTO_REFRESH generate
    -- Counter for refreshing the remote I input
    refresh_cntr_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if RESET = '1' or refr_timer = REFRESH_CYCLES then
                refr_timer <= (others => '0');
            else
                refr_timer <= refr_timer + 1;
            end if;
            if i_get = '1' then
                refr_timer_done <= '0';
            elsif (refr_timer = REFRESH_CYCLES) then
                refr_timer_done <= '1';
            end if;
        end if;
    end process;
end generate;

i_refresh <= refr_timer_done or REFRESH;

fsm_control_p: process(CLK)
begin
    if (rising_edge(CLK)) then
        -- Set the request flags when a change is detected and FSM is not busy
        if (busy = '0') then
            if (dir_change = '1') then
                dir_r   <= dir_sync;
                dir_set <= '1';
            end if;
            if (o_change = '1') then
                o_r   <= o_sync;
                o_set <= '1';
            end if;
            if (i_refresh = '1') then
                i_get <= '1';
            end if;
        end if;
        -- I2C operation started, clear the request flags
        --if (done = '1') then
            if (d_ack = '1') then
                dir_set <= '0';
            end if;
            if (o_ack = '1') then
                o_set <= '0';
            end if;
            if (i_ack = '1') then
                i_get <= '0';
            end if;
        --end if;
        if RESET = '1' then
            if PWR_UP_CONFIG then
                -- Set change detection registers in such way, that it forces
                -- the io expander to be re-configured (dir_change and o_change
                -- will be high) after reset
                dir_r <= not dir_sync;
                o_r   <= not o_sync;
            else
                dir_r <= dir_sync;
                o_r   <= o_sync;
            end if;
        end if;
    end if;
end process;

I2C_REQ   <= dir_set or o_set or i_get;
I2C_BUSY  <= busy;
I2C_DONE  <= done;

    fsm_p: process(CLK)
    begin
        if rising_edge(CLK) then
            iic_start <= '0';
            i_ack     <= '0';
            o_ack     <= '0';
            d_ack     <= '0';
            case state is

                -- Start I2C read operation
                when S_IDLE =>
                    done      <= '0';
                    ERROR     <= '0';
                    iic_dev   <= IIC_DEV_ADDR;
                    busy      <= '0';
                    iic_start <= '0';
                    -- I2c bus acess granted
                    if (I2C_GNT = '1') then
                        if (i_get = '1')  then
                            state     <= S_RD_BUSY;
                            iic_reg   <= IIC_REG_I;
                            iic_wr    <= '0';
                            iic_start <= '1';
                            busy      <= '1';
                            i_ack     <= '1';
                            o_ack     <= '0';
                            d_ack     <= '0';
                        end if;
                        if (o_set = '1') then
                            state     <= S_WR_BUSY;
                            iic_reg   <= IIC_REG_O;
                            iic_wr    <= '1';
                            iic_dwr   <= o_sync(7 downto 0);
                            iic_start <= '1';
                            busy      <= '1';
                            i_ack     <= '0';
                            o_ack     <= '1';
                            d_ack     <= '0';
                        end if;
                        if dir_set = '1' then
                            state     <= S_WR_BUSY;
                            iic_reg   <= IIC_REG_DIR;
                            iic_wr    <= '1';
                            iic_dwr   <= dir_sync(7 downto 0);
                            iic_start <= '1';
                            busy      <= '1';
                            i_ack     <= '0';
                            o_ack     <= '0';
                            d_ack     <= '1';
                       end if;
                   end if;

                -- Wait until the direction register write operation finishes
                when S_WR_BUSY =>
                    iic_start <= '0';
                    busy      <= '1';
                    if (iic_error = '1') then
                        state   <= S_DONE;
                        ERROR   <= '1';
                        done    <= '1';
                    elsif (iic_done = '1') then
                        state <= S_DONE;
                        done  <= '1';
                    end if;

                -- Wait until the direction register write operation finishes
                when S_RD_BUSY =>
                    iic_start <= '0';
                    busy      <= '1';
                    if (iic_error = '1') then
                        state   <= S_DONE;
                        ERROR   <= '1';
                        done    <= '1';
                    elsif (iic_done = '1') then
                        state <= S_DONE;
                        I     <= iic_drd(7 downto 0);
                        done  <= '1';
                    end if;

                -- One wait state to provide some time for bus arbiter
                when S_DONE =>
                    iic_start <= '0';
                    busy      <= '0';
                    done      <= '0';
                    ERROR     <= '0';
                    state   <= S_IDLE;

            end case;

            if RESET = '1' then
                state     <= S_IDLE;
                iic_start <= '0';
                busy      <= '0';
            end if;
        end if;
    end process;

    I2C_CTRL: entity work.i2c_op
    generic map (
       CLK_CNT => IIC_CLK_CNT
    )
    port map (
        RESET   => RESET,
        CLK     => CLK,
        -- I2C interface
        scl_i   => SCL_I,
        scl_o   => SCL_O,
        scl_oen => SCL_OEN,
        sda_i   => SDA_i,
        sda_o   => SDA_O,
        sda_oen => SDA_OEN,
        -- Operation control
        START   => iic_start,
        WR      => iic_wr,
        DEV     => iic_dev,
        REG     => iic_reg,
        DRD16   => '0',
        DRD     => iic_drd,
        DWD     => iic_dwr,
        ACK     => open,
        ERROR   => iic_error,
        BUSY    => iic_busy,
        DONE    => iic_done
    );

   end behavioral;
