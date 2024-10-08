-- i2c_switch.vhd : "Device driver" for the i2C switch chip (like PCA9545)
--                  Transforms i2c bus multiplexed bus into 4 virtual buses
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity i2c_switch is
    generic (
        IIC_CLK_CNT   : unsigned(15 downto 0) := X"007D";
        -- I2C switch device address (0xe0 is the default)
        SW_DEV_ADDR   : std_logic_vector( 6 downto 0) := "1110000"
    );
    port (
        -- =====================
        -- CLK and RST
        -- =====================

        RESET      : in  std_logic;
        CLK        : in  std_logic;

        -- =====================
        -- I2C bus arbitration
        -- =====================

        -- IIC bus request
        I2C_REQ    : out std_logic;
        -- IIC bus grant
        I2C_GNT    : in  std_logic := '1';
        -- MUX operation in progress
        I2C_BUSY   : out std_logic;
        -- MUX operation done
        I2C_DONE   : out std_logic;
        -- MUX operation done
        ERROR      : out std_logic;

        -- ======================================
        -- I2C master interfaces (virtual i2c buses "behind" the switch)
        -- ======================================

        -- Master request & grant
        MREQ        : in  std_logic_vector(3 downto 0) := (others => '0');
        MBUSY       : in  std_logic_vector(3 downto 0) := (others => '0');
        MDONE       : in  std_logic_vector(3 downto 0) := (others => '0');
        MGNT        : out std_logic_vector(3 downto 0);
        MSCL_I      : out std_logic_vector(3 downto 0);
        MSCL_O      : in  std_logic_vector(3 downto 0);
        MSCL_OEN    : in  std_logic_vector(3 downto 0);
        MSDA_I      : out std_logic_vector(3 downto 0);
        MSDA_O      : in  std_logic_vector(3 downto 0);
        MSDA_OEN    : in  std_logic_vector(3 downto 0);

        -- =================================
        -- Output I2C interface to MUX and slaves
        -- ==================================

        SCL_I      : in  std_logic;
        SCL_O      : out std_logic;
        SCL_OEN    : out std_logic;
        SDA_I      : in  std_logic;
        SDA_O      : out std_logic;
        SDA_OEN    : out std_logic
    );
end i2c_switch;

architecture behavioral of i2c_switch is

    -- COMPONENT i2c_ila
    -- PORT (
    --     clk : IN STD_LOGIC;
    --     probe0 : IN STD_LOGIC_VECTOR(15 DOWNTO 0)
    -- );
    -- END COMPONENT ;
    -- signal probe0  : std_logic_vector(15 downto 0);

type t_pool_state is (S_IDLE,
                      S_MUX_BUSY,
                      S_PAUSE,
                      S_PAUSE1,
                      S_START,
                      S_START1,
                      S_GNT,
                      S_MUX_BUSY2,
                      S_DONE
                     );

signal state         : t_pool_state;

signal iic_start     : std_logic;
signal iic_wr        : std_logic;
signal iic_ao        : std_logic;
signal iic_reg       : std_logic_vector(7 downto 0);
signal iic_drd       : std_logic_vector(15 downto 0);
signal iic_dwr       : std_logic_vector(7 downto 0);
signal iic_error     : std_logic;
signal iic_busy      : std_logic;
signal iic_done      : std_logic;
signal iic_event     : std_logic;
signal busy          : std_logic;
signal done          : std_logic;

signal o_change      : std_logic;
signal dir_change    : std_logic;
signal refr_timer    : unsigned(IIC_CLK_CNT'range);
signal refr_timer_done : std_logic := '0';
signal i_refresh       : std_logic;

signal msda_oen_r      : std_logic_vector(3 downto 0);
signal msda_r          : std_logic_vector(3 downto 0);

signal mux_scl_o       : std_logic;
signal mux_scl_oen     : std_logic;
signal mux_sda_o       : std_logic;
signal mux_sda_oen     : std_logic;

signal bus_req         : std_logic_vector(3 downto 0);
signal bus_gnt         : std_logic_vector(3 downto 0);
signal bus_stretch     : std_logic_vector(3 downto 0);
signal bus_sel         : std_logic_vector(3 downto 0);
signal start_gen       : std_logic;
signal bus_done        : std_logic;

begin

bus_req_p: process(CLK)
begin
    if rising_edge(CLK) then
        msda_r     <= MSDA_I;
        msda_oen_r <= MSDA_OEN;
        for i in 0 to 3 loop
            if ((msda_r(i) = '0' and MSDA_I(i) = '1' and MSCL_I(i) = '1') and (MBUSY(i) = '0')) or (MDONE(i) = '1') then -- stop condition
                bus_req(i) <= '0';
            elsif (msda_oen_r(i) = '1' and MSDA_OEN(i) = '0' and MSCL_OEN(i) = '1') or (MREQ(i) = '1') then -- Start condition
                bus_req(i) <= '1';
            end if;
        end loop;
    end if;
end process;

-- TBD: priorities
bus_sel <= "0001" when bus_req(0) = '1' else
           "0010" when bus_req(1) = '1' else
           "0100" when bus_req(2) = '1' else
           "1000" when bus_req(3) = '1' else
           "0000";

bus_done <= '1' when ((bus_gnt = "0001" and bus_req(0) = '0') or
                      (bus_gnt = "0010" and bus_req(1) = '0') or
                      (bus_gnt = "0100" and bus_req(2) = '0') or
                      (bus_gnt = "1000" and bus_req(3) = '0')) else
            '0';

I2C_REQ   <= or bus_req;
I2C_BUSY  <= busy;
I2C_DONE  <= done;

    fsm_p: process(CLK)
    begin
        if rising_edge(CLK) then
            iic_start <= '0';
            start_gen <= '0';
            case state is

                -- Start I2C mux configure operation
                when S_IDLE =>
                    done      <= '0';
                    ERROR     <= '0';
                    busy      <= '0';
                    iic_start <= '0';
                    bus_gnt   <= "0000";
                    if (I2C_REQ = '1') then
                        if (I2C_GNT = '1') then
                            state     <= S_MUX_BUSY;
                            iic_start <= '1';
                            iic_reg   <= "0000" & bus_sel;
                            busy      <= '1';
                        end if;
                    end if;

                -- Wait until the I2C bus MUX operation finishes
                when S_MUX_BUSY =>
                    iic_start <= '0';
                    busy      <= '1';
                    if (iic_error = '1') then
                        state   <= S_IDLE; -- Error
                        ERROR   <= '1';
                    elsif (iic_done = '1') then
                        --state <= S_GNT;
                        state <= S_PAUSE;
                        refr_timer <= (others => '0');
                    end if;

                -- TBD: generate start condition here???
                when S_PAUSE =>
                    bus_gnt    <= "0000";
                    iic_start  <= '0';
                    refr_timer <= refr_timer + 1;
                    if refr_timer = IIC_CLK_CNT then
                        refr_timer <= (others => '0');
                        state <= S_PAUSE1;
                    end if;

                when S_PAUSE1 =>
                    bus_gnt    <= "0000";
                    iic_start  <= '0';
                    refr_timer <= refr_timer + 1;
                    if refr_timer = IIC_CLK_CNT then
                        refr_timer <= (others => '0');
                        state <= S_START;
                    end if;

                -- Generate repeated start in place of the slave
                when S_START =>
                    bus_gnt    <= "0000";
                    iic_start  <= '0';
                    start_gen  <= '1';
                    refr_timer <= refr_timer + 1;
                    if refr_timer = IIC_CLK_CNT then
                        state <= S_START1;
                    end if;

                -- Generate repeated start in place of the slave
                when S_START1 =>
                    bus_gnt    <= "0000";
                    iic_start  <= '0';
                    start_gen  <= '1';
                    refr_timer <= refr_timer + 1;
                    if refr_timer = IIC_CLK_CNT then
                        state      <= S_GNT;
                        start_gen  <= '0';
                    end if;

                -- Grant bus for selected I2C master
                when S_GNT =>
                    bus_gnt <= iic_reg(3 downto 0);
                    if bus_done = '1' then
                        --state   <= S_DONE;
                        --done    <= '1';
                        -- busy      <= '0';
                        state     <= S_MUX_BUSY2;
                        bus_gnt   <= "0000";
                        iic_start <= '1'; -- Start switch bus release cycle
                        iic_reg   <= "0000" & "0000";
                    end if;

                when S_MUX_BUSY2 =>
                    iic_start <= '0';
                    busy      <= '1';
                    if (iic_error = '1') then
                        state   <= S_IDLE; -- Error
                        ERROR   <= '1';
                    elsif (iic_done = '1') then
                        state   <= S_DONE;
                        busy    <= '0';
                        done    <= '1';
                    end if;

                 -- One wait state to provide some time for bus arbiter
                when S_DONE =>
                    bus_gnt   <= "0000";
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
        scl_o   => mux_scl_o,
        scl_oen => mux_scl_oen,
        sda_i   => SDA_I,
        sda_o   => mux_sda_o,
        sda_oen => mux_sda_oen,
        -- Operation control
        START   => iic_start,
        WR      => '0',
        AO      => '1',
        DEV     => SW_DEV_ADDR,
        REG     => iic_reg,
        DRD16   => '0',
        DRD     => open, --iic_drd,
        DWD     => (others => '0'), --iic_dwr,
        ACK     => open,
        ERROR   => iic_error,
        BUSY    => iic_busy,
        DONE    => iic_done
    );

    ---------------------------------------------------------------------
    -- Bus MUXes
    ---------------------------------------------------------------------
    MGNT       <= bus_gnt;
    MSDA_I     <= (others => SDA_I);

    mscl_g: for i in MSCL_I'range generate
        bus_stretch(i) <= '1' when bus_req(i) = '1' and bus_gnt(i) = '0' else '0';
        MSCL_I(i)     <= '0' when bus_stretch(i) = '1' else
                         '1' when bus_gnt(i) = '0'     else
                         SCL_I;
    end generate;

    SCL_O      <= MSCL_O(0) when bus_gnt(0) = '1' else
                  MSCL_O(1) when bus_gnt(1) = '1' else
                  MSCL_O(2) when bus_gnt(2) = '1' else
                  MSCL_O(3) when bus_gnt(3) = '1' else
                  mux_scl_o;

    SCL_OEN    <= MSCL_OEN(0) when bus_gnt(0) = '1' else
                  MSCL_OEN(1) when bus_gnt(1) = '1' else
                  MSCL_OEN(2) when bus_gnt(2) = '1' else
                  MSCL_OEN(3) when bus_gnt(3) = '1' else
                  '1'         when start_gen  = '1' else
                  mux_scl_oen;

    SDA_O      <= MSDA_O(0) when bus_gnt(0) = '1' else
                  MSDA_O(1) when bus_gnt(1) = '1' else
                  MSDA_O(2) when bus_gnt(2) = '1' else
                  MSDA_O(3) when bus_gnt(3) = '1' else
                  '0'       when start_gen  = '1' else
                  mux_sda_o;

    SDA_OEN    <= MSDA_OEN(0) when bus_gnt(0) = '1' else
                  MSDA_OEN(1) when bus_gnt(1) = '1' else
                  MSDA_OEN(2) when bus_gnt(2) = '1' else
                  MSDA_OEN(3) when bus_gnt(3) = '1' else
                  '0'         when start_gen  = '1' else
                  mux_sda_oen;

end behavioral;
