-- bmc_driver.vhd: Board Management Controller driver 
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <benes.david2000@seznam.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component is bridge unit between MI32 protocol and SPI protocol
-- for communication with BMC device.
-- BMC device is capable of rebooting FPGA and changing boot flash.
-- This component supports 200 MHz clock. Default SPI frequency is 
-- 806 kHz and can be changed by divide ratio. SPI_CLK = (CLK/(4*spi_freq_div))
entity BMC_DRIVER is
    generic(
        -- Address width
        G_MI_ADDR_WIDTH  : integer := 8;
        -- Data width of MI32
        G_MI_DATA_WIDTH  : integer := 32
    );
    port (
        CLK            : in  std_logic;
        RST            : in  std_logic;

        -- SPI interface for communication with BMC device 
        SPI_CLK        : out std_logic;
        SPI_NSS        : out std_logic;
        SPI_MOSI       : out std_logic;
        SPI_MISO       : in  std_logic;
        SPI_INT        : in  std_logic;

        -- MI32 protocol signals 
        BMC_MI_ADDR : in  std_logic_vector(G_MI_ADDR_WIDTH - 1 downto 0);
        BMC_MI_DWR  : in  std_logic_vector(G_MI_DATA_WIDTH - 1 downto 0);
        BMC_MI_WR   : in  std_logic;
        BMC_MI_RD   : in  std_logic;
        BMC_MI_BE   : in  std_logic_vector(3 downto 0);
        BMC_MI_ARDY : out std_logic;
        BMC_MI_DRD  : out std_logic_vector(G_MI_DATA_WIDTH - 1 downto 0);
        BMC_MI_DRDY : out std_logic
    );
end BMC_DRIVER;

architecture FULL of BMC_DRIVER is
    type t_fsm_led_ctrl is (
        st_idle,                -- waiting for commands 
        st_boot_request,        -- reboot
        st_write,               -- writing 1 byte to SPI slave device
        st_write_delay,         -- delay between bytes
        st_wait,                -- state between write and read process
        st_read,                -- reading 1 byte data from SPI
        st_read_delay,          -- delay between bytes
        st_eos                  -- end of sequence
    );    

    -- Control logic (FSM)
    signal state, next_state: t_fsm_led_ctrl := st_idle;

    -- SPI clock generator
    signal spi_freq_div_d   : unsigned(5 downto 0):=to_unsigned(61, 6);
    signal spi_freq_div_q   : unsigned(5 downto 0):=to_unsigned(61, 6);
    signal spi_clk_cnt      : unsigned(6 downto 0):=to_unsigned(0, 7);
    signal spi_clk_en       : std_logic:= '0';
    signal spi_clk_event    : std_logic;

    -- SPI protocol
    signal mosi_data_d         : std_logic_vector(47 downto 0);
    signal mosi_data_q         : std_logic_vector(47 downto 0);
    signal mosi_data_cnt_d     : unsigned(3 downto 0) :=(others => '0');
    signal mosi_data_cnt_q     : unsigned(3 downto 0) :=(others => '0');
    signal mosi_word_cnt_d     : unsigned(2 downto 0) :=(others => '0');
    signal mosi_word_cnt_q     : unsigned(2 downto 0) :=(others => '0');

    signal miso_data_d         : std_logic_vector(15 downto 0);
    signal miso_data_q         : std_logic_vector(15 downto 0);
    signal miso_data_cnt_d     : unsigned(3 downto 0) :=(others => '0');
    signal miso_data_cnt_q     : unsigned(3 downto 0) :=(others => '0');
    signal miso_word_cnt_d     : unsigned(2 downto 0) :=(others => '0');
    signal miso_word_cnt_q     : unsigned(2 downto 0) :=(others => '0');

    -- Pulse generator 
    signal pulse_cnt           : unsigned(17 downto 0):=(others => '0');
    signal pulse_event         : std_logic;
    signal pulse_gen_en        : std_logic;

    -- Delay between writed or read bytes
    signal delay_duration_d    : std_logic_vector(7 downto 0):= (others => '0');
    signal delay_duration_q    : std_logic_vector(7 downto 0):= (others => '0');
    signal delay_cnt_d         : unsigned(7 downto 0);
    signal delay_cnt_q         : unsigned(7 downto 0);

    -- Delay between write and read in ms 
    signal wait_duration_d     : std_logic_vector(15 downto 0):= (others => '0');
    signal wait_duration_q     : std_logic_vector(15 downto 0):= (others => '0');
    signal wait_cnt_d          : unsigned(15 downto 0):= (others => '0');
    signal wait_cnt_q          : unsigned(15 downto 0):= (others => '0');
    signal timeout_event_d     : std_logic;
    signal timeout_event_q     : std_logic;

    -- Interrupt 
    signal interrupt_event     : std_logic;
    signal interrupt_re0       : std_logic;
    signal interrupt_re1       : std_logic;
    signal interrupt_detected  : std_logic;

    -- Status signals
    signal status_done_d       : std_logic;
    signal status_done_q       : std_logic;
    signal status_ready_d      : std_logic;
    signal status_ready_q      : std_logic;

    -- SPI buffer 
    signal spi_clk_s           : std_logic:= '0';
    signal spi_clk_d           : std_logic:= '0';
    signal spi_clk_q           : std_logic:= '0';
    signal spi_nss_d           : std_logic:= '0';
    signal spi_nss_q           : std_logic:= '0';
    signal spi_mosi_d          : std_logic:= '0';
    signal spi_mosi_q          : std_logic:= '0';
    signal spi_miso_s          : std_logic:= '0';

    -- Boot
    signal boot_cmd_d         : std_logic:= '0';
    signal boot_cmd_q         : std_logic:= '0';
    signal boot_timeout       : unsigned(25 downto 0) := (others => '0');

    -- MI buffer
    signal bmc_mi_ardy_d      : std_logic;
    signal bmc_mi_drd_d       : std_logic_vector(G_MI_DATA_WIDTH - 1 downto 0);
    signal bmc_mi_drdy_d      : std_logic;
    signal bmc_mi_ardy_q      : std_logic;
    signal bmc_mi_drd_q       : std_logic_vector(G_MI_DATA_WIDTH - 1 downto 0);
    signal bmc_mi_drdy_q      : std_logic;

    signal bmc_mi_wr_s        : std_logic;
    signal bmc_mi_rd_s        : std_logic;
    signal bmc_mi_be_s        : std_logic_vector(3 downto 0);

begin
    -----------------------------------------------------------------------------
    --                          INTERRUPT DETECTION
    -----------------------------------------------------------------------------    
    int_p: process(CLK)
    begin
        if rising_edge(CLK) then 
            -- Detection of interrupt rising_edge(re)
            interrupt_re0   <= SPI_INT;
            interrupt_re1   <= interrupt_re0;
            interrupt_event <= interrupt_re0 and (not interrupt_re1);

            -- Saving 're' information 
            if interrupt_event = '1' then 
                interrupt_detected <= '1';
            end if;

            if RST = '1' then 
                interrupt_detected <= '0';
                interrupt_event    <= '0';
            elsif state = st_idle then 
                interrupt_detected <= '0';
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                          SEQUENTIAL PART
    -----------------------------------------------------------------------------

    mem_p: process (CLK)
    begin 
        if rising_edge(CLK) then
            if RST = '1' then
                state                <= st_idle;
                mosi_data_cnt_q      <= (others => '0');
                mosi_word_cnt_q      <= (others => '0');
                delay_cnt_q          <= (others => '0');
                wait_cnt_q           <= (others => '0');
                timeout_event_q      <= '0';
                miso_data_cnt_q      <= (others => '0');
                miso_word_cnt_q      <= (others => '0');
                status_done_q        <= '0';
                delay_duration_q     <= x"80";
                wait_duration_q      <= x"0005";
                mosi_data_q          <= (others => '0');
                spi_mosi_q           <= '0';
                miso_data_q          <= (others => '0');
                spi_nss_q            <= '0';
                spi_clk_q            <= '1';
                spi_freq_div_q       <= to_unsigned(61, spi_freq_div_q'length);
                bmc_mi_drd_q         <= (others => '0');
                bmc_mi_drdy_q        <= '0';
                boot_cmd_q           <= '0';
                status_ready_q       <= '0';
            else
                state                <= next_state;
                mosi_data_cnt_q      <= mosi_data_cnt_d;
                mosi_word_cnt_q      <= mosi_word_cnt_d;
                delay_cnt_q          <= delay_cnt_d;
                wait_cnt_q           <= wait_cnt_d;
                timeout_event_q      <= timeout_event_d;
                miso_data_cnt_q      <= miso_data_cnt_d;
                miso_word_cnt_q      <= miso_word_cnt_d;
                status_done_q        <= status_done_d;
                delay_duration_q     <= delay_duration_d;
                wait_duration_q      <= wait_duration_d;
                mosi_data_q          <= mosi_data_d;
                spi_mosi_q           <= spi_mosi_d;
                miso_data_q          <= miso_data_d;
                spi_nss_q            <= spi_nss_d;
                spi_clk_q            <= spi_clk_d;
                spi_freq_div_q       <= spi_freq_div_d;
                bmc_mi_drd_q         <= bmc_mi_drd_d;
                bmc_mi_drdy_q        <= bmc_mi_drdy_d;
                boot_cmd_q           <= boot_cmd_d;
                status_ready_q       <= status_ready_d;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                         COMBINATIONAL PART
    -----------------------------------------------------------------------------
    -- MI32
    bmc_mi_wr_s <= BMC_MI_WR;
    bmc_mi_rd_s <= BMC_MI_RD;
    bmc_mi_be_s <= BMC_MI_BE;

    BMC_MI_DRD  <= bmc_mi_drd_q;
    BMC_MI_DRDY <= bmc_mi_drdy_q;
    BMC_MI_ARDY <= bmc_mi_wr_s or bmc_mi_rd_s;
    mi_rd_p: process(all)
    begin
        case BMC_MI_ADDR(3 downto 2) is
            when "00"   =>
                bmc_mi_drd_d(15 downto 0)     <= miso_data_q;     -- Received data (16 bit)
                bmc_mi_drd_d(16)              <= status_done_q;   -- Status done, occurs when the transaction is done or clock is set up
                bmc_mi_drd_d(17)              <= '0';
                bmc_mi_drd_d(18)              <= timeout_event_q; -- Timeout indication due to missing interrupt from BMC device (device is not ready to transmit data)
                bmc_mi_drd_d(19)              <= status_ready_q;  -- Ready for another transaction (st_idle) 
                bmc_mi_drd_d(23 downto 20)    <= (others => '0');
                bmc_mi_drd_d(31 downto 24)    <= x"02";           -- Controller version
            when others =>
                bmc_mi_drd_d <= (others => '0');
        end case;
        bmc_mi_drdy_d    <= bmc_mi_rd_s;  
    end process;

    fsm_p: process(all)
    begin
        spi_clk_en          <= '0';
        pulse_gen_en        <= '0';
        status_ready_d      <= '0';
        next_state          <= state;
        mosi_data_cnt_d     <= mosi_data_cnt_q;
        mosi_word_cnt_d     <= mosi_word_cnt_q;
        delay_cnt_d         <= delay_cnt_q;
        wait_cnt_d          <= wait_cnt_q;
        timeout_event_d     <= timeout_event_q;
        miso_data_cnt_d     <= miso_data_cnt_q;
        miso_word_cnt_d     <= miso_word_cnt_q;
        status_done_d       <= status_done_q;
        delay_duration_d    <= delay_duration_q;
        wait_duration_d     <= wait_duration_q;
        mosi_data_d         <= mosi_data_q;
        spi_mosi_d          <= spi_mosi_q;
        miso_data_d         <= miso_data_q;
        spi_nss_d           <= spi_nss_q;
        spi_clk_d           <= spi_clk_s;
        spi_freq_div_d      <= spi_freq_div_q;
        boot_cmd_d          <= boot_cmd_q;
           
        case(state) is
            when st_idle        =>
                spi_nss_d           <= '1';
                spi_mosi_d          <= '1';
                status_ready_d      <= '1';
                status_done_d       <= '0';      

                mosi_data_cnt_d     <= (others => '0');
                mosi_word_cnt_d     <= (others => '0');
                miso_data_cnt_d     <= (others => '0');
                miso_word_cnt_d     <= (others => '0');

                if bmc_mi_wr_s = '1' and boot_cmd_q = '0' then
                    case BMC_MI_ADDR(3 downto 2) is
                        when "00" =>
                            -- 31 downto 0: DATA
                            mosi_data_d(31 downto 0)    <= BMC_MI_DWR;
                        when "01" =>
                            -- 31 downto 28: CMD configuration
                            -- 27 downto 16: SUB_CMD configuration 
                            mosi_data_d(47 downto 32)   <= BMC_MI_DWR(31 downto 16);

                            -- Reboot
                            if BMC_MI_DWR(31 downto 28) = x"E" then
                                next_state     <= st_boot_request;
                                boot_cmd_d     <= '1';
                            elsif BMC_MI_DWR(31 downto 28) = x"A" then
                                case mosi_data_q(3 downto 0) is
                                    --SPI_CLK divide ratio
                                    when x"0"   => spi_freq_div_d <= to_unsigned( 0,spi_freq_div_q'length);
                                    when x"1"   => spi_freq_div_d <= to_unsigned( 1,spi_freq_div_q'length);
                                    when x"2"   => spi_freq_div_d <= to_unsigned( 4,spi_freq_div_q'length);
                                    when x"3"   => spi_freq_div_d <= to_unsigned( 9,spi_freq_div_q'length);
                                    when x"4"   => spi_freq_div_d <= to_unsigned(15,spi_freq_div_q'length);
                                    when x"5"   => spi_freq_div_d <= to_unsigned(19,spi_freq_div_q'length);
                                    when x"6"   => spi_freq_div_d <= to_unsigned(24,spi_freq_div_q'length);
                                    when x"7"   => spi_freq_div_d <= to_unsigned(39,spi_freq_div_q'length);
                                    when x"8"   => spi_freq_div_d <= to_unsigned(49,spi_freq_div_q'length);
                                    when x"9"   => spi_freq_div_d <= to_unsigned(61,spi_freq_div_q'length);
                                    when x"A"   => spi_freq_div_d <= to_unsigned(62,spi_freq_div_q'length);
                                    when others => spi_freq_div_d <= to_unsigned(24,spi_freq_div_q'length);
                                end case;

                                status_done_d       <= '1';
                                wait_duration_d     <= mosi_data_q(31 downto 16);
                                delay_duration_d    <= mosi_data_q(11 downto 4);
                            else
                                status_done_d       <= '0';
                                timeout_event_d     <= '0';
                                status_ready_d      <= '0';
                                next_state          <= st_write;
                            end if;

                        when others => null;
                    end case; 
                end if;

                if boot_cmd_q = '1' then 
                    next_state <= st_boot_request;
                end if;

            when st_boot_request    =>
                if boot_timeout(25) = '1' then 
                    status_done_d       <= '0';
                    timeout_event_d     <= '0';
                    next_state          <= st_write;
                end if;

            when st_write           =>
                spi_clk_en      <= '1';
                delay_cnt_d     <= (others => '0');

                if spi_clk_event = '1' then 
                    spi_nss_d       <= '0';

                    if spi_clk_s = '0' then 
                        mosi_data_d     <= mosi_data_q(mosi_data_q'high - 1 downto 0) & '0';
                        spi_mosi_d      <= mosi_data_q(mosi_data_q'high);
                        mosi_data_cnt_d <= mosi_data_cnt_q + 1;
                    end if;

                    if mosi_data_cnt_q = 8 then
                        next_state <= st_write_delay;
                    end if;
                end if;


            when st_write_delay     =>
                spi_clk_en          <= '1';
                mosi_data_cnt_d     <= (others => '0');
                
                if spi_clk_event = '1' then
                    spi_nss_d   <= '1';
                    delay_cnt_d <= delay_cnt_q + 1;

                    if delay_cnt_q = to_integer(unsigned(delay_duration_q(7 downto 1))) then
                        next_state      <= st_write;

                        mosi_word_cnt_d <= mosi_word_cnt_q + 1;
                        if mosi_word_cnt_q = 6 - 1 then 
                            next_state <= st_wait;
                        end if;
                    end if;
                end if;

            when st_wait            =>
                pulse_gen_en <= '1';

                if pulse_event = '1' then 
                    wait_cnt_d <= wait_cnt_q + 1;
                end if;

                if interrupt_detected = '1' then 
                    next_state      <= st_read;
                elsif wait_cnt_q = to_integer(unsigned(wait_duration_q)) then
                    next_state      <= st_read;
                    timeout_event_d <= '1';
                end if; 
                    
            when st_read            =>
                spi_clk_en      <= '1';
                delay_cnt_d     <= (others => '0');

                if spi_clk_event = '1' then
                    spi_nss_d   <= '0';

                    if spi_clk_s = '1' then 
                        miso_data_d     <= miso_data_q(miso_data_q'high - 1 downto 0)  & spi_miso_s;
                        miso_data_cnt_d <= miso_data_cnt_q + 1;
                    end if;

                    if miso_data_cnt_q = 8  then
                        next_state <= st_read_delay;
                    end if;
                end if;

                if miso_data_cnt_q = 8 then
                    next_state <= st_read_delay;
                end if;

            when st_read_delay      =>
                spi_clk_en      <= '1';
                miso_data_cnt_d <= (others => '0');
                    
                if spi_clk_event = '1' then
                    spi_nss_d   <= '1';
                    delay_cnt_d <= delay_cnt_q + 1;
                    
                    if delay_cnt_q = to_integer(unsigned(delay_duration_q(7 downto 1))) then
                        next_state      <= st_read;

                        miso_word_cnt_d <= miso_word_cnt_q + 1;
                        if miso_word_cnt_q = 2 - 1 then 
                            next_state <= st_eos;
                        end if;
                    end if;
                end if;            

            when st_eos             =>
                status_done_d   <= '1'; 
                next_state      <= st_idle;

            when others             => 
                status_done_d   <= '1'; 
                next_state      <= st_idle;

        end case;               
    end process;

    -----------------------------------------------------------------------------
    --                         SPI CLOCK GENERATOR
    -----------------------------------------------------------------------------

    spi_clk_p: process(CLK)
    begin
        if rising_edge(CLK) then
            spi_clk_event <= '0';
            if RST = '1' then
                spi_clk_cnt     <= (others => '0');
                spi_clk_event   <= '0';
                spi_clk_s       <= '1';
            elsif spi_clk_en = '1' then
                if spi_clk_cnt = ((spi_freq_div_q)*2) + 1 then
                    spi_clk_cnt     <= (others => '0');
                    spi_clk_event   <= '1';
                    spi_clk_s       <= not spi_clk_s;
                else
                    spi_clk_cnt <= spi_clk_cnt + 1;
                end if;
            else 
               spi_clk_cnt     <= (others => '0');
               spi_clk_event   <= '0';
               spi_clk_s       <= '1';
            end if;

            if state = st_write_delay or state = st_read_delay then 
                spi_clk_s       <= '1';
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                   1 ms PULSE GENERATOR (200 MHz CLK)
    -----------------------------------------------------------------------------
    
    ms_gen_i: process(CLK)
    begin
        if rising_edge(CLK) then
            pulse_event <= '0';
            if RST = '1' then
                pulse_event <= '0';
                pulse_cnt   <= (others => '0');
            elsif pulse_gen_en = '1' then 
                if pulse_cnt = 200000 - 1 then 

                    pulse_event <= '1';
                    pulse_cnt   <= (others => '0');
                else
                    pulse_cnt   <= pulse_cnt + 1;
                end if;
            else 
                pulse_event <= '0';
                pulse_cnt   <= (others => '0');
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                              SPI BUFFER 
    -----------------------------------------------------------------------------

    spi_buf_p: process(CLK)
    begin
        if rising_edge(CLK) then
            SPI_NSS        <= spi_nss_q;
            SPI_CLK        <= spi_clk_q;
            SPI_MOSI       <= spi_mosi_q;
            spi_miso_s     <= SPI_MISO;
        end if;
    end process;

    -----------------------------------------------------------------------------
    --                              REBOOT 
    -----------------------------------------------------------------------------

    boot_timeout_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (boot_cmd_q = '1') then
                boot_timeout <= boot_timeout + 1;
            else
                boot_timeout <= (others =>'0');
            end if;
        end if;
    end process;

end architecture;