-- adc_sim.vhd: Used for simulating the temp and volt IP cores used by sensor_interface for verification.
-- Copyright (C) 2019 CESNET
-- Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- This entity could be optimized to be less resource intensive, but since it
-- comforms to the Intel Stratix 10 ADC Specification (UG-S10ADC, 2019.05.17),
-- and is only used for verification, it isn't necessary.

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity ADC_SIM is
    Generic (
        IP_TYPE : string
    );
    Port (
        CLK               : in  std_logic;                     -- CLK
        RESET             : in  std_logic;                     -- RESET
        RSP_VALID         : out std_logic;                     -- valid
        RSP_DATA          : out std_logic_vector(31 downto 0); -- data
        RSP_CHANNEL       : out std_logic_vector(3 downto 0);  -- channel
        RSP_STARTOFPACKET : out std_logic;                     -- startofpacket
        RSP_ENDOFPACKET   : out std_logic;                     -- endofpacket
        CMD_VALID         : in  std_logic;                     -- valid
        CMD_READY         : out std_logic;                     -- ready
        CMD_DATA          : in  std_logic_vector(15 downto 0)  -- data
    );
end entity ADC_SIM;

architecture ARCH of ADC_SIM is

    -- =======================================================================
    -- HARDCODED VERIFICATION VALUES
    -- =======================================================================
    -- Temperatures are in the form x"00FF0---" where the index of the active bit
    -- indicates the temperature number minus 1. For example, value x"00FF0020" is
    -- for the 5th temperature. The values for voltages work the same way, but
    -- are in the form x"00FF----" to accomodate for more values.

    -- TEMPS
    signal temp0  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 0=>'1',  others=>'0');
    signal temp1  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 1=>'1',  others=>'0');
    signal temp2  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 2=>'1',  others=>'0');
    signal temp3  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 3=>'1',  others=>'0');
    signal temp4  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 4=>'1',  others=>'0');
    signal temp5  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 5=>'1',  others=>'0');
    signal temp6  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 6=>'1',  others=>'0');
    signal temp7  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 7=>'1',  others=>'0');
    signal temp8  : std_logic_vector(31 downto 0) := (31 downto 24=>'0', 23 downto 16=>'1', 8=>'1',  others=>'0');

    -- VOLTS
    signal volt0  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 0=>'1',  others=>'0');
    signal volt1  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 1=>'1',  others=>'0');
    signal volt2  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 2=>'1',  others=>'0');
    signal volt3  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 3=>'1',  others=>'0');
    signal volt4  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 4=>'1',  others=>'0');
    signal volt5  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 5=>'1',  others=>'0');
    signal volt6  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 6=>'1',  others=>'0');
    signal volt7  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 7=>'1',  others=>'0');
    signal volt8  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 8=>'1',  others=>'0');
    signal volt9  : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 9=>'1',  others=>'0');
    signal volt10 : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 10=>'1', others=>'0');
    signal volt11 : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 11=>'1', others=>'0');
    signal volt12 : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 12=>'1', others=>'0');
    signal volt13 : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 13=>'1', others=>'0');
    signal volt14 : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 14=>'1', others=>'0');
    signal volt15 : std_logic_vector(31 downto 0) := (31 downto 24=>'1', 23 downto 16=>'0', 15=>'1', others=>'0');

    -- =======================================================================
    -- INTERNAL SIGNALS
    -- =======================================================================
    -- Signal containing the cmd_data
    signal cmd_data_reg : std_logic_vector(15 downto 0);

    -- Signal used for differentiating volt and temp channel lengths
    signal channel_length : std_logic_vector(3 downto 0);

    -- Internal signals to access values in outputs
    signal cmd_rdy_internal_reg : std_logic;
    signal rsp_chn_internal_cnt : std_logic_vector(3 downto 0);
    signal rsp_vld_internal     : std_logic;

    -- Signals used to set SOP & EOP
    signal rsp_sop_reg : std_logic;
    signal rsp_eop     : std_logic;


    -- =======================================================================
    -- FUNCTIONS
    -- =======================================================================
    -- Function to find the highest active bit in a std_logic_vector
    function maxindex_f(signal vec : std_logic_vector) return integer is
        variable index : integer := 0;
    begin
        for i in 0 to vec'high loop
            if (vec(i)='1') then
                index := i;
            end if;
        end loop;
        return index;
    end function;

    -- Function to find the lowest active bit in a std_logic_vector
    function minindex_f(signal vec : std_logic_vector) return integer is
        variable index : integer := 0;
    begin
        while (vec(index) = '0' and index < vec'high) loop
            index := index+1;
        end loop;
        return index;
    end function;

begin

    -- =======================================================================
    -- GENERATING CONSTANTS
    -- =======================================================================
    constant_generate_temp_g: if (IP_TYPE = "TEMP") generate
        channel_length <= x"8";
    end generate;

    constant_generate_volt_g: if (IP_TYPE = "VOLT") generate
        channel_length <= x"F";
    end generate;

    -- =======================================================================
    -- ROUTING INTERNAL SIGNALS TO OUTPUTS
    -- =======================================================================
    CMD_READY         <= cmd_rdy_internal_reg;
    RSP_VALID         <= rsp_vld_internal;
    RSP_CHANNEL       <= rsp_chn_internal_cnt;
    RSP_STARTOFPACKET <= rsp_sop_reg;
    RSP_ENDOFPACKET   <= rsp_eop;

    -- =======================================================================
    -- COMMON LOGIC
    -- =======================================================================

    -- Set response valid if we aren't receiving commands and the current channel has been set to be read, otherwise keep this at '0'.
    rsp_vld_internal  <= '1' when (cmd_rdy_internal_reg='0' and CMD_VALID='0' and cmd_data_reg(to_integer(unsigned(rsp_chn_internal_cnt)))='1') else '0';

    -- Set EOP when we are at the last value that has been set for reading, and it is valid, otherwise keep this at '0'.
    rsp_eop <= '1' when (to_integer(unsigned(rsp_chn_internal_cnt)) = maxindex_f(cmd_data_reg)) else '0';

    -- Accepting commands
    cmd_rdy_internal_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            -- Prepare for receiving data.
            if (RESET='1') then
                cmd_rdy_internal_reg <= '1';
            else
                -- Once the data has been sent, stop receiving data.
                if (CMD_VALID='1') then
                    cmd_rdy_internal_reg <= '0';
                -- Once all the channels have been sampled, start receiving data again
                elsif (rsp_chn_internal_cnt = channel_length) then
                    cmd_rdy_internal_reg <= '1';
                end if;
            end if;
        end if;
    end process;

    -- Accepting command data
    cmd_data_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            -- If we are ready to receive and data is valid, save the data
            if (CMD_VALID='1' and cmd_rdy_internal_reg='1') then
                cmd_data_reg <= CMD_DATA;
            end if;
        end if;
    end process;

    -- Increment the response channel
    rsp_chn_internal_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            -- Start at the 0th channel...
            if (CMD_VALID='1' and cmd_rdy_internal_reg='1') then
                rsp_chn_internal_cnt <= (others => '0');
            -- ... and loop over all of them.
            elsif (rsp_chn_internal_cnt < channel_length) then
                rsp_chn_internal_cnt <= std_logic_vector(unsigned(rsp_chn_internal_cnt)+1);
            end if;
        end if;
    end process;

    -- Deciding where a new packet starts
    rsp_startofpacket_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET='1') then
                rsp_sop_reg <= '1';
            else
                -- If the data is valid, and we are the first active data values, set SOP to '0'.
                if (to_integer(unsigned(rsp_chn_internal_cnt)) = minindex_f(cmd_data_reg) and rsp_vld_internal='1') then
                    rsp_sop_reg <= '0';
                -- If the data is valid, and it is the last valid value, set SOP back to '1'.
                elsif (rsp_eop='1' and rsp_vld_internal='1') then
                    rsp_sop_reg <= '1';
                end if;
            end if;
        end if;
    end process;

    -- =======================================================================
    -- TEMPERATURE GENERATE
    -- =======================================================================
    temperature_g: if (IP_TYPE = "TEMP") generate
        with (rsp_chn_internal_cnt) select
            RSP_DATA <= temp0 when "0000",
                        temp1 when "0001",
                        temp2 when "0010",
                        temp3 when "0011",
                        temp4 when "0100",
                        temp5 when "0101",
                        temp6 when "0110",
                        temp7 when "0111",
                        temp8 when "1000",
                        (others => 'X') when others;
    end generate;

    -- =======================================================================
    -- VOLTAGE GENERATE
    -- =======================================================================
    voltage_g: if (IP_TYPE = "VOLT") generate
        with (rsp_chn_internal_cnt) select
            RSP_DATA <= volt0  when "0000",
                        volt1  when "0001",
                        volt2  when "0010",
                        volt3  when "0011",
                        volt4  when "0100",
                        volt5  when "0101",
                        volt6  when "0110",
                        volt7  when "0111",
                        volt8  when "1000",
                        volt9  when "1001",
                        volt10 when "1010",
                        volt11 when "1011",
                        volt12 when "1100",
                        volt13 when "1101",
                        volt14 when "1110",
                        volt15 when "1111",
                        (others => 'X') when others;
    end generate;

end architecture ARCH;
