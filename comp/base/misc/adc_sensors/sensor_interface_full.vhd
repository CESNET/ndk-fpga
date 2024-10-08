-- sensor_interface.vhd: An interface to the ADC IP Temperature and Voltage Cores for Stratix 10
-- Copyright (C) 2019 CESNET
-- Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- Sources
-- https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-adc.pdf
-- https://www.liberouter.org/wiki/index.php/Byte_Enable
-- https://www.liberouter.org/wiki/index.php/Endpoint_komponenta_Lok%C3%A1ln%C3%AD_sb%C4%9Brnice

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture ARCH of SENSOR_INTERFACE is

    -- =======================================================================
    -- CONTROL SIGNALS
    -- =======================================================================

    -- Bitmask showing the channels that should be measured for T and V.
    -- Bits 31 downto 16 are for volts, bits 8 downto 0 are for temps.
    signal conf_reg    : std_logic_vector(31 downto 0);
    -- Chip select
    signal conf_reg_cs : std_logic;
    -- Write enable
    signal conf_reg_we : std_logic;

    -- Signal used to initiate the request for new ADC readout. Bit 16
    -- controls the volt reading, bit 0 controls the temp reading.
    -- Others are unused.
    signal ctrl_reg    : std_logic_vector(31 downto 0);
    -- Chip select
    signal ctrl_reg_cs : std_logic;
    -- Write enable
    signal ctrl_reg_we : std_logic;

    -- This signal is used to keep track of data values that have been
    -- written to memory but not read yet. It has the same bit layout as conf_reg.
    signal stat_reg    : std_logic_vector(31 downto 0);

    -- Used to select which signal should be sent to DRD.
    signal mx_drd  : std_logic_vector(31 downto 0);

    -- =======================================================================
    -- SENSOR INTERFACE SIGNALS
    --
    -- TEMP INPUT
    -- =======================================================================

    signal temp_cmd_ready    : std_logic;
    signal temp_cmd_valid    : std_logic;
    signal temp_cmd_data : std_logic_vector(8 downto 0);
    -- =======================================================================
    -- SENSOR INTERFACE SIGNALS
    --
    -- TEMP OUTPUT
    -- =======================================================================

    signal temp_rsp_valid    : std_logic;
    signal temp_rsp_channel  : std_logic_vector(3 downto 0);
    signal temp_rsp_data     : std_logic_vector(31 downto 0);
    signal temp_rsp_sop      : std_logic;
    signal temp_rsp_eop      : std_logic;

    -- =======================================================================
    -- SENSOR INTERFACE SIGNALS
    --
    -- VOLT INPUT
    -- =======================================================================

    signal volt_cmd_ready    : std_logic;
    signal volt_cmd_valid    : std_logic;
    signal volt_cmd_data : std_logic_vector(15 downto 0);

    -- =======================================================================
    -- SENSOR INTERFACE SIGNALS
    --
    -- VOLT OUTPUT
    -- =======================================================================

    signal volt_rsp_valid    : std_logic;
    signal volt_rsp_channel  : std_logic_vector(3 downto 0);
    signal volt_rsp_data     : std_logic_vector(31 downto 0);
    signal volt_rsp_sop      : std_logic;
    signal volt_rsp_eop      : std_logic;

    -- =======================================================================
    -- MEMORY SIGNALS
    --
    -- Temp memory signals
    -- =======================================================================

    signal temp0_reg  : std_logic_vector(31 downto 0);
    signal temp1_reg  : std_logic_vector(31 downto 0);
    signal temp2_reg  : std_logic_vector(31 downto 0);
    signal temp3_reg  : std_logic_vector(31 downto 0);
    signal temp4_reg  : std_logic_vector(31 downto 0);
    signal temp5_reg  : std_logic_vector(31 downto 0);
    signal temp6_reg  : std_logic_vector(31 downto 0);
    signal temp7_reg  : std_logic_vector(31 downto 0);
    signal temp8_reg  : std_logic_vector(31 downto 0);

    -- =======================================================================
    -- MEMORY SIGNALS
    --
    -- Volt memory signals
    -- =======================================================================

    signal volt0_reg  : std_logic_vector(31 downto 0);
    signal volt1_reg  : std_logic_vector(31 downto 0);
    signal volt2_reg  : std_logic_vector(31 downto 0);
    signal volt3_reg  : std_logic_vector(31 downto 0);
    signal volt4_reg  : std_logic_vector(31 downto 0);
    signal volt5_reg  : std_logic_vector(31 downto 0);
    signal volt6_reg  : std_logic_vector(31 downto 0);
    signal volt7_reg  : std_logic_vector(31 downto 0);
    signal volt8_reg  : std_logic_vector(31 downto 0);
    signal volt9_reg  : std_logic_vector(31 downto 0);
    signal volt10_reg : std_logic_vector(31 downto 0);
    signal volt11_reg : std_logic_vector(31 downto 0);
    signal volt12_reg : std_logic_vector(31 downto 0);
    signal volt13_reg : std_logic_vector(31 downto 0);
    signal volt14_reg : std_logic_vector(31 downto 0);
    signal volt15_reg : std_logic_vector(31 downto 0);

    -- =======================================================================
    -- COMPONENT DECLARATION
    -- =======================================================================
    -- NOTE: Declaration and instantiation is separate for these IP Cores
    --       as this is code directly generated by Quartus Prime 18.1.0.
    --       They don't comform with the internal coding style for the same reason.
    component TEMP is
        Port (
            clk               : in  std_logic;                     -- clk
            reset             : in  std_logic;                     -- reset
            rsp_valid         : out std_logic;                     -- valid
            rsp_data          : out std_logic_vector(31 downto 0); -- data
            rsp_channel       : out std_logic_vector(3 downto 0);  -- channel
            rsp_startofpacket : out std_logic;                     -- startofpacket
            rsp_endofpacket   : out std_logic;                     -- endofpacket
            cmd_valid         : in  std_logic;                     -- valid
            cmd_ready         : out std_logic;                     -- ready
            cmd_data          : in  std_logic_vector(8 downto 0)   -- data
        );
    end component TEMP;

    component VOLT is
        Port (
            clk               : in  std_logic;                     -- clk
            reset             : in  std_logic;                     -- reset
            rsp_valid         : out std_logic;                     -- valid
            rsp_data          : out std_logic_vector(31 downto 0); -- data
            rsp_channel       : out std_logic_vector(3 downto 0);  -- channel
            rsp_startofpacket : out std_logic;                     -- startofpacket
            rsp_endofpacket   : out std_logic;                     -- endofpacket
            cmd_valid         : in  std_logic;                     -- valid
            cmd_ready         : out std_logic;                     -- ready
            cmd_data          : in  std_logic_vector(15 downto 0)  -- data
        );
    end component VOLT;

    -- =======================================================================
    -- write32_f FUNCTION
    --
    -- Used to write to a 32-bit register with byte enables
    -- =======================================================================

                       -- current value of the register
    function write32_f(reg : in std_logic_vector(31 downto 0);
                       -- new value of the register
                       val : in std_logic_vector(31 downto 0);
                       -- byte enables
                       be  : in std_logic_vector( 3 downto 0))
    return std_logic_vector is
    variable result : std_logic_vector(31 downto 0) := reg;
    begin
        for i in 0 to be'high  loop
            if be(i) = '1' then
                result((8*i+7) downto i*8) := val((8*i+7) downto i*8);
            end if;
        end loop;
        return result;
    end;

begin

    -- =======================================================================
    -- IP CORES USED FOR VERIFICATION
    -- =======================================================================
    veri_ip_cores_g: if (VERI = true) generate
        temp_ip_i : entity work.ADC_SIM(ARCH)
            Generic map (
                IP_TYPE => "TEMP" -- "TEMP", "VOLT"
            )
            Port map (
                CLK               => CLK,
                RESET             => RESET,
                RSP_VALID         => temp_rsp_valid,
                RSP_DATA          => temp_rsp_data,
                RSP_CHANNEL       => temp_rsp_channel,
                RSP_STARTOFPACKET => temp_rsp_sop,
                RSP_ENDOFPACKET   => temp_rsp_eop,
                CMD_VALID         => temp_cmd_valid,
                CMD_READY         => temp_cmd_ready,
                CMD_DATA          => (15 downto 9 =>'0') & temp_cmd_data
            );

        volt_ip_i : entity work.ADC_SIM(ARCH)
            Generic map (
                IP_TYPE => "VOLT" -- "TEMP", "VOLT"
            )
            Port map (
                CLK               => CLK,
                RESET             => RESET,
                RSP_VALID         => volt_rsp_valid,
                RSP_DATA          => volt_rsp_data,
                RSP_CHANNEL       => volt_rsp_channel,
                RSP_STARTOFPACKET => volt_rsp_sop,
                RSP_ENDOFPACKET   => volt_rsp_eop,
                CMD_VALID         => volt_cmd_valid,
                CMD_READY         => volt_cmd_ready,
                CMD_DATA          => volt_cmd_data
            );
    end generate;

    -- =======================================================================
    -- IP CORES USED IN PRODUCTION
    -- =======================================================================
    -- These don't comform to the coding style for the same reason as
    -- their component declaration.
    prod_ip_cores_g: if (VERI = false) generate
        temp_ip_i : component TEMP
            port map (
                clk               => CLK,
                reset             => RESET,
                rsp_valid         => temp_rsp_valid,
                rsp_data          => temp_rsp_data,
                rsp_channel       => temp_rsp_channel,
                rsp_startofpacket => temp_rsp_sop,
                rsp_endofpacket   => temp_rsp_eop,
                cmd_valid         => temp_cmd_valid,
                cmd_ready         => temp_cmd_ready,
                cmd_data          => temp_cmd_data
            );

        volt_ip_i : component VOLT
            port map (
                clk               => CLK,
                reset             => RESET,
                rsp_valid         => volt_rsp_valid,
                rsp_data          => volt_rsp_data,
                rsp_channel       => volt_rsp_channel,
                rsp_startofpacket => volt_rsp_sop,
                rsp_endofpacket   => volt_rsp_eop,
                cmd_valid         => volt_cmd_valid,
                cmd_ready         => volt_cmd_ready,
                cmd_data          => volt_cmd_data
            );
    end generate;

    -- =======================================================================
    -- ARDY
    -- =======================================================================
    ARDY <= RD or WR;

    -- =======================================================================
    -- MI32 WRITE LOGIC
    -- =======================================================================
    -- Chip select
    conf_reg_cs <= '1' when (ADDR(7 downto 0) = x"00") else '0';
    ctrl_reg_cs <= '1' when (ADDR(7 downto 0) = x"04") else '0';
    -- Write enable
    conf_reg_we <= conf_reg_cs and WR;
    ctrl_reg_we <= ctrl_reg_cs and WR;

    -- =======================================================================
    -- MI32 READ LOGIC
    -- =======================================================================
    -- Register for setting DRDY.
    data_ready_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET='1') then
                DRDY <= '0';
            else
                DRDY <= RD;
            end if;
        end if;
    end process;

    -- Register for setting DRD.
    data_read_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            DRD <= mx_drd;
        end if;
    end process;

    -- MX for setting the data that should be sent to DRD.
    with ADDR(7 downto 0) select
        mx_drd <= conf_reg   when x"00",
                  ctrl_reg   when x"04",
                  stat_reg   when x"08",
                  temp0_reg  when x"10",
                  temp1_reg  when x"14",
                  temp2_reg  when x"18",
                  temp3_reg  when x"1C",
                  temp4_reg  when x"20",
                  temp5_reg  when x"24",
                  temp6_reg  when x"28",
                  temp7_reg  when x"2C",
                  temp8_reg  when x"30",
                  volt0_reg  when x"40",
                  volt1_reg  when x"44",
                  volt2_reg  when x"48",
                  volt3_reg  when x"4C",
                  volt4_reg  when x"50",
                  volt5_reg  when x"54",
                  volt6_reg  when x"58",
                  volt7_reg  when x"5C",
                  volt8_reg  when x"60",
                  volt9_reg  when x"64",
                  volt10_reg when x"68",
                  volt11_reg when x"6C",
                  volt12_reg when x"70",
                  volt13_reg when x"74",
                  volt14_reg when x"78",
                  volt15_reg when x"7C",
                  x"DEADBEEF" when others;

    -- =======================================================================
    --  GENERAL REGISTERS
    -- =======================================================================
    -- This register is used for writing to the conf_reg signal.
    conf_reg_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET='1') then
                conf_reg <= (others => '0');
            elsif (conf_reg_we='1') then
                conf_reg <= write32_f(conf_reg, DWR, BE);
            end if;
        end if;
    end process;

    -- This register is used for resetting the control bit once
    -- the IP core received the request to read data.
    ctrl_reg_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET='1') then
                ctrl_reg <= (others => '0');
            end if;
            if (ctrl_reg_we='1') then
                ctrl_reg <= write32_f(ctrl_reg, DWR, BE);
            end if;
            if (temp_cmd_ready='1' and ctrl_reg(0)='1') then
                ctrl_reg(0) <= '0';
            end if;
            if (volt_cmd_ready='1' and ctrl_reg(16)='1') then
                ctrl_reg(16) <= '0';
            end if;
        end if;
    end process;

    -- This register is used for setting the bits of stat_reg signal.
    -- An active bit means that the value of that temperature has been
    -- written but not read yet. A zero means it has been read,
    -- or not written at all.
    stat_reg_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET='1') then
                stat_reg <= (others => '0');
            else
                if (RD='1') then
                    case (ADDR(7 downto 0)) is
                        when x"10" => stat_reg(0)  <= '0';
                        when x"14" => stat_reg(1)  <= '0';
                        when x"18" => stat_reg(2)  <= '0';
                        when x"1C" => stat_reg(3)  <= '0';
                        when x"20" => stat_reg(4)  <= '0';
                        when x"24" => stat_reg(5)  <= '0';
                        when x"28" => stat_reg(6)  <= '0';
                        when x"2C" => stat_reg(7)  <= '0';
                        when x"30" => stat_reg(8)  <= '0';
                        when x"40" => stat_reg(16) <= '0';
                        when x"44" => stat_reg(17) <= '0';
                        when x"48" => stat_reg(18) <= '0';
                        when x"4C" => stat_reg(19) <= '0';
                        when x"50" => stat_reg(20) <= '0';
                        when x"54" => stat_reg(21) <= '0';
                        when x"58" => stat_reg(22) <= '0';
                        when x"5C" => stat_reg(23) <= '0';
                        when x"60" => stat_reg(24) <= '0';
                        when x"64" => stat_reg(25) <= '0';
                        when x"68" => stat_reg(26) <= '0';
                        when x"6C" => stat_reg(27) <= '0';
                        when x"70" => stat_reg(28) <= '0';
                        when x"74" => stat_reg(29) <= '0';
                        when x"78" => stat_reg(30) <= '0';
                        when x"7C" => stat_reg(31) <= '0';
                        when others => null;
                    end case;
                end if;
                if (temp_rsp_valid='1') then
                    case (temp_rsp_channel) is
                        when x"0" => stat_reg(0) <= '1';
                        when x"1" => stat_reg(1) <= '1';
                        when x"2" => stat_reg(2) <= '1';
                        when x"3" => stat_reg(3) <= '1';
                        when x"4" => stat_reg(4) <= '1';
                        when x"5" => stat_reg(5) <= '1';
                        when x"6" => stat_reg(6) <= '1';
                        when x"7" => stat_reg(7) <= '1';
                        when x"8" => stat_reg(8) <= '1';
                        when others => null;
                    end case;
                end if;
                if (volt_rsp_valid='1') then
                    case (volt_rsp_channel) is
                        when x"0" => stat_reg(16) <= '1';
                        when x"1" => stat_reg(17) <= '1';
                        when x"2" => stat_reg(18) <= '1';
                        when x"3" => stat_reg(19) <= '1';
                        when x"4" => stat_reg(20) <= '1';
                        when x"5" => stat_reg(21) <= '1';
                        when x"6" => stat_reg(22) <= '1';
                        when x"7" => stat_reg(23) <= '1';
                        when x"8" => stat_reg(24) <= '1';
                        when x"9" => stat_reg(25) <= '1';
                        when x"A" => stat_reg(26) <= '1';
                        when x"B" => stat_reg(27) <= '1';
                        when x"C" => stat_reg(28) <= '1';
                        when x"D" => stat_reg(29) <= '1';
                        when x"E" => stat_reg(30) <= '1';
                        when x"F" => stat_reg(31) <= '1';
                        when others => null;
                    end case;
                end if;
            end if;
        end if;
    end process;

    -- =======================================================================
    -- TEMP SENDING LOGIC
    -- =======================================================================
    temp_cmd_data  <= conf_reg(8 downto 0);
    temp_cmd_valid <= temp_cmd_ready and ctrl_reg(0);

    -- =======================================================================
    --  TEMPERATURE SPECIFIC REGISTERS
    -- =======================================================================
    -- This generate is used for verification, so that values for temperatures are
    -- reset between tests, and the entity can be verified correctly.
    veri_temp_g: if (VERI) generate
        -- This process is used setting the temperature register values
        -- once the data is received from the IP core.
        temp_readout_p: process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET='1') then
                    temp0_reg <= (others => '0');
                    temp1_reg <= (others => '0');
                    temp2_reg <= (others => '0');
                    temp3_reg <= (others => '0');
                    temp4_reg <= (others => '0');
                    temp5_reg <= (others => '0');
                    temp6_reg <= (others => '0');
                    temp7_reg <= (others => '0');
                    temp8_reg <= (others => '0');
                elsif (temp_rsp_valid='1') then
                    case (temp_rsp_channel) is
                        when x"0" => temp0_reg <= temp_rsp_data;
                        when x"1" => temp1_reg <= temp_rsp_data;
                        when x"2" => temp2_reg <= temp_rsp_data;
                        when x"3" => temp3_reg <= temp_rsp_data;
                        when x"4" => temp4_reg <= temp_rsp_data;
                        when x"5" => temp5_reg <= temp_rsp_data;
                        when x"6" => temp6_reg <= temp_rsp_data;
                        when x"7" => temp7_reg <= temp_rsp_data;
                        when x"8" => temp8_reg <= temp_rsp_data;
                        when others => null;
                    end case;
                end if;
            end if;
        end process;
    end generate;

    -- This generate is used in production as resetting data values is not necessary.
    prod_temp_g: if (VERI = false) generate
        -- Same as temp_readout_p inside veri_temp_g
        temp_readout_p: process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (temp_rsp_valid='1') then
                    case (temp_rsp_channel) is
                        when x"0" => temp0_reg <= temp_rsp_data;
                        when x"1" => temp1_reg <= temp_rsp_data;
                        when x"2" => temp2_reg <= temp_rsp_data;
                        when x"3" => temp3_reg <= temp_rsp_data;
                        when x"4" => temp4_reg <= temp_rsp_data;
                        when x"5" => temp5_reg <= temp_rsp_data;
                        when x"6" => temp6_reg <= temp_rsp_data;
                        when x"7" => temp7_reg <= temp_rsp_data;
                        when x"8" => temp8_reg <= temp_rsp_data;
                        when others => null;
                    end case;
                end if;
            end if;
        end process;
    end generate;

    -- =======================================================================
    -- VOLT SENDING LOGIC
    -- =======================================================================
    volt_cmd_data  <= conf_reg(31 downto 16);
    volt_cmd_valid <= volt_cmd_ready and ctrl_reg(16);

    -- =======================================================================
    --  VOLTAGE SPECIFIC REGISTERS
    -- =======================================================================
    -- This generate is used for verification, so that values for voltages are
    -- reset between tests, and the entity can be verified correctly.
    veri_volt_g: if (VERI) generate
        -- This process is used setting the voltage register values
        -- once the data is received from the IP core.
        volt_readout_p: process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET='1') then
                    volt0_reg  <= (others => '0');
                    volt1_reg  <= (others => '0');
                    volt2_reg  <= (others => '0');
                    volt3_reg  <= (others => '0');
                    volt4_reg  <= (others => '0');
                    volt5_reg  <= (others => '0');
                    volt6_reg  <= (others => '0');
                    volt7_reg  <= (others => '0');
                    volt8_reg  <= (others => '0');
                    volt9_reg  <= (others => '0');
                    volt10_reg <= (others => '0');
                    volt11_reg <= (others => '0');
                    volt12_reg <= (others => '0');
                    volt13_reg <= (others => '0');
                    volt14_reg <= (others => '0');
                    volt15_reg <= (others => '0');
                elsif (volt_rsp_valid='1') then
                    case (volt_rsp_channel) is
                        when x"0" => volt0_reg  <= volt_rsp_data;
                        when x"1" => volt1_reg  <= volt_rsp_data;
                        when x"2" => volt2_reg  <= volt_rsp_data;
                        when x"3" => volt3_reg  <= volt_rsp_data;
                        when x"4" => volt4_reg  <= volt_rsp_data;
                        when x"5" => volt5_reg  <= volt_rsp_data;
                        when x"6" => volt6_reg  <= volt_rsp_data;
                        when x"7" => volt7_reg  <= volt_rsp_data;
                        when x"8" => volt8_reg  <= volt_rsp_data;
                        when x"9" => volt9_reg  <= volt_rsp_data;
                        when x"A" => volt10_reg <= volt_rsp_data;
                        when x"B" => volt11_reg <= volt_rsp_data;
                        when x"C" => volt12_reg <= volt_rsp_data;
                        when x"D" => volt13_reg <= volt_rsp_data;
                        when x"E" => volt14_reg <= volt_rsp_data;
                        when x"F" => volt15_reg <= volt_rsp_data;
                        when others => null;
                    end case;
                end if;
            end if;
        end process;
    end generate;

    -- This generate is used in production as resetting data values is not necessary.
    prod_volt_g: if (VERI = false) generate
        -- Same as volt_readout_p inside veri_volt_g
        volt_readout_p: process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (volt_rsp_valid='1') then
                    case (volt_rsp_channel) is
                        when x"0" => volt0_reg  <= volt_rsp_data;
                        when x"1" => volt1_reg  <= volt_rsp_data;
                        when x"2" => volt2_reg  <= volt_rsp_data;
                        when x"3" => volt3_reg  <= volt_rsp_data;
                        when x"4" => volt4_reg  <= volt_rsp_data;
                        when x"5" => volt5_reg  <= volt_rsp_data;
                        when x"6" => volt6_reg  <= volt_rsp_data;
                        when x"7" => volt7_reg  <= volt_rsp_data;
                        when x"8" => volt8_reg  <= volt_rsp_data;
                        when x"9" => volt9_reg  <= volt_rsp_data;
                        when x"A" => volt10_reg <= volt_rsp_data;
                        when x"B" => volt11_reg <= volt_rsp_data;
                        when x"C" => volt12_reg <= volt_rsp_data;
                        when x"D" => volt13_reg <= volt_rsp_data;
                        when x"E" => volt14_reg <= volt_rsp_data;
                        when x"F" => volt15_reg <= volt_rsp_data;
                        when others => null;
                    end case;
                end if;
            end if;
        end process;
    end generate;

end architecture;
