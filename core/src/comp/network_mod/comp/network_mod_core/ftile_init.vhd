-- ftile_xcvr_init.vhd: F-Tile PMA initialization (set PMA mode) via the AVMM interface
-- For more details see:
--    * https://www.intel.com/content/www/us/en/docs/programmable/683872/22-4-4-3-0/fgt-attribute-access-method.html
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity ftile_xcvr_init is
generic (
    PHY_LANE : natural range 0 to 3 := 0  -- Physical lane index
);
port (
    RST              : in  std_logic;
    CLK              : in  std_logic;
    XCVR_RDY         : in  std_logic;
    -- Select ROM code to execute. 0 = set_medi_mode(0x14) code, 1 = ROM for set_medi_mode(0x10) code
    ROM_SEL          : in  std_logic_vector(0 downto 0) := "0";
    BUSY             : out std_logic;
    DONE             : out std_logic;
    -- AVMM
    ADDRESS          : out std_logic_vector(17 downto 0);
    READ             : out std_logic;
    WRITE            : out std_logic;
    READDATA         : in  std_logic_vector(31 downto 0);
    READDATA_VALID   : in  std_logic;
    WRITEDATA        : out std_logic_vector(31 downto 0);
    WAITREQUEST      : in  std_logic;
    --
    STATE            : out std_logic_vector(31 downto 0)  -- Debug & status
 );
end entity;

architecture full of ftile_xcvr_init is

    type t_avmm_state is (AVMM_INIT,
                          AVMM_WAIT,
                          AVMM_RBUSY,
                          AVMM_WBUSY,
                          AVMM_DONE
                         );
    signal avmm_state : t_avmm_state := AVMM_INIT;

    type t_init_fsm_state is (INIT,
                              START,
                              READ_CHECK,
                              ADDR_INC,
                              INIT_DONE
                             );
    signal init_fsm_state : t_init_fsm_state := INIT;

    constant LANE      : std_logic_vector(3 downto 0) := std_logic_vector(to_unsigned(PHY_LANE, 4));
    constant OP_READ   : std_logic_vector(0 downto 0) := "0";
    constant OP_WRITE  : std_logic_vector(0 downto 0) := "1";
    constant ROM_SIZE  : natural := 5;

    type t_config_rom is array(natural range <>) of std_logic_vector(1+20+32+16-1 downto 0);

    -- ROM0 contains code for setting the media mode to 0x14 (-LR,-SR mode)
    constant ftile_config_rom0 : t_config_rom(0 to ROM_SIZE-1) := (
     -- |   OP    |  Addr    |   Data                   |  Mask       1-5: cpi_request(data=0x14, option=0xA, opcode=0x64)
        OP_READ   & X"24011" &  X"0000000F"             &  X"FFFF", -- 1. cpi_stat = (drp_read(0x90044) & 0xffff) must not equal to 0xf
        OP_WRITE  & X"2400f" &  X"0014A" & LANE & X"64" &  X"0000", -- 2. val = (0x14 << 16)  + (0xA << 12) + (phy_lane << 8) + 0x64; write(0x9003c, val)
        OP_READ   & X"24010" &  X"00008000"             &  X"C000", -- 3. poll 0x90040 until bit 14 = 0 and bit 15 = 1
        OP_WRITE  & X"2400f" &  X"00142" & LANE & X"64" &  X"0000", -- 4. val = (0x14 << 16)  + (0x2 << 12) + (phy_lane << 8) + 0x64; write(0x9003c, val)
        OP_READ   & X"24010" &  X"00000000"             &  X"C000"  -- 5. poll 0x90040 until bit 14 = 0 and bit 15 = 0
    );

    -- ROM1 contains code for setting the media mode to 0x10 (-CR mode)
    constant ftile_config_rom1 : t_config_rom(0 to ROM_SIZE-1) := (
     -- |   OP    |  Addr    |   Data                   |  Mask       1-5: cpi_request(data=0x10, option=0xA, opcode=0x64)
        OP_READ   & X"24011" &  X"0000000F"             &  X"FFFF", -- 1. cpi_stat = (drp_read(0x90044) & 0xffff) must not equal to 0xf
        OP_WRITE  & X"2400f" &  X"0010A" & LANE & X"64" &  X"0000", -- 2. val = (0x10 << 16)  + (0xA << 12) + (phy_lane << 8) + 0x64; write(0x9003c, val)
        OP_READ   & X"24010" &  X"00008000"             &  X"C000", -- 3. poll 0x90040 until bit 14 = 0 and bit 15 = 1
        OP_WRITE  & X"2400f" &  X"00102" & LANE & X"64" &  X"0000", -- 4. val = (0x10 << 16)  + (0x2 << 12) + (phy_lane << 8) + 0x64; write(0x9003c, val)
        OP_READ   & X"24010" &  X"00000000"             &  X"C000"  -- 5. poll 0x90040 until bit 14 = 0 and bit 15 = 0
    );

    signal cfg_rom_out : std_logic_vector(ftile_config_rom0(0)'range);
    signal rom_cntr    : natural range 0 to ftile_config_rom0'high;

    alias rom_op   : std_logic_vector( 0 downto 0) is cfg_rom_out(1+20+32+16-1 downto 20+32+16); -- Operation type
    alias rom_addr : std_logic_vector(19 downto 0) is cfg_rom_out(  20+32+16-1 downto    32+16); -- Address in direct AVMM read/write operations
    alias rom_data : std_logic_vector(31 downto 0) is cfg_rom_out(     32+16-1 downto       16); -- Data to be written (in write transactions) or data to be compared to in reads
    alias rom_mask : std_logic_vector(15 downto 0) is cfg_rom_out(        16-1 downto        0); -- Mask for data comparison

    signal rst_sync        : std_logic;

    signal avmm_fsm_rd     : std_logic;
    signal avmm_fsm_wr     : std_logic;
    signal avmm_fsm_done   : std_logic;
    signal avmm_addr       : std_logic_vector(19 downto 0);
    signal avmm_dwr        : std_logic_vector(31 downto 0);
    signal avmm_drd        : std_logic_vector(31 downto 0);

begin

    rst_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true ,
        REPLICAS => 1
    )
    port map (
        CLK         => CLK,
        ASYNC_RST   => RST,
        OUT_RST(0)  => rst_sync
    );

    -- --------------------------------------------------------------------------
    -- AVMM read/write FSM
    -- --------------------------------------------------------------------------
    avmm_fsm: process(CLK)
    begin
        if rising_edge(CLK) then
            avmm_fsm_done <= '0';
            case avmm_state is

                when AVMM_INIT =>
                    READ      <= avmm_fsm_rd;
                    WRITE     <= avmm_fsm_wr;
                    ADDRESS   <= avmm_addr(ADDRESS'range);
                    WRITEDATA <= avmm_dwr;
                    if avmm_fsm_rd = '1' then
                        avmm_state <= AVMM_WAIT;
                    elsif avmm_fsm_wr = '1' then
                        avmm_state <= AVMM_WAIT;
                    end if;

                when AVMM_WAIT =>
                    if WAITREQUEST = '1' then
                        if avmm_fsm_rd = '1' then
                            avmm_state <= AVMM_RBUSY;
                        elsif avmm_fsm_wr = '1' then
                            avmm_state <= AVMM_WBUSY;
                        end if;
                    end if;

                when AVMM_RBUSY  =>
                    if WAITREQUEST = '0' then
                        READ          <= '0';
                        WRITE         <= '0';
                    end if;
                    if READDATA_VALID = '1' then
                        READ          <= '0';
                        WRITE         <= '0';
                        avmm_drd      <= READDATA;
                        avmm_state    <= AVMM_DONE;
                        avmm_fsm_done <= '1';
                    end if;

                when AVMM_WBUSY  =>
                    if WAITREQUEST = '0' then
                        READ          <= '0';
                        WRITE         <= '0';
                        avmm_state    <= AVMM_DONE;
                        avmm_fsm_done <= '1';
                    end if;

                when AVMM_DONE =>
                    avmm_state <= AVMM_INIT;
            end case;

            if rst_sync = '1' then
                avmm_state <= AVMM_INIT;
            end if;
        end if;
    end process;

    -- --------------------------------------------------------------------------
    -- Main FSM (Read config ROM and perform the sequence)
    -- --------------------------------------------------------------------------

    avmm_addr   <= rom_addr;
    avmm_dwr    <= rom_data;

    init_fsm: process(CLK)
    begin
        if rising_edge(CLK) then
            avmm_fsm_wr    <= '0';
            avmm_fsm_rd    <= '0';
            DONE            <= '0';

            case init_fsm_state is

                when INIT =>
                    rom_cntr       <= 0;
                    avmm_fsm_wr    <= '0';
                    avmm_fsm_rd    <= '0';
                    BUSY           <= '0';
                    if XCVR_RDY = '1' then
                        init_fsm_state  <= START;
                    end if;

                when START =>
                    BUSY  <= '1';
                    if (rom_op = OP_WRITE) then
                        avmm_fsm_wr <= '1';
                        if avmm_fsm_done = '1' then
                            init_fsm_state <= ADDR_INC;
                            avmm_fsm_wr <= '0';
                        end if;
                    else
                        avmm_fsm_rd <= '1';
                        if avmm_fsm_done = '1' then
                            init_fsm_state <= READ_CHECK;
                            avmm_fsm_rd <= '0';
                        end if;
                    end if;

                when READ_CHECK =>
                    -- Check if masked data read from AVMM are as defined in ROM
                    if ((avmm_drd(rom_mask'range) and rom_mask) = rom_data(rom_mask'range)) then
                        init_fsm_state <= ADDR_INC;
                    else
                        init_fsm_state <= START;  -- Retry the read operation
                    end if;

                when ADDR_INC =>
                    if rom_cntr = ROM_SIZE-1 then -- Last address in ROM - all done
                        init_fsm_state <= INIT_DONE;
                        BUSY  <= '0';
                        DONE  <= '1';
                    else
                        rom_cntr       <= rom_cntr + 1;
                        init_fsm_state <= START;
                    end if;

                when INIT_DONE =>
                    BUSY  <= '0';

            end case;

            if rst_sync = '1' then
                rom_cntr        <= 0;
                init_fsm_state  <= INIT;
            end if;

        end if;
    end process;

    cfg_rom_out <= ftile_config_rom0(rom_cntr) when ROM_SEL = "0" else
                   ftile_config_rom1(rom_cntr);

    -- --------------------------------------------------------------------------
    -- Debug and status
    -- --------------------------------------------------------------------------
    STATE(3 downto 0) <= "0000" when init_fsm_state = INIT        else
                         "0001" when init_fsm_state = START       else --
                         "0010" when init_fsm_state = READ_CHECK  else
                         "0100" when init_fsm_state = ADDR_INC    else
                         "1111"; -- INIT_DONE

    STATE(7 downto 4) <= "0000";

    STATE(11 downto 8) <= "0000" when avmm_state = AVMM_INIT       else
                          "0001" when avmm_state = AVMM_WAIT       else
                          "0010" when avmm_state = AVMM_RBUSY      else --
                          "0011" when avmm_state = AVMM_WBUSY      else --
                          "1111"; -- AVMM_DONE

    STATE(15 downto 12) <= std_logic_vector(to_unsigned(rom_cntr, 4));
    STATE(31 downto 16) <= X"0000";

end architecture;
