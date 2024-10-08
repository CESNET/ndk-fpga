-- etile_xcvr_init.vhd: E-Tile PMA initialization (RX Adaptation) via the AVMM interface
-- For more details see:
--    * https://www.intel.com/content/www/us/en/docs/programmable/683723/current/pma-bring-up-flow.html
--    * https://www.intel.com/content/www/us/en/docs/programmable/683723/current/reconfiguring-the-duplex-pma-using-the.html
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity etile_xcvr_init is
port (
    RST              : in  std_logic;
    CLK              : in  std_logic;
    XCVR_RDY         : in  std_logic;
    BUSY             : out std_logic;
    DONE             : out std_logic;
    -- AVMM
    ADDRESS          : out std_logic_vector(18 downto 0);
    READ             : out std_logic;
    WRITE            : out std_logic;
    READDATA         : in  std_logic_vector(31 downto 0);
    WRITEDATA        : out std_logic_vector(31 downto 0);
    WAITREQUEST      : in  std_logic;
    --
    STATE            : out std_logic_vector(31 downto 0)  -- Debug & status
 );
end entity;

architecture full of etile_xcvr_init is

    type t_avst_state is (AVMM_INIT,
                          AVMM_WAIT,
                          AVMM_BUSY,
                          AVMM_DONE
                         );
    signal avst_state : t_avst_state := AVMM_INIT;

    type t_attr_state is (ATTR_INIT,
                          ATTR_CLR_STAT,
                          ATTR_CODE_WR0,
                          ATTR_CODE_WR1,
                          ATTR_VAL_WR0,
                          ATTR_VAL_WR1,
                          ATTR_OP_START,
                          ATTR_BUSY_CHECK,
                          ATTR_WAIT,
                          ATTR_READ0,
                          ATTR_READ1,
                          ATTR_DONE
                         );
    signal attr_state : t_attr_state := ATTR_INIT;

    type t_init_fsm_state is (INIT,
                              START,
                              READ_CHECK,
                              AREAD_CHECK,
                              ADDR_INC,
                              INIT_DONE
                             );
    signal init_fsm_state : t_init_fsm_state := INIT;

    constant OP_READ   : std_logic_vector(1 downto 0) := "00";
    constant OP_WRITE  : std_logic_vector(1 downto 0) := "01";
    constant OP_AREAD  : std_logic_vector(1 downto 0) := "10";
    constant OP_AWRITE : std_logic_vector(1 downto 0) := "11";

    type t_config_rom is array(natural range <>) of std_logic_vector(2+32+16+16-1 downto 0);
    constant etile_config_rom : t_config_rom(0 to 11) := (
     -- |   OP    | Addr/val+code |   Data    |  Mask
        std_logic_vector'(OP_WRITE  & X"000400E2"   &  X"0055"  &  X"0000"), -- 1. Activate reset: write(0x400E2, 0x0f)
        std_logic_vector'(OP_AWRITE & X"03250002"   &  X"0000"  &  X"0000"), -- 2. PRBS generator on: attrib(0x0325,0x0002)
        std_logic_vector'(OP_AWRITE & X"01010008"   &  X"0000"  &  X"0000"), -- 3. Change to internal serial loopback mode: attrib(0x0101, 0x0008)
        std_logic_vector'(OP_AWRITE & X"0001000a"   &  X"0000"  &  X"0000"), -- 4. Enable initial coarse adaptive equalization: attrib(0x0001, 0x000a)
        std_logic_vector'(OP_AREAD  & X"0b000126"   &  X"0000"  &  X"0001"), -- 5. Read initial coarse adaptation status: val = attrib(0x0b00, 0x0126). Repeat current step until val[0] = 0 to indicate that initial coarse adaptation has completed.
        std_logic_vector'(OP_AWRITE & X"01000008"   &  X"0000"  &  X"0000"), -- 6. Disable Internal Serial Loopback: attrib(0x0100, 0x0008)
        std_logic_vector'(OP_AWRITE & X"0001000a"   &  X"0000"  &  X"0000"), -- 7. Perform initial adaptation: attrib(0x0001, 0x000A)
        std_logic_vector'(OP_AREAD  & X"0b000126"   &  X"0080"  &  X"00FF"), -- 8. Read adaptation status: val=0; while (val & 0x00ff) != 0x80: val = attrib(0x0b00, 0x0126)
        std_logic_vector'(OP_WRITE  & X"000400E2"   &  X"0000"  &  X"0000"), -- 9. Deassert tx_reset/rx_reset: write(0x400E2, 0x0)
        std_logic_vector'(OP_AREAD  & X"03ff0002"   &  X"0002"  &  X"00FF"), -- 10. PRBS generator off: ret = 0 while (ret & 0x00ff) != 0x02: ret = attrib(0x3ff, 0x0002)
        std_logic_vector'(OP_AWRITE & X"0006000a"   &  X"0000"  &  X"0000"), -- 11. Enable continuous adaptive equalization: attrib(0x0006, 0x000A);
        std_logic_vector'(OP_AREAD  & X"0b000126"   &  X"00E2"  &  X"00FF")  -- 12. Read initial coarse adaptation status: val = 0 while (val & 0x00ff) != 0xE2: val = attrib(0x0b00, 0x0126)
    );

    signal cfg_rom_out : std_logic_vector(etile_config_rom(0)'range);
    signal rom_cntr    : natural range 0 to etile_config_rom'high;

    alias rom_op   : std_logic_vector( 1 downto 0) is cfg_rom_out(2+32+16+16-1 downto 32+16+16); -- Operation type
    alias rom_val  : std_logic_vector(15 downto 0) is cfg_rom_out(  32+16+16-1 downto 16+16+16); -- "Value" in attribute operations
    alias rom_code : std_logic_vector(15 downto 0) is cfg_rom_out(  16+16+16-1 downto    16+16); -- "Code" in attribute operations
    alias rom_addr : std_logic_vector(19 downto 0) is cfg_rom_out(  20+16+16-1 downto    16+16); -- Address in direct AVMM read/write operations
    alias rom_data : std_logic_vector(15 downto 0) is cfg_rom_out(     16+16-1 downto       16); -- Data to be written (in write transactions) or data to be compared to in reads
    alias rom_mask : std_logic_vector(15 downto 0) is cfg_rom_out(        16-1 downto        0); -- Mask for data comparison

    signal rst_sync        : std_logic;

    signal avst_fsm_rd     : std_logic;
    signal avst_fsm_wr     : std_logic;
    signal avst_fsm_done   : std_logic;
    signal avst_addr       : std_logic_vector(19 downto 0);
    signal avst_dwr        : std_logic_vector(15 downto 0);
    signal avst_drd        : std_logic_vector(31 downto 0);

    signal attr_avst_start : std_logic;
    signal attr_avst_wr    : std_logic;
    signal attr_avst_rd    : std_logic;
    signal attr_avst_done  : std_logic;
    signal attr_avst_addr  : std_logic_vector(avst_addr'range);
    signal attr_avst_dwr   : std_logic_vector(15 downto 0);
    signal attr_avst_drd   : std_logic_vector(15 downto 0);
    signal init_avst_wr    : std_logic;
    signal init_avst_rd    : std_logic;

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
    avst_fsm: process(CLK)
    begin
        if rising_edge(CLK) then
            avst_fsm_done <= '0';
            case avst_state is

                when AVMM_INIT =>
                    READ      <= avst_fsm_rd;
                    WRITE     <= avst_fsm_wr;
                    ADDRESS   <= avst_addr(ADDRESS'range);
                    WRITEDATA <= X"0000" & avst_dwr;
                    if avst_fsm_rd = '1' then
                        avst_state <= AVMM_WAIT;
                    elsif avst_fsm_wr = '1' then
                        avst_state <= AVMM_BUSY;
                    end if;

                when AVMM_WAIT =>
                    if WAITREQUEST = '1' then
                        avst_state <= AVMM_BUSY;
                    end if;

                when AVMM_BUSY  =>
                    if WAITREQUEST = '0' then
                        READ          <= '0';
                        WRITE         <= '0';
                        avst_drd      <= READDATA;
                        avst_state    <= AVMM_DONE;
                        avst_fsm_done <= '1';
                    end if;

                when AVMM_DONE =>
                    avst_state <= AVMM_INIT;
            end case;

            if rst_sync = '1' then
                avst_state <= AVMM_INIT;
            end if;
        end if;
    end process;

    avst_fsm_wr <= attr_avst_wr or init_avst_wr;
    avst_fsm_rd <= attr_avst_rd or init_avst_rd;
    avst_addr   <= rom_addr when rom_op(1) = '0' else attr_avst_addr;
    avst_dwr    <= rom_data when rom_op(1) = '0' else attr_avst_dwr;

    -- --------------------------------------------------------------------------
    -- XCVR attribute read/write FSM (read/write attribute code and data)
    -- --------------------------------------------------------------------------
    attr_ctrl_fsm: process(CLK)
    begin
        -- See https://www.intel.com/content/www/us/en/docs/programmable/683723/current/pma-attribute-codes.html
        -- see https://www.intel.com/content/www/us/en/docs/programmable/683723/current/reconfiguring-the-duplex-pma-using-the.html
        if rising_edge(CLK) then
            attr_avst_rd   <= '0';
            attr_avst_wr   <= '0';
            attr_avst_done <= '0';

            case attr_state is
                when ATTR_INIT =>
                    if (attr_avst_start = '1') then
                      -- TBD: stop operation when done
                        attr_state <= ATTR_CLR_STAT;
                    end if;

                when ATTR_CLR_STAT =>
                    -- Clear 0x8a[7]: write(0x8a, 0x80)
                    attr_avst_addr <= X"0008a";
                    attr_avst_dwr  <= X"0080";
                    attr_avst_wr   <= '1';
                    if avst_fsm_done = '1' then
                        attr_state   <= ATTR_CODE_WR0;
                        attr_avst_wr <= '0';
                    end if;

                when ATTR_CODE_WR0   =>
                    -- # Write PMA attribute code and data: write(0x84, (value & 0x00ff))
                    attr_avst_addr <= X"00084";
                    attr_avst_dwr  <= rom_val;
                    attr_avst_wr   <= '1';
                    if avst_fsm_done = '1' then
                        attr_state   <= ATTR_CODE_WR1;
                        attr_avst_wr <= '0';
                    end if;

                when ATTR_CODE_WR1   =>
                    -- write(0x85, (value >> 8 ))
                    attr_avst_addr <= X"00085";
                    attr_avst_dwr  <= X"00" & rom_val(15 downto 8);
                    attr_avst_wr   <= '1';
                    if avst_fsm_done = '1' then
                        attr_state   <= ATTR_VAL_WR0;
                        attr_avst_wr <= '0';
                    end if;

                when ATTR_VAL_WR0 =>
                --         write(0x86, (code & 0x00ff))
                    attr_avst_addr <= X"00086";
                    attr_avst_dwr  <= rom_code(15 downto 0);
                    attr_avst_wr   <= '1';
                    if avst_fsm_done = '1' then
                        attr_state   <= ATTR_VAL_WR1;
                        attr_avst_wr <= '0';
                    end if;

                when ATTR_VAL_WR1 =>
                --        write(0x87, (code >> 8))
                    attr_avst_addr <= X"00087";
                    attr_avst_dwr  <= X"00" & rom_code(15 downto 8);
                    attr_avst_wr   <= '1';
                    if avst_fsm_done = '1' then
                        attr_state   <= ATTR_OP_START;
                        attr_avst_wr <= '0';
                    end if;

                when ATTR_OP_START =>
                --         write(0x90, 0x1)
                    attr_avst_addr <= X"00090";
                    attr_avst_dwr  <= X"0001";
                    attr_avst_wr   <= '1';
                    if avst_fsm_done = '1' then
                        attr_state   <= ATTR_BUSY_CHECK;
                        attr_avst_wr <= '0';
                    end if;

                when ATTR_BUSY_CHECK =>
                    -- Read 0x8a. Bit 7 should be 1: if bit(read(0x8a, 7) != 1: return False
                    attr_avst_addr <= X"0008a";
                    attr_avst_rd   <= '1';
                    if avst_fsm_done = '1' then
                        attr_avst_rd  <= '0';
                        if avst_drd(7) = '0' then
                            attr_state <= ATTR_OP_START;
                        else
                            attr_state <= ATTR_WAIT;
                        end if;
                    end if;

                when ATTR_WAIT =>
                    -- while bit(read(0x8b), 0) != 0: time.sleep(0.001)
                    attr_avst_addr <= X"0008b";
                    attr_avst_rd   <= '1';
                    if avst_fsm_done = '1' then
                        attr_avst_rd  <= '0';
                        if avst_drd(0) = '1' then
                            attr_state <= ATTR_WAIT;
                        else
                            if rom_op = OP_AREAD then
                                attr_state <= ATTR_READ0;
                            else
                                attr_state <= ATTR_DONE;
                                attr_avst_done <= '1';
                            end if;
                        end if;
                    end if;

                when ATTR_READ0 =>
                    -- # Read return data: ret = read(0x89); ret = ret << 8
                    attr_avst_addr <= X"00089";
                    attr_avst_rd   <= '1';
                    if avst_fsm_done = '1' then
                        attr_avst_rd  <= '0';
                        attr_avst_drd(15 downto 8) <= avst_drd(7 downto 0);
                        attr_state <= ATTR_READ1;
                    end if;

                when ATTR_READ1 =>
                    --  ret |= (read(0x88) & 0x000000ff)
                    attr_avst_addr <= X"00088";
                    attr_avst_rd   <= '1';
                    if avst_fsm_done = '1' then
                        attr_avst_rd  <= '0';
                        attr_avst_drd(7 downto 0) <= avst_drd(7 downto 0);
                        attr_state <= ATTR_DONE;
                        attr_avst_done <= '1';
                    end if;

                when ATTR_DONE =>
                    attr_state <= ATTR_INIT;

                when others => null;

            end case;
            if rst_sync = '1' then
                attr_state <= ATTR_INIT;
            end if;
        end if;
    end process;

    -- --------------------------------------------------------------------------
    -- Main FSM (Read config ROM and perform the sequence)
    -- --------------------------------------------------------------------------
    init_fsm: process(CLK)
    begin
        if rising_edge(CLK) then
            init_avst_wr    <= '0';
            init_avst_rd    <= '0';
            attr_avst_start <= '0';
            DONE            <= '0';

            case init_fsm_state is

                when INIT =>
                    rom_cntr        <= 0;
                    init_avst_wr    <= '0';
                    init_avst_rd    <= '0';
                    attr_avst_start <= '0';
                    BUSY            <= '0';
                    if XCVR_RDY = '1' then
                        init_fsm_state  <= START;
                    end if;

                when START =>
                    BUSY  <= '1';
                    if (rom_op = OP_WRITE) then
                        init_avst_wr <= '1';
                        if avst_fsm_done = '1' then
                            init_fsm_state <= ADDR_INC;
                            init_avst_wr <= '0';
                        end if;
                    elsif (rom_op = OP_READ) then
                        init_avst_rd <= '1';
                        if avst_fsm_done = '1' then
                            init_fsm_state <= READ_CHECK;
                            init_avst_rd <= '0';
                        end if;
                    elsif (rom_op = OP_AREAD) then
                        attr_avst_start <= '1';
                        if attr_avst_done = '1' then
                            init_fsm_state <= AREAD_CHECK;
                            attr_avst_start <= '0';
                        end if;
                    else
                        attr_avst_start <= '1';
                        if attr_avst_done = '1' then
                            init_fsm_state <= ADDR_INC;
                            attr_avst_start <= '0';
                        end if;
                    end if;

                when READ_CHECK =>
                    -- Check if masked data read from AVMM are as defined in ROM
                    if ((avst_drd(rom_mask'range) and rom_mask) = rom_data) then
                        init_fsm_state <= ADDR_INC;
                    else
                        init_fsm_state <= START;  -- Retry the read operation
                    end if;

                when AREAD_CHECK =>
                    -- Check if masked attribute data read from AVMM are as defined in ROM
                    if ((attr_avst_drd(rom_mask'range) and rom_mask) = rom_data) then
                        init_fsm_state <= ADDR_INC;
                    else
                        init_fsm_state <= START;  -- Retry the read operation
                    end if;

                when ADDR_INC =>
                    if rom_cntr = etile_config_rom'high then -- Last address in ROM - all done
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

    cfg_rom_out <= etile_config_rom(rom_cntr);

    -- --------------------------------------------------------------------------
    -- Debug and status
    -- --------------------------------------------------------------------------
    STATE(3 downto 0) <= "0000" when init_fsm_state = INIT        else
                         "0001" when init_fsm_state = START       else
                         "0010" when init_fsm_state = READ_CHECK  else
                         "0011" when init_fsm_state = AREAD_CHECK else
                         "0100" when init_fsm_state = ADDR_INC    else
                         "1111"; -- INIT_DONE

    STATE(7 downto 4) <= "0000" when attr_state = ATTR_INIT       else
                         "0001" when attr_state = ATTR_CLR_STAT   else
                         "0010" when attr_state = ATTR_CODE_WR0   else
                         "0011" when attr_state = ATTR_CODE_WR1   else
                         "0100" when attr_state = ATTR_VAL_WR0    else
                         "0101" when attr_state = ATTR_VAL_WR1    else
                         "0110" when attr_state = ATTR_OP_START   else
                         "0111" when attr_state = ATTR_BUSY_CHECK else
                         "1000" when attr_state = ATTR_WAIT       else
                         "1001" when attr_state = ATTR_READ0      else
                         "1010" when attr_state = ATTR_READ1      else
                         "1111"; -- ATTR_DONE

    STATE(11 downto 8) <= "0000" when avst_state = AVMM_INIT       else
                          "0001" when avst_state = AVMM_WAIT       else
                          "0010" when avst_state = AVMM_BUSY       else
                          "1111"; -- AVMM_DONE

    STATE(15 downto 12) <= std_logic_vector(to_unsigned(rom_cntr, 4));
    STATE(31 downto 16) <= X"0000";

end architecture;
