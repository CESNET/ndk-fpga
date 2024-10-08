-- sdm_ctrl_arch.vhd: SDM controller architecture
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture FULL of SDM_CTRL is

    constant MC_ADDR_WIDTH : natural := 4;

    component mailbox_client_ip is
    port (
        in_clk_clk         : in  std_logic                     := 'X';             -- clk
        in_reset_reset     : in  std_logic                     := 'X';             -- reset
        avmm_address       : in  std_logic_vector(3 downto 0)  := (others => 'X'); -- address
        avmm_write         : in  std_logic                     := 'X';             -- write
        avmm_writedata     : in  std_logic_vector(31 downto 0) := (others => 'X'); -- writedata
        avmm_read          : in  std_logic                     := 'X';             -- read
        avmm_readdata      : out std_logic_vector(31 downto 0);                    -- readdata
        avmm_readdatavalid : out std_logic;                                        -- readdatavalid
        avmm_waitrequest   : out std_logic;                                        -- waitrequest
        irq_irq            : out std_logic                                         -- irq
    );
    end component mailbox_client_ip;

    -- mi2avmm out signals
    signal avmm_addr    : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal avmm_wr      : std_logic;
    signal avmm_rd      : std_logic;
    signal avmm_dwr     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal avmm_drd     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal avmm_drd_vld : std_logic;
    signal avmm_wait    : std_logic;

    -- mailbox client signals
    signal mc_offset    : std_logic_vector(MC_ADDR_WIDTH-1 downto 0);
    signal mc_wr        : std_logic;
    signal mc_rd        : std_logic;
    signal mc_dwr       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mc_drd       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mc_drd_vld   : std_logic;
    signal mc_wait      : std_logic;

    -- mailbox client data register
    signal mc_drd_reg   : std_logic_vector(DATA_WIDTH-1 downto 0);

    -- state machine constants and signals
    constant MC_GET_CHIPID_CMD : std_logic_vector(DATA_WIDTH-1 downto 0)    := (7 downto 0 => "00010010", others => '0');

    constant MC_LAST_WORD_ADDR : std_logic_vector(MC_ADDR_WIDTH-1 downto 0) := "0001";
    constant MC_RESPONSE_ADDR  : std_logic_vector(MC_ADDR_WIDTH-1 downto 0) := "0101";
    constant MC_RES_FILL_ADDR  : std_logic_vector(MC_ADDR_WIDTH-1 downto 0) := "0110";
    constant MC_ISR_ADDR       : std_logic_vector(MC_ADDR_WIDTH-1 downto 0) := "1000";

    constant MC_ISR_VALID_BIT  : natural := 0;
    constant MC_RES_FILL_SOP   : natural := 0;
    constant MC_RES_FILL_EOP   : natural := 1;

    constant MC_ERR_CODE_WIDTH : natural := 11;

    type chip_id_state is (
        IDLE,                  -- held during RESET signal active
        SEND_CMD,              -- write get_chipid command to Mailbox Client
        READ_ISR,              -- poll interrupt status register
        READ_RES_FILL_SOP,     -- poll response fifo fill level and SOP
        READ_RES_HEADER,       -- read the first response word (response header)
        CHECK_RES_FILL,        -- check response fifo fill level after reading first response word
        READ_RES_FILL,         -- poll response fifo fill level after reading first response word (not always)
        READ_LSW,              -- read the second response word (chip_id LSW)
        READ_RES_FILL_EOP,     -- poll response fifo fill level and EOP
        READ_MSW,              -- read the third response word (chip_id MSW)
        WAIT_FOR_DATA,         -- wait for valid data from mailbox client ip
        DONE                   -- MI interface enabled - normal function
    );
    signal p_state            : chip_id_state := IDLE;
    signal n_state            : chip_id_state;
    signal p_state_reg        : chip_id_state;

    signal p_state_save       : std_logic;

    signal res_fill           : std_logic_vector(DATA_WIDTH-2-1 downto 0);
    signal res_fill_reg       : std_logic_vector(DATA_WIDTH-2-1 downto 0);
    signal res_fill_vld       : std_logic;
    signal res_fill_reg_vld   : std_logic;
    signal res_fill_vld_reg   : std_logic;
    signal res_fill_dec       : std_logic;

    signal res_header_err     : std_logic;
    signal res_header_err_reg : std_logic;

    signal chip_id_reg        : std_logic_vector(64-1 downto 0) := x"DEADDEADDEADDEAD";

    signal retry_cnt          : std_logic_vector(2-1 downto 0);
    signal retry_stop         : std_logic;

    signal chip_id_done       : std_logic;

begin

    read_chip_id_g: if READ_CHIP_ID = true generate

        -- chip_id reading: state register
        chip_id_state_reg_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    p_state <= IDLE;
                elsif (mc_wait = '0') then
                    p_state <= n_state;
                end if;
            end if;
        end process;

        -- chip_id reading: second state register
        chip_id_state_reg_reg_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    p_state_reg <= IDLE;
                elsif (p_state_save = '1') then
                    p_state_reg <= p_state;
                end if;
            end if;
        end process;

        -- chip_id reading: next state logic
        chip_id_n_state_logic_p: process (all)
        begin
            n_state <= p_state;
            case p_state is
                when IDLE =>
                    n_state <= SEND_CMD;
                when SEND_CMD =>
                    if (retry_stop = '1') then
                        n_state <= DONE;
                    else
                        n_state <= READ_ISR;
                    end if;
                when READ_ISR =>
                    if (mc_drd_vld = '1') then
                        if (mc_drd(MC_ISR_VALID_BIT) = '1') then
                            n_state <= READ_RES_FILL_SOP;
                        end if;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        if (mc_drd_reg(MC_ISR_VALID_BIT) = '1') then
                            n_state <= READ_RES_FILL_SOP;
                        end if;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when READ_RES_FILL_SOP =>
                    if (mc_drd_vld = '1') then
                        if (mc_drd(MC_RES_FILL_SOP) = '1' and res_fill_vld = '1') then
                            n_state <= READ_RES_HEADER;
                        end if;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        if (mc_drd_reg(MC_RES_FILL_SOP) = '1' and res_fill_vld_reg = '1') then
                            n_state <= READ_RES_HEADER;
                        end if;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when READ_RES_HEADER =>
                    if (mc_drd_vld = '1') then
                        if (res_header_err = '0') then
                            n_state <= CHECK_RES_FILL;
                        else
                            n_state <= SEND_CMD;
                        end if;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        if (res_header_err_reg = '0') then
                            n_state <= CHECK_RES_FILL;
                        else
                            n_state <= SEND_CMD;
                        end if;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when CHECK_RES_FILL =>
                    if (res_fill_reg_vld = '0') then
                        n_state <= READ_RES_FILL;
                    else
                        n_state <= READ_LSW;
                    end if;
                when READ_RES_FILL =>
                    if (mc_drd_vld = '1') then
                        if (res_fill_vld = '1') then
                            n_state <= READ_LSW;
                        end if;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        if (res_fill_vld_reg = '1') then
                            n_state <= READ_LSW;
                        end if;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when READ_LSW =>
                    if (mc_drd_vld = '1') then
                        n_state <= READ_RES_FILL_EOP;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        n_state <= READ_RES_FILL_EOP;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when READ_RES_FILL_EOP =>
                    if (mc_drd_vld = '1') then
                        if (mc_drd(MC_RES_FILL_EOP) = '1' and res_fill_vld = '1') then
                            n_state <= READ_MSW;
                        end if;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        if (mc_drd_reg(MC_RES_FILL_EOP) = '1' and res_fill_vld_reg = '1') then
                            n_state <= READ_MSW;
                        end if;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when READ_MSW =>
                    if (mc_drd_vld = '1') then
                        n_state <= DONE;
                    elsif (p_state_reg = WAIT_FOR_DATA) then
                        n_state <= DONE;
                    else
                        n_state <= WAIT_FOR_DATA;
                    end if;
                when WAIT_FOR_DATA =>
                    if (mc_drd_vld = '1') then
                        n_state <= p_state_reg;
                    end if;
                when others =>
                    n_state <= DONE;
            end case;
        end process;

        -- chip_id reading: state signals
        chip_id_signals_logic_p: process(all)
        begin
            mc_offset     <= (others => '0');
            mc_wr         <= '0';
            mc_rd         <= '0';
            mc_dwr        <= (others => '0');
            avmm_drd      <= (others => '0');
            avmm_drd_vld  <= '0';
            avmm_wait     <= '1';
            chip_id_done  <= '0';

            p_state_save  <= '0';
            res_fill_dec  <= '0';
            case p_state is
                when SEND_CMD =>
                    mc_offset    <= MC_LAST_WORD_ADDR;
                    mc_wr        <= '1';
                    mc_dwr       <= MC_GET_CHIPID_CMD;
                when READ_ISR =>
                    mc_offset    <= MC_ISR_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                when READ_RES_FILL_SOP =>
                    mc_offset    <= MC_RES_FILL_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                when READ_RES_HEADER =>
                    mc_offset    <= MC_RESPONSE_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                    res_fill_dec <= '1' when (n_state = CHECK_RES_FILL) else '0';
                when READ_RES_FILL =>
                    mc_offset    <= MC_RES_FILL_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                when READ_LSW =>
                    mc_offset    <= MC_RESPONSE_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                when READ_RES_FILL_EOP =>
                    mc_offset    <= MC_RES_FILL_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                when READ_MSW =>
                    mc_offset    <= MC_RESPONSE_ADDR;
                    mc_rd        <= '0' when (p_state_reg = WAIT_FOR_DATA) else '1';
                    p_state_save <= '1';
                when WAIT_FOR_DATA =>
                    p_state_save <= '1' when (mc_drd_vld = '1') else '0';
                when DONE =>
                    mc_offset    <= avmm_addr(MC_ADDR_WIDTH+2-1 downto 2);
                    mc_wr        <= avmm_wr;
                    mc_rd        <= avmm_rd;
                    mc_dwr       <= avmm_dwr;
                    avmm_drd     <= mc_drd;
                    avmm_drd_vld <= mc_drd_vld;
                    avmm_wait    <= mc_wait;
                    chip_id_done <= '1';
                when others =>
                    null;
            end case;
        end process;

        -- chip_id reading: auxiliary data registers
        chip_id_data_reg_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                mc_drd_reg         <= mc_drd;
                res_fill_vld_reg   <= res_fill_vld;
                res_header_err_reg <= res_header_err;
            end if;
        end process;

        -- chip_id reading: response fifo fill level register
        res_fill         <= mc_drd(DATA_WIDTH-1 downto 2);
        res_fill_vld     <= or res_fill;
        res_fill_reg_vld <= or res_fill_reg;
        res_fill_reg_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (p_state = READ_RES_FILL_SOP) then
                    res_fill_reg <= res_fill;
                elsif (res_fill_dec = '1') then
                    res_fill_reg <= std_logic_vector(unsigned(res_fill_reg) - 1);
                end if;
            end if;
        end process;

        res_header_err <= or mc_drd(MC_ERR_CODE_WIDTH-1 downto 0);

        -- chip_id reading: chip_id LSW and MSW data register
        chip_id_reg_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                CHIP_ID_VLD <= chip_id_done;
                if (p_state = READ_LSW) then
                    if (mc_drd_vld = '1') then
                        chip_id_reg(32-1 downto 0) <= mc_drd;
                    else
                        chip_id_reg(32-1 downto 0) <= mc_drd_reg;
                    end if;
                elsif (p_state = READ_MSW) then
                    if (mc_drd_vld = '1') then
                        chip_id_reg(64-1 downto 32) <= mc_drd;
                    else
                        chip_id_reg(64-1 downto 32) <= mc_drd_reg;
                    end if;
                end if;
            end if;
        end process;

        -- chip_id reading: retry counter
        retry_stop <= and retry_cnt;
        retry_cnt_p: process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    retry_cnt <= (others => '0');
                elsif (p_state = SEND_CMD and mc_wait = '0') then
                    retry_cnt <= std_logic_vector(unsigned(retry_cnt) + 1);
                end if;
            end if;
        end process;

    else generate

        mc_offset    <= avmm_addr(MC_ADDR_WIDTH+2-1 downto 2);
        mc_wr        <= avmm_wr;
        mc_rd        <= avmm_rd;
        mc_dwr       <= avmm_dwr;
        avmm_drd     <= mc_drd;
        avmm_drd_vld <= mc_drd_vld;
        avmm_wait    <= mc_wait;

    end generate;

    CHIP_ID <= chip_id_reg;

    -- MI to Avalon MM interface converter
    mi2avmm_i : entity work.MI2AVMM
    generic map(
        DATA_WIDTH => DATA_WIDTH,
        ADDR_WIDTH => ADDR_WIDTH,
        META_WIDTH => 1,
        DEVICE     => DEVICE
    )
    port map(
        CLK                => CLK,
        RESET              => RESET,

        MI_DWR             => MI_DWR,
        MI_MWR             => (others => '0'),
        MI_ADDR            => MI_ADDR,
        MI_RD              => MI_RD,
        MI_WR              => MI_WR,
        MI_BE              => MI_BE,
        MI_DRD             => MI_DRD,
        MI_ARDY            => MI_ARDY,
        MI_DRDY            => MI_DRDY,
        
        AVMM_ADDRESS       => avmm_addr,
        AVMM_WRITE         => avmm_wr,
        AVMM_READ          => avmm_rd,
        AVMM_BYTEENABLE    => open,
        AVMM_WRITEDATA     => avmm_dwr,
        AVMM_READDATA      => avmm_drd,
        AVMM_READDATAVALID => avmm_drd_vld,
        AVMM_WAITREQUEST   => avmm_wait
    );

    -- Mailbox Client IP component
    mailbox_client_i : component mailbox_client_ip
    port map (
        in_clk_clk         => CLK,
        in_reset_reset     => RESET,
        avmm_address       => mc_offset,
        avmm_write         => mc_wr,
        avmm_writedata     => mc_dwr,
        avmm_read          => mc_rd,
        avmm_readdata      => mc_drd,
        avmm_readdatavalid => mc_drd_vld,
        avmm_waitrequest   => mc_wait,
        irq_irq            => open
    );

end architecture;
