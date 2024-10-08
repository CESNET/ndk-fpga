-- fifox_multi_full.vhd: FIFOX MULTI architecture
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
-- This architecture consists of a SHAKEDOWN, a BARREL SHIFTER, multiple FIFOXs
-- and another BARREL SHIFTER on output.
-- PROS:
--     - MUXes are only as wide as 2**(log2(max(INPUT_PORTS,OUTPUT_PORTS))).
--     - Native removing of gaps in data words (if reading slower then writing).
-- CONS:
--     - More resources used by multiple FIFOXs.
--     - Output propagated through an asynchronous BARREL SHIFTER.

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of FIFOX_MULTI is

    -- Quartus max fanout constraint
    attribute maxfan : integer;

    -- -------------------------------------------------------------------------
    -- Constants
    -- -------------------------------------------------------------------------

    -- function for 2**N ceiling
    function ceil2N(x : integer) return integer is
        variable v : integer := 1;
    begin
        while (v<x) loop
            v := v*2;
        end loop;

        return v;
    end function;

    -- Actual number of items
    constant ITEMS_ACT      : integer := ceil2N(ITEMS);
    --Address bus width
    constant ADDR_WIDTH     : integer := log2(ITEMS_ACT);
    -- Number of items in memory when almost full is triggered.
    constant AFULL_CAPACITY : integer := ITEMS_ACT - ALMOST_FULL_OFFSET;

    -- Actual number of FIFOX instances
    constant FIFOX_COUNT    : integer := ceil2N(max(WRITE_PORTS,READ_PORTS));
    -- Number of items in each FIFOX instance
    constant FIFOX_ITEMS    : integer := ITEMS_ACT/FIFOX_COUNT;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Signals
    -- -------------------------------------------------------------------------

    -- ----------------
    -- Data path
    -- ----------------

    -- input registers before shakedown
    signal in_reg0        : slv_array_t     (WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal in_reg0_vld    : std_logic_vector(WRITE_PORTS-1 downto 0);
    signal in_reg0_vld_or : std_logic;
    signal in_reg0_en     : std_logic;

    -- shakedown input/output
    signal in_shake_in_data  : std_logic_vector(WRITE_PORTS*(DATA_WIDTH+1)-1 downto 0); -- data & vld
    signal in_shake_out_data : std_logic_vector(WRITE_PORTS*(DATA_WIDTH+1)-1 downto 0); -- data & vld

    -- input registers after shakedown
    signal in_reg1        : slv_array_t     (WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal in_reg1_vld    : std_logic_vector(WRITE_PORTS-1 downto 0);
    signal in_reg1_vld_or : std_logic;
    signal in_reg1_en     : std_logic;

    -- can write in fifo from this port
    signal can_write : std_logic_vector(WRITE_PORTS-1 downto 0);

    -- input barrel shifter input/output
    signal in_barsh_in_data  : std_logic_vector(FIFOX_COUNT*(DATA_WIDTH+1)-1 downto 0); -- data & vld
    signal in_barsh_in_sel   : std_logic_vector(log2(FIFOX_COUNT)         -1 downto 0);
    signal in_barsh_out_data : std_logic_vector(FIFOX_COUNT*(DATA_WIDTH+1)-1 downto 0); -- data & vld

    -- input registers after barrel shifter
    signal in_reg2        : slv_array_t     (FIFOX_COUNT-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal in_reg2_vld    : std_logic_vector(FIFOX_COUNT-1 downto 0);
    signal in_reg2_en     : std_logic_vector(FIFOX_COUNT-1 downto 0);

    -- fifox input/output
    signal fifox_di       : slv_array_t     (FIFOX_COUNT-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal fifox_wr       : std_logic_vector(FIFOX_COUNT-1 downto 0);
    signal fifox_full     : std_logic_vector(FIFOX_COUNT-1 downto 0);
    signal fifox_do       : slv_array_t     (FIFOX_COUNT-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal fifox_rd       : std_logic_vector(FIFOX_COUNT-1 downto 0);
    signal fifox_empty    : std_logic_vector(FIFOX_COUNT-1 downto 0);

    -- output barrel shifter input/output
    signal out_barsh_in_data  : std_logic_vector(FIFOX_COUNT*(DATA_WIDTH+1)-1 downto 0);
    signal out_barsh_in_sel   : std_logic_vector(log2(FIFOX_COUNT)         -1 downto 0);
    signal out_barsh_out_data : std_logic_vector(FIFOX_COUNT*(DATA_WIDTH+1)-1 downto 0);

    -- output read barrel shifter input/output
    signal out_re_barsh_in_data  : std_logic_vector(FIFOX_COUNT*1    -1 downto 0);
    signal out_re_barsh_in_sel   : std_logic_vector(log2(FIFOX_COUNT)-1 downto 0);
    signal out_re_barsh_out_data : std_logic_vector(FIFOX_COUNT*1    -1 downto 0);

    -- an actual safe read from fifo on this port
    signal read_act : std_logic_vector(READ_PORTS-1 downto 0);

    -- ----------------

    -- ----------------
    -- Control
    -- ----------------

    -- wr/rd pointer registers
    signal wr_ptr_reg    : unsigned(log2(FIFOX_COUNT)-1 downto 0);
    signal rd_ptr_reg    : unsigned(log2(FIFOX_COUNT)-1 downto 0);

    -- number of writes to be committed register
    signal wr_num_reg1   : unsigned(log2(WRITE_PORTS+1)-1 downto 0);

    -- number of reads now
    signal rd_num        : unsigned(log2(READ_PORTS+1)-1 downto 0);
    signal rd_num_reg    : unsigned(log2(READ_PORTS+1)-1 downto 0);

    -- status register
    signal status_reg    : unsigned(log2(ITEMS_ACT+WRITE_PORTS*3+1)-1 downto 0);
    signal status_reg1   : unsigned(log2(ITEMS_ACT+WRITE_PORTS*3+1)-1 downto 0);
    signal status_reg2   : unsigned(log2(ITEMS_ACT+WRITE_PORTS*3+1)-1 downto 0);

    -- almost full / almost empty
    signal al_full_reg   : std_logic;
    signal al_empty_reg  : std_logic;

    -- ----------------

    -- -------------------------------------------------------------------------

    attribute maxfan of wr_ptr_reg     : signal is 64;
    attribute maxfan of rd_ptr_reg     : signal is 64;
    attribute maxfan of in_reg1_vld_or : signal is 64;
    attribute maxfan of in_reg1_vld    : signal is 64;
    attribute maxfan of in_reg2_vld    : signal is 64;

begin

    -- -------------------------------------------------------------------------
    -- Assert checking
    -- -------------------------------------------------------------------------

    assert_pr : process (CLK)
        variable rd_en : boolean;
    begin
        if (FIFOX_ITEMS < 2) then
            assert (false)
                report "ERROR: FIFOX Multi: FIFOX_ITEMS < 2!"
                severity failure;
        end if;

        if (rising_edge(CLK)) then
            if (RESET/='1') then
                rd_en := true;
                for i in 0 to READ_PORTS-1 loop
                    if (SAFE_READ_MODE=false and RD(i)='1' and EMPTY(i)='1') then
                        assert (false)
                            report "ERROR: FIFOX Multi: Non-safe Read Mode condition violated! Reading from port " & to_string(i) & " is forbidden when EMPTY is active!"
                            severity failure;
                    end if;

                    if (RD(i)/='1' and EMPTY(i)/='1') then
                        rd_en := false;
                    end if;
                    if (rd_en=false and RD(i)='1' and EMPTY(i)/='1') then
                        assert (false)
                            report "ERROR: FIFOX Multi: Aligned read condition viloated! Reading from non-empty port " & to_string(i) & " is forbidden when not reading from ports 0 to " & to_string(i-1) & "!"
                            severity failure;
                    end if;
                end loop;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    single_fifox_gen : if (FIFOX_COUNT=1 and ALLOW_SINGLE_FIFO=true) generate
    -- =========================================================================
    -- SINGLE FIFOX VARIANT
    -- =========================================================================

    fifox_i : entity work.FIFOX
    generic map (
        DATA_WIDTH          => DATA_WIDTH,
        ITEMS               => FIFOX_ITEMS,
        RAM_TYPE            => RAM_TYPE,
        ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
        ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
        DEVICE              => DEVICE
    )
    port map (
        CLK    => CLK,
        RESET  => RESET,

        DI     => DI,
        WR     => WR(0),
        FULL   => FULL,
        AFULL  => AFULL,

        DO     => DO,
        RD     => RD(0),
        EMPTY  => EMPTY(0),
        AEMPTY => AEMPTY
    );

    -- =========================================================================
    end generate;

    multi_fifox_gen : if (FIFOX_COUNT>1 or ALLOW_SINGLE_FIFO=false) generate
    -- =========================================================================
    -- TRUE MULTI FIFOX VARIANT
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- Input register 0
    -- -------------------------------------------------------------------------

    input_reg0_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (in_reg0_en='1') then
                for i in 0 to WRITE_PORTS-1 loop
                    in_reg0(i)      <= DI(DATA_WIDTH*(i+1)-1 downto DATA_WIDTH*i);
                end loop;
                in_reg0_vld    <= WR;
                in_reg0_vld_or <= (or WR);
            end if;

            if (RESET='1') then
                in_reg0_vld    <= (others => '0');
                in_reg0_vld_or <= '0';
            end if;
        end if;
    end process;

    in_reg0_en <= '1' when in_reg1_en='1' else '0';

    -- FULL propagation
    FULL <= not in_reg0_en;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input shakedown unit
    -- -------------------------------------------------------------------------

    in_shak_i : entity work.MERGE_N_TO_M
    generic map (
        INPUTS     => WRITE_PORTS,
        OUTPUTS    => WRITE_PORTS,
        DATA_WIDTH => DATA_WIDTH+1,
        OUTPUT_REG => false
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,

        INPUT_DATA  => in_shake_in_data,
        OUTPUT_DATA => in_shake_out_data
    );

    in_shake_input_gen : for i in 0 to WRITE_PORTS-1 generate
        in_shake_in_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i) <= in_reg0(i) & in_reg0_vld(i);
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input register 1
    -- -------------------------------------------------------------------------

    input_reg1_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (in_reg1_en='1') then
                for i in 0 to WRITE_PORTS-1 loop
                    in_reg1(i)     <= in_shake_out_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i+1);
                    in_reg1_vld(i) <= in_shake_out_data((DATA_WIDTH+1)*i);
                end loop;
                in_reg1_vld_or <= in_reg0_vld_or;
            end if;

            if (RESET='1') then
                in_reg1_vld    <= (others => '0');
                in_reg1_vld_or <= '0';
            end if;
        end if;
    end process;

    in_reg1_en <= '1' when (and in_reg2_en)='1' else '0';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input barrel shifter
    -- -------------------------------------------------------------------------

    in_barsh_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => FIFOX_COUNT,
        BLOCK_SIZE => DATA_WIDTH+1,
        SHIFT_LEFT => true -- rotate in opposite direction
    )
    port map(
        DATA_IN  => in_barsh_in_data,
        SEL      => in_barsh_in_sel,
        DATA_OUT => in_barsh_out_data
    );

    in_barsh_input_low_gen : for i in 0 to WRITE_PORTS-1 generate
        in_barsh_in_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i) <= in_reg1(i) & in_reg1_vld(i);
    end generate;

    in_barsh_input_high_gen : for i in WRITE_PORTS to FIFOX_COUNT-1 generate
        in_barsh_in_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i) <= (others => '0');
    end generate;

    in_barsh_in_sel <= std_logic_vector(wr_ptr_reg);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input register 2
    -- -------------------------------------------------------------------------

    input_reg2_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            for i in 0 to FIFOX_COUNT-1 loop
                if (in_reg2_en(i)='1') then
                    in_reg2(i)     <= in_barsh_out_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i+1);
                    in_reg2_vld(i) <= in_barsh_out_data((DATA_WIDTH+1)*i) and in_reg1_en;
                end if;
            end loop;

            if (RESET='1') then
                in_reg2_vld <= (others => '0');
            end if;
        end if;
    end process;

    in_reg2_en_gen : for i in 0 to FIFOX_COUNT-1 generate
        in_reg2_en(i) <= '1' when fifox_full(i)='0' or in_reg2_vld(i)='0' else '0';
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- FIFOX instances
    -- -------------------------------------------------------------------------

    fifox_gen : for i in 0 to FIFOX_COUNT-1 generate

        fifox_i : entity work.FIFOX
        generic map (
            DATA_WIDTH => DATA_WIDTH,
            ITEMS      => FIFOX_ITEMS,
            RAM_TYPE   => RAM_TYPE,
            DEVICE     => DEVICE
        )
        port map (
            CLK   => CLK,
            RESET => RESET,

            DI    => fifox_di(i),
            WR    => fifox_wr(i),
            FULL  => fifox_full(i),

            DO    => fifox_do(i),
            RD    => fifox_rd(i),
            EMPTY => fifox_empty(i)
        );

        fifox_di(i) <= in_reg2(i);
        fifox_wr(i) <= in_reg2_vld(i);
        fifox_rd(i) <= out_re_barsh_out_data(i);

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Output barrel shifter
    -- -------------------------------------------------------------------------

    out_barsh_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => FIFOX_COUNT,
        BLOCK_SIZE => DATA_WIDTH+1,
        SHIFT_LEFT => false
    )
    port map(
        DATA_IN  => out_barsh_in_data,
        SEL      => out_barsh_in_sel,
        DATA_OUT => out_barsh_out_data
    );

    out_barsh_input_gen : for i in 0 to FIFOX_COUNT-1 generate
        out_barsh_in_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i) <= fifox_do(i) & fifox_empty(i);
    end generate;

    out_barsh_in_sel <= std_logic_vector(rd_ptr_reg);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Output read enable barrel shifter
    -- -------------------------------------------------------------------------

    out_re_barsh_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => FIFOX_COUNT,
        BLOCK_SIZE => 1,
        SHIFT_LEFT => true -- rotate in opposite direction
    )
    port map(
        DATA_IN  => out_re_barsh_in_data,
        SEL      => out_re_barsh_in_sel,
        DATA_OUT => out_re_barsh_out_data
    );

    out_re_barsh_input_low_gen : for i in 0 to READ_PORTS-1 generate
        out_re_barsh_in_data(i) <= RD(i);
    end generate;

    out_re_barsh_input_high_gen : for i in READ_PORTS to FIFOX_COUNT-1 generate
        out_re_barsh_in_data(i) <= '0';
    end generate;

    out_re_barsh_in_sel <= std_logic_vector(rd_ptr_reg);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Data output
    -- -------------------------------------------------------------------------

    -- an actual safe read from fifo on each port
    read_act_gen : for i in 0 to READ_PORTS-1 generate
        read_act(i) <= '1' when (out_barsh_out_data((DATA_WIDTH+1)*i)='0' or SAFE_READ_MODE=false) and RD(i)='1' else '0';
    end generate;

    -- data output propagation
    output_gen : for i in 0 to READ_PORTS-1 generate
        DO(DATA_WIDTH*(i+1)-1 downto DATA_WIDTH*i) <= out_barsh_out_data((DATA_WIDTH+1)*(i+1)-1 downto (DATA_WIDTH+1)*i+1);
    end generate;

    -- EMPTY propagation
    empty_gen : for i in 0 to READ_PORTS-1 generate
        EMPTY(i) <= out_barsh_out_data((DATA_WIDTH+1)*i);
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Number of writes and reads counting
    -- -------------------------------------------------------------------------

    -- writes number counter register
    wr_num_reg_pr : process (CLK)
        variable num : unsigned(log2(WRITE_PORTS+1)-1 downto 0);
    begin
        if (CLK'event and CLK='1') then
            if (in_reg1_en='1') then
                -- ones counter
                num := (others => '0');
                for i in 0 to WRITE_PORTS-1 loop
                    if (in_reg0_vld(i)='1') then
                        num := num + 1;
                    end if;
                end loop;

                wr_num_reg1 <= num;
            end if;

            -- reset not needed; value in_reg1_vld_or is being reset
            --if (RESET='1') then
            --   wr_num_reg <= (others => '0');
            --end if;
        end if;
    end process;

    -- reads number counter
    rd_num_pr : process (RD,read_act)
        variable num : unsigned(log2(READ_PORTS+1)-1 downto 0);
    begin
        num := (others => '0');

        -- ones counter
        for i in 0 to READ_PORTS-1 loop
            if (read_act(i)='1') then
                num := num + 1;
            end if;
        end loop;

        rd_num <= num;
    end process;

    rd_num_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            rd_num_reg <= rd_num;
            if (RESET='1') then
                rd_num_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- WR/RD pointer registers
    -- -------------------------------------------------------------------------

    -- write pointer register
    wr_ptr_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            if (in_reg1_en='1') then
                wr_ptr_reg <= resize(wr_ptr_reg + wr_num_reg1,wr_ptr_reg'high+1);
            end if;

            if (RESET='1') then
                wr_ptr_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- read pointer register
    rd_ptr_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            rd_ptr_reg <= resize(rd_ptr_reg + rd_num,rd_ptr_reg'high+1);

            if (RESET='1') then
                rd_ptr_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Status register
    -- -------------------------------------------------------------------------

    -- status register
    status_reg_pr : process (CLK)
    begin
        if (CLK'event and CLK='1') then
            status_reg1 <= status_reg  - rd_num;
            status_reg2 <= status_reg1 - rd_num;

            if (in_reg1_en='1') then
                status_reg <= status_reg - rd_num + wr_num_reg1;
            else
                status_reg <= status_reg - rd_num;
            end if;

            if (RESET='1') then
                status_reg  <= (others => '0');
                status_reg1 <= (others => '0');
                status_reg2 <= (others => '0');
            end if;
        end if;
    end process;

    -- almost full / almost empty
    almost_reg_pr : process (CLK)
    begin

        if (CLK'event and CLK='1') then

            al_full_reg  <= '1' when (status_reg  + wr_num_reg1)>=AFULL_CAPACITY      else '0';
            al_empty_reg <= '1' when (status_reg2 - rd_num     )<=ALMOST_EMPTY_OFFSET else '0';

            if (RESET='1') then
                al_full_reg  <= '0';
                al_empty_reg <= '1';
            end if;
        end if;
    end process;

    AFULL  <= al_full_reg;
    AEMPTY <= al_empty_reg;

    -- -------------------------------------------------------------------------

    -- =========================================================================
    end generate;

end architecture;
