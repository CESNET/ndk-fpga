-- pcs_rx_fifo.vhd : FIFO for 40/100GBASE-R PCS - rate compensation, idle block
--                    removing
-- Copyright (C) 2012-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity pcs_rx_fifo is
    generic (
        NUM_LANES : natural := 8;
        DEVICE    : string  := "ULTRASCALE" --! "VIRTEX6", "7SERIES", "ULTRASCALE"
    );
    port (
        RESET_D : in std_logic;
        CLK_D   : in std_logic; -- D clock
        WE      : in std_logic; -- Data write enable
        D       : in std_logic_vector(NUM_LANES*66-1 downto 0);  -- Input data
        --
        RESET_Q : in std_logic;
        CLK_Q   : in std_logic; -- Q clock
        Q       : out std_logic_vector(NUM_LANES*66-1 downto 0);  -- Output data
        -- Status
        FIFO_FULL  : out std_logic;
        FIFO_EMPTY : out std_logic;

        DBG_FIFO_AFULL  : out std_logic;
        DBG_FIFO_AEMPTY : out std_logic;
        DBG_FIFO_RDEN   : out std_logic
    );
end pcs_rx_fifo;

architecture behavioral of pcs_rx_fifo is

    signal discard      : std_logic;
    signal insert       : std_logic;
    signal idle0        : std_logic_vector(NUM_LANES-1 downto 0);
    signal idle         : std_logic_vector(NUM_LANES-1 downto 0);
    signal sh_din       : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal sh_drop      : std_logic;
    signal sh_val       : std_logic;
    signal sh_index     : natural range 0 to NUM_LANES-1;
    signal fifo_dout    : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal fifo_din     : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal fifo_dout_r  : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal fifo_ren     : std_logic;
    signal fifo_wen     : std_logic;
    signal emptying     : std_logic;
    signal fifo_full_i  : std_logic;
    signal fifo_empty_i : std_logic;
    signal fifo_afull   : std_logic;
    signal fifo_aempty  : std_logic;
    signal idle_found0  : std_logic;
    signal idle_found   : std_logic;
    signal drop         : std_logic;
    signal drop_index   : natural range 0 to NUM_LANES-1;
    signal insert_index : natural range 0 to NUM_LANES-1;
    signal d_dly        : std_logic_vector(NUM_LANES*66-1 downto 0);  -- Input data
    signal we_dly       : std_logic;

begin

    d_dly  <= D after 500 ps;
    we_dly <= WE after 500 ps;

    -- Idle drop logic  -----------------------------------------------------------
    IDLE_DETECT_DROP: process(d_dly)
    begin
        idle_found0 <= '0';
        -- Detect IDLE characters on individual lanes
        for i in 0 to NUM_LANES-1 loop
            if (d_dly(1+i*66 downto i*66) = "01") and (d_dly(9+i*66 downto i*66+2) = X"1E") then
                idle0(i) <= '1';
                idle_found0 <= '1';
            else
                idle0(i) <= '0';
            end if;
        end loop;
    end process;

    GEN_DROP_INDEX : process(idle0)
    begin
        drop_index <= 0;
        for i in 0 to NUM_LANES-1 loop
            if idle0(i) = '1' then
                drop_index <= i;
            end if;
        end loop;
    end process;

    drop <= discard and idle_found0;

    GEN_MULTILANE_DROP: if (NUM_LANES > 1) generate
        PIPE: process(CLK_D)
        begin
            if CLK_D'event and CLK_D = '1' then
                discard  <= fifo_afull;
                sh_din   <= d_dly;
                sh_drop  <= drop;
                sh_index <= drop_index;
                sh_val   <= we_dly;
            end if;
        end process;

        BLOCK_DROP: entity work.block_shifter
        generic map (
            NUM_LANES => NUM_LANES
        )
        port map (
            RESET => RESET_D,
            CLK   => CLK_D,
            D     => sh_din,
            D_VAL => sh_val,
            DROP  => sh_drop,
            IDX   => sh_index,
            INS   => '0',
            --
            Q_VAL => fifo_wen,
            Q     => fifo_din
        );
    end generate;

    GEN_SINGLELANE_DROP: if (NUM_LANES = 1) generate
        PIPE: process(CLK_D)
        begin
            if CLK_D'event and CLK_D = '1' then
                discard  <= fifo_afull;
                if (we_dly = '1') then
                    sh_din   <= d_dly;
                    sh_drop  <= drop;
                end if;
            end if;
        end process;

        fifo_din <= sh_din;
        fifo_wen <= we_dly and (not(sh_drop) or not(idle_found0)) and not(fifo_full_i);
    end generate;


    ASFIFO: entity work.ASFIFO_BRAM_XILINX
    generic map (
        DEVICE                  => DEVICE,
        DATA_WIDTH              => 66*NUM_LANES,
        ITEMS                   => 512,
        FIRST_WORD_FALL_THROUGH => true,
        DO_REG                  => true,
        ALMOST_FULL_OFFSET      => 492,
        ALMOST_EMPTY_OFFSET     => 8
    )
    port map (
        CLK_WR   => CLK_D,
        RST_WR   => RESET_D,
        DI       => fifo_din,
        WR       => fifo_wen,
        AFULL    => fifo_afull,
        FULL     => fifo_full_i,
        --
        CLK_RD   => CLK_Q,
        RST_RD   => RESET_Q,
        DO       => fifo_dout,
        RD       => fifo_ren,
        AEMPTY   => fifo_aempty,
        EMPTY    => fifo_empty_i
    );

    FIFO_FULL  <= fifo_full_i;
    FIFO_EMPTY <= fifo_empty_i;

    emptying <= fifo_aempty;

    -- Idle insert logic  --------------------------------------------------------
    IDLE_DETECT_INSERT: process(fifo_dout)
    begin
        idle_found <= '0';
        -- Detect IDLE characters on individual lanes
        for i in 0 to NUM_LANES-1 loop
            if (fifo_dout(1+i*66 downto i*66) = "01") and (fifo_dout(9+i*66 downto i*66+2) = X"1E") then
                idle(i) <= '1';
                idle_found <= '1';
            else
                idle(i) <= '0';
            end if;
        end loop;
    end process;

    PIPELINE: process(CLK_Q)
    begin
        if CLK_Q'event and CLK_Q = '1' then
            if fifo_ren = '1' then
                fifo_dout_r <= fifo_dout;
                insert <= emptying and idle_found;
                --
                insert_index <= 0;
                for i in 0 to NUM_LANES-1 loop
                    if idle(i) = '1' then
                        insert_index <= i;
                    end if;
                end loop;
            end if;
        end if;
    end process;

    GEN_MULTILANE_INSERT: if (NUM_LANES > 1) generate
        BLOCK_INSERT: entity work.block_shifter
        generic map (
            NUM_LANES => NUM_LANES
        )
        port map (
            RESET => RESET_Q,
            CLK   => CLK_Q,
            D     => fifo_dout_r,
            RE    => fifo_ren,
            DROP  => '0', --drop,
            INS   => insert,
            IDX   => insert_index,
            --
            Q_VAL => open,
            Q     => Q
        );
    end generate;

    GEN_SINGLELANE_INSERT: if (NUM_LANES = 1) generate
        fifo_ren <= '0' when ((insert = '1' and emptying = '1') or (fifo_empty_i = '1')) else '1';
        Q <= fifo_dout_r;
    end generate;

    DBG_FIFO_AFULL  <= fifo_afull;
    DBG_FIFO_AEMPTY <= fifo_aempty;
    DBG_FIFO_RDEN   <= fifo_ren;

end behavioral;
