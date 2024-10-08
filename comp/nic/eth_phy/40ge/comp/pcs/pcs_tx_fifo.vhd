-- pcs_tx_fifo.vhd : FIFO for 40/100GBASE-R PCS - speed rate compensation, idle block
--                   dropping
-- Copyright (C) 2012-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity pcs_tx_fifo is
    generic (
        NUM_LANES : natural := 8;
        DEVICE    : string  := "ULTRASCALE" --! "VIRTEX6", "7SERIES", "ULTRASCALE"
   );
   port (
       RESET_D : in std_logic; -- D-clock reset
       CLK   : in std_logic; -- D clock
       D     : in std_logic_vector(NUM_LANES*66-1 downto 0);  -- Input data
       --
       RESET_Q : in std_logic; -- Q-clock reset
       TXCLK : in std_logic; -- Q clock
       RE    : in std_logic; -- Read enable
       Q     : out std_logic_vector(NUM_LANES*66-1 downto 0) := (others => '0');  -- Output data
       -- Debug
       FIFO_EMPTY_O : out std_logic;
       FIFO_FULL_O  : out std_logic;
       FIFO_AFULL_O : out std_logic;
       FIFO_DIN_O   : out std_logic_vector(NUM_LANES*66-1 downto 0);
       DROP_O       : out std_logic;
       INDEX_O      : out std_logic_vector(3 downto 0)
    );
end pcs_tx_fifo;

architecture behavioral of pcs_tx_fifo is

    signal discard       : std_logic;
    signal idle          : std_logic_vector(NUM_LANES-1 downto 0);
    signal term          : std_logic_vector(NUM_LANES-1 downto 0);
    signal fifo_din      : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal fifo_dout     : std_logic_vector(NUM_LANES*66-1 downto 0);
    signal fifo_wen      : std_logic;
    signal fifo_full     : std_logic;
    signal fifo_empty    : std_logic;
    signal fifo_ren      : std_logic;
    signal fifo_afull    : std_logic;
    signal fifo_aempty   : std_logic;
    signal idle_found    : std_logic;
    signal drop          : std_logic;
    signal drop_index    : natural range 0 to NUM_LANES-1;
    signal sh_din        : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal sh_drop       : std_logic;
    signal sh_index      : natural range 0 to NUM_LANES-1;
    signal fifo_re_delay : std_logic_vector(7 downto 0);

begin

    -- Detect IDLE control blocks
    IDLE_DETECT_LOGIC: process(D)
    begin
        idle_found <= '0';
        idle       <= (others => '0');
        -- Detect IDLE characters on individual lanes
        for i in 0 to NUM_LANES-1 loop
            if (D(1+i*66 downto i*66) = "01") and (D(9+i*66 downto i*66+2) = X"1E") then
                idle(i) <= '1';
                idle_found <= '1';
            else
                idle(i) <= '0';
            end if;
        end loop;
    end process;

    GEN_DROP_INDEX : process(idle)
    begin
        drop_index <= 0;
        for i in 0 to NUM_LANES-1 loop
            if idle(i) = '1' then
                drop_index <= i;
            end if;
        end loop;
    end process;

    drop <= discard and idle_found;

    TX_PIPE: process(CLK)
    begin
        if CLK'event and CLK = '1' then
            discard  <= fifo_afull;
            sh_din   <= D;
            sh_drop  <= drop;
            sh_index <= drop_index;
        end if;
    end process;

    GEN_MULTILANE_DROP: if (NUM_LANES > 1) generate
        BLOCK_DROP: entity work.block_shifter
        generic map (
            NUM_LANES => NUM_LANES
        )
        port map (
            RESET => RESET_D,
            CLK   => CLK,
            D     => sh_din,
            DROP  => sh_drop,
            IDX   => sh_index,
            INS   => '0',
            --
            Q_VAL => fifo_wen,
            Q     => fifo_din
        );
    end generate;

    GEN_SINGLELANE_DROP: if (NUM_LANES = 1) generate
        fifo_din <= sh_din;
        fifo_wen <= (not(sh_drop) or not(idle_found)) and not(fifo_full);
    end generate;

    ASFIFO: entity work.ASFIFO_BRAM_XILINX
    generic map (
        DEVICE                  => DEVICE,
        DATA_WIDTH              => 66*NUM_LANES,
        ITEMS                   => 512,
        FIRST_WORD_FALL_THROUGH => true,
        DO_REG                  => true,
        ALMOST_FULL_OFFSET      => 496,
        ALMOST_EMPTY_OFFSET     => 8
    )
    port map (
        CLK_WR   => CLK,
        RST_WR   => RESET_D,
        DI       => fifo_din,
        WR       => fifo_wen,
        AFULL    => fifo_afull,
        FULL     => fifo_full,
        --
        CLK_RD   => TXCLK,
        RST_RD   => RESET_Q,
        DO       => fifo_dout,
        RD       => fifo_ren,
        AEMPTY   => fifo_aempty,
        EMPTY    => fifo_empty
    );

    fifo_ren <= RE and fifo_re_delay(fifo_re_delay'high);

    OUT_REG: process(TXCLK)
    begin
        if TXCLK'event and TXCLK = '1' then
           if RE = '1' then
               Q <= fifo_dout;
           end if;
           -- Disable FIFO read after startup for 8 clock cycles
           if (fifo_empty = '1') then
               fifo_re_delay <= (others => '0');
           else
               fifo_re_delay <= fifo_re_delay(6 downto 0) & '1';
           end if;
        end if;
    end process;

    FIFO_FULL_O  <= fifo_full;
    FIFO_EMPTY_O <= fifo_empty;
    FIFO_AFULL_O <= fifo_afull;
    FIFO_DIN_O   <= fifo_din;
    DROP_O       <= sh_drop;
    INDEX_O      <= std_logic_vector(to_unsigned(sh_index,4));

end behavioral;
