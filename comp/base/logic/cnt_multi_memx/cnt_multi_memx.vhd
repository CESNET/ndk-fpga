-- cnt_multi_memx.vhd: Multi-channel MEMX counter
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Implements statistics counters for multiple Channels using MEMX.
entity CNT_MULTI_MEMX is
generic(
    -- Traget device
    DEVICE               : string  := "STRATIX10";

    -- Total number of Counter Channels
    CHANNELS             : natural := 8;

    -- Counter width
    CNT_WIDTH            : natural := 64;

    -- Increment width
    INC_WIDTH            : natural := 1;

    -- Size of input increments FIFO
    -- Set to 0 to remove the FIFO
    INC_FIFO_SIZE        : natural := 512
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================
    CLK          : in  std_logic;
    RESET        : in  std_logic;

    -- =====================================================================
    --  Other interfaces
    -- =====================================================================
    -- Counter Increment
    INC_CH       : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
    INC_VAL      : in  std_logic_vector(INC_WIDTH-1 downto 0);
    INC_VLD      : in  std_logic;
    INC_RDY      : out std_logic;

    -- Reset order
    RST_CH       : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
    RST_VLD      : in  std_logic;

    -- Read order: When RD_VLD='1' and RST_VLD='1' and RD_CH=RST_CH the old value (before reset)
    -- will appear on RD_VAL
    RD_CH        : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
    RD_VLD       : in  std_logic;
    RD_VAL       : out std_logic_vector(CNT_WIDTH-1 downto 0) -- 1 CLK latency
);
end entity;

architecture FULL of CNT_MULTI_MEMX is

    -- =====================================================================
    --  Constants, aliases, functions
    -- =====================================================================

    -- =====================================================================

    -- =====================================================================
    --  Increments FIFO
    -- =====================================================================

    signal inc_fifo_full   : std_logic;
    signal inc_fifo_do     : std_logic_vector(INC_WIDTH+log2(CHANNELS)-1 downto 0);
    signal inc_fifo_rd     : std_logic;
    signal inc_fifo_empty  : std_logic;
    signal inc_fifo_do_val : std_logic_vector(INC_WIDTH-1 downto 0);
    signal inc_fifo_do_ch  : std_logic_vector(log2(CHANNELS)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Counter MEMX
    -- =====================================================================

    signal memx_wr_data    : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal memx_wr_addr    : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal memx_wr_en      : std_logic;
    signal memx_rd_data    : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal memx_rd_addr    : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal memx_rd_pipe_en : std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Incrementation logic
    -- =====================================================================

    signal inc_reg_ch       : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal inc_reg          : std_logic_vector(INC_WIDTH-1 downto 0);
    signal inc_reg_vld      : std_logic;

    signal cnt_data         : std_logic_vector(CNT_WIDTH-1 downto 0);

    signal cnt_inc_reg_ch   : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal cnt_inc_reg      : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal cnt_inc_reg_inc  : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal cnt_inc_reg_vld  : std_logic;

    signal put_away_reg_ch  : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal put_away_reg     : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal put_away_reg_vld : std_logic;

    -- =====================================================================

begin

    -- =====================================================================
    --  Increments FIFO
    -- =====================================================================

    inc_fifo_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => INC_WIDTH+log2(CHANNELS),
        ITEMS               => INC_FIFO_SIZE           ,
        RAM_TYPE            => "AUTO"                  ,
        DEVICE              => DEVICE                  ,
        ALMOST_FULL_OFFSET  => 0                       ,
        ALMOST_EMPTY_OFFSET => 0                       ,
        FAKE_FIFO           => (INC_FIFO_SIZE=0)
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => INC_VAL & INC_CH,
        WR     => INC_VLD         ,
        FULL   => inc_fifo_full   ,
        AFULL  => open            ,
        STATUS => open            ,

        DO     => inc_fifo_do     ,
        RD     => inc_fifo_rd     ,
        EMPTY  => inc_fifo_empty  ,
        AEMPTY => open
    );

    INC_RDY <= not inc_fifo_full;

    inc_fifo_do_val <= inc_fifo_do(INC_WIDTH+log2(CHANNELS)-1 downto log2(CHANNELS));
    inc_fifo_do_ch  <= inc_fifo_do(log2(CHANNELS)-1 downto 0);

    -- Remove increment when niether Reset nor Read is requested
    inc_fifo_rd <= '1' when RST_VLD='0' and RD_VLD='0' else '0';

    -- =====================================================================

    -- =====================================================================
    --  Counter MEMX
    -- =====================================================================

    cnt_memx_i : entity work.SDP_MEMX
    generic map(
        DATA_WIDTH => CNT_WIDTH,
        ITEMS      => CHANNELS ,
        RAM_TYPE   => "AUTO"   ,
        DEVICE     => DEVICE   ,
        OUTPUT_REG => false
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        WR_DATA    => memx_wr_data   ,
        WR_ADDR    => memx_wr_addr   ,
        WR_EN      => memx_wr_en     ,

        RD_DATA    => memx_rd_data   ,
        RD_ADDR    => memx_rd_addr   ,
        RD_PIPE_EN => memx_rd_pipe_en
    );

    memx_wr_data <= (others => '0') when RST_VLD='1' else cnt_inc_reg;
    memx_wr_addr <= RST_CH          when RST_VLD='1' else cnt_inc_reg_ch;
    memx_wr_en   <= RST_VLD or cnt_inc_reg_vld;

    memx_rd_addr    <= RD_CH when RD_VLD='1' else inc_fifo_do_ch;
    memx_rd_pipe_en <= '1';

    RD_VAL <= memx_rd_data;

    -- =====================================================================

    -- =====================================================================
    --  Incrementation logic
    -- =====================================================================

    -- Increment is stored while data are being loaded from MEMX
    inc_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- If increment can be done
            if (RST_VLD='0') then
                inc_reg_ch  <= inc_fifo_do_ch;
                inc_reg     <= inc_fifo_do_val;
                inc_reg_vld <= (not inc_fifo_empty) and (not RD_VLD); -- data is only read from FIFO when RD_VLD='0'
            end if;

            if (RESET='1') then
                inc_reg_vld <= '0';
            end if;
        end if;
    end process;

    -- Incrementation is being done
    cnt_inc_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- If increment can be done
            if (RST_VLD='0') then
                -- Increment counter value
                cnt_inc_reg_ch  <= inc_reg_ch;
                cnt_inc_reg     <= std_logic_vector(unsigned(cnt_data) + resize(unsigned(inc_reg),CNT_WIDTH));
                cnt_inc_reg_inc <= std_logic_vector(resize(unsigned(inc_reg),CNT_WIDTH));
                cnt_inc_reg_vld <= inc_reg_vld;
            end if;

            -- If there is reset on this Channel
            if (RST_VLD='1' and RST_CH=cnt_inc_reg_ch) then
                -- Forget the old counter value, only count the increment
                cnt_inc_reg <= cnt_inc_reg_inc;
            end if;

            if (RESET='1') then
                cnt_inc_reg_vld <= '0';
            end if;
        end if;
    end process;

    -- Put away register for quick read
    -- Stores value, so it can be read in the next cycle
    put_away_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Remember new counter value written to MEMX
            put_away_reg_ch  <= cnt_inc_reg_ch;
            put_away_reg     <= cnt_inc_reg;
            put_away_reg_vld <= cnt_inc_reg_vld;

            -- If there is read on the incremented Channel
            if (RD_VLD='1') then
                -- Remember value about to be incremented
                put_away_reg_ch  <= inc_reg_ch;
                put_away_reg     <= cnt_data;
                put_away_reg_vld <= inc_reg_vld;
            end if;

            -- If there is reset on the incremented Channel
            if (RST_VLD='1' and RST_CH=inc_reg_ch) then
                -- Remember reset value written to MEMX
                put_away_reg_ch  <= RST_CH;
                put_away_reg     <= (others => '0');
                put_away_reg_vld <= '1';
            end if;

            if (RESET='1') then
                put_away_reg_vld <= '0';
            end if;
        end if;
    end process;

    -- Values written in MEMX in the previous 2 cycles cannot be read the classical way
    -- They are stored in put_away_reg and cnt_inc_reg.
    -- If they have the same Channel is this increment, use them instead. (read-after-write dependency bypass).
    cnt_data <= cnt_inc_reg  when cnt_inc_reg_vld ='1' and cnt_inc_reg_ch =inc_reg_ch else
                put_away_reg when put_away_reg_vld='1' and put_away_reg_ch=inc_reg_ch else memx_rd_data;

    -- =====================================================================

end architecture;
