-- avst_loop.vhd: Loopback for Intel E-Tile AVST Interface
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

entity avst_loop is
generic (
    SEGMENTS : natural := 1 --  segment width is 64 bits
);
port (
    RST              : in  std_logic;
    CLK              : in  std_logic;
    --
    IN_AVST_DATA     : in  std_logic_vector(SEGMENTS*64-1 downto 0);
    IN_AVST_SOP      : in  std_logic;
    IN_AVST_EOP      : in  std_logic;
    IN_AVST_EMPTY    : in  std_logic_vector(log2(SEGMENTS*8)-1 downto 0); -- 3 or 6 bit
    IN_AVST_VALID    : in  std_logic;

    -- OUTPUT AVST INTERFACE (Intel E-Tile Ethernet IP)
    TX_AVST_DATA     : out std_logic_vector(SEGMENTS*64-1 downto 0);
    TX_AVST_SOP      : out std_logic;
    TX_AVST_EOP      : out std_logic;
    TX_AVST_EMPTY    : out std_logic_vector(log2(SEGMENTS*8)-1 downto 0);
    TX_AVST_VALID    : out std_logic;
    TX_AVST_READY    : in  std_logic
 );
end entity;


architecture full of  avst_loop is

constant FIFO_WIDTH  : natural := SEGMENTS*64 + 1 + 1 + 1 + log2(SEGMENTS*8);
constant C_IDLE_GAP  : natural := 0;

signal fifo_din       : std_logic_vector(FIFO_WIDTH-1 downto 0);
signal fifo_do        : std_logic_vector(FIFO_WIDTH-1 downto 0);
signal fifo_afull     : std_logic;
signal fifo_aempty    : std_logic;
signal fifo_wr        : std_logic;
signal fifo_rd        : std_logic;
signal fifo_rd_en     : std_logic;
signal fifo_wr_skip   : std_logic;
signal fifo_rd_skip   : std_logic;
signal in_mac_idle    : std_logic;
signal in_mac_idle_r  : std_logic;
signal out_mac_idle   : std_logic;
signal out_mac_idle_r : std_logic;
signal eof_idles      : std_logic;
signal inframe_r      : std_logic;
signal in_mac_inframe : std_logic;
signal mask_in        : std_logic_vector(SEGMENTS-1 downto 0);

begin

    fifo_din  <= IN_AVST_EMPTY & IN_AVST_EOP & IN_AVST_SOP & IN_AVST_VALID & IN_AVST_DATA;

    in_idle_reg: process(CLK)
    begin
        if rising_edge(CLK) then
            in_mac_idle_r <= in_mac_idle or eof_idles;
            if RST = '1' then
                inframe_r <= '0';
            elsif IN_AVST_EOP = '1' and IN_AVST_VALID = '1' then
                inframe_r <= '0';
            elsif IN_AVST_SOP = '1' and IN_AVST_VALID = '1' then
                inframe_r <= '1';
            end if;
        end if;
    end process;

    in_mac_inframe <= (IN_AVST_SOP and IN_AVST_VALID) or inframe_r;
    in_mac_idle    <= not in_mac_inframe;
    eof_idles      <= '1' when (IN_AVST_EOP = '1' and IN_AVST_VALID = '1') and (to_integer(unsigned(IN_AVST_EMPTY)) >= C_IDLE_GAP) else '0';
    fifo_wr_skip   <= in_mac_idle and in_mac_idle_r and fifo_afull;
    fifo_wr        <= ((not in_mac_inframe) and (not fifo_wr_skip)) or (in_mac_inframe and IN_AVST_VALID);

    fifo_i: entity work.FIFOX
    generic map (
        DATA_WIDTH          => FIFO_WIDTH,
        ITEMS               => 64,
        RAM_TYPE            => "BRAM",
        ALMOST_FULL_OFFSET  => 48,
        ALMOST_EMPTY_OFFSET => 8,
        DEVICE              => "AGILEX"
    )
    port map (
        CLK    => CLK,
        RESET  => RST,
        DI     => fifo_din,
        WR     => fifo_wr,
        FULL   => open,
        AFULL  => fifo_afull,
        STATUS => open,
        DO     => fifo_do,
        RD     => fifo_rd,
        EMPTY  => open,
        AEMPTY => fifo_aempty
    );

   fifo_rd_p: process(CLK)
   begin
       if rising_edge(CLK) then
           if RST = '1' then
               fifo_rd_en <= '0';
           elsif fifo_aempty = '0' then
               fifo_rd_en <= '1';
           end if;
       end if;
   end process;

   out_idle_reg: process(CLK)
   begin
       if rising_edge(CLK) then
            out_mac_idle_r <= not TX_AVST_VALID;
       end if;
   end process;

   fifo_rd <= TX_AVST_READY and fifo_rd_en and (not fifo_rd_skip);

   out_mac_idle <= not TX_AVST_VALID;
   fifo_rd_skip <= out_mac_idle and out_mac_idle_r and fifo_aempty;

   TX_AVST_DATA  <= fifo_do(TX_AVST_DATA'high downto 0);
   TX_AVST_VALID <= fifo_do(TX_AVST_DATA'high+1);
   TX_AVST_SOP   <= fifo_do(TX_AVST_DATA'high+2);
   TX_AVST_EOP   <= fifo_do(TX_AVST_DATA'high+3);
   TX_AVST_EMPTY <= fifo_do(TX_AVST_DATA'high+TX_AVST_EMPTY'length+3 downto TX_AVST_DATA'high+4);

end architecture;
