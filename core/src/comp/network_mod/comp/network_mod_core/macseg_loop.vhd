-- macseg_loop.vhd: Loopback for Intel F-Tile MAC Segmented Interface
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity macseg_loop is
generic (
    SEGMENTS : natural := 16
);
port (
    RST              : in  std_logic;
    CLK              : in  std_logic;
    --
    IN_MAC_DATA      : in  std_logic_vector(SEGMENTS*64-1 downto 0);
    IN_MAC_INFRAME   : in  std_logic_vector(SEGMENTS-1 downto 0);
    IN_MAC_EOP_EMPTY : in  std_logic_vector(SEGMENTS*3-1 downto 0);
    IN_MAC_VALID     : in  std_logic;
    -- OUTPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
    OUT_MAC_DATA      : out std_logic_vector(SEGMENTS*64-1 downto 0);
    OUT_MAC_INFRAME   : out std_logic_vector(SEGMENTS-1 downto 0);
    OUT_MAC_EOP_EMPTY : out std_logic_vector(SEGMENTS*3-1 downto 0);
    OUT_MAC_ERROR     : out std_logic_vector(SEGMENTS-1 downto 0);
    OUT_MAC_VALID     : out std_logic;
    OUT_MAC_READY     : in  std_logic
 );
end entity;


architecture full of macseg_loop is

constant FIFO_WIDTH  : natural := SEGMENTS*(64 + 1 + 3);
constant EFIFO_WIDTH : natural := SEGMENTS*64;

signal efifo_din      : std_logic_vector(EFIFO_WIDTH-1 downto 0);
signal efifo_do       : std_logic_vector(EFIFO_WIDTH-1 downto 0);
signal efifo_aux_din  : std_logic_vector((SEGMENTS*64/8)-1 downto 0);
signal efifo_aux_do   : std_logic_vector((SEGMENTS*64/8)-1 downto 0);

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
signal mask_in        : std_logic_vector(IN_MAC_INFRAME'range);

begin

    fifo_din     <= IN_MAC_EOP_EMPTY & IN_MAC_INFRAME & IN_MAC_DATA;

    in_idle_reg: process(CLK)
    begin
        if rising_edge(CLK) then
            if IN_MAC_VALID = '1' then
                in_mac_idle_r <= not IN_MAC_INFRAME(IN_MAC_INFRAME'high);
            end if;
        end if;
    end process;

    in_mac_idle  <= not (or IN_MAC_INFRAME);
    fifo_wr_skip <= in_mac_idle and in_mac_idle_r and fifo_afull;
    fifo_wr      <= IN_MAC_VALID and (not fifo_wr_skip);

    fifo_i: entity work.FIFOX
    generic map (
        DATA_WIDTH          => FIFO_WIDTH,
        ITEMS               => 64,
        RAM_TYPE            => "BRAM",
        ALMOST_FULL_OFFSET  => 6,
        ALMOST_EMPTY_OFFSET => 48,
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
           if OUT_MAC_READY = '1' then
               out_mac_idle_r <= not OUT_MAC_INFRAME(OUT_MAC_INFRAME'high);
           end if;
       end if;
   end process;

   fifo_rd <= (OUT_MAC_READY and fifo_rd_en) and (not fifo_rd_skip);

   out_mac_idle <= not (or OUT_MAC_INFRAME);
   fifo_rd_skip <= out_mac_idle and out_mac_idle_r and fifo_aempty;

   OUT_MAC_DATA      <= fifo_do(IN_MAC_DATA'high downto 0);
   OUT_MAC_INFRAME   <= fifo_do(IN_MAC_DATA'high+SEGMENTS downto IN_MAC_DATA'high+1);
   OUT_MAC_EOP_EMPTY <= fifo_do(FIFO_WIDTH-1 downto IN_MAC_DATA'high+SEGMENTS+1);
   OUT_MAC_ERROR     <= (others => '0');

    -----------------------------------------------------------
    -- Elastic FIFO implementation - TBD
    --  (consumes a lot of resources)
    -----------------------------------------------------------

    -- efifo_din_g: for i in 0 to SEGMENTS-1 generate
    --     efifo_din(64*i+63   downto 64*i)   <= IN_MAC_DATA(64*i+63 downto 64*i);
    --     efifo_aux_din(8*i)                 <= IN_MAC_INFRAME(i);
    --     efifo_aux_din(8*i+7 downto 8*i+1)  <= "0000" & IN_MAC_EOP_EMPTY(i*3+2 downto i*3);
    -- end generate;

    -- mask_in(0) <= in_mac_idle_r and (not IN_MAC_INFRAME(0));
    -- --mask_in_g: if mask_in'high > 0 generate
    --     mask_in(mask_in'high downto 1) <= not IN_MAC_INFRAME(mask_in'high downto 1);
    -- --end generate;

    -- efifo_i: entity work.ELASTIC_FIFO
    -- generic map (
    --     FIFO_ITEMS          => 64,
    --     FIFO_RAM_TYPE       => "BRAM",
    --     DEVICE              => "AGILEX",
    --     ALMOST_FULL_OFFSET  => 16,
    --     ALMOST_EMPTY_OFFSET => 48,
    --     BLOCK_WIDTH         => 64,
    --     BLOCK_COUNT         => SEGMENTS,
    --     OUTPUT_REGISTERS    => true
    -- )
    -- port map (
    --     WR_CLK              => CLK,
    --     WR_CE               => IN_MAC_VALID,
    --     RD_CLK              => CLK,
    --     RD_CE               => OUT_MAC_READY,
    --     AS_RST              => RST,
    --     -- Data input, containing blocks
    --     DIN                 => efifo_din,
    --     AUX_IN              => efifo_aux_din,
    --     MASK_IN             => mask_in,
    --     --
    --     DOUT                => efifo_do,
    --     AUX_OUT             => efifo_aux_do
    -- );

    -- OUT_MAC_ERROR     <= (others => '0');

    -- efifo_aux_do_g: for i in 0 to SEGMENTS-1 generate
    --     OUT_MAC_DATA(i*64+63 downto i*64)   <= efifo_do(64*i+63   downto 64*i);
    --     OUT_MAC_INFRAME(i)                  <= efifo_aux_do(8*i);
    --     OUT_MAC_EOP_EMPTY(i*3+2 downto i*3) <= efifo_aux_do(8*i+3 downto 8*i+1);
    -- end generate;

    -- ----------------------------------
    mac_valid_p: process (CLK)
    begin
        if rising_edge(CLK) then
            OUT_MAC_VALID <= OUT_MAC_READY;
            if (RST = '1') then
                OUT_MAC_VALID <= '0';
            end if;
        end if;
    end process;

end architecture;
