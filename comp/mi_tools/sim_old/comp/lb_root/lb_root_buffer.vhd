--
-- lb_root_buffer.vhd: Local Bus Root Buffer
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- TODO : add blockram fifo - root can get stucked

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ROOT_BUFFER is
   generic(
      BASE_ADDR       : std_logic_vector(31 downto 0);
      ADDR_WIDTH      : integer
   );
   port(
      -- Common Interface
      CLK             : in std_logic;
      RESET           : in std_logic;

      -- Write Interface
      ADDR_WR         : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      DWR             : in  std_logic_vector(63 downto 0);
      BE_WR           : in  std_logic_vector(7 downto 0);
      WR              : in  std_logic;
      RDY_WR          : out std_logic;
      SOF_WR          : in  std_logic;
      EOF_WR          : in  std_logic;

      -- Read Interface
      ADDR_RD         : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      BE_RD           : in  std_logic_vector(7  downto 0);
      DRD             : out std_logic_vector(63 downto 0);
      RD              : in  std_logic;
      ARDY_RD         : out std_logic;
      DRDY_RD         : out std_logic;
      ERDY_RD         : in  std_logic;
      SOF_RD          : in  std_logic;
      EOF_RD          : in  std_logic;

      -- Root Core Interface
      BUFFER_ADDR     : out std_logic_vector(31 downto 0);
      BUFFER_SOF      : out std_logic;
      BUFFER_EOF      : out std_logic;
      BUFFER_DATA     : out std_logic_vector(63 downto 0);
      BUFFER_BE       : out std_logic_vector(7 downto 0);
      BUFFER_RD       : out std_logic;
      BUFFER_WR       : out std_logic;
      BUFFER_VLD      : out std_logic;
      BUFFER_NEXT     : in  std_logic;
      BUFFER_DRD      : in  std_logic_vector(63 downto 0);
      BUFFER_DRDY     : in  std_logic;
      BUFFER_DRD_LAST : in  std_logic
  );
end entity LB_ROOT_BUFFER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ROOT_BUFFER_ARCH of LB_ROOT_BUFFER is

     -- Multiplexors
     signal addr_mux_sel            : std_logic_vector(1 downto 0);
     signal addr_mux                : std_logic_vector(ADDR_WIDTH-1 downto 0);
     signal be_mux                  : std_logic_vector(7 downto 0);

     signal sof                     : std_logic;
     signal eof                     : std_logic;

     -- transaction buffer
     signal transaction_buffer_din   : std_logic_vector(ADDR_WIDTH+75 downto 0);
     signal transaction_buffer_wr    : std_logic;
     signal transaction_buffer_full  : std_logic;
     signal transaction_buffer_dout  : std_logic_vector(ADDR_WIDTH+75 downto 0);
     signal transaction_buffer_rd    : std_logic;
     signal transaction_buffer_empty : std_logic;

     -- drd_buffer
     signal drd_buffer_wr           : std_logic;
     signal drd_buffer_di           : std_logic_vector(64 downto 0);
     signal drd_buffer_rd           : std_logic;
     signal drd_buffer_do           : std_logic_vector(64 downto 0);
     signal drd_buffer_vld          : std_logic;
     signal drd_buffer_empty        : std_logic;

     -- drd flag
     signal drd_last_flag           : std_logic;
     signal drd_last_flag_set       : std_logic;
     signal drd_last_flag_rst       : std_logic;



begin

-- ib2adc out interface mapping
--RDY_WR        <= WR and BUFFER_NEXT;
--ARDY_RD       <= RD and BUFFER_NEXT;

--BUFFER_ADDR   <= BASE_ADDR(31 downto ADDR_WIDTH) & addr_mux;
--BUFFER_DATA   <= DWR;
--BUFFER_BE     <= be_mux;
--BUFFER_WR     <= WR;
--BUFFER_RD     <= RD;
--BUFFER_SOF    <= SOF_RD or SOF_WR;
--BUFFER_EOF    <= EOF_RD or EOF_WR;
--BUFFER_VLD    <= RD or WR;


addr_mux_sel(0) <= WR;
addr_mux_sel(1) <= '1' when (be_mux(3 downto 0) = "0000") else '0';

-- multiplexor addr_mux ------------------------------------------------------
addr_muxp: process(addr_mux_sel, ADDR_RD, ADDR_WR)
begin
    case addr_mux_sel is
       when "00" => addr_mux <= ADDR_RD;
       when "01" => addr_mux <= ADDR_WR;
       when "10" => addr_mux <= ADDR_RD+X"4";
       when "11" => addr_mux <= ADDR_WR+X"4";
       when others => addr_mux <= (others => 'X');
    end case;
end process;

-- multiplexor be_mux --------------------------------------------------------
be_muxp: process(WR, BE_RD, BE_WR)
begin
    case WR is
       when '0' => be_mux <= BE_RD;
       when '1' => be_mux <= BE_WR;
       when others => be_mux <= (others => 'X');
    end case;
end process;


-- -----------------------------------------------------------------------------
--  Transaction buffer
-- -----------------------------------------------------------------------------

RDY_WR        <= WR and not transaction_buffer_full;
ARDY_RD       <= RD and not transaction_buffer_full;

sof                    <= SOF_RD or SOF_WR;
eof                    <= EOF_RD or EOF_WR;
transaction_buffer_din <= addr_mux &  DWR & be_mux & RD & WR & sof & eof;
transaction_buffer_wr  <= RD or WR;
transaction_buffer_rd  <= BUFFER_NEXT;

BUFFER_ADDR   <= BASE_ADDR(31 downto ADDR_WIDTH) & transaction_buffer_dout(ADDR_WIDTH+75 downto 76);
BUFFER_DATA   <= transaction_buffer_dout(75 downto 12);
BUFFER_BE     <= transaction_buffer_dout(11 downto 4);
BUFFER_RD     <= transaction_buffer_dout(3);
BUFFER_WR     <= transaction_buffer_dout(2);
BUFFER_SOF    <= transaction_buffer_dout(1);
BUFFER_EOF    <= transaction_buffer_dout(0);
BUFFER_VLD    <= not transaction_buffer_empty;

-- ----------------------------------------------------------------
transaction_buffer : entity work.FIFO
   generic map (
      ITEMS        => 64,
      DATA_WIDTH   => ADDR_WIDTH+76
   )
   port map (
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,
      -- Write interface
      DATA_IN     => transaction_buffer_din,
      WRITE_REQ   => transaction_buffer_wr,
      FULL        => transaction_buffer_full,
      LSTBLK      => open,

      -- Read interface
      DATA_OUT    => transaction_buffer_dout,
      READ_REQ    => transaction_buffer_rd,
      EMPTY       => transaction_buffer_empty
   );
-- -----------------------------------------------------------------------------
--  DRD buffer
-- -----------------------------------------------------------------------------


-- register drd_last_flag ------------------------------------------------------
drd_last_flagp: process(RESET, CLK)
begin
   if (RESET = '1') then
      drd_last_flag <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (drd_last_flag_set = '1') then
         drd_last_flag <= '1';
      end if;
      if (drd_last_flag_rst = '1') then
         drd_last_flag <= '0';
      end if;
   end if;
end process;


drd_buffer_di     <= BUFFER_DRD_LAST & BUFFER_DRD;
drd_buffer_wr     <= BUFFER_DRDY;
drd_buffer_rd     <= drd_last_flag and ERDY_RD;
drd_last_flag_set <= BUFFER_DRD_LAST;
drd_last_flag_rst <= drd_buffer_do(64) and drd_buffer_vld and ERDY_RD;
DRD               <= drd_buffer_do(63 downto 0);
DRDY_RD           <= drd_buffer_vld and drd_last_flag;


-- ----------------------------------------------------------------
drd_buffer : entity work.FIFO
   generic map (
      ITEMS        => 64,
      DATA_WIDTH   => 65
   )
   port map (
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,
      -- Write interface
      DATA_IN     => drd_buffer_di,
      WRITE_REQ   => drd_buffer_wr,
      FULL        => open,
      LSTBLK      => open,

      -- Read interface
      DATA_OUT    => drd_buffer_do,
      READ_REQ    => drd_buffer_rd,
      EMPTY       => drd_buffer_empty
   );

drd_buffer_vld <= not drd_buffer_empty;


end architecture LB_ROOT_BUFFER_ARCH;
