--!
--! asfifo_bram.vhd: Asynchronous fifo from BlockRAM memories
--! Copyright (C) 2003 CESNET
--! Author(s): Martinek Tomas <martinek@liberouter.org>
--!            Martin Mikusek <martin.mikusek@liberouter.org>
--!            Jakub Cabal    <cabal@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!
--! TODO:
--!
--!
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! library containing log2 function
use work.math_pack.all;

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------

entity asfifo_bram is
    generic(
      --! ITEMS = Numer of items in FIFO
      --! !!!!!!!!!!! Must be (2^n), n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS          : integer := 512;

      --! Data Width
      DATA_WIDTH     : integer := 512;

      --! Width of status information of fifo fullness
      --! Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --!       than ITEMS
     STATUS_WIDTH    : integer := 4;
     RESET_DATA_PATH : boolean := true; --! Allow the output data register to be reset
     AUTO_PIPELINE   : boolean := false;

      -- additional status signal width (default must be 0, other option 1 when expressing status on log2(ITEMS+1) bits)
      STATUS_ADD_WIDTH : integer := 0
   );
   port (

      --! Write interface
      CLK_WR      : in  std_logic;
      RST_WR      : in  std_logic;
      WR          : in  std_logic;
      DI          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL        : out std_logic;
      STATUS      : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      --! Read interface
      CLK_RD      : in  std_logic;
      RST_RD      : in  std_logic;
      RD          : in  std_logic;
      DO          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_DV       : out std_logic;
      EMPTY       : out std_logic
   );
end asfifo_bram;

--! ----------------------------------------------------------------------------
--!                      Architecture declaration
--! ----------------------------------------------------------------------------

architecture behavioral of asfifo_bram is

   --! Number of address bits
   constant FADDR         : integer := LOG2(ITEMS);

   --! FIFO part signals
   signal rd_addr         : std_logic_vector(FADDR-1 downto 0);
   signal rd_bin          : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal rd_ptr          : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal sync_rd_ptr     : std_logic_vector(FADDR downto 0);
   signal sync_rd_ptr_bin    : std_logic_vector(FADDR downto 0);

   signal rd_bin_next     : std_logic_vector(FADDR downto 0);
   signal rd_gray_next    : std_logic_vector(FADDR downto 0);

   signal wr_addr         : std_logic_vector(FADDR-1 downto 0);
   signal wr_bin          : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal wr_ptr          : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal sync_wr_ptr     : std_logic_vector(FADDR downto 0);

   signal wr_bin_next     : std_logic_vector(FADDR downto 0);
   signal wr_gray_next    : std_logic_vector(FADDR downto 0);

   signal empty_signal    : std_logic := '1';
   signal full_signal     : std_logic := '0';

   signal write_allow     : std_logic;
   signal read_allow      : std_logic;

   signal sig_rd          : std_logic;
   signal sig_dv          : std_logic;

   signal status_signal      : std_logic_vector(FADDR-1 downto 0) := (others=>'0');
   signal status_signal_wide : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal status_signal_next : std_logic_vector(FADDR downto 0);

begin

   --! ------------------------------------------------------------------------
   --!                        Memory Control Part
   --! ------------------------------------------------------------------------

   memory : entity work.sdp_bmem(behavioral)
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      ITEMS       => ITEMS,
      OUTPUT_REG  => TRUE,
      RESET_DATA_PATH => RESET_DATA_PATH
   )
   port map(
      --! Interface A, will be used for writing only
      RSTA        => RST_WR,
      CLKA        => CLK_WR,
      WEA         => write_allow,
      ADDRA       => wr_addr,
      DIA         => DI,

      --! Interface B, will be used for reading only
      RSTB        => RST_RD,
      CLKB        => CLK_RD,
      PIPE_ENB    => sig_rd,
      REB         => read_allow,
      ADDRB       => rd_addr,
      DOB_DV      => sig_dv,
      DOB         => DO
   );

   --! ------------------------------------------------------------------------

   FULL   <= full_signal;
   EMPTY  <= empty_signal;
   DO_DV  <= sig_dv;

   write_allow <= (WR and not full_signal);
   read_allow <= (sig_rd and not empty_signal);

   cond_ap : if AUTO_PIPELINE = true generate
      sig_rd <= RD or not sig_dv;
   end generate;

   cond_nap : if AUTO_PIPELINE = false generate
      sig_rd <= RD;
   end generate;

   --! -------------------------------------------------------------
   --! Read pointer & empty generation logic
   --! -------------------------------------------------------------

   process (CLK_RD)
   begin
      if (rising_edge(CLK_RD)) then
         if (RST_RD = '1') then
            rd_bin <= (others=>'0');
            rd_ptr <= (others=>'0');
         else
            rd_bin <= rd_bin_next;
            rd_ptr <= rd_gray_next;
         end if;
      end if;
   end process;

   rd_bin_next <= rd_bin + read_allow;
   rd_addr <= rd_bin(FADDR-1 downto 0);

   process (rd_bin_next)
   begin
      --! binary to gray convertor
      rd_gray_next(FADDR) <= rd_bin_next(FADDR);
      for i in FADDR-1 downto 0 loop
         rd_gray_next(i) <= rd_bin_next(i+1) xor rd_bin_next(i);
      end loop;
   end process;

   --! empty flag generate
   process (CLK_RD)
   begin
      if (rising_edge(CLK_RD)) then
         if (RST_RD = '1') then
            empty_signal <= '1';
         elsif (rd_gray_next = sync_wr_ptr) then
            empty_signal <= '1';
         else
            empty_signal <= '0';
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------
   --! Write pointer & full generation logic
   --! -------------------------------------------------------------

   process (CLK_WR)
   begin
      if (rising_edge(CLK_WR)) then
         if (RST_WR = '1') then
            wr_bin <= (others=>'0');
            wr_ptr <= (others=>'0');
         else
            wr_bin <= wr_bin_next;
            wr_ptr <= wr_gray_next;
         end if;
      end if;
   end process;

   wr_bin_next <= wr_bin + write_allow;
   wr_addr <= wr_bin(FADDR-1 downto 0);

   process (wr_bin_next)
   begin
      --! binary to gray convertor
      wr_gray_next(FADDR) <= wr_bin_next(FADDR);
      for i in FADDR-1 downto 0 loop
         wr_gray_next(i) <= wr_bin_next(i+1) xor wr_bin_next(i);
      end loop;
   end process;

   --! full flag generate
   process (CLK_WR)
   begin
      if (rising_edge(CLK_WR)) then
         if (RST_WR = '1') then
            full_signal <= '0';
         elsif (wr_gray_next = ( NOT sync_rd_ptr(FADDR downto FADDR-1) & sync_rd_ptr(FADDR-2 downto 0) )) then
            full_signal <= '1';
         else
            full_signal <= '0';
         end if;
      end if;
   end process;

   --! -------------------------------------------------------------
   --! ASYNC_OPEN_LOOP_SMD synchronization
   --! -------------------------------------------------------------

   --! ASYNC_OPEN_LOOP_SMD for read pointer
   ASYNC_OPEN_LOOP_SMD_RD: entity work.ASYNC_OPEN_LOOP_SMD
   generic map(
      DATA_WIDTH => FADDR+1
   )
   port map(
      ACLK     => CLK_RD,
      BCLK     => CLK_WR,
      ARST     => RST_RD,
      BRST     => RST_WR,
      ADATAIN  => rd_ptr,
      BDATAOUT => sync_rd_ptr
   );

   --! ASYNC_OPEN_LOOP_SMD for write pointer
   ASYNC_OPEN_LOOP_SMD_WR: entity work.ASYNC_OPEN_LOOP_SMD
   generic map(
      DATA_WIDTH => FADDR+1
   )
   port map(
      ACLK     => CLK_WR,
      BCLK     => CLK_RD,
      ARST     => RST_WR,
      BRST     => RST_RD,
      ADATAIN  => wr_ptr,
      BDATAOUT => sync_wr_ptr
   );

   --! -------------------------------------------------------------
   --! Status register
   --! -------------------------------------------------------------

   --! transformation to binary format
   sync_rd_ptr_bin(FADDR) <= sync_rd_ptr(FADDR);

   sync_rd_ptr_bin_gen : for i in FADDR-1 downto 0 generate
      sync_rd_ptr_bin(i) <= sync_rd_ptr_bin(i+1) xor sync_rd_ptr(i);
   end generate;

   status_signal <= status_signal_next(FADDR-1 downto 0);
   status_signal_wide <= status_signal_next(FADDR downto 0);
   status_signal_next <= wr_bin_next - sync_rd_ptr_bin;

   wide_status_signal_gen : if (STATUS_ADD_WIDTH=1) generate
      STATUS <= status_signal_wide(FADDR downto FADDR+1-STATUS_WIDTH); --! we use only few MSB bits
   end generate;

   small_status_signal_gen : if (STATUS_ADD_WIDTH=0) generate
      STATUS <= status_signal(FADDR-1 downto FADDR-STATUS_WIDTH); --! we use only few MSB bits
   end generate;

end architecture behavioral;
