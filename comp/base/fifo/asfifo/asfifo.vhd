--!
--! asfifo: Asynchronous FIFO from LUTs
--! Copyright (C) 2003 CESNET
--! Author(s): Martinek Tomas <martinek@liberouter.org>
--!            Martin Mikusek <martin.mikusek@liberouter.org>
--!            Jakub Cabal    <jakubcabal@gmail.com>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!
--! TODO:
--!
--!
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! library containing log2 function
use work.math_pack.all;

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------
entity asfifo is
   generic(
      --! Data Width
      DATA_WIDTH  : integer := 16;
      --! Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer := 16;
      --! Width of status information of fifo fullness
      --! Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --!       than ITEMS
      STATUS_WIDTH : integer := 4
   );
   port(
      --! Write interface
      CLK_WR   : in  std_logic;
      RST_WR   : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      WR       : in  std_logic;
      FULL     : out std_logic;
      STATUS   : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      --! Read interface
      CLK_RD   : in  std_logic;
      RST_RD   : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD       : in  std_logic;
      EMPTY    : out std_logic
   );
end entity asfifo;

--! ----------------------------------------------------------------------------
--!                      Architecture declaration
--! ----------------------------------------------------------------------------

architecture behavioral of asfifo is

   --! Number of address bits
   constant FADDR         : integer := LOG2(ITEMS);

   --! FIFO part signals
   signal rd_data         : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal rd_addr         : std_logic_vector(FADDR-1 downto 0);
   signal rd_bin          : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal rd_ptr          : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal sync_rd_ptr     : std_logic_vector(FADDR downto 0);
   signal sync_rd_ptr_bin : std_logic_vector(FADDR downto 0);

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

   signal out_reg_we      : std_logic;
   signal reg_rd_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_empty       : std_logic;

   signal status_signal      : std_logic_vector(FADDR downto 0) := (others=>'0');
   signal status_signal_next : std_logic_vector(FADDR downto 0);

--! ------------------------------------------------------------------------
begin
--! ------------------------------------------------------------------------

   --! ------------------------------------------------------------------------
   --!                       Memory Instantion
   --! ------------------------------------------------------------------------

   MEM_U : entity work.sdp_distmem
   generic map(
      DATA_WIDTH   => DATA_WIDTH,
      ITEMS        => ITEMS
   )
   port map(
      WCLK       => CLK_WR,
      ADDRA      => wr_addr,
      DI         => DI,
      WE         => write_allow,
      ADDRB      => rd_addr,
      DOB        => rd_data
   );

   write_allow <= (WR AND NOT full_signal);
   --! allow reading data from the memory
   --!    when reading and both the memory and the output registers are not empty OR
   --!    when the memory is not empty while the output registers are empty
   read_allow  <= (RD AND NOT empty_signal AND NOT reg_empty) OR
                  (NOT empty_signal AND reg_empty);

   FULL   <= full_signal;

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
         else
            wr_bin <= wr_bin_next;
         end if;
         wr_ptr <= wr_gray_next;
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

   --! ------------------------------------------------------------------------
   --! Output registers
   --! ------------------------------------------------------------------------

   --! write enable signal for output registers
   --!    when reading from the memory OR
   --!    when reading data from registers only while the memory is empty
   out_reg_we <= read_allow OR
                 (RD AND empty_signal AND NOT reg_empty);

   --! output data register
   reg_rd_data_p : process(CLK_RD)
   begin
      if (rising_edge(CLK_RD)) then
         if (out_reg_we = '1') then
            reg_rd_data <= rd_data;
         end if;
      end if;
   end process reg_rd_data_p;

   --! output empty register
   reg_empty_p : process(CLK_RD)
   begin
      if (rising_edge(CLK_RD)) then
         if (RST_RD = '1') then
            reg_empty <= '1';
         elsif (out_reg_we = '1') then
            reg_empty <= empty_signal;
         end if;
      end if;
   end process reg_empty_p;

   --! driving output ports
   DO    <= reg_rd_data;
   EMPTY <= reg_empty;

   --! -------------------------------------------------------------
   --! Status register
   --! -------------------------------------------------------------

   --! transformation to binary format
   sync_rd_ptr_bin(FADDR) <= sync_rd_ptr(FADDR);
   sync_rd_ptr_bin_gen : for i in FADDR-1 downto 0 generate
      sync_rd_ptr_bin(i) <= sync_rd_ptr_bin(i+1) xor sync_rd_ptr(i);
   end generate;

   --! generate STATUS signal
   status_signal <= status_signal_next;
   status_signal_next <= wr_bin_next - sync_rd_ptr_bin;
   STATUS <= status_signal(FADDR-1 downto FADDR-STATUS_WIDTH); -- we use only few MSB bits

end architecture behavioral;
