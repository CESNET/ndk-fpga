-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity MI32_CONTROL is
   generic(
      NUM_BYTES_WD      : integer := 48;
      NUM_PACKETS_WD    : integer := 48;
      ADDRESS_WIDTH     : integer := 10
   );
   port(
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      --! MI32 interface
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_WR           : in  std_logic;
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_DRDY         : out std_logic;
      MI32_ARDY         : out std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);

      RM_ADDR           : out std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      RM_RD_ENABLE      : out std_logic;
      RM                : out std_logic;
      RM_ARDY           : in  std_logic;

      CNT_NUM_BYTES     : in  std_logic_vector(NUM_BYTES_WD-1 downto 0);
      CNT_NUM_PACKETS   : in  std_logic_vector(NUM_PACKETS_WD-1 downto 0);
      CNT_VLD           : in  std_logic;
      CNT_NEXT          : out std_logic
    );
end entity;

architecture full of MI32_CONTROL is
   constant num_regs_bytes    : integer := div_roundup(NUM_BYTES_WD, 32);
   constant num_regs_packets  : integer := div_roundup(NUM_PACKETS_WD, 32);
   constant num_regs          : integer := 3 + num_regs_bytes + num_regs_packets;
   constant log_regs          : integer := log2(num_regs);
   signal mux_rd              : std_logic_vector(32*num_regs-1 downto 0);

   signal rm_address          : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal next_req            : std_logic;
   signal bytes_reg           : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal packets_reg         : std_logic_vector(NUM_PACKETS_WD-1 downto 0);

   signal addr_wr             : std_logic;

begin

   MI32_ARDY <= MI32_RD or MI32_WR;
   MI32_DRDY <= MI32_RD;
   RM_RD_ENABLE <= '1';

   addr_wr <= MI32_WR when MI32_ADDR(log_regs+1 downto 2) = conv_std_logic_vector(0, log_regs) else
              '0';

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if(addr_wr = '1') then
           rm_address <= MI32_DWR(ADDRESS_WIDTH-1 downto 0);
         end if;
      end if;
   end process;
   RM_ADDR  <= rm_address;
   mux_rd(ADDRESS_WIDTH-1 downto 0) <= rm_address;
   mux_rd(31 downto ADDRESS_WIDTH) <= (others => '0');

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if RESET = '1' then
            RM <= '0';
         else
            if(addr_wr = '1') then
               RM <= '1';
            elsif(RM_ARDY = '1') then
               RM <= '0';
            end if;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if RESET = '1' then
            next_req <= '1';
         else
            if(addr_wr = '1') then
               next_req <= '0';
            elsif(CNT_VLD = '1') then
               next_req <= '1';
            end if;
         end if;
      end if;
   end process;
   mux_rd(32) <= next_req;
   mux_rd(32*2-1 downto 33) <= (others => '0');

   mux_rd(32*3-1 downto 32*2) <= conv_std_logic_vector(NUM_PACKETS_WD, 11) &
                                 conv_std_logic_vector(NUM_BYTES_WD, 11) &
                                 conv_std_logic_vector(ADDRESS_WIDTH, 10);

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if(CNT_VLD = '1') then
            bytes_reg   <= CNT_NUM_BYTES;
            packets_reg <= CNT_NUM_PACKETS;
         end if;
      end if;
   end process;
   CNT_NEXT <= '1';

   gen_bytes_regs : for I in 0 to num_regs_bytes-1 generate
      constant reg_range : integer := 32 * (I + 3 + 1);
   begin
      gen_others : if I < num_regs_bytes - 1 generate
         mux_rd(reg_range-1 downto reg_range-32) <= CNT_NUM_BYTES(32*(I+1)-1 downto 32*I);
      end generate;

      gen_last : if I = num_regs_bytes - 1 generate
         constant vld_bist  : integer := 32 - (num_regs_bytes * 32 - NUM_BYTES_WD);
      begin
         mux_rd(reg_range-1 downto reg_range - vld_bist) <= (others => '0');
         mux_rd(reg_range-vld_bist-1 downto reg_range-32) <= CNT_NUM_BYTES(CNT_NUM_BYTES'length-1 downto 32*I);
      end generate;
   end generate;

   gen_packets_regs : for I in 0 to num_regs_packets-1 generate
      constant reg_range : integer := 32 * (I + 3 + 1 + num_regs_bytes);
   begin
      gen_others : if I < num_regs_packets - 1 generate
         mux_rd(reg_range-1 downto reg_range-32) <= CNT_NUM_PACKETS(32*(I+1)-1 downto 32*I);
      end generate;

      gen_last : if I = num_regs_packets - 1 generate
         constant vld_bist  : integer := 32 - (num_regs_packets * 32 - NUM_PACKETS_WD);
      begin
         mux_rd(reg_range-1 downto reg_range - vld_bist) <= (others => '0');
         mux_rd(reg_range - vld_bist-1 downto reg_range-32) <= CNT_NUM_PACKETS(CNT_NUM_PACKETS'length-1 downto 32*I);
      end generate;
   end generate;

   mi_rd_mux : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 32,
      MUX_WIDTH   => num_regs
   )
   port map(
      DATA_IN     => mux_rd,
      SEL         => MI32_ADDR(log_regs+1 downto 2),
      DATA_OUT    => MI32_DRD
   );

end architecture;
