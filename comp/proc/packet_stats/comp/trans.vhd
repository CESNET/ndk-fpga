--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! \brief DSP slice ALU entity
entity TRANS_STATS is
   generic (
      PACKET_LENGTH_WD  : integer := 16;
      ADDRESS_WIDTH     : integer := 10
   );
   port (
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      RM_ADDRESS        : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      RM_RD_ENABLE      : in  std_logic;
      RM_REQ            : in  std_logic;

      IN_CNT_ADDRESS    : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      IN_PACKET_LENGTH  : in  std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      IN_ADD_PACKET     : in  std_logic;
      IN_SRC_RDY        : in  std_logic;
      IN_DST_RDY        : out std_logic;

      OUT_CNT_ADDRESS   : out std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      OUT_PACKET_LENGTH : out std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      OUT_ADD_PACKET    : out std_logic;
      OUT_RST_COUNTERS  : out std_logic
   );
end entity;

architecture FULL of TRANS_STATS is
begin

   IN_DST_RDY <= '1' when RM_REQ = '0' else
                 '0';

   OUT_CNT_ADDRESS <= IN_CNT_ADDRESS when RM_REQ = '0' else
                      RM_ADDRESS;

   OUT_PACKET_LENGTH <= IN_PACKET_LENGTH;

   process(RM_REQ, IN_SRC_RDY, IN_ADD_PACKET, RM_RD_ENABLE)
   begin
      OUT_ADD_PACKET <= '0';
      OUT_RST_COUNTERS <= '0';
      if(RM_REQ = '1') then
         if(RM_RD_ENABLE = '1') then
            OUT_ADD_PACKET <= '1';
         else
            OUT_ADD_PACKET <= '0';
         end if;
         OUT_RST_COUNTERS <= '1';
      elsif(IN_SRC_RDY = '1' and IN_ADD_PACKET = '1') then
         OUT_ADD_PACKET <= '1';
      end if;
   end process;

end architecture;
