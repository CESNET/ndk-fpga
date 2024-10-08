--
-- ib_endpoint_op_done_buffer.vhd: Internal Bus Busmaster Operation Done Buffer
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_OP_DONE_BUFFER is
   port(
      -- ========================
      -- Common Interface
      -- ========================

      CLK              : in  std_logic;
      RESET            : in  std_logic;

      -- =======================================
      -- IB_Endpoint Input Interface
      --
      -- Listening for completition transactions
      -- =======================================

      RD_COMPL_TAG     : in  std_logic_vector(15 downto 0);
      -- Read completition transaction goes for processing
      RD_COMPL_START   : in  std_logic;
      -- Write/completition transaction is done
      RD_COMPL_DONE    : in  std_logic;
      -- BM Tag
      BM_TAG           : in  std_logic_vector(15 downto 0);
      BM_DONE          : in  std_logic;

      -- ========================
      -- OP Done Interface
      -- ========================

      -- Busmaster Tag
      OP_TAG           : out std_logic_vector(15 downto 0);
      -- BM completition transaction recived
      OP_DONE          : out std_logic
      );
end entity IB_ENDPOINT_OP_DONE_BUFFER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_OP_DONE_BUFFER_ARCH of IB_ENDPOINT_OP_DONE_BUFFER is

      signal tag_reg               : std_logic_vector(15 downto 0);
      signal bm_tag_reg            : std_logic_vector(15 downto 0);
      signal bm_tag_vld            : std_logic;
      signal rd_compl_start_reg    : std_logic;
      signal local_op_done         : std_logic;
      signal tag_mux               : std_logic_vector(15 downto 0);

begin

OP_TAG           <= tag_mux;
local_op_done    <= RD_COMPL_DONE and rd_compl_start_reg;
OP_DONE          <= bm_tag_vld or local_op_done;

-- multiplexor tag_mux ------------------------------------------------------
tag_muxp: process(local_op_done, tag_reg, bm_tag_reg)
begin
   case local_op_done is
      when '0' => tag_mux <= bm_tag_reg;
      when '1' => tag_mux <= tag_reg;
      when others => tag_mux <= (others => 'X');
   end case;
end process;


-- register rd_compl_start_reg ------------------------------------------------------
rd_compl_start_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      rd_compl_start_reg <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (RD_COMPL_START = '1') then
         rd_compl_start_reg <= '1';
      end if;
      if (RD_COMPL_DONE = '1') then
         rd_compl_start_reg <= '0';
      end if;
   end if;
end process;


-- register tag_reg -----------------------------------------------------------------
tag_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      tag_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (RD_COMPL_START='1') then
         tag_reg <= RD_COMPL_TAG;
      end if;
   end if;
end process;

-- register bm_tag_reg -----------------------------------------------------------------
bm_tag_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      bm_tag_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (BM_DONE = '1') then
         bm_tag_reg <= BM_TAG;
      end if;
   end if;
end process;

-- register bm_tag_vld -----------------------------------------------------------------
bm_tag_vldp: process(RESET, CLK)
begin
   if (RESET = '1') then
      bm_tag_vld <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (BM_DONE = '1') then
         bm_tag_vld <= '1';
      elsif (local_op_done = '0') then
         bm_tag_vld <= '0';
      end if;
   end if;
end process;


end architecture IB_ENDPOINT_OP_DONE_BUFFER_ARCH;

