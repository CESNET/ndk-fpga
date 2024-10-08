--
-- lb_endpoint_hdr_gen_slave.vhd: Internal Bus Header Generator Slave
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
entity IB_ENDPOINT_HDR_GEN_SLAVE is
   port (
      -- ========================
      -- Header Data
      -- ========================

      RD_COMPL_DST_ADDR     : in  std_logic_vector(31 downto 0);
      RD_COMPL_SRC_ADDR     : in  std_logic_vector(31 downto 0);
      RD_COMPL_TAG          : in  std_logic_vector(15 downto 0);
      RD_COMPL_LENGTH       : in  std_logic_vector(11 downto 0);

      -- ========================
      -- Control
      -- ========================

      -- Get second header
      GET_SECOND_HDR        : in  std_logic;

      -- ========================
      -- Output Interface
      -- ========================

      -- Header data
      HEADER_DATA           : out std_logic_vector(63 downto 0)
      );
end entity IB_ENDPOINT_HDR_GEN_SLAVE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_HDR_GEN_SLAVE_ARCH of IB_ENDPOINT_HDR_GEN_SLAVE is

   signal rd_completition_hdr1 : std_logic_vector(63 downto 0);
   signal rd_completition_hdr2 : std_logic_vector(63 downto 0);
   signal mux_header_data_sel  : std_logic_vector(1 downto 0);

begin

rd_completition_hdr1 <= RD_COMPL_DST_ADDR & RD_COMPL_TAG & '1' & C_IB_RD_COMPL_TRANSACTION & RD_COMPL_LENGTH;
rd_completition_hdr2 <= X"00000000" & RD_COMPL_SRC_ADDR;

-- multiplexor header_data ---------------------------------------------------
mux_header_datap: process(GET_SECOND_HDR, rd_completition_hdr1, rd_completition_hdr2)
begin
   case GET_SECOND_HDR is
      when '0'    => HEADER_DATA <= rd_completition_hdr1;
      when '1'    => HEADER_DATA <= rd_completition_hdr2;
      when others => HEADER_DATA <= (others => 'X');
   end case;
end process;


end architecture IB_ENDPOINT_HDR_GEN_SLAVE_ARCH;

