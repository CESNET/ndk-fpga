-- mi_pipe_arch.vhd: MI Pipe - wrapper to generic pipe
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ----------------------------------------------------------------------------

architecture mi_pipe_arch of MI_PIPE is

   signal in_data  : std_logic_vector(META_WIDTH + DATA_WIDTH + ADDR_WIDTH + DATA_WIDTH/8 + 1 downto 0);
   signal out_data : std_logic_vector(META_WIDTH + DATA_WIDTH + ADDR_WIDTH + DATA_WIDTH/8 + 1 downto 0);

   signal in_req      : std_logic;
   signal in_dst_rdy  : std_logic;
   signal out_src_rdy : std_logic;
   signal out_dst_rdy : std_logic;

   signal OUT_RD_aux  : std_logic;
   signal OUT_WR_aux  : std_logic;

begin

   in_data <= IN_WR & IN_RD & IN_BE & IN_ADDR & IN_DWR & IN_MWR;

   OUT_MWR    <= out_data(META_WIDTH-1 downto 0);
   OUT_DWR    <= out_data(META_WIDTH+DATA_WIDTH-1 downto META_WIDTH);
   OUT_ADDR   <= out_data(META_WIDTH+DATA_WIDTH+ADDR_WIDTH-1 downto META_WIDTH+DATA_WIDTH);
   OUT_BE     <= out_data(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8-1 downto META_WIDTH+DATA_WIDTH+ADDR_WIDTH);
   OUT_RD_aux <= out_data(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8)   and out_src_rdy;
   OUT_WR_aux <= out_data(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1) and out_src_rdy;

   OUT_RD <= OUT_RD_aux;
   OUT_WR <= OUT_WR_aux;

   in_req      <= IN_RD or IN_WR;
   out_dst_rdy <= ((not (OUT_RD_aux or OUT_WR_aux)) or OUT_ARDY);

   PIPE: entity work.PIPE
   generic map(
      DATA_WIDTH  => META_WIDTH + DATA_WIDTH + ADDR_WIDTH + DATA_WIDTH/8 + 2,
      PIPE_TYPE   => PIPE_TYPE,
      USE_OUTREG  => USE_OUTREG,
      FAKE_PIPE   => FAKE_PIPE,
      DEVICE      => DEVICE
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,

      IN_DATA     => in_data,
      IN_SRC_RDY  => in_req,
      IN_DST_RDY  => in_dst_rdy,

      OUT_DATA    => out_data,
      OUT_SRC_RDY => out_src_rdy,
      OUT_DST_RDY => out_dst_rdy
   );

   IN_ARDY <= in_dst_rdy and in_req;

   NOT_FAKE: if (FAKE_PIPE = false) generate
      in_drdp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            IN_DRD <= OUT_DRD;
         end if;
      end process;

      in_drdyp: process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               IN_DRDY <= '0';
            else
               IN_DRDY <= OUT_DRDY;
            end if;
         end if;
      end process;
   end generate;

   FAKE: if (FAKE_PIPE = true) generate
      IN_DRD  <= OUT_DRD;
      IN_DRDY <= OUT_DRDY;
   end generate;

end mi_pipe_arch;
