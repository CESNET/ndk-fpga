
-- merge_n_to_m.vhd : Implementation of merger from n inputs to m outputs
--!
--! \file
--! \brief Implementation of merger from n inputs to m outputs
-- SPDX-License-Identifier: BSD-3-Clause
--! \Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET z. s. p. o.
--!
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.numeric_std_unsigned.all;
use work.math_pack.all;

architecture full of merge_n_to_m is

   --! signals

   type sels_t is array (0 to OUTPUTS-1) of std_logic_vector(max(log2(INPUTS),1)-1 downto 0);

   signal sels_ext         : sels_t;
   signal reg_sels_ext     : sels_t;
   signal sels             : sels_t;
   signal mux_in           : std_logic_vector(INPUTS*(DATA_WIDTH-1)-1 downto 0);
   signal mux_out          : std_logic_vector(OUTPUTS*(DATA_WIDTH-1)-1 downto 0);
   signal ones             : std_logic_vector(INPUTS-1 downto 0);
   signal reg_vld_in       : std_logic_vector(OUTPUTS-1 downto 0);
   signal reg_vld          : std_logic_vector(OUTPUTS-1 downto 0);
   signal reg_input_data   : std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);

   --! -------------------------------------------------------------------------


begin

    reg_input_data <= INPUT_DATA;

   --! Multiplexers ------------------------------------------------------------

   mux_ing: for i in 0 to INPUTS-1 generate
      mux_in((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1)) <= reg_input_data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH+1);
   end generate;

   muxg: for i in 0 to OUTPUTS-1 generate
      --! Multiplexer
      muxi: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => DATA_WIDTH-1,
         MUX_WIDTH => INPUTS-i
      )
      port map(
         DATA_IN => mux_in(INPUTS*(DATA_WIDTH-1)-1 downto (i)*(DATA_WIDTH-1)),
         SEL => sels(i)(max(log2(INPUTS-i), 1)-1 downto 0),
         DATA_OUT => mux_out((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1))
      );

   end generate;

   --! -------------------------------------------------------------------------

   --! Selection signals generate ----------------------------------------------

   onesg: for i in 0 to INPUTS-1 generate
      ones(i) <= INPUT_DATA(i*DATA_WIDTH);
   end generate;

   selsg: for i in 0 to OUTPUTS-1 generate

      n_onei: entity work.N_ONE
      generic map(
         --! \brief Data width of input vector
         DATA_WIDTH => INPUTS
      )
      port map(

         --! \name Clock & reset interface
         --! --------------------------------------------------------------------------
         --! \brief Common clock
         CLK => CLK,
         --! \brief Common reset
         RESET => RESET,

         --! \name Input vector
         --! --------------------------------------------------------------------------
         D => ones,

         --! \name N one number
         --! -------------------------------------------------------------------------
         N => std_logic_vector(to_unsigned(i, max(log2(INPUTS),1))),

         --! \name Output address
         --! --------------------------------------------------------------------------
         A => sels_ext(i),
         --! \brief Valid bit
         VLD => reg_vld_in(i)

      );

      sels(i) <= std_logic_vector(unsigned(reg_sels_ext(i)) - to_unsigned(i, max(1,log2(INPUTS))));

   end generate;

   reg_vld <= reg_vld_in;
   reg_sels_ext <= sels_ext;

   --! registers

   reg_vld0g: if OUTPUT_REG = true generate
      reg_vldp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (OUTPUT_DST_RDY='1' or OUTPUT_SRC_RDY='0') then
               for i in 0 to OUTPUTS-1 loop
                  OUTPUT_DATA(i*DATA_WIDTH) <= reg_vld(i);
                  OUTPUT_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH+1) <= mux_out((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1));
                  OUTPUT_SRC_RDY <= INPUT_SRC_RDY;

                  if (RESET = '1') then
                     OUTPUT_DATA(i*DATA_WIDTH) <= '0';
                  end if;
               end loop;
            end if;

            if (RESET='1') then
               OUTPUT_SRC_RDY <= '0';
            end if;
         end if;
      end process;
      INPUT_DST_RDY <= OUTPUT_DST_RDY or (not OUTPUT_SRC_RDY);
   end generate;

   reg_vld1g: if OUTPUT_REG /= true generate
      no_outreg_gen : for i in 0 to OUTPUTS-1 generate
         OUTPUT_DATA(i*DATA_WIDTH) <= reg_vld(i);
         OUTPUT_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH+1) <= mux_out((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1));
      end generate;
      OUTPUT_SRC_RDY <= INPUT_SRC_RDY;
      INPUT_DST_RDY  <= OUTPUT_DST_RDY;
   end generate;

   --! -------------------------------------------------------------------------

end full;
