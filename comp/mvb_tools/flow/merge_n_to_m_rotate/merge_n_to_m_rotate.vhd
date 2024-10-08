-- merge_n_to_m_rotate.vhd : Implementation of merger from n inputs to m outputs and rotate
--!
--! \file
--! \brief Implementation of merger from n inputs to m outputs and rotate
-- SPDX-License-Identifier: BSD-3-Clause
--! \Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET z. s. p. o.
--!
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.numeric_std_unsigned.all;
use work.math_pack.all;

architecture full of merge_n_to_m_rotate is

   --! signals

   type sels_t  is array (0 to OUTPUTS-1)   of std_logic_vector(max(log2(INPUTS),1)-1 downto 0);
   type sels3_t is array (0 to OUTPUTS*3-1) of std_logic_vector(max(log2(INPUTS),1)-1 downto 0);

   signal selI             : integer := 0;
   signal sel_u            : unsigned(log2(OUTPUTS)-1 downto 0);

   signal sels_ext         : sels_t;
   signal reg_sels_ext     : sels_t;
   signal sels             : sels_t;
   signal sels3            : sels3_t;
   signal sels_rot         : sels_t;
   signal mux_in           : std_logic_vector(INPUTS*(DATA_WIDTH-1)-1 downto 0);
   signal mux_out          : std_logic_vector(OUTPUTS*(DATA_WIDTH-1)-1 downto 0);
   signal ones             : std_logic_vector(INPUTS-1 downto 0);
   signal reg_vld_in       : std_logic_vector(OUTPUTS-1 downto 0);
   signal reg_vld_in3      : std_logic_vector(OUTPUTS*3-1 downto 0);
   signal reg_vld          : std_logic_vector(OUTPUTS-1 downto 0);
   signal reg_input_data   : std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);

   --! -------------------------------------------------------------------------


begin

   reg_input_data0g: if OUTPUT_REG = true generate
      reg_input_datap: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            reg_input_data <= INPUT_DATA;
         end if;
      end process;
   end generate;

   reg_input_data1g: if OUTPUT_REG /= true generate
      reg_input_data <= INPUT_DATA;
   end generate;

   --! Multiplexers ------------------------------------------------------------

   mux_ing: for i in 0 to INPUTS-1 generate
      mux_in((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1)) <= reg_input_data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH+1);
   end generate;

   muxg: for i in 0 to OUTPUTS-1 generate
      --! Multiplexer
      muxi: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => DATA_WIDTH-1,
         MUX_WIDTH => INPUTS
      )
      port map(
         DATA_IN => mux_in(INPUTS*(DATA_WIDTH-1)-1 downto 0),
         SEL => sels_rot(i),
         DATA_OUT => mux_out((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1))
      );

      OUTPUT_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH+1) <= mux_out((i+1)*(DATA_WIDTH-1)-1 downto i*(DATA_WIDTH-1));

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

      OUTPUT_DATA(i*DATA_WIDTH) <= reg_vld(i);

      sels(i)  <= std_logic_vector(unsigned(reg_sels_ext(i)));

      sels3(i)           <= sels(i);
      sels3(OUTPUTS+i)   <= sels(i);
      sels3(OUTPUTS*2+i) <= sels(i);

      reg_vld_in3(i)           <= reg_vld_in(i);
      reg_vld_in3(OUTPUTS+i)   <= reg_vld_in(i);
      reg_vld_in3(OUTPUTS*2+i) <= reg_vld_in(i);

   end generate;


   --! Output rotation

   selI  <= to_integer(unsigned(SEL));
   sel_u <= unsigned(SEL);

   sel_rot_pr : process (sels,sels3,selI)
   begin
      if SHIFT_LEFT = true then
         for i in 0 to OUTPUTS-1 loop
            --sels_rot(i) <= std_logic_vector(to_unsigned(to_integer(unsigned(sels(i)))+selI,sels_rot(i)'high+1));
            sels_rot(i) <= sels3(OUTPUTS*2+i-selI);
         end loop;
      else
         for i in 0 to OUTPUTS-1 loop
            --sels_rot(i) <= std_logic_vector(to_unsigned(to_integer(unsigned(sels(i)))-selI,sels_rot(i)'high+1));
            sels_rot(i) <= sels3(          i+selI);
         end loop;
      end if;
   end process;

   --! registers

   reg_vld0g: if OUTPUT_REG = true generate
      reg_vldp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_vld <= (others => '0');
            else
               --reg_vld <= reg_vld_in;
               if SHIFT_LEFT = true then
                  for i in 0 to OUTPUTS-1 loop
                     reg_vld(i) <= reg_vld_in3(OUTPUTS*2+i-selI);
                  end loop;
               else
                  for i in 0 to OUTPUTS-1 loop
                     reg_vld(i) <= reg_vld_in3(          i+selI);
                  end loop;
               end if;
            end if;
         end if;
      end process;


      reg_sels_extp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            reg_sels_ext <= sels_ext;
         end if;
      end process;
   end generate;

   reg_vld1g: if OUTPUT_REG /= true generate
      --reg_vld <= reg_vld_in;
      reg_vld_pr: process(reg_vld_in3,selI)
      begin
         if SHIFT_LEFT = true then
            for i in 0 to OUTPUTS-1 loop
               reg_vld(i) <= reg_vld_in3(OUTPUTS*2+i-selI);
            end loop;
         else
            for i in 0 to OUTPUTS-1 loop
               reg_vld(i) <= reg_vld_in3(          i+selI);
            end loop;
         end if;
      end process;

      reg_sels_ext <= sels_ext;
   end generate;

   --! -------------------------------------------------------------------------

end full;
