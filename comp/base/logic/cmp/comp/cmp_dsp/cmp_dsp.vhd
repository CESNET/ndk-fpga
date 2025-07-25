--! cmp_dsp.vhd
--!
--! \file
--! \brief generic comparator implemented with Virtex-7 DSP slices
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

architecture STRUCTURAL of CMP_DSP is
    type   p_pom_t is array (0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1)) of std_logic_vector(1 downto 0);
    signal p_pom   : p_pom_t;
    type   dec_pom_t is array (0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2)) of std_logic_vector(1 downto 0);
    signal dec_pom : dec_pom_t;

begin
    --! generate decoders
    gen_decoders: if(DATA_WIDTH > 48) generate
        dec_pom(0) <= p_pom(0);

        --! generate decoders before last
        gen_for: for i in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 3) generate
            cmp_decode_inst: entity work.CMP_DECODE
            port map (
                L_IN => dec_pom(I),
                H_IN => p_pom(I + 1),
                P    => dec_pom(I + 1)
            );
        end generate;

        -- generate last decoder
        cmp_decode_inst: entity work.CMP_DECODE
        port map (
            L_IN => dec_pom(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2)),
            H_IN => p_pom((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1),
            P    => P
        );
    end generate;


    gen_alu_div: for i in 0 to (DATA_WIDTH/48)-1 generate
    begin
        --! generate DSP only for 48 bit
        gen_port_reg_one_48: if(DATA_WIDTH = 48) generate
            cmp48_inst: entity work.CMP48
            generic map (
                REG_IN  => REG_IN,
                REG_OUT => REG_OUT
            )
            port map (
                CLK    => CLK,
                RESET  => RESET,
                A      => A(47+I*48 downto 0+I*48),
                B      => B(47+I*48 downto 0+I*48),
                CE_IN  => CE_IN,
                CE_OUT => CE_OUT,
                P      => P
            );
        end generate;

        --! generate DSPs when DATA_WIDTH > 48
        gen_port_between: if(DATA_WIDTH > 48) generate
        begin
            cmp48_inst: entity work.CMP48
            generic map (
                REG_IN  => REG_IN,
                REG_OUT => REG_OUT
            )
            port map (
                CLK    => CLK,
                RESET  => RESET,
                A      => A(47+I*48 downto 0+I*48),
                B      => B(47+I*48 downto 0+I*48),
                CE_IN  => CE_IN,
                CE_OUT => CE_OUT,
                P      => p_pom(I)
            );
        end generate;
    end generate;

    gen_alu_mod: if (DATA_WIDTH mod 48 > 0) generate
        signal amod : std_logic_vector(47 downto 0);
        signal bmod : std_logic_vector(47 downto 0);
    begin
        Amod((DATA_WIDTH mod 48)-1 downto 0) <= A(A'LENGTH-1 downto A'LENGTH-1-(DATA_WIDTH mod 48)+1);
        Amod(47 downto (DATA_WIDTH mod 48))  <= (others => '0');
        Bmod((DATA_WIDTH mod 48)-1 downto 0) <= B(B'LENGTH-1 downto B'LENGTH-1-(DATA_WIDTH mod 48)+1);
        Bmod(47 downto (DATA_WIDTH mod 48))  <= (others => '0');

        --! generate one DSP when DATA_WIDTH < 48
        gen_dsp_one: if(DATA_WIDTH < 48) generate
            cmp48_inst: entity work.CMP48
            generic map (
                REG_IN  => REG_IN,
                REG_OUT => REG_OUT
            )
            port map (
                CLK    => CLK,
                RESET  => RESET,
                A      => Amod,
                B      => Bmod,
                CE_IN  => CE_IN,
                CE_OUT => CE_OUT,
                P      => P
            );
        end generate;

        --! generate last DSP when DATA_WIDTH mod 48 /= 0
        gen_dsp_last: if(DATA_WIDTH > 48) generate

            cmp48_inst: entity work.CMP48
            generic map (
                REG_IN  => REG_IN,
                REG_OUT => REG_OUT
            )
            port map (
                CLK    => CLK,
                RESET  => RESET,
                A      => Amod,
                B      => Bmod,
                CE_IN  => CE_IN,
                CE_OUT => CE_OUT,
                P      => p_pom(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)) - 1))
            );
        end generate;
    end generate;
end architecture;
