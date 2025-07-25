-- gen_dsp_shifter_rotate.vhd: 17 bits barrel shifter with generic data width and support rotation
-- Copyright (C) 2015 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity GEN_DSP_SHIFTER_ROTATE is
    generic (
        DATA_WIDTH        : integer := 48;
        -- set true to shift left, false to shift right
        SHIFT_LEFT        : boolean := true;
        -- input registers (0 -> false, 1 -> true)
        REG_IN            : integer := 0;
        -- output registers (0 -> false, 1 -> true)
        REG_OUT           : integer := 0;
        -- connect output registers with DPS or normal logic
        REG_OUT_WITH_DSP  : boolean := true
    );
    port (
        CLK         : in std_logic;
        RESET       : in std_logic;
        -- Input interface
        DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);
        NUM_SHIFT   : in  std_logic_vector(15 downto 0);
        -- clock enbale for input registers
        CE_IN       : in std_logic;
        -- clock enbale for output registers
        CE_OUT      : in std_logic
    );
end entity;

architecture FULL of GEN_DSP_SHIFTER_ROTATE is
    signal zeros   : std_logic_vector(63 downto 0);

    type   cascade_t is array (0 to ((DATA_WIDTH/24) + (1 mod ((DATA_WIDTH mod 24) +1)))) of std_logic_vector(15 downto 0);
    signal cascade : cascade_t;

    signal data_in_inv   : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal data_out_inv  : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal data_out_reg  : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal tmp_num_shift : std_logic_vector(16 downto 0);

begin
    zeros <= (others => '0');

    -- configure null bit
    process (NUM_SHIFT)
    begin
        if (NUM_SHIFT /= 0) then
            tmp_num_shift(0) <= '0';
        else
            tmp_num_shift(0) <= '1';
        end if;
    end process;

    tmp_num_shift(16 downto 1) <= NUM_SHIFT;

    -- generate output registers
    gen_output_registers: if(REG_OUT = 1) generate
        -- with DSP
        gen_out_reg_dsp: if(REG_OUT_WITH_DSP = true) generate
            pipe_inst: entity work.ALU_DSP
            generic map (
                DATA_WIDTH  => DATA_WIDTH,
                REG_IN      => 1,
                REG_OUT     => 0
            )
            port map (
                CLK         => CLK,
                RESET       => RESET,
                A           => data_out_reg,
                B           => (others => '0'),
                CE_IN       => CE_OUT,
                CE_OUT      => '1',
                ALUMODE     => "0000",
                CARRY_IN    => '0',
                P           => DATA_OUT
            );
        end generate;

        -- normal logic
        gen_out_reg_normal: if(REG_OUT_WITH_DSP = false) generate
            process (CLK)
            begin
                if ((CLK'event) and (CLK = '1')) then
                    if (RESET = '1') then
                        DATA_OUT <= (others => '0');
                    elsif (CE_OUT = '1') then
                        DATA_OUT <= data_out_reg;
                    end if;
                end if;
            end process;
        end generate;
    end generate;

    gen_output_registers_off: if(REG_OUT = 0) generate
        DATA_OUT <= data_out_reg;
    end generate;

    -- generate left shifter
    gen_shift_right: if(SHIFT_LEFT = false) generate
        gen_for_shift_rigth: for i in 0 to (DATA_WIDTH-1) generate
            data_in_inv(I)                   <= DATA_IN((DATA_WIDTH-1) - I);
            data_out_reg((DATA_WIDTH-1) - I) <= data_out_inv(I);
        end generate;
    end generate;

    -- right shifter
    gen_shift_left: if(SHIFT_LEFT = true) generate
        data_in_inv  <= DATA_IN;
        data_out_reg <= data_out_inv;
    end generate;

    div_data: for i in 0 to (DATA_WIDTH/24)-1 generate
    begin
        -- generate first shifter
        gen_first_dsp: if(I = 0) generate
            dsp_shifter_inst: entity work.DSP_SHIFTER
            generic map (
                REG_IN    => REG_IN,
                EN_CAS_IN => 1
            )
            port map (
                CLK   => CLK,
                RESET => RESET,
                A     => data_in_inv(23+I*24 downto 0+I*24),

                SHIFT   => tmp_num_shift,
                OUT_CAS => cascade(I),
                IN_CAS  => cascade(((DATA_WIDTH/24)-1) + (1 mod ((DATA_WIDTH mod 24) + 1))),
                CE_IN   => CE_IN,
                CE_OUT  => '1',
                P       => data_out_inv(23+I*24 downto 0+I*24)
            );
        end generate;

        -- others shifters
        gen_next_dsp: if(I /= 0) generate
            dsp_shifter_inst: entity work.DSP_SHIFTER
            generic map (
                REG_IN    => REG_IN,
                EN_CAS_IN => 1
            )
            port map (
                CLK     => CLK,
                RESET   => RESET,
                A       => data_in_inv(23+I*24 downto 0+I*24),
                SHIFT   => tmp_num_shift,
                OUT_CAS => cascade(I),
                IN_CAS  => cascade(I - 1),
                CE_IN   => CE_IN,
                CE_OUT  => '1',
                P       => data_out_inv(23+I*24 downto 0+I*24)
            );
        end generate;
    end generate;

    gen_last_dsp_mod: if (DATA_WIDTH mod 24 > 0) generate
        signal data_in_mod  : std_logic_vector(23 downto 0);
        signal data_out_mod : std_logic_vector(23 downto 0);
    begin
        data_in_mod((DATA_WIDTH mod 24)-1 downto 0) <= data_in_inv(data_in_inv'LENGTH-1 downto data_in_inv'LENGTH-1-(DATA_WIDTH mod 24)+1);
        data_in_mod(23 downto (DATA_WIDTH mod 24))  <= (others => '0');

        --! generate one shifter when DATA_WIDTH < 24
        gen_only_one_dsp: if(DATA_WIDTH < 24) generate
            signal tmp_rotate : std_logic_vector(15 downto 0);
        begin
            dsp_shifter_inst: entity work.DSP_SHIFTER
            generic map (
                REG_IN         => REG_IN,
                EN_CAS_IN      => 1,
                EN_CON_CAS_OUT => 1,
                UP             => (DATA_WIDTH mod 24) + 15,
                DOWN           => (DATA_WIDTH mod 24)
            )
            port map (
                CLK     => CLK,
                RESET   => RESET,
                A       => data_in_mod,
                SHIFT   => tmp_num_shift,
                IN_CAS  => tmp_rotate,
                OUT_CAS => tmp_rotate,
                CE_IN   => CE_IN,
                CE_OUT  => '1',
                P       => data_out_mod
            );
        end generate;

        --! generate last shifter when DATA_WIDTH mod 24 /= 0
        gen_dsp_last: if(DATA_WIDTH > 24) generate
            dsp_shifter_inst: entity work.DSP_SHIFTER
            generic map (
                REG_IN         => REG_IN,
                EN_CAS_IN      => 1,
                EN_CON_CAS_OUT => 1,
                UP             => (DATA_WIDTH mod 24) + 15,
                DOWN           => (DATA_WIDTH mod 24)
            )
            port map (
                CLK     => CLK,
                RESET   => RESET,
                A       => data_in_mod,
                SHIFT   => tmp_num_shift,
                IN_CAS  => cascade((DATA_WIDTH/24)-1),
                OUT_CAS => cascade(DATA_WIDTH/24),
                CE_IN   => CE_IN,
                CE_OUT  => '1',
                P       => data_out_mod
            );
        end generate;

        data_out_inv(data_out_inv'LENGTH-1 downto data_out_inv'LENGTH-1-(DATA_WIDTH mod 24)+1) <= data_out_mod((DATA_WIDTH mod 24)-1 downto 0);
    end generate;
end architecture;

