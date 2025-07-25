--! mul_dsp.vhd
--!
--! \file
--! \brief generic mul implemented with Virtex-7 DSP slices
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


architecture FULL of MUL_DSP is
    constant B_MOD_17     : integer := B_DATA_WIDTH mod 17;
    constant B_MOD_24     : integer := B_DATA_WIDTH mod 24;
    constant B_DIV_17     : integer := B_DATA_WIDTH / 17;
    constant B_DIV_24     : integer := B_DATA_WIDTH / 24;
    constant FIRST_ALU_24 : integer := A_DATA_WIDTH+B_MOD_24+24+(24-(24*(1 mod (B_MOD_24+1))));
    constant FIRST_ALU_17 : integer := A_DATA_WIDTH+B_MOD_17+17+(17-(17*(1 mod (B_MOD_17+1))));
    constant A_CONST_24   : integer := B_DIV_24-1+(1 mod (B_MOD_24+1));
    constant A_CONST_17   : integer := B_DIV_17-1+(1 mod (B_MOD_17+1));
    constant FOR_NUM      : integer := (B_DIV_24) + (1 mod (B_MOD_24+1)) - 1;
    constant FOR_NUM_17   : integer := (B_DIV_17) + (1 mod (B_MOD_17+1)) - 1;

    signal zeros   : std_logic_vector(511 downto 0);

    signal mul1_a     : std_logic_vector(24 downto 0);
    signal mul1_b     : std_logic_vector(17 downto 0);
    signal mul1_cout  : std_logic_vector(47 downto 0);

    signal mul2_b    : std_logic_vector(17 downto 0);
    signal mul2_out  : std_logic_vector(47 downto 0);
    signal mul2_pcin : std_logic_vector(47 downto 0);
begin

    assert (A_DATA_WIDTH < 25)
        report " A_DATA_WIDTH > 24bits !!! "
        severity failure;

    zeros <= (others => '0');

    gne_only_one_mul: if((A_DATA_WIDTH < 25 and B_DATA_WIDTH < 18)
                        or
                        (A_DATA_WIDTH < 18 and B_DATA_WIDTH < 25))
   generate
        signal only_one_a : std_logic_vector(24 downto 0);
        signal only_one_b : std_logic_vector(17 downto 0);
        signal only_one_p : std_logic_vector(47 downto 0);
    begin

        gen_input1: if(A_DATA_WIDTH < B_DATA_WIDTH) generate
            only_one_A <= zeros(24-B_DATA_WIDTH downto 0) & B;
            only_one_B <= zeros(17-A_DATA_WIDTH downto 0) & A;
        end generate;

        gen_input2: if(A_DATA_WIDTH >= B_DATA_WIDTH) generate
            only_one_A <= zeros(24-A_DATA_WIDTH downto 0) & A;
            only_one_B <= zeros(17-B_DATA_WIDTH downto 0) & B;
        end generate;


        mul48_inst: entity work.MUL48
        generic map (
            REG_IN      => REG_IN,
            REG_OUT     => REG_OUT
        )
        port map (
            CLK         => CLK,
            RESET       => RESET,
            A           => only_one_A,
            B           => only_one_B,
            CE_IN       => CE,
            CE_OUT      => CE,
            P           => only_one_P,
            PCIN        => (others => '0')
        );

        P <= only_one_P(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);
    end generate;

    gne_no_only: if(not(A_DATA_WIDTH < 25 and B_DATA_WIDTH < 18) and
                    not(A_DATA_WIDTH < 18 and B_DATA_WIDTH < 25))
    generate
        split_24: if(A_DATA_WIDTH < 18) generate
            type mul_out_t is array (0 to B_DIV_24+1) of std_logic_vector(47 downto 0);
            type alu_out_t is array (0 to B_MOD_24) of std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);

            signal mul_out : mul_out_t;
            signal alu_out : alu_out_t;

            signal oper_b : std_logic_vector(17 downto 0);
        begin
            oper_B <= zeros(17-A_DATA_WIDTH downto 0) & A;

            gen_dsp_lvls: for i in 0 to (B_DIV_24) + (1 mod (B_MOD_24+1)) - 1 generate
            begin
                ----------------------FIRST MUL----------------------------------------------------------
                gen_first_mul: if(I = 0) generate
                    signal first_mul_a : std_logic_vector(24 downto 0);
                begin
                    gen_mod: if(B_DATA_WIDTH mod 24 /= 0) generate
                        first_mul_A <= zeros(24-B_MOD_24 downto 0) & B(B_DATA_WIDTH-1 downto 24*(B_DIV_24));
                    end generate;

                    gwn_normal: if(B_MOD_24 = 0) generate
                        first_mul_A <= '0' & B(B_DATA_WIDTH-1 downto 24*(B_DIV_24-1));
                    end generate;

                    mul48_inst: entity work.MUL48
                    generic map (
                        REG_IN      => REG_IN,
                        REG_OUT     => 1
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        A           => first_mul_A,
                        B           => oper_B,
                        CE_IN       => CE,
                        CE_OUT      => CE,
                        P           => mul_out(I),
                        PCIN        => (others => '0')
                    );
                end generate;

                ----------------------SECOND MUL----------------------------------------------------------
                gen_second_mul: if(I = 1) generate
                    signal second_mul_a      : std_logic_vector(24 downto 0);
                    signal second_mul_pcin   : std_logic_vector(47 downto 0);
                    signal second_mul_a_pipe : std_logic_vector(24 downto 0);
                    signal second_mul_b_pipe : std_logic_vector(17 downto 0);
                begin
                    second_mul_A <= '0' & B(24*(A_CONST_24)-1 downto 24*(A_CONST_24-1));

                    gen_inter_alu: if(FIRST_ALU_24 < 49) generate
                        signal pipe_in    : std_logic_vector(18+25-1 downto 0);
                        signal pipe_out   : std_logic_vector(18+25-1 downto 0);
                    begin
                        second_mul_pcin <= mul_out(I-1)(23 downto 0) & zeros(23 downto 0);

                        pipe_in           <= second_mul_A & oper_B;
                        second_mul_A_pipe <= pipe_out(18+25-1 downto 18);
                        second_mul_B_pipe <= pipe_out(17 downto 0);

                        pipe_inst: entity work.PIPE_DSP
                        generic map (
                            PIPE_EN     => true,
                            DATA_WIDTH  => 18+25,
                            ENABLE_DSP  => false,
                            NUM_REGS    => REG_IN
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            DATA_IN     => pipe_in,
                            DATA_OUT    => pipe_out,
                            CE          => CE
                        );

                        mul48_inst: entity work.MUL48
                        generic map (
                            REG_IN      => 1,
                            REG_OUT     => (1 mod ((I mod FOR_NUM)+1+REG_OUT))
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            A           => second_mul_A_pipe,
                            B           => second_mul_B_pipe,
                            CE_IN       => CE,
                            CE_OUT      => CE,
                            P           => mul_out(I),
                            PCIN        => second_mul_pcin
                        );

                        alu_out(0)(FIRST_ALU_24-1 downto 0) <= mul_out(I)(FIRST_ALU_24-1 downto 0);
                    end generate;

                    gen_normal_alu: if(FIRST_ALU_24 > 48) generate
                        signal first_alu_a       : std_logic_vector(FIRST_ALU_24-1 downto 0);
                        signal first_alu_a_shift : std_logic_vector(FIRST_ALU_24-1 downto 0);
                        signal first_alu_b       : std_logic_vector(FIRST_ALU_24-1 downto 0);
                    begin
                        second_mul_pcin   <= (others => '0');
                        second_mul_A_pipe <= second_mul_A;
                        second_mul_B_pipe <= oper_B;

                        mul48_inst: entity work.MUL48
                        generic map (
                            REG_IN      => REG_IN,
                            REG_OUT     => 1
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            A           => second_mul_A_pipe,
                            B           => second_mul_B_pipe,
                            CE_IN       => CE,
                            CE_OUT      => CE,
                            P           => mul_out(I),
                            PCIN        => (others => '0')
                        );

                        first_alu_A       <= zeros(FIRST_ALU_24-1 downto 48) & mul_out(I-1);
                        first_alu_A_shift <= first_alu_A(FIRST_ALU_24-24-1 downto 0) & zeros(23 downto 0);
                        first_alu_B       <= zeros(FIRST_ALU_24-1 downto 48) & mul_out(I);
                        fisrt_alu: entity work.ALU_DSP
                        generic map (
                            DATA_WIDTH  => FIRST_ALU_24,
                            REG_IN      => 0,
                            REG_OUT     => (1 mod ((I mod FOR_NUM)+1+REG_OUT))
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            A           => first_alu_A_shift,
                            B           => first_alu_B,
                            CE_IN       => CE,
                            CE_OUT      => CE,
                            ALUMODE     => "0000",
                            CARRY_IN    => '0',
                            P           => alu_out(0)(FIRST_ALU_24-1 downto 0)
                        );
                    end generate;
                end generate;

                ----------------------OTHERS MULS----------------------------------------------------------
                gen_others: if(I > 1) generate
                    constant ALU_WIDTH   : integer := FIRST_ALU_24+(24*(I-1));
                    constant ALU_BEFORE  : integer := alu_width-24;

                    signal mul_a         : std_logic_vector(24 downto 0);
                    signal pipe_in       : std_logic_vector(25+18-1 downto 0);
                    signal pipe_out      : std_logic_vector(25+18-1 downto 0);

                    signal others_alu_a       : std_logic_vector(alu_width-1 downto 0);
                    signal others_alu_a_shift : std_logic_vector(alu_width-1 downto 0);
                    signal others_alu_b       : std_logic_vector(alu_width-1 downto 0);
                begin
                    mul_A    <= '0' & B(24*(A_CONST_24-(I-1))-1 downto 24*(A_CONST_24-1-(I-1)));
                    pipe_in  <= mul_A & oper_B;

                    pipe_inst: entity work.PIPE_DSP
                    generic map (
                        PIPE_EN     => true,
                        DATA_WIDTH  => 18+25,
                        ENABLE_DSP  => false,
                        NUM_REGS    => (I-2)+REG_IN
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        DATA_IN     => pipe_in,
                        DATA_OUT    => pipe_out,
                        CE          => CE
                    );

                    mul48_inst: entity work.MUL48
                    generic map (
                        REG_IN      => 1,
                        REG_OUT     => 1
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        A           => pipe_out(25+18-1 downto 18),
                        B           => pipe_out(17 downto 0),
                        CE_IN       => CE,
                        CE_OUT      => CE,
                        P           => mul_out(I),
                        PCIN        => (others => '0')
                    );

                    others_alu_A       <= zeros(alu_width-1 downto alu_before) & alu_out(I-2)(alu_before-1 downto 0);
                    others_alu_A_shift <= others_alu_A(alu_width-24-1 downto 0) & zeros(23 downto 0);
                    others_alu_B       <= zeros(alu_width-1 downto 48) & mul_out(I);

                    others_alu: entity work.ALU_DSP
                    generic map (
                        DATA_WIDTH  => alu_width,
                        REG_IN      => 0,
                        REG_OUT     => (1 mod ((I mod FOR_NUM)+1+REG_OUT))
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        A           => others_alu_A_shift,
                        B           => others_alu_B,
                        CE_IN       => CE,
                        CE_OUT      => CE,
                        ALUMODE     => "0000",
                        CARRY_IN    => '0',
                        P           => alu_out(I-1)(alu_width-1 downto 0)
                    );
                end generate;
            end generate;
            P <= alu_out((B_DIV_24)+(1 mod (B_MOD_24+1))-1-1)(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);
        end generate;

        ---------------------------------- SPLIT 17 bits -----------------------------------------
        split_17: if(A_DATA_WIDTH > 17) generate
            type mul_out_t is array (0 to B_DIV_17+1) of std_logic_vector(47 downto 0);
            type alu_out_t is array (0 to B_MOD_17) of std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);

            signal mul_out : mul_out_t;
            signal alu_out : alu_out_t;

            signal oper_a : std_logic_vector(24 downto 0);
        begin
            oper_A <= zeros(24-A_DATA_WIDTH downto 0) & A;

            gen_dsp_lvls: for i in 0 to (B_DIV_17) + (1 mod (B_MOD_17+1)) - 1 generate
            begin
                ----------------------FIRST MUL----------------------------------------------------------
                gen_first_mul: if(I = 0) generate
                    signal first_mul_b : std_logic_vector(17 downto 0);
                begin
                    gen_mod: if(B_MOD_17 /= 0) generate
                        first_mul_B <= zeros(17-B_MOD_17 downto 0) & B(B_DATA_WIDTH-1 downto 17*(B_DIV_17));
                    end generate;

                    gwn_normal: if(B_MOD_17 = 0) generate
                        first_mul_B <= '0' & B(B_DATA_WIDTH-1 downto 17*(B_DIV_17-1));
                    end generate;

                    mul48_inst: entity work.MUL48
                    generic map (
                        REG_IN      => REG_IN,
                        REG_OUT     => 1
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        A           => oper_A,
                        B           => first_mul_B,
                        CE_IN       => CE,
                        CE_OUT      => CE,
                        P           => mul_out(I),
                        PCIN        => (others => '0')
                    );
                end generate;

                ----------------------SECOND MUL----------------------------------------------------------
                gen_second_mul: if(I = 1) generate
                    signal second_mul_b      : std_logic_vector(17 downto 0);
                    signal second_mul_pcin   : std_logic_vector(47 downto 0);
                    signal second_mul_b_pipe : std_logic_vector(17 downto 0);
                    signal second_mul_a_pipe : std_logic_vector(24 downto 0);
                begin
                    second_mul_B <= '0' & B(17*(A_CONST_17)-1 downto 17*(A_CONST_17-1));

                    gen_inter_alu: if(FIRST_ALU_17 < 49) generate
                        signal pipe_in    : std_logic_vector(18+25-1 downto 0);
                        signal pipe_out   : std_logic_vector(18+25-1 downto 0);
                    begin
                        second_mul_pcin <= mul_out(I-1)(23 downto 0) & zeros(23 downto 0);

                        pipe_in           <= second_mul_B & oper_A;
                        second_mul_B_pipe <= pipe_out(18+25-1 downto 25);
                        second_mul_A_pipe <= pipe_out(24 downto 0);

                        pipe_inst: entity work.PIPE_DSP
                        generic map (
                            PIPE_EN     => true,
                            DATA_WIDTH  => 18+25,
                            ENABLE_DSP  => false,
                            NUM_REGS    => REG_IN
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            DATA_IN     => pipe_in,
                            DATA_OUT    => pipe_out,
                            CE          => CE
                        );

                        mul48_inst: entity work.MUL48
                        generic map (
                            REG_IN      => 1,
                            REG_OUT     => (1 mod ((I mod FOR_NUM_17)+1+REG_OUT))
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            A           => second_mul_A_pipe,
                            B           => second_mul_B_pipe,
                            CE_IN       => CE,
                            CE_OUT      => CE,
                            P           => mul_out(I),
                            PCIN        => second_mul_pcin
                        );

                        alu_out(0)(FIRST_ALU_17-1 downto 0) <= mul_out(I)(FIRST_ALU_17-1 downto 0);
                    end generate;

                    gen_normal_alu: if(FIRST_ALU_24 > 48) generate
                        signal first_alu_b       : std_logic_vector(FIRST_ALU_17-1 downto 0);
                        signal first_alu_b_shift : std_logic_vector(FIRST_ALU_17-1 downto 0);
                        signal first_alu_a       : std_logic_vector(FIRST_ALU_17-1 downto 0);
                    begin
                        second_mul_pcin   <= (others => '0');
                        second_mul_A_pipe <= oper_A;
                        second_mul_B_pipe <= second_mul_B;

                        mul48_inst: entity work.MUL48
                        generic map (
                            REG_IN      => REG_IN,
                            REG_OUT     => 1
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            A           => second_mul_A_pipe,
                            B           => second_mul_B_pipe,
                            CE_IN       => CE,
                            CE_OUT      => CE,
                            P           => mul_out(I),
                            PCIN        => (others => '0')
                        );

                        first_alu_B       <= zeros(FIRST_ALU_17-1 downto 48) & mul_out(I-1);
                        first_alu_B_shift <= first_alu_B(FIRST_ALU_17-17-1 downto 0) & zeros(16 downto 0);
                        first_alu_A       <= zeros(FIRST_ALU_17-1 downto 48) & mul_out(I);
                        fisrt_alu: entity work.ALU_DSP
                        generic map (
                            DATA_WIDTH  => FIRST_ALU_17,
                            REG_IN      => 0,
                            REG_OUT     => (1 mod ((I mod FOR_NUM_17)+1+REG_OUT))
                        )
                        port map (
                            CLK         => CLK,
                            RESET       => RESET,
                            A           => first_alu_A,
                            B           => first_alu_B_shift,
                            CE_IN       => CE,
                            CE_OUT      => CE,
                            ALUMODE     => "0000",
                            CARRY_IN    => '0',
                            P           => alu_out(0)(FIRST_ALU_17-1 downto 0)
                        );
                    end generate;
                end generate;

                ----------------------OTHERS MULS----------------------------------------------------------
                gen_others: if(I > 1) generate
                    constant ALU_WIDTH   : integer := FIRST_ALU_17+(17*(I-1));
                    constant ALU_BEFORE  : integer := alu_width-17;

                    signal mul_b         : std_logic_vector(17 downto 0);
                    signal pipe_in       : std_logic_vector(25+18-1 downto 0);
                    signal pipe_out      : std_logic_vector(25+18-1 downto 0);

                    signal others_alu_b       : std_logic_vector(alu_width-1 downto 0);
                    signal others_alu_b_shift : std_logic_vector(alu_width-1 downto 0);
                    signal others_alu_a       : std_logic_vector(alu_width-1 downto 0);
                begin
                    mul_B    <= '0' & B(17*(A_CONST_17-(I-1))-1 downto 17*(A_CONST_17-1-(I-1)));
                    pipe_in  <= mul_B & oper_A;

                    pipe_inst: entity work.PIPE_DSP
                    generic map (
                        PIPE_EN     => true,
                        DATA_WIDTH  => 18+25,
                        ENABLE_DSP  => false,
                        NUM_REGS    => (I-2)+REG_IN
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        DATA_IN     => pipe_in,
                        DATA_OUT    => pipe_out,
                        CE          => CE
                    );

                    mul48_inst: entity work.MUL48
                    generic map (
                        REG_IN      => 1,
                        REG_OUT     => 1
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        A           => pipe_out(24 downto 0),
                        B           => pipe_out(25+18-1 downto 25),
                        CE_IN       => CE,
                        CE_OUT      => CE,
                        P           => mul_out(I),
                        PCIN        => (others => '0')
                    );

                    others_alu_B       <= zeros(alu_width-1 downto alu_before) & alu_out(I-2)(alu_before-1 downto 0);
                    others_alu_B_shift <= others_alu_B(alu_width-17-1 downto 0) & zeros(16 downto 0);
                    others_alu_A       <= zeros(alu_width-1 downto 48) & mul_out(I);

                    others_alu: entity work.ALU_DSP
                    generic map (
                        DATA_WIDTH  => alu_width,
                        REG_IN      => 0,
                        REG_OUT     => (1 mod ((I mod FOR_NUM_17)+1+REG_OUT))
                    )
                    port map (
                        CLK         => CLK,
                        RESET       => RESET,
                        A           => others_alu_A,
                        B           => others_alu_B_shift,
                        CE_IN       => CE,
                        CE_OUT      => CE,
                        ALUMODE     => "0000",
                        CARRY_IN    => '0',
                        P           => alu_out(I-1)(alu_width-1 downto 0)
                    );
                end generate;
            end generate;
            P <= alu_out((B_DIV_17)+(1 mod (B_MOD_17+1))-1-1)(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);
        end generate;
    end generate;
end architecture;
