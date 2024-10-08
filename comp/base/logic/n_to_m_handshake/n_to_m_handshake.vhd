-- n_to_m_handshake.vhd: Unit for SRC_RDY/DST_RDY handshake from N sources to M destinations
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- -----------------------------------------------------------------------------
--                                 Description
-- -----------------------------------------------------------------------------
-- Connects N sources and M destination using shared SRC_RDY/DST_RDY handshake.
--
-- Data is only transfered when all sources and all destinations are ready.
--
-- The most common usage is 1 source and 2 destinations.
--
-- The handshake logic is written in a way, so that any source DST_RDY is dependent
-- on the all the destination's DST_RDYs and the SRC_RDYs of all THE OTHER sources,
-- but not the SRC_RDY of itself!
-- (e.g.: When all destinations have DST_RDY set to '1' and all but one sources
--        have SRC_RDY set to '1', then all these sources will get DST_RDY=='0',
--        but the one source with inactive SRC_RDY will get DST_RDY=='1'.)
-- WARNING: This logic fails if you drive multiple SRC_RDYs by the same signal!
-- The same logic (but with inverted SRC_RDY and DST_RDY) applies to the output
-- handshake.
-- Because of this another port called "ALL_RDY" is added to signal, that data
-- from all the sources can actually be transfered.

-- -----------------------------------------------------------------------------
--                              Entity declaration
-- -----------------------------------------------------------------------------

entity N_TO_M_HANDSHAKE is
generic (

    -- Number of sources
    SOURCES            : integer := 1;
    -- Number of destinations
    DESTINATIONS       : integer := 2;
    -- Width of the widest data
    -- (All data ports are set to this width since they are declared as an array.)
    MAX_DATA_WIDTH     : integer := 8;

    -- Output register enable
    OUTPUT_REG_EN      : boolean := false

);
port (

    -- Clock and Reset (only used when OUTPUT_REG_EN==true) --
    CLK               : in  std_logic;
    RESET             : in  std_logic;

    -- Data input --
    -- Every surce can send data to all destinations can choose any combination of them.
    IN_DATA           : in  slv_array_2d_t(SOURCES-1 downto 0)(DESTINATIONS-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    IN_SRC_RDY        : in  std_logic_vector(SOURCES-1 downto 0);
    IN_DST_RDY        : out std_logic_vector(SOURCES-1 downto 0);

    -- Data output --
    -- Every destination has access to all input data and can choose any combination of them.
    -- All the other data paths get optimised out.
    OUT_DATA          : out slv_array_2d_t(DESTINATIONS-1 downto 0)(SOURCES-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    OUT_SRC_RDY       : out std_logic_vector(DESTINATIONS-1 downto 0);
    OUT_DST_RDY       : in  std_logic_vector(DESTINATIONS-1 downto 0);

    -- Data transfer ready
    ALL_RDY           : out std_logic

);
end entity N_TO_M_HANDSHAKE;

-- -----------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
--                           Architecture declaration
-- -----------------------------------------------------------------------------

architecture full of N_TO_M_HANDSHAKE is

    -- internal otuput signals
    signal s_out_data    : slv_array_2d_t(DESTINATIONS-1 downto 0)(SOURCES-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal s_out_src_rdy : std_logic_vector(DESTINATIONS-1 downto 0);
    signal s_out_dst_rdy : std_logic_vector(DESTINATIONS-1 downto 0);

begin

    -- -------------------------------------------------------------------------
    -- IN_DST_RDY logic
    -- -------------------------------------------------------------------------

    input_pr : process (all)
    begin
        IN_DST_RDY <= (others => '1');

        for i in 0 to SOURCES-1 loop

            for e in 0 to SOURCES-1 loop
                if (i/=e and IN_SRC_RDY(e)='0') then
                    -- some OF THE OTHER sources is not ready for data transfer
                    IN_DST_RDY(i) <= '0';
                end if;
            end loop;

            if ((and s_out_dst_rdy)='0') then
                -- some of the destinations is not ready for data transfer
                IN_DST_RDY(i) <= '0';
            end if;

        end loop;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- OUT_SRC_RDY logic
    -- -------------------------------------------------------------------------

    output_pr : process (all)
    begin
        s_out_src_rdy <= (others => '1');

        for i in 0 to DESTINATIONS-1 loop

            for e in 0 to DESTINATIONS-1 loop
                if (i/=e and s_out_dst_rdy(e)='0') then
                    -- some OF THE OTHER destinations is not ready for data transfer
                    s_out_src_rdy(i) <= '0';
                end if;
            end loop;

            if ((and IN_SRC_RDY)='0') then
                -- some of the sources is not ready for data transfer
                s_out_src_rdy(i) <= '0';
            end if;

        end loop;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- ALL_RDY logic
    -- -------------------------------------------------------------------------

    ALL_RDY <= (and IN_SRC_RDY) and (and s_out_dst_rdy);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Output generation
    -- -------------------------------------------------------------------------

    -- matrix transposition
    out_data_gen : for i in 0 to DESTINATIONS-1 generate
        out_dest_data_gen : for e in 0 to SOURCES-1 generate
            s_out_data(i)(e) <= IN_DATA(e)(i);
        end generate;
    end generate;

    output_reg_gen : if (OUTPUT_REG_EN) generate -- output register

        output_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                for i in 0 to DESTINATIONS-1 loop
                    if (s_out_dst_rdy(i)='1') then
                        OUT_DATA   (i) <= s_out_data   (i);
                        OUT_SRC_RDY(i) <= s_out_src_rdy(i);
                    end if;
                end loop;

--                if (ALL_RDY='1') then
--                    OUT_DATA    <= s_out_data;
--                    OUT_SRC_RDY <= s_out_src_rdy;
--                end if;

                if (RESET='1') then
                    OUT_SRC_RDY <= (others => '0');
                end if;
            end if;
        end process;

        s_out_dst_rdy <= OUT_DST_RDY or (not OUT_SRC_RDY);

    else generate -- no output register

        OUT_DATA      <= s_out_data;
        OUT_SRC_RDY   <= s_out_src_rdy;
        s_out_dst_rdy <= OUT_DST_RDY;

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    --
    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    --
    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------

end architecture;
