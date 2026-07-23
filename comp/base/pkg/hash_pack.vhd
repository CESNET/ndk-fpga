-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.type_pack.all;

-- common functions for firmware implementation of hash functions.
package hash_pack is

    -- creates and returns the configuration of the pipeline for all the components of a specific type
    function f_get_reg_setup (
        comp_count: natural;                  -- number of components of the specific type
        comp_pipeline_length: natural;        -- length of the pipeline of one component
        comp_offset: natural;                 -- number of the previous components * length of their pipelines
        reg_setup: std_logic_vector;          -- general register setup
        reg_setup_override_flag: boolean;     -- wheter the general or specific register setup shall be used
        reg_setup_override: std_logic_vector  -- the specific register setup, used when the reg_setup_override_flag is set
    ) return slv_array_t;

    -- duplicates a number of times
    function f_duplicate_std_logic_vector (
        vector : std_logic_vector; -- the vector to be duplicated
        count  : natural           -- number of duplications
    ) return std_logic_vector;

end package;

package body hash_pack is

    -- creates and returns the configuration of the pipeline for all the components of a specific type
    function f_get_reg_setup (
        comp_count: natural;                  -- number of components of the specific type
        comp_pipeline_length: natural;        -- length of the pipeline of one component
        comp_offset: natural;                 -- number of the previous components * length of their pipelines
        reg_setup: std_logic_vector;          -- general register setup
        reg_setup_override_flag: boolean;     -- wheter the general or specific register setup shall be used
        reg_setup_override: std_logic_vector  -- the specific register setup, used when the reg_setup_override_flag is set
    ) return slv_array_t is

        variable chosen_reg_setup  : slv_array_t(comp_count - 1 downto 0)(comp_pipeline_length - 1 downto 0);
        variable rotated_reg_setup : unsigned(reg_setup'length - 1 downto 0) := rotate_left(unsigned(reg_setup), comp_offset mod reg_setup'length);
        variable cpw               : natural  := 0;
        variable remainder         : natural  := 0;

    begin
        -- use override if the flag is set
        if (reg_setup_override_flag) then
            for i in 0 to comp_count-1 loop
                chosen_reg_setup(i) := reg_setup_override;
            end loop;
        else
            -- for reg setup of every component
            for i in 0 to comp_count - 1 loop

                -- copy the rotated reg setup multiple times into reg setup for the component if it's pipeline length is greater
                if (comp_pipeline_length > reg_setup'length) then

                    -- comp pipeline words (word'length = reg_setup'length)
                    cpw := comp_pipeline_length / reg_setup'length;

                    -- copy words into chosen reg setup
                    for j in 0 to cpw - 1 loop
                        chosen_reg_setup(i)(comp_pipeline_length - (j * reg_setup'length) - 1 downto comp_pipeline_length - ((j + 1) * reg_setup'length)) := std_logic_vector(rotated_reg_setup);
                    end loop;

                    -- calculate and insert the remainder
                    remainder := comp_pipeline_length mod reg_setup'length;

                    if (remainder > 0) then
                        chosen_reg_setup(i)(remainder - 1 downto 0) := std_logic_vector(rotated_reg_setup(rotated_reg_setup'high downto rotated_reg_setup'length - remainder));
                    end if;

                    -- rotate the reg setup to align it fot the next component
                    rotated_reg_setup := rotate_left(rotated_reg_setup, remainder);

                else
                    -- copy part of the reg setup
                    chosen_reg_setup(i) := std_logic_vector(rotated_reg_setup(rotated_reg_setup'high downto rotated_reg_setup'length - comp_pipeline_length));
                    -- rotate the reg setup to align it fot the next component
                    rotated_reg_setup   := rotate_left(rotated_reg_setup, comp_pipeline_length);

                end if;
            end loop;
        end if;

        return chosen_reg_setup;

    end function;

    -- duplicates a number of times
    function f_duplicate_std_logic_vector (
        vector : std_logic_vector; -- the vector to be duplicated
        count  : natural           -- number of duplications
    ) return std_logic_vector is
        variable arr : slv_array_t(count-1 downto 0)(vector'length-1 downto 0);
    begin
        for i in count-1 downto 0 loop
            arr(i) := vector;
        end loop;

        return slv_array_ser(arr);
    end function;

end package body;
