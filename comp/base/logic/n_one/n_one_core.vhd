-- n_one_core.vhd : Structural implementation of n one detector
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author: Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

entity N_ONE_CORE is
    port (
        -- Input vector
        D                 : in  std_logic_vector(1 downto 0);
        -- N one number: 0 = first, 1 = second
        N                 : in  std_logic;
        -- Output address
        A                 : out std_logic;
        -- Valid bit
        VLD               : out std_logic
    );
end entity;

architecture FULL of N_ONE_CORE is

begin

    A <= '1' when((D(1) = '1' and D(0) = '0' and N = '0') or (D(1) = '1' and D(0) = '1' and N = '1')) else
         '0' when((D(1) = '0' and D(0) = '1' and N = '0') or (D(1) = '1' and D(0) = '1' and N = '0')) else
         '0';

    VLD  <= '1' when((D(1) = '0' and D(0) = '1' and N = '0') or (D(1) = '1' and D(0) = '0' and N = '0') or
                     (D(1) = '1' and D(0) = '1' and N = '0') or (D(1) = '1' and D(0) = '1' and N = '1')) else
            '0';

end architecture;
