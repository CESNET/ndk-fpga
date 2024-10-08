-- dsp_counter_intel_empty.vhd: It's an empty architecture that is loaded when synthesizing with Vivado.
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

architecture EMPTY of DSP_COUNTER_INTEL is

begin

    RESULT <= (others => '0');

end architecture;
