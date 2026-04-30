-- ptc_pkg.vhd: PTC package with forward definitions
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.dma_bus_pack.all;

package ptc_pkg is

    pure function ptc_get_dma_route (DMA_PORTS : natural) return dma_route_path_array_t;

    pure function priv_ptc_get_dma_junc (DMA_PORTS : natural) return dma_route_junction_t;
end package;

package body ptc_pkg is

    pure function ptc_get_dma_route (DMA_PORTS : natural) return dma_route_path_array_t is
        constant JUNC   : dma_route_junction_t := priv_ptc_get_dma_junc(DMA_PORTS);

        variable cfg    : dma_route_path_array_t(0 to DMA_PORTS-1);
    begin
        for i in 0 to DMA_PORTS-1 loop
            cfg(i) := dma_route_path(JUNC, i);
        end loop;
        return cfg;
    end function;

    pure function priv_ptc_get_dma_junc (DMA_PORTS : natural) return dma_route_junction_t is
        constant ROOT   : dma_route_path_t  := dma_route_root(DMA_REQUEST_UNITID_W);
        constant JUNC   : dma_route_junction_t := dma_route_junction(ROOT, DMA_PORTS);
    begin
        return JUNC;
    end function;

end package body;
