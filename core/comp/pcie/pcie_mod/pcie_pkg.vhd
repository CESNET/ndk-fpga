-- pcie_pkg.vhd: Core PCIe package with forward definitions
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;
use work.ptc_pkg.all;

package core_pcie_pkg is

    pure function core_pcie_get_dma_route (DMA_PORTS, PCIE_ENDPOINTS: natural) return dma_route_path_array_t;

end package;

package body core_pcie_pkg is

    pure function core_pcie_get_dma_route (DMA_PORTS, PCIE_ENDPOINTS: natural) return dma_route_path_array_t is
        constant DMA_PORTS_PER_EP   : natural := DMA_PORTS / PCIE_ENDPOINTS;
        constant PTC_ROUTE          : dma_route_path_array_t := ptc_get_dma_route(DMA_PORTS_PER_EP);
        variable cfg                : dma_route_path_array_t(0 to DMA_PORTS-1);
    begin

        for i in 0 to PCIE_ENDPOINTS-1 loop
            for j in 0 to DMA_PORTS_PER_EP-1 loop
                cfg(i*DMA_PORTS_PER_EP+j) := PTC_ROUTE(j);
            end loop;
        end loop;

        return cfg;
    end function;

end package body;
