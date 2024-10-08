/*
 * file       : config.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: configuration object for RESET agent
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/



class config_item extends uvm_object;

    uvm_active_passive_enum active;
    string interface_name;

endclass
