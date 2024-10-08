/*!
 * \file       ram.sv
 * \brief      RAM emulation unit
 * \author     Martin Spinler <spinler@cesnet.cz>
 * \date       2018
 * \copyright  CESNET, z. s. p. o.
 */

/* SPDX-License-Identifier: BSD-3-Clause */

class Ram #(ADDR_WIDTH = 32) extends ram_base #(ADDR_WIDTH);
    string inst;
    byte unsigned data[];
    longint size;
    longint allocated;

    function new(string inst, longint pMemorySize = 1024*1024*1024);
        super.new(inst);
        this.inst   = inst;
        //data        = new[pMemorySize];
        size        = pMemorySize;
        allocated   = 0;
    endfunction

    function logic [ADDR_WIDTH-1:0] malloc(longint unsigned length, logic[ADDR_WIDTH-1:0] alignmask = 64'h0000000000000003);
        malloc = (allocated + alignmask) & (~alignmask);
        if (malloc + length > size) begin
            $error("%s: Can't allocate memory! (Allocated: %h; Requested: %h; Total RAM size: %h)\n", inst, malloc, length, size);
            $stop;
        end

        data = new[malloc + length](data);
        allocated = malloc + length;
        return malloc;
    endfunction

    virtual function void read(logic[ADDR_WIDTH-1:0] addr, longint unsigned length, inout byte unsigned data[]);
        readToOffset(addr, length, 0, data);
    endfunction

    virtual function void write(logic[ADDR_WIDTH-1:0] addr, longint unsigned length, byte unsigned data[]);
        writeFromOffset(addr, length, 0, data);
    endfunction

    function void readToOffset(longint unsigned addr, longint unsigned length, longint unsigned offset = 0, inout byte unsigned data[]);
        if (addr + offset + length > size) begin
            $error("RootComplex: RAM read access out of address range: base %x, length %x. RAM size is only %x.\n", addr, length, size);
            $stop;
            return;
        end

        for (longint unsigned i = 0; i < length; i++)
            data[offset + i] = this.data[addr + i];
    endfunction

    function void writeFromOffset(longint unsigned addr, int length, longint unsigned offset = 0, byte unsigned data[]);
        if (addr + offset + length > size) begin
            $error("RootComplex: RAM write access out of address range: base %x, length %x. RAM size is only %x.\n", addr, length, size);
            $stop;
            return;
        end

        for (longint unsigned i = 0; i < length; i++)
            this.data[addr + i] = data[offset + i];
    endfunction

    virtual function void free(logic[ADDR_WIDTH-1:0] addr);
        $write("This memmory model dosnt support free function\n");
    endfunction
endclass
