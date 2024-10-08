/*
 * my_component.vhd: Description of my component.
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class ram_random  #(ADDR_WIDTH) extends ram_base #(ADDR_WIDTH);

    byte unsigned memory[logic[ADDR_WIDTH-1:0]][];

    function new(string inst);
        super.new(inst);
    endfunction

    virtual function logic[ADDR_WIDTH-1:0] malloc(longint unsigned length, logic[ADDR_WIDTH-1:0] alignmask = 64'h0000000000000003);
        bit loop_end;
        logic [ADDR_WIDTH-1:0] addr_new;
        logic [ADDR_WIDTH-1:0] addr_new_prev;
        logic [ADDR_WIDTH-1:0] addr_new_next;
        logic [ADDR_WIDTH-1:0] addr_new_max = '1;

        addr_new_max -= length;
        do begin
            loop_end = 1'b1;
            assert(std::randomize(addr_new));
            addr_new &= ~alignmask;
            addr_new_prev = addr_new;
            addr_new_next = addr_new;

            //check if generated address is applicable.
            //(ADDR_PREV+ADDR_PREV.size < ADDR < ADDR + ADDR.size < ADDR_NEXT)
            if(memory.exists(addr_new) == 1'b1) begin
                loop_end = 1'b0;
            end else if (memory.prev(addr_new_prev) == 1 &&
                        ((addr_new_prev + memory[addr_new_prev].size()) >= addr_new)) begin
                loop_end = 1'b0;
            end else if (memory.next(addr_new_next) == 1 &&
                        ((addr_new + length) >= addr_new_next)) begin
                loop_end = 1'b0;
            //check if addres is not on end of address space
            end else if(addr_new_max < addr_new) begin
                 loop_end = 1'b0;
            end
        end while(loop_end != 1'b1);

        memory[addr_new] = new[length];
        return addr_new;
    endfunction

    function void get_data(logic[ADDR_WIDTH-1:0]  addr, longint unsigned length, output logic[ADDR_WIDTH-1:0] base, output int unsigned offset_ret, input string dir = "");
        logic[ADDR_WIDTH-1:0] offset;

        base = addr;
        if(memory.exists(addr) == 0) begin
            if (memory.prev(base) == 0) begin
                logic[ADDR_WIDTH-1:0] next = addr;
                memory.next(next);
                $write("%s %s access on uknown address %x, length %x.\n", inst, dir, addr, length);
                $write("\tNearest next addres is %h with size %d\n", next, memory[next].size());
                $stop();
            end
        end

        offset     = addr - base;
        offset_ret = offset;
        if((offset + length) > memory[base].size()) begin
            logic[ADDR_WIDTH-1:0] next = addr;
            memory.next(next);
            $write("%s %s access on uknown address %x, length %x\n", inst, dir, addr, length);
            $write("\tNearest previous addres is %h with size %d\n", base, memory[base].size());
            $write("\tNearest next addres is %h with size %d\n", next, memory[next].size());
            $stop();
        end
    endfunction

    virtual function void read(logic[ADDR_WIDTH-1:0]  addr, longint unsigned length, inout byte unsigned data[]);
        logic[ADDR_WIDTH-1:0] base;
        int unsigned  offset;

        get_data(addr, length, base, offset, "READ");

        for (int it = 0; it < length; it++) begin
            data[it] = memory[base][offset + it];
        end
    endfunction

    virtual function void write(logic[ADDR_WIDTH-1:0] addr, longint unsigned length,       byte unsigned data[]);
        logic[ADDR_WIDTH-1:0] base;
        int unsigned  offset;

        get_data(addr, length, base, offset, "WRITE");

        for (int it = 0; it < length; it++) begin
             memory[base][offset + it] = data[it];
        end
    endfunction

    virtual function void free(logic[ADDR_WIDTH-1:0] addr);
        if(memory.exists(addr) == 1'b1) begin
            memory.delete(addr);
        end else begin
            $write("%s Cannot free memory %h becouse this address haven't been allocated\n", inst, addr);
        end
    endfunction
endclass

