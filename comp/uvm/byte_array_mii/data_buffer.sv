/*
 * file       : data_buffer.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Object, which will store data until it can be sent
 *              to specified MII interface
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class data_buffer #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_object;

    `uvm_object_param_utils(uvm_byte_array_mii::data_buffer #(CHANNELS, CHANNEL_WIDTH))

    localparam BYTES_IN_CHANNEL = CHANNEL_WIDTH >> 3;

    local byte unsigned data[$];
    local logic unsigned control[$];

    function new(string name = "data_buffer");
        super.new(name);
    endfunction

    // Adds data to buffer
    function void add(ref byte unsigned data[$], ref logic control[$]);
        const int unsigned size = data.size();
        SAME_SIZE : assert(data.size() == control.size());

        for (int i = 0; i < size; i++) begin
            this.data.push_back(data.pop_front());
            this.control.push_back(control.pop_front());
        end
    endfunction

    // Tries to get data from buffer, which can be sent to specified
    // MII interface, if returns '1' if successful
    function bit get(ref byte unsigned data[$], ref logic control[$]);
        QUEUE_EMPTY : assert(data.size() == 0 && control.size() == 0);

        if (this.data.size() >= CHANNELS * BYTES_IN_CHANNEL) begin
            for (int i = 0; i < CHANNELS * BYTES_IN_CHANNEL; i++) begin
                data.push_back(this.data.pop_front());
                control.push_back(this.control.pop_front());
            end
            return 1'b1;
        end else begin
            return 1'b0;
        end
    endfunction

    // Adds data to buffer and tries to get back data which can be sent to
    // specified MII interface, returns '1' if get operation was successful
    function bit add_and_get(ref byte unsigned data[$], ref logic control[$]);
        this.add(data, control);
        return get(data, control);
    endfunction

    function bit is_empty();
        return this.data.size() == 0;
    endfunction

    // Empties the buffer and returns data of (n * CHANNELS * CHANNEL_WIDTH / 8) bytes
    function void flush(ref byte unsigned data[$], ref logic control[$]);
        int unsigned size = this.data.size();
        int unsigned bytes_overflowed = size % (CHANNELS * BYTES_IN_CHANNEL);
        int unsigned bytes_to_fill = (CHANNELS * BYTES_IN_CHANNEL) - bytes_overflowed;

        QUEUE_EMPTY : assert(data.size() == 0 && control.size() == 0);

        data = {data, this.data};
        control = {control, this.control};

        for (int i = 0; i < bytes_to_fill; i++) begin
            data.push_back(8'h07);
            control.push_back(1'b1);
        end

        this.data.delete();
        this.control.delete();
    endfunction
endclass
