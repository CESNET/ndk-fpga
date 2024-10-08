/*!
 * \file        driver.sv
 * \brief       AXI4S Driver
 * \author      Martin Spinler <spinler@cesnet.cz>
 * \date        2018
 * \copyright   CESNET, z. s. p. o.
 */

class AxiCQTransaction extends AxiTransaction;
    byte firstBe;
    byte lastBe;
endclass

class AxiCCTransaction #(AXI_ITEM_WIDTH) extends AxiTransaction #(AXI_ITEM_WIDTH);
    byte firstBe;
    byte lastBe;
endclass

class MiTransaction extends Transaction;

    rand byte unsigned data[];
    rand longint unsigned addr;
    rand bit rw;

    constraint arr_size {
        data.size() > 0;
        data.size() <= 512;

        (addr % 4096) + data.size() <= 4096;

        if (rw == 1) {
            /* Max Payload Size for write requests */
            data.size() <= 256;
        }
    }

    virtual function Transaction copy(Transaction to = null);
        MiTransaction tr;

        if (to == null)
            tr = new();
        else
            $cast(tr, to);

        copy = tr;
    endfunction

endclass

class AxiCQDriver #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, AXI_ITEM_WIDTH) extends Axi4SDriver #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, AXI_ITEM_WIDTH);

    function new(string inst, tTransMbx transMbx, virtual iAxi4SRx#(DATA_WIDTH, USER_WIDTH, ITEM_WIDTH).tb v);
        super.new(inst, transMbx, v);
    endfunction

    virtual task invalidateWordData();
        super.invalidateWordData();
        vif.cb.TUSER <= 'x;
    endtask

    virtual task exposeWordData(AxiTransaction tr, int cycle, inout finished);
        AxiCQTransaction cq;

        logic[AXI_CCUSER_WIDTH-1:0] data = 'x;

        $cast(cq, tr);
        super.exposeWordData(tr, cycle, finished);

        data[80] = 1'b0;

        if (cycle == 0) begin
            data[3:0] = cq.firstBe;
            data[11:8] = cq.lastBe;
            data[80] = 1'b1;
        end

        if (finished) begin
        end

        vif.cb.TUSER <= data;
    endtask

endclass

class Axi4SCMiRoot #(AXI_ITEM_WIDTH) extends MonitorCbs;

    string inst;
    bit enabled;
    int verbosity = 0;
    tTransMbx transMbx;
    tTransMbx transMbxRead;

    semaphore read_sem;

    function new(string i);
        inst = i;
        enabled = 0;
        transMbx = new();
        transMbxRead = new();
        read_sem = new(1);
    endfunction

    task setEnabled();
        fork
            run();
        join_none;
    endtask

    task run();
    endtask

    task nfb_read64(logic [31:0] address, output logic [63:0] data);
        Transaction transaction;
        MiTransaction tr = new();
        tr.rw = 0;
        tr.addr = address;
        tr.data = new[8];
        read_sem.get(1);
        sendRequest(tr);
        transMbxRead.get(transaction);
        $cast(tr, transaction);
        /* Bytes 0-11 is PCIe/AXI header */
        {>>byte{data}} = tr.data[12:19];
        read_sem.put(1);
    endtask

    task nfb_read32(logic [31:0] address, output logic [31:0] data);
        Transaction transaction;
        MiTransaction tr = new();
        tr.rw = 0;
        tr.addr = address;
        tr.data = new[4];
        read_sem.get(1);
        sendRequest(tr);
        transMbxRead.get(transaction);
        $cast(tr, transaction);
        /* Bytes 0-11 is PCIe/AXI header */
        {>>byte{data}} = tr.data[12:15];
        read_sem.put(1);
    endtask

    task nfb_write32(longint unsigned address, logic [31:0] data);
        MiTransaction tr = new();
        tr.rw = 1;
        tr.addr = address;
        tr.data = {<<byte{data}};
        sendRequest(tr);
    endtask

    task sendRequest(MiTransaction trIn);
        logic[127:0] header;

        logic[15:0] requester;
        logic[10:0] length;
        logic[3:0] reqType;
        logic[7:0] tag = 0;
        logic[7:0] func;
        logic[2:0] bar;
        logic[5:0] barap;

        logic[3:0] mapFirstBe[integer];
        logic[3:0] mapLastBe[integer];

        byte unsigned headerArray[16];
        byte unsigned data[];
        int dataLength;

        Transaction toIn;
        AxiCQTransaction trOut;

        mapFirstBe[0] = 4'hF;
        mapFirstBe[1] = 4'hE;
        mapFirstBe[2] = 4'hC;
        mapFirstBe[3] = 4'h8;

        mapLastBe[0] = 4'hF;
        mapLastBe[1] = 4'h1;
        mapLastBe[2] = 4'h3;
        mapLastBe[3] = 4'h7;

        dataLength = trIn.data.size();
        length = (trIn.addr % 4 + dataLength + 3) / 4;

        if (trIn.rw) begin
            reqType = 4'h1;
            dataLength = (dataLength + 3) & ~3;
            dataLength = length * 4;
            data = new[dataLength];

            for (int i = 0; i < trIn.data.size(); i++)
                data[i + trIn.addr % 4] = trIn.data[i];
        end else begin
            reqType = 4'h0;
            dataLength = 0;
            data = new[dataLength];
        end

        trOut = new();

        trOut.firstBe = mapFirstBe[trIn.addr % 4];
        trOut.lastBe = mapLastBe[(trIn.addr + trIn.data.size()) % 4];
        if (length <= 1) begin
            trOut.firstBe &= trOut.lastBe;
            trOut.lastBe = 0;
        end
        trOut.lastBe = mapLastBe[(trIn.addr + trIn.data.size()) % 4];

        barap = 6'd26;
        bar = 0;
        tag++;
        func= 8'h0;

        header = {
            7'h0, barap, bar, func, tag,
            requester, 1'b0, reqType, length,
            (trIn.addr & 64'hFFFFFFC)
        };

        {<<byte{headerArray}} = header;
        trOut.data = {headerArray, data};

        if (verbosity) begin
            trIn.display();
            trOut.display();
        end

        transMbx.put(trOut);
    endtask

    virtual task post_rx(Transaction transaction, string inst);
        AxiCCTransaction #(AXI_ITEM_WIDTH) tr;
        MiTransaction mi;

        $cast(tr, transaction);

        mi = new();
        mi.data = {>>byte{tr.data}};
        transMbxRead.put(mi);
    endtask

endclass
