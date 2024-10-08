//-- idTable.sv: Object that holds information about each ID.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

// -- This class is designed to contain information about Ids. ----------------
class IdTable;

    typedef struct {
        int idCount =0; //  Count of transactions with this id in component at the moment.
        bit status  =0; //  Status of the ID. 0-ready (can send this id to input interface) 1-confirmed (this id is confirmed at the moment).
    } tIdTableItem;

    tIdTableItem idTable [2**ID_WIDTH];
    semaphore sem;

    function new();
        sem = new(1);
    endfunction

    //  The transaction with same ID as index was sent to component. Counter in idTable[index] was incresed.
    task addToCounter(int index);
        sem.get(1);
        idTable[index].idCount+=1;
        if(VERBOSE_LEVEL>1)begin
            $timeformat(-9, 3, " ns", 8);
            $write("ID %1d is in the component %d times\nAnd status is %d %t\n",index,idTable[index].idCount,idTable[index].status,$time);
        end
        sem.put(1);
    endtask

    //  The transaction with same ID as index was sent from component. Counter in idTable[index] was decreased.
    task subFromCounter(int index);
        sem.get(1);
        idTable[index].idCount-=1;

        if(idTable[index].idCount<=0)begin
            if(VERBOSE_LEVEL>1)begin
                $timeformat(-9, 3, " ns", 8);
                $write("ID: %d is no longer in the component %t\n",index,$time);
            end
            idTable[index].status=0;
            idTable[index].idCount=0;
        end

        if(VERBOSE_LEVEL>1)begin
            $timeformat(-9, 3, " ns", 8);
            $write("Transaction with ID: %d is at the output of component\nThere is %d same IDs in the component\nAnd status is: %d %t\n",index,idTable[index].idCount,idTable[index].status,$time);
        end
        sem.put(1);
    endtask

    //  Change status of the idTable[index] to confirmed.
    //  The task was successful if the status is 1. Otherwise the task was failure.
    task setCounterToConfState(int index, ref bit status);
        sem.get(1);
        if(idTable[index].status==0&&idTable[index].idCount>0)begin
            idTable[index].status=1;
            if(VERBOSE_LEVEL>1)begin
                $timeformat(-9, 3, " ns", 8);
                $write("ID %d confirmed. With this value there is %d IDs in the component\nAnd the status is: %d %t\n",index,idTable[index].idCount,idTable[index].status,$time);
            end
        end
        status = idTable[index].status;
        sem.put(1);
    endtask

    task display();
        sem.get(1);
        foreach(idTable[i])$write("ID: %d - count %d, status %d\n",i,idTable[i].idCount,idTable[i].status);
        sem.put(1);
    endtask

endclass
