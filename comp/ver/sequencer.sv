//-- sequencer.sv: Sequencer of sequences
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class Sequencer;

    int indexOfActualGenerator = -1;

    int indexOfActualSequence = -1;

    Sequence listOfSequences[$];

    Generator listOfGenerators[$];

    function new();
        indexOfActualGenerator = -1;
        indexOfActualSequence = -1;
    endfunction

    function bit isEnabled ();
        bit returnCode = 0;

        if (indexOfActualSequence >=0 && listOfSequences[indexOfActualSequence].enabled) begin
            returnCode = 1;
        end


        if(indexOfActualGenerator >=0 && listOfGenerators[indexOfActualGenerator].enabled)begin
            returnCode = 1;
        end

        return returnCode;
    endfunction

    task addSeq(Sequence seq);
        this.listOfSequences.push_back(seq);
        this.indexOfActualSequence=this.listOfSequences.size - 1;
    endtask

    task runSeqByName(string name);
        bit find=0;
        for(int index = 0; index<this.listOfSequences.size && find == 0; index++)begin
            if(this.listOfSequences[index].name == name)begin
                this.listOfSequences[index].setEnabled();
                this.indexOfActualSequence = index;
                find = 1;
            end
        end

        if(find == 0)begin
            $write("Sequence with name \"%s\" do not exist\n", name);
        end


    endtask

    task stopActSeq();
        this.listOfSequences[indexOfActualSequence].setDisabled();
    endtask

    task addGen(Generator gen);
        this.listOfGenerators.push_back(gen);
        this.indexOfActualGenerator=this.listOfGenerators.size - 1;
    endtask

    task runGenByIndex(int numOfTrans);
        if(indexOfActualGenerator >= 0 && indexOfActualGenerator <= listOfGenerators.size-1 && !listOfGenerators[indexOfActualGenerator].enabled) begin;
            fork
                this.listOfGenerators[indexOfActualGenerator].setEnabled(numOfTrans);
            join_none;
        end
    endtask

    task stopActGen();
        this.listOfGenerators[indexOfActualGenerator].setDisabled();
    endtask

    task display();
        $write("Actual sequence: %s\n", this.listOfSequences[indexOfActualSequence].name);
        foreach(this.listOfSequences[index])begin;
            this.listOfSequences[index].display();
        end
        $write("Index of actual generator: %s\n", this.indexOfActualGenerator);
        // foreach(this.listOfGenerators[index])begin;
        //     $write("%i. generator with transaction type %s", index, type(this.listOfGenerators[index].blueprint));
        // end
    endtask

endclass
