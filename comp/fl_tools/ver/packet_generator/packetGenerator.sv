/*
 * packetGenerator.sv: Packet generator
 * Copyright (C) 2008 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */
import sv_common_pkg::*;

/*
 * Structure used for storage of protocol class and it's probability.
 */
typedef struct
{
   Layer    protocol;
   int      probability;
} LayerP;

/*
 * This class implements packet generator, which generates random packets
 * acording set of used protocols and their probabilities. Packets are
 * generated into PacketFrameLink transaction, which is standart FrameLink
 * transaction with added pointer to double linked list containing used
 * randomized protocols. FrameLink data are set to generated packet data.
 * This class inherates from Generator abstract class.
 */
class PacketGenerator extends Generator;
   /*
    * Class attributes:
    * protocols     - array of protocols with their probabilities
    * protocolCount - number of protocols
    * minMTU        - minimal size of packet (can be grater if generated
    *                 protocol's header's sizes are grater)
    * maxMTU        - maximal size of packet (can be grater if generated
    *                 protocol's header's sizes are grater)
    *
    * Class constants:
    * arrayFactor - indicate how much entities will be added to dynamic array
    *               during reallocation.
    * treshold    - number of generated protocols. When this value is reached
    *               generation is stoped. Used to prevent inifinity number of
    *               generated protocols when protocol encapsulation is used.
    */
         LayerP   protocols[];
         int      protocolCount;
         int      minMTU;
         int      maxMTU;

   const int      arrayFactor = 5;
   const int      treshold    = 50;

   /*
    * Class constructor.
    *
    * Parametrs:
    * inst      - name of instance
    * stream_id - id of generated stream, default -1
    * transMbx  - output transaction mailbox, default null which means that
    *             transaction mailbox will be created by generator
    * minMTU    - minimal size of packet, defaul 64B
    * maxMTU    - maximal size of packet, default 1522B
    */
   function new(string inst, int stream_id = -1, tTransMbx transMbx = null, int minMTU = 64, int maxMTU = 1522);
      super.new(inst, stream_id, transMbx);
      protocols = new[arrayFactor];
      protocolCount = 0;
      this.minMTU = minMTU;
      this.maxMTU = maxMTU;
   endfunction: new

   /*
    * Enables generator for generating transactions.
    *
    * Parametrs:
    * nInst - number of generated instances, default 32'hFFFFFFFF
    */
   task setEnabled(int unsigned nInst=32'hFFFFFFFF);
      enabled = 1;
      stop_after_n_insts = nInst;
      data_id = 0;

      if ( blueprint != null)
      begin
         fork
            run();
         join_none;
      end
      else
         $write("The blueprint transaction in generator must be set\n");

   endtask : setEnabled

   /*
    * Function adds protocol blueprint with it's probability to generator.
    *
    * Parametrs:
    * protocol    - protocol blueprint
    * probability - protocol probability
    *
    * Return 1 if OK.
    */
   function bit addProtocol(Layer protocol, int probability);
      if (protocolCount == protocols.size)
      begin
         protocols = new[protocols.size + arrayFactor](protocols);
      end;

      protocolCount = protocolCount + 1;
      protocols[protocolCount - 1].protocol = protocol;
      protocols[protocolCount - 1].probability = probability;

      return 1'b1;
   endfunction: addProtocol

   /*
    * This task generates random packet.
    */
   virtual task automatic run();
      // used variables
      PacketFrameLinkTransaction trans;
      Transaction                mezi;
      LayerP                     lProtocols[];
      int                        protocolProbabilitySum = 0;
      int                        lProtocolCount = 0;
      int                        random = 0;
      int                        currentProbabilitySum = 0;
      Layer                      protocol;
      Layer                      pomProtocol, pomProtocol2;

      int                        pom = 0;

      // While is enabled or stop = 0 or number of generated transactions not
      // exceed limit
      while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0) && protocolCount > 0) begin
         // resets variables for new random packet generation
         lProtocols.delete;
         protocolProbabilitySum = 0;
         lProtocolCount = 0;
         random = 0;
         currentProbabilitySum = 0;
         protocol = null;
         pomProtocol = null;
         pomProtocol2 = null;

         pom = 0;

         // Selects protocols which can be in the lowest level of protocol
         // hierarchy such as Ethernet. This done by comparsion of protocol
         // atrtribute level with 0. If comparsion is true then protocol is
         // added and sum of probabilities is upgraded.
         for (int j = 0; j < protocolCount; j++)
         begin
            if (protocols[j].protocol.level == 0)
            begin
               if (lProtocolCount == lProtocols.size)
               begin
                  lProtocols = new[lProtocols.size + arrayFactor](lProtocols);
               end;

               lProtocolCount = lProtocolCount + 1;
               lProtocols[lProtocolCount - 1].protocol = protocols[j].protocol.copy;
               lProtocols[lProtocolCount - 1].probability = protocols[j].probability;
               protocolProbabilitySum = protocolProbabilitySum + protocols[j].probability;
            end;
         end;

         // generate random number in range <0, protocolProbabilitySum)
         random = {$random} %  protocolProbabilitySum;

         // Randomly select one of the lowest protocol in protocol hierarchy,
         // which were selected in previous for cycle. The currently selected
         // protocol is added to the double linked list.
         for (int j = 0; j < lProtocolCount; j++)
         begin
            if (random < lProtocols[j].probability + currentProbabilitySum)
            begin
               protocol = lProtocols[j].protocol.copy;
               protocol.previous = null;
               protocol.next = null;
               pomProtocol = protocol;
               break;
            end
            else
               currentProbabilitySum = currentProbabilitySum + lProtocols[j].probability;
         end

         // Randomly selects upper layer protocols until last is selected.
         do
         begin
            // variable reinitialisation
            lProtocols.delete;
            lProtocols = new[arrayFactor];
            lProtocolCount = 0;
            protocolProbabilitySum = 0;

            // Select upper protocols which are compatibile with current
            // protocol. This is done by invoking current class method
            // checkType(). If the protocol is compatible then protocol is
            // added and sum of probabilities is upgraded.
            for (int j = 0; j < protocolCount; j++)
            begin
               if (pomProtocol.checkType(protocols[j].protocol.typ, protocols[j].protocol.subtype, protocols[j].protocol.name) == 1)
               begin
                  if (lProtocolCount == lProtocols.size)
                  begin
                     lProtocols = new[lProtocols.size + arrayFactor](lProtocols);
                  end;

                  lProtocolCount = lProtocolCount + 1;
                  lProtocols[lProtocolCount - 1].protocol = protocols[j].protocol.copy;
                  lProtocols[lProtocolCount - 1].probability = protocols[j].probability;
                  protocolProbabilitySum = protocolProbabilitySum + protocols[j].probability;
               end
            end

            // generate random number in range <0, protocolProbabilitySum)
            random = {$random} %  protocolProbabilitySum;

            // Randomly select one of selected compatibile protocols, which
            // were selected in previous for cycle. The currently selected
            // protocol is added to the double linked list.
            for (int j = 0; j < lProtocolCount; j++)
            begin
               if (random < lProtocols[j].probability + currentProbabilitySum)
               begin
                  pomProtocol2 = lProtocols[j].protocol.copy;
                  pomProtocol2.previous = pomProtocol;
                  pomProtocol2.next = null;
                  pomProtocol.next = pomProtocol2;
                  pomProtocol = pomProtocol2;
                  break;
               end
               else
                  currentProbabilitySum = currentProbabilitySum + lProtocols[j].probability;
            end

            // Upgarde count of used prtocols if is this number grater the
            // treshold stop generation. This is used to prevent infinity
            // number of protocol encapsulations such as IP in IP, etc.
            pom = pom + 1;
            if (pom == treshold)
               $stop();

         end
         while (pomProtocol.typ != "RAW");  // when protocol type is RAW
                                            // end generation

         // PacketFrameLink Transaction blueprint will be copied for final
         // transaction generation.
         mezi = blueprint.copy;
         $cast(trans, mezi);

         // set minimal and maximal size of packet
         protocol.minMTU = minMTU;
         protocol.maxMTU = maxMTU;

         // Randomize generated list of protocols to generate random packet
         // content.
         void'(protocol.randomize);

         // When getLength() function is called first time length/size fields
         // in protocols are filled.
         void'(protocol.getLength(0));

         // Add double linked list to the generated transaction.
         trans.packet = protocol;


         // Set common transaction attributes used for identifing transaction
         // origin.
         trans.stream_id    = stream_id;       // Set stream id
         trans.scenario_id  = -1;              // Set default scenario
         trans.data_id      = data_id;         // Set instance count

         // FrameLink data array is filled with protocol data.
         trans.connect;

         transMbx.put(trans);                  // Put transaction to mailbox
         data_id=data_id + 1;                    // Increment instance counter
      end;

      // When last transaction is sent, disable generator.
      enabled = 0;

   endtask : run

endclass: PacketGenerator

