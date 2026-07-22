# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from concurrent.futures import ThreadPoolExecutor, Future
from threading import Thread, Event
from queue import Queue
from typing import Callable
from hashlib import sha3_512
from copy import copy

# NOTE: multithreaded implementation does not always return correct results (the thread pairs are not correctly synchonized)


class PCASD:
    # rules for celluar automatons
    _rules = (90, 105, 60, 75, 135, 165, 149, 45, 89, 150, 30, 101, 102, 153, 86, 195)

    # constants for random diffusion
    _A = 0xC4CA4238
    _B = 0xC81E728D
    _C = 0xECCBC87E
    _D = 0xA87FF679
    _E = 0xE4DA3B7F
    _F = 0x1679091C
    _G = 0x8F14E45F
    _H = 0xC9F0F895
    _K = (
        0x6B86B273FF34FCE1, 0xD4735E3A265E16EE, 0x4E07408562BEDB8B, 0x4B227777D4DD1FC6,
        0xEF2D127DE37B942B, 0xE7F6C011776E8DB7, 0x7902699BE42C8A8E, 0x2C624232CDD22177,
        0x19581E27DE7CED00, 0x4A44DC15364204A8, 0x4FC82B26AECB47D2, 0x6B51D431DF5D7F14,
        0x3FDBA35F04DC8C46, 0x8527A891E2241369, 0xE629FA6598D73276, 0xB17EF6D19C7A5B1E,
        0x4523540F1504CD17, 0x4EC9599FC203D176, 0x9400F1B21CB527D7, 0xF5CA38F748A1D6EA,
        0x6F4B6612125FB3A0, 0x785F3EC7EB32F30B, 0x535FA30D7E25DD8A, 0xC2356069E9D1E79C,
        0xB7A56873CD771F2C, 0x5F9C4AB08CAC7457, 0x670671CD97404156, 0x59E19706D51D39F6,
        0x35135AAA6CC23891, 0x624B60C58C9D8BFB, 0xEB1E33E8A81B697B, 0xE29C9C180C6279B0,
        0xC6F3AC57944A5314, 0x86E5014965866131, 0x9F14025AF0065B30, 0x76A50887D8F1C2E9,
        0x7A61B53701BEFDAE, 0xAEA92132C4CBEB26, 0x0B918943DF0962BC, 0xD59ECED1DED07F84,
        0x3D914F9348C9CC0F, 0x73475CB40A568E8D, 0x44CB730C420480A0, 0x71EE45A3C0DB9A98,
        0x811786AD1AE74ADF, 0x25FC0E7096FC6537, 0x31489056E0916D59, 0x98010BD9270F9B10,
        0x0E17DACA5F3E175F, 0x1A6562590EF19D10, 0x031B4AF5197EC30A, 0x41CFC0D1F2D127B0,
        0x2858DCD1057D3EAE, 0x2FCA346DB6561871, 0x02D20BBD7E394AD5, 0x7688B6EF52555962,
        0xC837649CCE43F272, 0x6208EF0F7750C111, 0x3E1E967E9B793E90, 0x39FA9EC190EEE7B6,
        0xD029FA3A95E174A1, 0x81B8A03F97E8787C, 0xDA4EA2A5506F2693, 0xA68B412C4282555F
    )

    # constants for SipRound
    _V0 = 0x736f6d6570736575
    _V1 = 0x646f72616e646f6d
    _V2 = 0x6c7967656e657261
    _V3 = 0x7465646279746573

    def __init__(self, key: bytes, ca_rounds: int = 20, rd_rounds: int = 64, block_width: int = 64,
                 mix_function: str = "RD_ROUND", multithreaded: bool = True):
        self._ca_rounds   : int      = ca_rounds
        self._rd_rounds   : int      = rd_rounds
        self._block_width : int      = block_width # bytes
        self.key          : int      = key
        self._mix_func    : str      = mix_function
        self._hash        : Callable = self._hash_multithreaded if multithreaded else self._hash_singlethreaded

    @property
    def key(self):
        return self._key.to_bytes(self._key_width // 8, "little")

    @key.setter
    def key(self, value: bytes):
        self._key       : int = int.from_bytes(value, "little")
        self._key_width : int = len(value) * 8

    def hash(self, message: bytes):
        return self._hash(message)

    def _hash_singlethreaded(self, message: bytes):
        block_index     : int        = 0
        results         : Queue[int] = Queue()

        # extending and padding the message
        message_aligned, blocks = self._extend_and_pad_message(message)

        # process all initial blocks
        for _ in range(blocks):
            block = int.from_bytes(message_aligned[:self._block_width], "little")
            message_aligned = message_aligned[self._block_width:]
            result = self._compression_function(block, block_index)
            results.put_nowait(result)
            block_index += 1

        # while there are results to be processed
        while results.qsize() > 1:
            queue_size = results.qsize()

            # getting all pairs, adding them and running compression function
            for _ in range(queue_size // 2):
                result1  = results.get_nowait()
                result2  = results.get_nowait()
                result = (result1 + result2) & (2**(self._block_width * 8) - 1)

                # if this is the last result
                if results.empty():
                    break

                new_result = self._compression_function(result, block_index)

                results.put_nowait(new_result)
                block_index += 1

            if queue_size % 2 == 1 and not results.empty():
                result = results.get_nowait()
                new_result = self._compression_function(result, block_index)
                results.put_nowait(new_result)
                block_index += 1

        # last result in queue is the resulting hash
        hash: bytes = result.to_bytes(self._block_width, "little")

        return hash

    def _hash_multithreaded(self, message: bytes):
        running_threads        : Queue[Future]      = Queue()
        thread_results         : Queue[int]         = Queue()
        new_thread_event       : Event              = Event()
        new_result_event       : Event              = Event()
        executor               : ThreadPoolExecutor = ThreadPoolExecutor()

        # extending and padding the message
        message_aligned, blocks = self._extend_and_pad_message(message)
        nodes: int = blocks * 2 - 1

        # creating threads for collecting and processing thread results
        collect_results_thread: Thread = Thread(target=self._collect_results, args=(nodes, running_threads, thread_results, new_thread_event, new_result_event))
        process_results_thread: Thread = Thread(target=self._process_results, args=(nodes, blocks, running_threads, thread_results, executor, new_thread_event, new_result_event))

        # starting collecting and processing threads
        collect_results_thread.start()
        process_results_thread.start()

        # start compression threads for all message blocks
        for i in range(blocks):
            # converting message block to int and removing it from message
            block = int.from_bytes(message_aligned[:self._block_width], "little")
            message_aligned = message_aligned[self._block_width:]
            # starting thread processing the message block
            comp_thread = executor.submit(self._compression_function, block, i)
            running_threads.put(comp_thread)
            new_thread_event.set()

        # waiting for the processing and collecting threads to finish
        collect_results_thread.join()
        process_results_thread.join()

        # last remaining value in results queue is the final hash
        hash: bytes = (thread_results.get()).to_bytes(self._block_width, "little")

        return hash

    def _collect_results(self, nodes: int, running_threads: Queue[Future], thread_results: Queue[int], new_thread_event: Event, new_result_event: Event):
        """
        Collecting results of threads and storing them in thread_results queue.
        """
        for _ in range(nodes):
            new_thread_event.wait()
            comp_thread = running_threads.get()
            result = comp_thread.result()
            # storing result to the queue
            thread_results.put(result)
            new_result_event.set()

    def _process_results(self, nodes: int, blocks: int, running_threads: Queue[Future], thread_results: Queue[int], executor: ThreadPoolExecutor, new_thread_event: Event, new_result_event: Event):
        """
        Looking for results from finished compression threads.
        """
        for i in range(nodes // 2):
            new_result_event.wait()
            result1 = thread_results.get()
            new_result_event.wait()
            result2 = thread_results.get()

            # compress all results accept for the last one
            if i < (nodes // 2) - 1:
                comp_thread = executor.submit(self._compression_function, (result1 + result2) & (2**(self._block_width * 8) - 1), blocks)
            else:
                comp_thread = executor.submit(lambda result: result, (result1 + result2) & (2**(self._block_width * 8) - 1))

            running_threads.put(comp_thread)
            blocks += 1
            new_thread_event.set()

    def _extend_and_pad_message(self, message: bytes) -> tuple[bytearray, int]:
        length_padding  : int        = self._block_width // 8
        blocks          : int        = PCASD._Ceildiv(len(message) + length_padding + 1, self._block_width)
        message_aligned : bytearray  = bytearray(blocks * self._block_width)

        # aligning the message to whole blocks
        message_aligned[:len(message)] = message

        # adding padding byte
        message_aligned[len(message)] = 0x80

        # adding length od the message to the end of the padded message
        message_aligned[len(message_aligned) - length_padding:] = (len(message) * 8).to_bytes(length_padding, "little")

        return message_aligned, blocks

    def _extend_message(self, m: int) -> list[int]:
        mw         : list[int] = list()
        word_count : int       = self._block_width // 4

        mb = m.to_bytes(self._block_width, "little")
        mw = [int.from_bytes(mb[i * 4: (i + 1) * 4], "little") for i in range(word_count)]

        if self._rd_rounds > 4:
            sigma_max = self._rd_rounds + 4
        else:
            sigma_max = word_count

        # scaling the word choice based on the word count
        match (word_count):
            case 4:
                ch = (4, 1, 3, 2)
            case 8:
                ch = (8, 1, 5, 3)
            case 16:
                ch = (16, 3, 9, 4)
            case _:
                raise ValueError(f"Word count of {word_count} is not supported by _extend_message of PCASD.")

        for i in range(word_count, sigma_max):
            x = mw[i - ch[0]] ^ PCASD._Rotl32(mw[i - ch[1]], 7) ^ PCASD._Rotl32(mw[i - ch[2]], 1)

            if i >= word_count and i < sigma_max // 2:
                mw.append(PCASD._Sigma0_32(x) ^ PCASD._Rotl32(mw[i - ch[3]], 19))
            else:
                mw.append(PCASD._Sigma1_32(x) ^ PCASD._Rotl32(mw[i - ch[3]], 19))

        for i in range(sigma_max, sigma_max + self._rd_rounds):
            mw.append(mw[i - sigma_max] ^ mw[i - sigma_max + 4])

        return mw

    def _rd_round(self, mw: list[int], a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int, k: int
                  ) -> tuple[int, int, int, int, int, int, int, int]:
        word_count = self._block_width // 4

        if self._rd_rounds > 4:
            sigma_max = self._rd_rounds + 4
        else:
            sigma_max = word_count

        maj_ABC   = PCASD._Maj(a, b, c)
        rotl12_A  = PCASD._Rotl32(a, 12)
        rotlk_Kk  = PCASD._Rotl32(self._K[k] & 0xFFFFFFFF, k)
        add_AEK   = (rotl12_A + e + rotlk_Kk) & 0xFFFFFFFF
        rotl7_AEK = PCASD._Rotl32(add_AEK, 7)

        ch_ABC    = PCASD._Ch(a, b, c)
        sigma_arg = (ch_ABC + h + rotl7_AEK + mw[k]) & 0xFFFFFFFF

        # A = Maj(A,B,C) + D + ROTL7(ROTL12(A) + E + ROTLk(K)) + ROTL12(A) + MW[k + 68]
        new_a = (maj_ABC + d + rotl7_AEK + rotl12_A + mw[k + sigma_max]) & 0xFFFFFFFF
        # B = CA(A, k, 1)
        new_b = PCASD._CA(a, 32, self._rules[k % 16], 1) & 0xFFFFFFFF
        # C = ROTL9(B)
        new_c = PCASD._Rotl32(b, 9)
        # D = C
        new_d = c
        # E = Sigma0(Ch(A, B, C) + H + ROTL7(ROTL12(A) + E + ROTLk(K)) + MW[k])
        new_e = self._Sigma0_32(sigma_arg)
        # F = E
        new_f = e
        # G = ROTL19(F)
        new_g = PCASD._Rotl32(f, 19)
        # H = G
        new_h = g

        return new_a, new_b, new_c, new_d, new_e, new_f, new_g, new_h

    def _compression_function(self, block: int, index: int) -> int:
        # getting the coresponding rule based on the key and index
        rule: int = self._get_rule_at_index(index)

        # running the celluar automaton
        temp: int = PCASD._CA(block, self._block_width * 8, rule, self._ca_rounds)

        match (self._mix_func):
            # generates random diffusion function specified by PCASD
            case "RD_ROUND":
                # setting up the initial state
                initial_state = [self._A, self._B, self._C, self._D, self._E, self._F, self._G, self._H]
                state = copy(initial_state)

                # extending the message block
                mw: list[int] = self._extend_message(temp)

                for k in range(self._rd_rounds):
                    a, b, c, d, e, f, g, h = state
                    state = list(self._rd_round(mw, a, b, c, d, e, f, g, h, k))

                # concanating the registers
                result = 0

                for i, reg in enumerate(state):
                    result |= reg << (i * 32)

            # generating siphash-style mix function
            case "SIPROUND":
                word_count: int = self._block_width // 8

                v0, v1, v2, v3 = (self._V0, self._V1, self._V2, self._V3)

                for i in range(word_count):
                    v3 ^= (temp >> (i * 64)) & 0xFFFFFFFFFFFFFFFF

                    for _ in range(self._rd_rounds):
                        v0, v1, v2, v3 = PCASD._SipRound(v0, v1, v2, v3)

                    v0 ^= (temp >> (i * 64)) & 0xFFFFFFFFFFFFFFFF

                # concanating the registers
                result = (v3 << 192) | (v2 << 128) | (v1 << 64) | v0

            case _:
                raise AttributeError(f"Unsupported mix function '{self._mix_func}'.")

        return result & (2**(self._block_width * 8) - 1)

    def _get_rule_at_index(self, index: int):
        return self._rules[PCASD._RotrY(self._key, self._key_width, (index * 4) % self._key_width) & 0xF]

    @staticmethod
    def _Rotl32(x: int, b: int) -> int:
        return PCASD._RotlY(x, 32, b)

    @staticmethod
    def _Rotl64(x: int, b: int) -> int:
        return PCASD._RotlY(x, 64, b)

    @staticmethod
    def _RotlY(x: int, y: int, b: int) -> int:
        return ((x << b) | (x >> y - b)) & (2 ** y - 1)

    @staticmethod
    def _RotrY(x: int, y: int, b: int) -> int:
        return ((x >> b) | (x << (y - b))) & (2 ** y - 1)

    @staticmethod
    def _Ceildiv(n: int, d: int) -> int:
        return (n + d - 1) // d

    @staticmethod
    def _CA(state: int, bit_length: int, rule: int, rounds: int) -> int:
        if bit_length <= 0:
            return 0 if rounds > 0 else state

        mask = (1 << bit_length) - 1

        r0 = rule & 1
        r1 = rule & 2
        r2 = rule & 4
        r3 = rule & 8
        r4 = rule & 16
        r5 = rule & 32
        r6 = rule & 64
        r7 = rule & 128

        for _ in range(rounds):
            L = ((state >> 1) | (state << (bit_length - 1))) & mask
            C = state
            R = ((state << 1) | (state >> (bit_length - 1))) & mask

            nL = L ^ mask
            nC = C ^ mask
            nR = R ^ mask

            new_state = 0

            if r0:
                new_state |= (nL & nC & nR)
            if r1:
                new_state |= (nL & nC & R)
            if r2:
                new_state |= (nL & C & nR)
            if r3:
                new_state |= (nL & C & R)
            if r4:
                new_state |= (L & nC & nR)
            if r5:
                new_state |= (L & nC & R)
            if r6:
                new_state |= (L & C & nR)
            if r7:
                new_state |= (L & C & R)

            state = new_state

        return state

    @staticmethod
    def _Sigma0_32(x: int) -> int:
        return (x ^ PCASD._Rotl32(x, 13) ^ PCASD._Rotl32(x, 14)) & 0xFFFFFFFF

    @staticmethod
    def _Sigma0_64(x: int) -> int:
        return (x ^ PCASD._Rotl64(x, 13) ^ PCASD._Rotl64(x, 14)) & 0xFFFFFFFFFFFFFFFF

    @staticmethod
    def _Sigma1_32(x: int) -> int:
        return (x ^ PCASD._Rotl32(x, 31) ^ PCASD._Rotl32(x, 29)) & 0xFFFFFFFF

    @staticmethod
    def _Ch(x: int, y: int, z: int) -> int:
        return ((x & y) ^ ((~x) & z)) & 0xFFFFFFFFFFFFFFFF

    @staticmethod
    def _Maj(x: int, y: int, z: int) -> int:
        return ((x & y) ^ (x & z) ^ (y & z)) & 0xFFFFFFFFFFFFFFFF

    @staticmethod
    def _SipRound(v0: int, v1: int, v2: int, v3: int):
        v0  = (v0 + v1) & 0xFFFFFFFFFFFFFFFF
        v1  = PCASD._Rotl64(v1, 13)
        v1 ^= v0
        v0  = PCASD._Rotl64(v0, 32)
        v2  = (v2 + v3) & 0xFFFFFFFFFFFFFFFF
        v3  = PCASD._Rotl64(v3, 16)
        v3 ^= v2
        v0  = (v0 + v3) & 0xFFFFFFFFFFFFFFFF
        v3  = PCASD._Rotl64(v3, 21)
        v3 ^= v0
        v2  = (v2 + v1) & 0xFFFFFFFFFFFFFFFF
        v1  = PCASD._Rotl64(v1, 17)
        v1 ^= v2
        v2  = PCASD._Rotl64(v2, 32)

        return v0, v1, v2, v3


# self test - comparing results of single-threaded and multi-threaded implementations
def test():
    block_width = 16

    key_hash = sha3_512()
    key_hash.update(b"secret key")
    key = key_hash.digest()[:block_width]

    pcasd_singlethreaded = PCASD(key, multithreaded=False, rd_rounds=32, block_width=block_width)
    pcasd_multithreaded  = PCASD(key, multithreaded=True, rd_rounds=32, block_width=block_width)

    # testing examples messages from the article
    example_messages = [
        "1",
        "Parallel Hash Algorithm Based on Cellular automata and Stochastic Diffusion Model",
        "Parallel Hash Algorithm Based on cellular automata and Stochastic Diffusion Model",
        "1Parallel Hash Algorithm Based on Cellular automata and Stochastic Diffusion Model",
        "Parallel Hash Algorithm Based on Cellular-Automata and Stochastic Diffusion Model",
        "Parallel Hosh Algorithm Based on Cellular automata and Stochastic Diffusion Modl",
        "Paralllel Hash Algorithm Based on Cellular automata and Stochastic Diffusion Model",
        "Parallel Hash Algorithm Based on CellularAutomata and Stochastic Diffusion Model"
    ]

    for example in example_messages:
        print("single threaded:\n")
        hash_single = int.from_bytes(pcasd_singlethreaded.hash(example.encode()), "little")
        print(f"\nMessage: '{example}' generated hash {hex(hash_single)}, bits: {hash_single.bit_count()}. (single)\n\n")

        hash_multi  = int.from_bytes(pcasd_multithreaded.hash(example.encode()), "little")
        print("multithreaded:\n")
        print(f"\nMessage: '{example}' generated hash {hex(hash_multi)}, bits: {hash_multi.bit_count()}. (multi)\n\n")

        # testing if the single and multi threaded implementations match
        if hash_single != hash_multi:
            print(f"Single and multi threaded hashes don't match for message '{example}'! {hex(hash_single)=}, {hex(hash_multi)=}")
            exit(1)
