# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# This implementation has been greatly inspired by
# SMHasher3 Chaskey C++ implementation available at
# https://gitlab.com/fwojcik/smhasher3/-/blob/main/hashes/chaskey.cpp

from copy import copy
from typing import Union


class Chaskey:
    @staticmethod
    def Hash_8_64(message: bytes, key: bytes) -> bytes:
        return Chaskey.Hash64(message, key, 8)

    @staticmethod
    def Hash_12_64(message: bytes, key: bytes) -> bytes:
        return Chaskey.Hash64(message, key, 12)

    @staticmethod
    def Hash64(message: bytes, key: bytes, rounds: int) -> bytes:
        return Chaskey._Hash(message, key, rounds)[:8]

    @staticmethod
    def Hash_8_128(message: bytes, key: bytes) -> bytes:
        return Chaskey.Hash128(message, key, 8)

    @staticmethod
    def Hash_12_128(message: bytes, key: bytes) -> bytes:
        return Chaskey.Hash128(message, key, 12)

    @staticmethod
    def Hash128(message: bytes, key: bytes, rounds: int) -> bytes:
        return Chaskey._Hash(message, key, rounds)

    _C = (0x00, 0x87)

    @staticmethod
    def _Rotl32(x: int, b: int) -> int:
        return ((x << b) | (x >> 32 - b)) & 0xFFFFFFFF

    @staticmethod
    def _Ceildiv(n: int, d: int) -> int:
        return (n + d - 1) // d

    @staticmethod
    def _TimesTwo(x: list) -> list[int]:
        out = [0, 0, 0, 0]

        out[0] = ((x[0] << 1) ^ Chaskey._C[x[3] >> 31]) & 0xFFFFFFFF
        out[1] = ((x[1] << 1) | (x[0] >> 31))           & 0xFFFFFFFF
        out[2] = ((x[2] << 1) | (x[1] >> 31))           & 0xFFFFFFFF
        out[3] = ((x[3] << 1) | (x[2] >> 31))           & 0xFFFFFFFF

        return out

    @staticmethod
    def _Round(v: list):
        v[0]  = (v[0] + v[1]) & 0xFFFFFFFF
        v[1]  = Chaskey._Rotl32(v[1],  5)
        v[1] ^= v[0]
        v[0]  = Chaskey._Rotl32(v[0], 16)
        v[2]  = (v[2] + v[3]) & 0xFFFFFFFF
        v[3]  = Chaskey._Rotl32(v[3],  8)
        v[3] ^= v[2]
        v[0]  = (v[0] + v[3]) & 0xFFFFFFFF
        v[3]  = Chaskey._Rotl32(v[3], 13)
        v[3] ^= v[0]
        v[2]  = (v[2] + v[1]) & 0xFFFFFFFF
        v[1]  = Chaskey._Rotl32(v[1],  7)
        v[1] ^= v[2]
        v[2]  = Chaskey._Rotl32(v[2], 16)

    @staticmethod
    def _Hash(message: bytes, key: bytes, rounds: int) -> bytes:
        msg    : bytes = copy(message)
        msglen : int   = len(msg)
        remain : int   = msglen & 0xF
        k      : list  = [int.from_bytes(key[0:4], "little"),
                          int.from_bytes(key[4:8], "little"),
                          int.from_bytes(key[8:12], "little"),
                          int.from_bytes(key[12:16], "little")]

        k1     : list  = Chaskey._TimesTwo(k)
        k2     : list  = Chaskey._TimesTwo(k1)
        v      : list  = copy(k)
        cycles : int   = Chaskey._Ceildiv(msglen, 16) - 1

        if msglen > 0:
            for _ in range(cycles):
                v[0] ^= int.from_bytes(msg[0:4], "little")
                v[1] ^= int.from_bytes(msg[4:8], "little")
                v[2] ^= int.from_bytes(msg[8:12], "little")
                v[3] ^= int.from_bytes(msg[12:16], "little")

                for _ in range(rounds):
                    Chaskey._Round(v)

                msg = msg[16:]

        lastblock: Union[bytes, bytearray]
        if msglen > 0 and remain == 0:
            lastkey   = k1
            lastblock = msg
        else:
            lastkey   = k2
            lastblock = bytearray(remain + 1)
            lastblock[:remain] = msg
            lastblock[remain]  = 0x01

        v[0] ^= int.from_bytes(lastblock[0:4], "little")
        v[1] ^= int.from_bytes(lastblock[4:8], "little")
        v[2] ^= int.from_bytes(lastblock[8:12], "little")
        v[3] ^= int.from_bytes(lastblock[12:16], "little")

        v[0] ^= lastkey[0]
        v[1] ^= lastkey[1]
        v[2] ^= lastkey[2]
        v[3] ^= lastkey[3]

        for _ in range(rounds):
            Chaskey._Round(v)

        v[0] ^= lastkey[0]
        v[1] ^= lastkey[1]
        v[2] ^= lastkey[2]
        v[3] ^= lastkey[3]

        hash: int = v[0] | (v[1] << 32) | (v[2] << 64) | (v[3] << 96)

        return hash.to_bytes(16, "little")


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Chaskey hash function")
    parser.add_argument("message", help="message to be hashed.")
    parser.add_argument("key", help="128-bit key, enter in hexadecimal format.")
    parser.add_argument("-r", "--rounds", default=8, type=int, help="Number of round functions that will be run. 8 by default.")
    parser.add_argument("-w", "--width", default=16, type=int, help="Width of the resulting hash in bytes. Maximum is 16B. 16 by default.")

    args = parser.parse_args()

    if len(args.key) < 32:
        args.key += "0" * (32 - len(args.key))

    if len(args.key) > 32:
        print("Warning: the key has been truncated to 16 bytes.")
        args.key = args.key[:32]

    if args.width <= 0:
        print("Error: hash width must be greater than zero.")
        exit(1)

    if args.width > 16:
        print("Error: hash width must not be larger than 16 bytes.")
        exit(1)

    message = str(args.message).encode()
    key = int(args.key, 16).to_bytes(16, "big")

    print(f"{Chaskey.Hash128(message, key, args.rounds)[:args.width].hex()}")
