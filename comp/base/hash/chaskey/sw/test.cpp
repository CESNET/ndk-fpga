// SPDX-License-Identifier: BSD-3-Clause
// Copyright (C) 2026 CESNET z. s. p. o
// Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "chaskey.h"

#define DIV_ROUNDUP(n, d) ((n + d - 1) / d)

void print_help()
{
    printf("Test of C++ Chaskey implementation. Accepts message and key in hex as arguments and returns hashes calculated by all the functions.\n\nUsage: test -m <message as text> -k <key in hex>\n\n");
}

// converts hexadecimal string into array of bytes
void convert_hex_to_bytes(char* in, unsigned char* out, size_t out_size)
{
    char num_buff[3] = "";
    size_t out_offset = 0;

    for (size_t i = 0; i < strlen(in); i += 2)
    {
        num_buff[0] = in[i];
        num_buff[1] = in[i + 1];
        out[out_offset] = (unsigned char)strtol(num_buff, NULL, 16);
        out_offset++;

        // end the cycle to not overflow the out buffer
        if (out_offset == out_size)
            return;
    }
}

int main(int argc, char* argv[])
{
    int opt;
    char* message_str = NULL;
    char* key_str = NULL;

    while ((opt = getopt(argc, argv, "m:k:h")) != -1)
    {
        switch (opt)
        {
            case 'm':
                message_str = optarg;
                break;
            case 'k':
                key_str = optarg;
                break;
            case 'h':
                print_help();
                return 0;
            default:
                print_help();
                return 1;
        }
    }

    if (message_str == NULL || key_str == NULL)
    {
        printf("Message or key not passed.\n");
        print_help();
        return 1;
    }

    // setting up key and message
    //size_t message_len = DIV_ROUNDUP(strlen(message_str), 2);
    size_t message_len = strlen(message_str);
    unsigned char message[message_len];
    unsigned char key[16];

    //convert_hex_to_bytes(message_str, message, message_len);
    memcpy(message, message_str, message_len);
    convert_hex_to_bytes(key_str, key, sizeof(key));

    uint64_t key1 = ((uint64_t*)key)[0];
    uint64_t key2 = ((uint64_t*)key)[1];
    uint64_t hash1 = key1;
    uint64_t hash2 = key2;

    // running all public chaskey methods
    printf("Chaskey::Hash_8_64 = %lx\n", Chaskey::Hash_8_64(message, message_len, key1, key2));
    printf("Chaskey::Hash_12_64 = %lx\n", Chaskey::Hash_12_64(message, message_len, key1, key2));

    Chaskey::Hash_8_128(message, message_len, &hash1, &hash2);
    printf("Chaskey::Hash_8_128 = %lx%016lx\n", hash2, hash1);

    hash1 = key1;
    hash2 = key2;
    Chaskey::Hash_12_128(message, message_len, &hash1, &hash2);
    printf("Chaskey::Hash_12_128 = %lx%016lx\n", hash2, hash1);

    return 0;
}
