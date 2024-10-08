/**
 * valcon.c: Used for converting voltage and data values read by sensor_interface.vhd into a readable format.
 * Copyright (C) 2019 CESNET
 * Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#define AUTHOR "xhejcm01@stud.fit.vutbr.cz"
#define VERSION "0.1"

#include <math.h>
#include <stdio.h>
#include <string.h>

void print_help()
{
    printf("val_convert %s\n", VERSION);
    printf("%s\n", AUTHOR);
    printf("Syntax:\n");
    printf("val_conv [-t <arg>] \n");
    printf("         [-v <arg>] \n");
    printf("Usage: \n");
    printf("-------\n");
    printf("[-t] \t Convert the following HEX value into celsius \n");
    printf("[-v] \t Convert the following HEX value into volts \n");
}

int main(int argc, char **argv)
{
    // Used as index
    unsigned int i;
    // Used to know to which power to raise the number
    int j;
    // Final answer
    double ans = 0;
    // Used to store the binary representation of the input
    char bin[32];

    // Arg control
    if (argc != 3)
    {
        print_help();
        return 1;
    }

    // When the ADC is asked to return a value from a sensor that doesn't exist or is unavailable,
    // it returns "00000000". This function just prints out that the value from the sensor is not valid.
    if (!strcmp(argv[2], "00000000"))
    {
        printf("---\n");
        return 0;
    }

    // Used to convert from HEX to BIN
    for (i = 0; i < strlen(argv[2]); i++)
    {
        switch (argv[2][i])
        {
        case '0':
            strcat(bin, "0000");
            break;
        case '1':
            strcat(bin, "0001");
            break;
        case '2':
            strcat(bin, "0010");
            break;
        case '3':
            strcat(bin, "0011");
            break;
        case '4':
            strcat(bin, "0100");
            break;
        case '5':
            strcat(bin, "0101");
            break;
        case '6':
            strcat(bin, "0110");
            break;
        case '7':
            strcat(bin, "0111");
            break;
        case '8':
            strcat(bin, "1000");
            break;
        case '9':
            strcat(bin, "1001");
            break;
        case 'a':
        case 'A':
            strcat(bin, "1010");
            break;
        case 'b':
        case 'B':
            strcat(bin, "1011");
            break;
        case 'c':
        case 'C':
            strcat(bin, "1100");
            break;
        case 'd':
        case 'D':
            strcat(bin, "1101");
            break;
        case 'e':
        case 'E':
            strcat(bin, "1110");
            break;
        case 'f':
        case 'F':
            strcat(bin, "1111");
            break;
        default:
            printf("Invalid hexadecimal input.");
        }
    }

    // Used for converting voltages
    if (!strcmp(argv[1], "-v"))
    {
        for (i = 1, j = 15; i < strlen(bin); i++, j--)
        {
            ans += ((int)bin[i]-48)*exp2(j); // -48 is to convert ASCII code value to 1 or 0
        }
        printf("%g\n", ans);
    }
    // Used for converting temperatures
    else if (!strcmp(argv[1], "-t"))
    {
        ans -= ((int)bin[1]-48)*exp2(23); // Used for 2's complement

        for (i = 2, j = 22; i < strlen(bin); i++, j--)
        {
            ans += ((int)bin[i]-48)*exp2(j);
        }
        printf("%g\n", ans);
    }
    else
    {
        print_help();
        return 1;
    }

    return 0;
}
