/*****************************************************
core.h: program for communication with mem-tester comp
Copyright (C) 2021 CESNET z. s. p. o.
Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

SPDX-License-Identifier: BSD-3-Clause
*****************************************************/

#ifndef CORE_MEM_TESTER
#define CORE_MEM_TESTER

#include "common.h"

#define DEFAULT_BURST_CNT 4

#define AMM_READY_MAX_ASKS  2000     // Max times sw will ask for amm ready
#define AMM_READY_ASK_DELAY 10000   // Amm ready ask delay [us]

#define TEST_MAX_ASKS  2000      // Max times sw will ask for test result
#define TEST_ASK_DELAY 50000   // Test result ask delay [us]

#define CSV_DELIM       ","

#define LAT_TEST_BURST_CNT 22
#define LAT_TEST_ADDR_CNT  10      // Addresses for each burst during latency test
#define LAT_TEST_SEED      7        // Seed for generating random data

#define XML_HEAD                    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
#define XML_START(item)             "<" item ">\n"
#define XML_END(item)               "</" item ">\n"
#define XML_VALUE(item, format)     "\t<" item ">" format "</" item ">\n"

#define XML_START_2(item)           "\t" XML_START(item)
#define XML_END_2(item)             "\t" XML_END(item)
#define XML_VALUE_2(item, format)   "\t" XML_VALUE(item, format)

#define XML_START_3(item)           "\t" XML_START_2(item)
#define XML_END_3(item)             "\t" XML_END_2(item)
#define XML_VALUE_3(item, format)   "\t" XML_VALUE_2(item, format)


// ---------------- //
// Common functions //
// ---------------- //

void GetDevConfig(struct DevConfig *config);
void PrintDevConfig(struct DevConfig *config);
void PrintDevConfigCSV(struct DevConfig *config);
void PrintDevConfigXML(struct DevConfig *config);
void PrintDevStatus();
void PrintDevStatusCSV();
void PrintDevStatusXML();
void PrintRegs();
bool Reset(bool emif);
int Init(char *dev, char *compatibile, long index, bool printCompCnt);
void Finish();
void SetRefreshPeriod(uint32_t ticks);
void PrintHist();
void PrintLogHistogram(uint32_t *data, uint32_t width, double xScale, bool xml, bool justRange);
void PrintLinearHistogram(uint32_t *data, uint32_t width, double xScale, bool xml, bool justRange);

// ------------------- //
// AMM probe functions //
// ------------------- //

void AMMProbeLoadData(struct AMMProbeData_s *data);
void AMMProbeFreeData(struct AMMProbeData_s *data);
void AMMProbeCalcResults(struct AMMProbeData_s *data, struct AMMProbeResults_s *res);
void AMMProbePrintResults(struct AMMProbeData_s *rawData, struct AMMProbeResults_s *data);
void AMMProbePrintResultsCSV(struct AMMProbeResults_s *data);
void AMMProbePrintResultsXML(struct AMMProbeResults_s *data);
void AMMProbePrintDataCSV(struct AMMProbeData_s *data);


// ----------------- //
// AMM gen functions //
// ----------------- //

void PrintManualBuff();
void FillManualBuff(long burst, char *data);
void WriteManualBuff();
void ReadManualBuff();
void AMMGenSetAddr(long addr);
void AMMGenSetBurst(long burst);

// ---------------------- //
// Test related functions //
// ---------------------- //

void PrintTestResult(bool rand);
void SetRandomAMMData(uint32_t burstCnt);
unsigned CmpRandomAMMData(uint32_t burstCnt);
bool RunTest(struct TestParams_s *testParams);
bool RunTestIntern(struct TestParams_s *testParams);


#endif
