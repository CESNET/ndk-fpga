/*****************************************************
core.c: program for communication with mem-tester component
Copyright (C) 2021 CESNET z. s. p. o.
Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

SPDX-License-Identifier: BSD-3-Clause
*****************************************************/

#include "core.h"

struct nfb_device *device;
struct nfb_comp *component;
struct DevConfig devConfig;

// ---------------- //
// Common functions //
// ---------------- //

void GetDevConfig(struct DevConfig *config)
{
    config->amm_data_width      = ReadReg(component, AMM_DATA_WIDTH_REG);
    config->amm_addr_width      = ReadReg(component, AMM_ADDR_WIDTH_REG);
    config->amm_burst_width     = ReadReg(component, AMM_BURST_WIDTH_REG);
    config->lat_ticks_width     = ReadReg(component, LAT_TICKS_WIDTH_REG);
    config->hist_cnter_cnt      = ReadReg(component, HIST_CNTER_CNT_REG);
    config->amm_freq            = ReadReg(component, AMM_FREQ_REG) / 1000.0;
    config->slicesCnt           = config->amm_data_width / MI_DATA_WIDTH;
    config->defRefreshPeriod    = ReadReg(component, DEF_REFRESH_PERIOD);
}

void PrintDevConfig(struct DevConfig *config)
{
    printf("    AMM_DATA_WIDTH          = %7d\n", config->amm_data_width);
    printf("    AMM_ADDR_WIDTH          = %7d\n", config->amm_addr_width);
    printf("    AMM_BURST_CNT_WIDTH     = %7d\n", config->amm_burst_width);
    printf("    LATENCY TICKS WIDTH     = %7d\n", config->lat_ticks_width);
    printf("    HIST CNTER CNT          = %7d\n", config->hist_cnter_cnt);
    printf("    AMM_FREQ [MHz]          = %.2lf\n", config->amm_freq);
    printf("    slicesCnt               = %7d\n", config->slicesCnt);
    printf("    default refresh period  = %7d ticks\n", config->defRefreshPeriod);
}

// TODO: depreciated
void PrintDevConfigCSV(struct DevConfig *config)
{
    printf("%7d %s"     , config->amm_data_width,   CSV_DELIM);
    printf("%7d %s"     , config->amm_addr_width,   CSV_DELIM);
    printf("%7d %s"     , config->amm_burst_width,  CSV_DELIM);
    printf("%7d %s"     , config->lat_ticks_width,  CSV_DELIM);
    printf("%.2lf \n"   , config->amm_freq);
    //printf("%7d\n"      , config->slicesCnt);
}

void PrintDevConfigXML(struct DevConfig *config)
{
    printf(XML_HEAD);
    printf(XML_START("dev_config"));
    printf(XML_VALUE("AMM_DATA_WIDTH", "%d"),   config->amm_data_width);
    printf(XML_VALUE("AMM_ADDR_WIDTH", "%d"),   config->amm_addr_width);
    printf(XML_VALUE("AMM_BURST_WIDTH", "%d"),  config->amm_burst_width);
    printf(XML_VALUE("LAT_TICKS_WIDTH", "%d"),  config->lat_ticks_width);
    printf(XML_VALUE("HIST_CNTER_CNT", "%d"),   config->hist_cnter_cnt);
    printf(XML_VALUE("AMM_FREQ", "%.3lf"),      config->amm_freq);
    printf(XML_VALUE("DEF_REFRESH_PERIOD", "%d"), config->defRefreshPeriod);

    // Print latency histogram ranges => in probe data cen be just non zero histogram values
    bool histIsLinear = (ReadReg(component, PROBE_CTRL) >> HIST_IS_LINEAR) & 1;

    printf(XML_START_2("latency_hist_ranges"));
    if (histIsLinear)
        PrintLinearHistogram(NULL, config->hist_cnter_cnt, config->amm_freq, true, true);
    else
        PrintLogHistogram(NULL, config->hist_cnter_cnt, config->amm_freq, true, true);
    printf(XML_END_2("latency_hist_ranges"));

    printf(XML_END("dev_config"));
}

void PrintDevStatus()
{
    uint32_t data;
    data = ReadReg(component, CTRL_OUT);
    printf("ctrl_out:\n");
    printf("  test done             = %7d\n", (data >> TEST_DONE)        & 1);
    printf("  test success          = %7d\n", (data >> TEST_SUCCESS)     & 1);
    printf("  ecc error occured     = %7d\n", (data >> ECC_ERR)          & 1);
    printf("  calib success         = %7d\n", (data >> CALIB_SUCCESS)    & 1);
    printf("  calib fail            = %7d\n", (data >> CALIB_FAIL)       & 1);
    printf("  amm ready             = %7d\n", (data >> MAIN_AMM_READY)   & 1);

    data = ReadReg(component, ERR_CNT);
    printf("err cnt                 = %7u\n", data);
    data = ReadReg(component, BURST_CNT);
    printf("burst cnt               = %7u\n", data);
    data = ReadReg(component, ADDR_LIM);
    printf("address limit           = %7u\n", data);
    data = ReadReg(component, REFRESH_PERIOD);
    printf("refresh period          = %7u\n", data);
}

// TODO: depreciated
void PrintDevStatusCSV()
{
    uint32_t data;
    data = ReadReg(component, CTRL_OUT);
    printf("%7d %s", (data >> TEST_DONE)            & 1, CSV_DELIM);
    printf("%7d %s", (data >> TEST_SUCCESS)         & 1, CSV_DELIM);
    printf("%7d %s", (data >> ECC_ERR)              & 1, CSV_DELIM);
    printf("%7d %s", (data >> CALIB_SUCCESS)        & 1, CSV_DELIM);
    printf("%7d %s", (data >> CALIB_FAIL)           & 1, CSV_DELIM);
    printf("%7d %s", (data >> MAIN_AMM_READY)       & 1, CSV_DELIM);
}

void PrintDevStatusXML()
{
    uint32_t data;
    data = ReadReg(component, CTRL_OUT);

    printf(XML_HEAD);
    printf(XML_START("dev_status"));
    printf(XML_VALUE("test_done", "%d"),            (data >> TEST_DONE) & 1);
    printf(XML_VALUE("test_success", "%d"),         (data >> TEST_SUCCESS) & 1);
    printf(XML_VALUE("ecc_err_occ", "%d"),          (data >> ECC_ERR) & 1);
    printf(XML_VALUE("calib_success", "%d"),        (data >> CALIB_SUCCESS) & 1);
    printf(XML_VALUE("calib_fail", "%d"),           (data >> CALIB_FAIL) & 1);
    printf(XML_VALUE("amm_ready", "%d"),            (data >> MAIN_AMM_READY) & 1);

    data = ReadReg(component, ERR_CNT);
    printf(XML_VALUE("err_cnt", "%d"), data);
    data = ReadReg(component, BURST_CNT);
    printf(XML_VALUE("burst_cnt", "%d"), data);
    data = ReadReg(component, ADDR_LIM);
    printf(XML_VALUE("addr_lim", "%d"), data);
    data = ReadReg(component, REFRESH_PERIOD);
    printf(XML_VALUE("refresh_period", "%d"), data);
    printf(XML_END("dev_status"));
}

void PrintRegs()
{
    uint32_t data;
    printf("------------------------------------------------------------\n");
    printf("Mem-tester core:\n");

    data = ReadReg(component, CTRL_IN);
    printf("ctrl_in:\n");
    printf("  reset                 = %7d\n", (data >> RESET)           & 1);
    printf("  reset EMIF            = %7d\n", (data >> RESET_EMIF)      & 1);
    printf("  run test              = %7d\n", (data >> RUN_TEST)        & 1);
    printf("  AMM_GEN enable        = %7d\n", (data >> AMM_GEN_EN)      & 1);
    printf("  random addr en        = %7d\n", (data >> RANDOM_ADDR_EN)  & 1);
    printf("  only one simult read  = %7d\n", (data >> ONLY_ONE_SIMULT_READ)  & 1);
    printf("  auto precharge        = %7d\n", (data >> AUTO_PRECHARGE_REQ)  & 1);

    PrintDevStatus();

    printf("Config:\n");
    PrintDevConfig(&devConfig);

    printf("------------------------------------------------------------\n");
    printf("AMM_GEN:\n");

    data = ReadReg(component, AMM_GEN_CTRL);
    printf("ctrl:\n");
    printf("  mem write             = %7d\n", (data >> MEM_WR)          & 1);
    printf("  mem read              = %7d\n", (data >> MEM_RD)          & 1);
    printf("  buff valid            = %7d\n", (data >> BUFF_VLD)        & 1);
    printf("  amm ready             = %7d\n", (data >> AMM_READY)       & 1);

    data = ReadReg(component, AMM_GEN_ADDR);
    printf("addr                    = %7u\n", data);

    data = ReadReg(component, AMM_GEN_DATA);
    printf("data                    = %7u\n", data);

    data = ReadReg(component, AMM_GEN_BURST);
    printf("burst                   = %7u\n", data);

    PrintManualBuff();

    struct AMMProbeData_s probeData;
    struct AMMProbeResults_s probeResults;
    AMMProbeLoadData(&probeData);
    AMMProbeCalcResults(&probeData, &probeResults);
    AMMProbePrintResults(&probeData, &probeResults);
    AMMProbeFreeData(&probeData);
}

bool Reset(bool emif)
{
    ToggleBit(component, CTRL_IN, (emif) ? RESET_EMIF : RESET);
    if (emif)
    {
        if (! WaitForBit(component, CTRL_OUT, MAIN_AMM_READY, 1, AMM_READY_MAX_ASKS, AMM_READY_ASK_DELAY))
        {
            printf("AMM was not rested\n");
            return false;
        }
    }

    return true;
}

int Init(char *dev, char *compatibile, long index, bool printCompCnt)
{
    // Opening component
    device = nfb_open(dev);
    if ( ! device)
    {
        fprintf(stderr, "Can't open NFB device (%s)\n", strerror(errno));
        return 1;
    }

    int compCnt = nfb_comp_count(device, compatibile);
    if (compCnt <= 0)
    {
        fprintf(stderr, "No compatibile component found\n");
        return 1;
    }

    if (printCompCnt)
        printf("%d\n", compCnt);

    //printf("Found %d components\n", compCnt);

    int compOffset = nfb_comp_find(device, compatibile, index);
    component = nfb_comp_open(device, compOffset);
    if ( ! component)
    {
        fprintf(stderr, "Cant open compatibile component\n");
        return 1;
    }

    GetDevConfig(&devConfig);
    return 0;
}

void Finish()
{
    if (component)
        nfb_comp_close(component);
    if (device)
        nfb_close(device);
}

void SetRefreshPeriod(uint32_t ticks)
{
    WriteReg(component, REFRESH_PERIOD, ticks);
}

void PrintHist()
{
    struct AMMProbeData_s probeData;
    AMMProbeLoadData(&probeData); // Could be simplified

    printf("    latency histogram [ns]\n");
    if (probeData.histIsLinear)
        PrintLinearHistogram(probeData.latencyHist, devConfig.hist_cnter_cnt, devConfig.amm_freq, false, false);
    else
        PrintLogHistogram(probeData.latencyHist, devConfig.hist_cnter_cnt, devConfig.amm_freq, false, false);

    AMMProbeFreeData(&probeData);
}

void PrintHistItem(uint32_t data, double from, double to, int i, bool xml, bool justRange)
{
    if (data == 0 && ! justRange)
        return;

    if (xml)
    {
        printf(XML_START_3("item"));
        printf(XML_VALUE_3("i", "%d"),          i);
        printf(XML_VALUE_3("from", "%.4lf"),    from);
        printf(XML_VALUE_3("to", "%.4lf"),      to);
        if ( ! justRange)
            printf(XML_VALUE_3("value", "%u"),  data);
        printf(XML_END_3("item"));
    }
    else
        printf("        %10.2lf - %-10.2lf ... %-u\n", from, to, data);
}
/*
void FindFirstLastNonZero(uint32_t *data, size_t len, size_t *first, size_t *last)
{
    *first = 0;
    *last = 0;

    for (uint32_t i = 0; i < len; i++)
    {
        if (data[i] != 0)
        {
            if (*first == 0)    // Set just first
                *first = i;

            *last = i;
        }
    }
}*/

void PrintLogHistogram(uint32_t *data, uint32_t width, double ammFreq, bool xml, bool justRange)
{
    double xScale = 1000.0 / ammFreq;
    uint32_t from   = 0;
    uint32_t to     = 1;

    uint32_t d = 0;
    for (uint32_t i = 0; i < width; i++)
    {
        if ( ! justRange)
            d = data[i];
        PrintHistItem(d, from * xScale, to * xScale, i, xml, justRange);

        from = to;
        to *= (i == 0) ? 4 : 2;
    }
}

void PrintLinearHistogram(uint32_t *data, uint32_t width, double ammFreq, bool xml, bool justRange)
{
    double xScale       = 1000.0 / ammFreq;
    uint32_t maxTicks   = pow(2, devConfig.lat_ticks_width);
    double ticksStep    = maxTicks / width;

    size_t first = 0, last = width;
    //FindFirstLastNonZero(data, width, &first, &last);

    uint32_t d = 0;
    for (size_t i = first; i < last; i++)
    {
        double from       = ticksStep * i       * xScale;
        double to         = ticksStep * (i + 1) * xScale;

        if ( ! justRange)
            d = data[i];
        PrintHistItem(d, from, to, i, xml, justRange);
    }
}

// ------------------- //
// AMM probe functions //
// ------------------- //

void AMMProbeLoadData(struct AMMProbeData_s *data)
{
    uint32_t reg            = ReadReg(component, CTRL_OUT);
    data->errOcc            = ! ((reg >> TEST_SUCCESS) & 1);
    data->eccErrOcc         = (reg >> ECC_ERR) & 1;

    reg                     =  ReadReg(component,  PROBE_CTRL);
    data->latencyToFirst    = (reg >> LATENCY_TO_FIRST   ) & 1;
    data->wrTicksOvf        = (reg >> WR_TICKS_OVF       ) & 1;
    data->rdTicksOvf        = (reg >> RD_TICKS_OVF       ) & 1;
    data->rwTicksOvf        = (reg >> RW_TICKS_OVF       ) & 1;
    data->wrWordsOvf        = (reg >> WR_WORDS_OVF       ) & 1;
    data->rdWordsOvf        = (reg >> RD_WORDS_OVF       ) & 1;
    data->reqCntOvf         = (reg >> REQ_CNT_OVF        ) & 1;
    data->latencyTicksOvf   = (reg >> LATENCY_TICKS_OVF  ) & 1;
    data->latencyCntersOvf  = (reg >> LATENCY_CNTERS_OVF ) & 1;
    data->latencySumOvf     = (reg >> LATENCY_SUM_OVF    ) & 1;
    data->histCntOvf        = (reg >> HIST_CNT_OVF       ) & 1;
    data->histIsLinear      = (reg >> HIST_IS_LINEAR     ) & 1;

    data->burst             = ReadReg(component, BURST_CNT);
    data->errCnt            = ReadReg(component, ERR_CNT);
    data->ctrlReg           = ReadReg(component, PROBE_CTRL);
    data->writeTicks        = ReadReg(component, PROBE_WR_TICKS);
    data->readTicks         = ReadReg(component, PROBE_RD_TICKS);
    data->totalTicks        = ReadReg(component, PROBE_RW_TICKS);
    data->writeWords        = ReadReg(component, PROBE_WR_WORDS);
    data->readWords         = ReadReg(component, PROBE_RD_WORDS);
    data->reqCnt            = ReadReg(component, PROBE_REQ_CNT);
    data->latencySum        = ReadReg(component, PROBE_LATENCY_SUM_1);
    data->latencySum        = ((uint64_t) ReadReg(component, PROBE_LATENCY_SUM_2) << 32) + data->latencySum;
    data->latencyMin        = ReadReg(component, PROBE_LATENCY_MIN);
    data->latencyMax        = ReadReg(component, PROBE_LATENCY_MAX);

    size_t histCnt = devConfig.hist_cnter_cnt;
    data->latencyHist       = malloc(sizeof(uint32_t) * histCnt);
    if ( ! data->latencyHist)
        return; // TODO

    for (uint32_t i = 0; i < histCnt; i++)
    {
        WriteReg(component, PROBE_HIST_SEL, i);
        data->latencyHist[i] = ReadReg(component, PROBE_HIST_CNT);
    }
}

void AMMProbeFreeData(struct AMMProbeData_s *data)
{
    free(data->latencyHist);
}

void AMMProbeCalcResults(struct AMMProbeData_s *data, struct AMMProbeResults_s *res)
{
    res->raw = *data;

    res->writeTime_ms       = TicksToMS(devConfig.amm_freq, data->writeTicks);
    res->readTime_ms        = TicksToMS(devConfig.amm_freq, data->readTicks);
    res->totalTime_ms       = TicksToMS(devConfig.amm_freq, data->totalTicks);

    res->writeFlow_bs       = MSToDataFlow(&devConfig, res->writeTime_ms, data->writeWords);
    res->readFlow_bs        = MSToDataFlow(&devConfig, res->readTime_ms , data->readWords);
    res->totalFlow_bs       = MSToDataFlow(&devConfig, res->totalTime_ms, data->writeWords + data->writeWords);     //TODO

    if (res->raw.reqCnt != 0)
        res->avgLatency_ns  = TicksToNS(devConfig.amm_freq, data->latencySum / data->reqCnt);
    res->minLatency_ns      = TicksToNS(devConfig.amm_freq, data->latencyMin);
    res->maxLatency_ns      = TicksToNS(devConfig.amm_freq, data->latencyMax);
}

void AMMProbePrintResults(struct AMMProbeData_s *rawData, struct AMMProbeResults_s *data)
{
    printf("------------------------------------------------------------\n");
    printf("AMM probe:\n");

    printf("    err occ                 = %u\n", data->raw.errOcc);
    printf("    err cnt                 = %u\n", data->raw.errCnt);
    printf("    ECC err occ             = %u\n", data->raw.eccErrOcc);
    printf("    burst count             = %u\n", data->raw.burst);
    printf("    latency to first        = %u\n", data->raw.latencyToFirst);
    printf("    hist is linear          = %u\n", data->raw.histIsLinear);
    printf("\n");

    //printf("    write ticks overflow    = %u\n", data->raw.wrTicksOvf);
    //printf("    read ticks overflow     = %u\n", data->raw.rdTicksOvf);
    //printf("    total ticks overflow    = %u\n", data->raw.rwTicksOvf);
    //printf("    write words overflow    = %u\n", data->raw.wrWordsOvf);
    //printf("    read words overflow     = %u\n", data->raw.rdWordsOvf);
    //printf("    req cnt overflow        = %u\n", data->raw.reqCntOvf);
    //printf("    latency ticks overflow  = %u\n", data->raw.latencyTicksOvf);
    //printf("    latency counter overflow= %u\n", data->raw.latencyCntersOvf);
    //printf("    latency sum overflow    = %u\n", data->raw.latencySumOvf);
    //printf("    histogram cnt overflow  = %u\n", data->raw.histCntOvf);
    //printf("\n");

    if (data->raw.wrTicksOvf)
        printf("    !! Write ticks overflow occurred\n");
    if (data->raw.rdTicksOvf)
        printf("    !! Read ticks overflow occurred\n");
    if (data->raw.rwTicksOvf)
        printf("    !! ReadWrite ticks overflow occurred\n");
    if (data->raw.wrWordsOvf)
        printf("    !! Write words overflow occurred\n");
    if (data->raw.rdWordsOvf)
        printf("    !! Read words overflow occurred\n");
    if (data->raw.reqCntOvf)
        printf("    !! Request cnt overflow occurred\n");
    if (data->raw.latencyTicksOvf)
        printf("    !! Latency ticks overflow occurred\n");
    if (data->raw.latencyCntersOvf)
        printf("    !! Latency counters overflow occurred\n");
    if (data->raw.latencySumOvf)
        printf("    !! Latency sum counter overflow occurred\n");
    if (data->raw.histCntOvf)
        printf("    !! Histogram counter overflow occurred\n");

    printf("    write time [ms]         = %.4lf\n", data->writeTime_ms);
    printf("    read  time [ms]         = %.4lf\n", data->readTime_ms);
    printf("    total time [ms]         = %.4lf\n", data->totalTime_ms);

    printf("\n");
    printf("    write flow [Gb/s]       = %.4lf\n", data->writeFlow_bs / 1000000000.0);
    printf("    read  flow [Gb/s]       = %.4lf\n", data->readFlow_bs  / 1000000000.0);
    printf("    total flow [Gb/s]       = %.4lf\n", data->totalFlow_bs / 1000000000.0);

    printf("\n");
    printf("    words written           = %7u\n", data->raw.writeWords);
    printf("    words read              = %7u\n", data->raw.readWords);
    printf("    request made            = %7u\n", data->raw.reqCnt);

    printf("\n");
    printf("    latency avg [ns]        = %.4lf\n", data->avgLatency_ns);
    printf("    latency min [ns]        = %.4lf\n", data->minLatency_ns);
    printf("    latency max [ns]        = %.4lf\n", data->maxLatency_ns);

    printf("\n");
    printf("    latency avg [ticks]     = %.4lf\n", (double) rawData->latencySum / data->raw.reqCnt);
    printf("    latency min [ticks]     = %-u\n", rawData->latencyMin);
    printf("    latency max [ticks]     = %-u\n", rawData->latencyMax);
    printf("\n");
}

void AMMProbePrintResultsCSV(struct AMMProbeResults_s *data)
{
    printf("%u  %s ", data->raw.burst       , CSV_DELIM);
    printf("%u  %s ", data->raw.errCnt      , CSV_DELIM);
    //printf("%lf %s ", data->writeTime_ms    , CSV_DELIM);
    //printf("%lf %s ", data->readTime_ms     , CSV_DELIM);
    //printf("%lf %s ", data->totalTime_ms    , CSV_DELIM);
    printf("%lf %s ", data->writeFlow_bs    , CSV_DELIM);
    printf("%lf %s ", data->readFlow_bs     , CSV_DELIM);
    printf("%lf %s ", data->totalFlow_bs    , CSV_DELIM);
    printf("%u  %s ", data->raw.writeWords  , CSV_DELIM);
    printf("%u  %s ", data->raw.readWords   , CSV_DELIM);
    printf("%u  %s ", data->raw.reqCnt      , CSV_DELIM);
    printf("%lf %s ", data->minLatency_ns   , CSV_DELIM);
    printf("%lf %s ", data->maxLatency_ns   , CSV_DELIM);
    printf("%lf \n" , data->avgLatency_ns);
}

void AMMProbePrintResultsXML(struct AMMProbeResults_s *data)
{
    printf(XML_HEAD);
    printf(XML_START("probe_data"));

    printf(XML_VALUE("err_occ",             "%d"),  data->raw.errOcc);
    printf(XML_VALUE("ecc_err_occ",         "%d"),  data->raw.eccErrOcc);

    printf(XML_VALUE("latency_to_first",    "%d"), data->raw.latencyToFirst  );
    printf(XML_VALUE("wr_ticks_ovf",        "%d"), data->raw.wrTicksOvf      );
    printf(XML_VALUE("rd_ticks_ovf",        "%d"), data->raw.rdTicksOvf      );
    printf(XML_VALUE("rw_ticks_ovf",        "%d"), data->raw.rwTicksOvf      );
    printf(XML_VALUE("wr_words_ovf",        "%d"), data->raw.wrWordsOvf      );
    printf(XML_VALUE("rd_words_ovf",        "%d"), data->raw.rdWordsOvf      );
    printf(XML_VALUE("req_cnt_ovf",         "%d"), data->raw.reqCntOvf       );
    printf(XML_VALUE("latency_ticks_ovf",   "%d"), data->raw.latencyTicksOvf );
    printf(XML_VALUE("latency_cnters_ovf",  "%d"), data->raw.latencyCntersOvf);
    printf(XML_VALUE("latency_sum_ovf",     "%d"), data->raw.latencySumOvf   );
    printf(XML_VALUE("hist_cnt_ovf",        "%d"), data->raw.histCntOvf      );
    printf(XML_VALUE("hist_is_linear",      "%d"), data->raw.histIsLinear    );

    printf(XML_VALUE("burst",               "%u"), data->raw.burst           );
    printf(XML_VALUE("err_cnt",             "%u"), data->raw.errCnt          );
    printf(XML_VALUE("ctrl_reg",            "%u"), data->raw.ctrlReg         );
    printf(XML_VALUE("write_ticks",         "%u"), data->raw.writeTicks      );
    printf(XML_VALUE("read_ticks",          "%u"), data->raw.readTicks       );
    printf(XML_VALUE("total_ticks",         "%u"), data->raw.totalTicks      );
    printf(XML_VALUE("write_words",         "%u"), data->raw.writeWords      );
    printf(XML_VALUE("read_words",          "%u"), data->raw.readWords       );
    printf(XML_VALUE("req_cnt",             "%u"), data->raw.reqCnt          );
    printf(XML_VALUE("sum_latency_ticks",   "%lu"), data->raw.latencySum     );
    printf(XML_VALUE("min_latency_ticks",   "%u"), data->raw.latencyMin      );
    printf(XML_VALUE("max_latency_ticks",   "%u"), data->raw.latencyMax      );

    printf(XML_VALUE("write_time",          "%.4lf"), data->writeTime_ms );
    printf(XML_VALUE("read_time",           "%.4lf"), data->readTime_ms  );
    printf(XML_VALUE("total_time",          "%.4lf"), data->totalTime_ms );
    printf(XML_VALUE("write_flow",          "%.4lf"), data->writeFlow_bs );
    printf(XML_VALUE("read_flow",           "%.4lf"), data->readFlow_bs  );
    printf(XML_VALUE("total_flow",          "%.4lf"), data->totalFlow_bs );
    printf(XML_VALUE("avg_latency",         "%.4lf"), data->avgLatency_ns);
    printf(XML_VALUE("min_latency",         "%.4lf"), data->minLatency_ns);
    printf(XML_VALUE("max_latency",         "%.4lf"), data->maxLatency_ns);

    printf(XML_START_2("latency_hist"));
    if (data->raw.histIsLinear)
        PrintLinearHistogram(data->raw.latencyHist, devConfig.hist_cnter_cnt, devConfig.amm_freq, true, false);
    else
        PrintLogHistogram(data->raw.latencyHist, devConfig.hist_cnter_cnt, devConfig.amm_freq, true, false);
    printf(XML_END_2("latency_hist"));

    printf(XML_END("probe_data"));
}


// ----------------- //
// AMM gen functions //
// ----------------- //

void PrintManualBuff()
{
    uint32_t prevAddr = ReadReg(component, AMM_GEN_ADDR);
    uint32_t burst_cnt = 0;

    burst_cnt = ReadReg(component, AMM_GEN_BURST);

    printf("manual data (%d bursts):\n", burst_cnt);
    for(unsigned b = 0; b < burst_cnt; b++)
    {
        printf("0x");
        for(int s = (devConfig.slicesCnt - 1); s >= 0; s--)
        {
            WriteReg(component, AMM_GEN_ADDR, b);
            WriteReg(component, AMM_GEN_SLICE, s);
            printf("%08X", ReadReg(component,  AMM_GEN_DATA));
        }
        printf("\n");
    }

    WriteReg(component, AMM_GEN_ADDR, prevAddr);  // Restore address
}

void FillManualBuff(long burst, char *data)
{
    uint32_t slicedData[devConfig.slicesCnt];
    AMMHexaToMISlices(devConfig.slicesCnt, slicedData, data);

    uint32_t prevAddr = ReadReg(component, AMM_GEN_ADDR);
    for(uint32_t s = 0; s < (devConfig.slicesCnt); s++)
    {
        WriteReg(component, AMM_GEN_ADDR, burst);
        WriteReg(component, AMM_GEN_SLICE, s);
        WriteReg(component, AMM_GEN_DATA, slicedData[s]);
    }
    WriteReg(component, AMM_GEN_ADDR, prevAddr);  // Restore address
}

void WriteManualBuff()
{
    WriteReg_bit(component, CTRL_IN, AMM_GEN_EN, 1);
    ToggleBit(component, PROBE_CTRL, PROBE_RESET);

    ToggleBit(component, AMM_GEN_CTRL, MEM_WR);

    WriteReg_bit(component, CTRL_IN, AMM_GEN_EN, 0);
}

void ReadManualBuff()
{
    WriteReg_bit(component, CTRL_IN, AMM_GEN_EN, 1);
    ToggleBit(component, PROBE_CTRL, PROBE_RESET);

    ToggleBit(component, AMM_GEN_CTRL, MEM_RD);

    WriteReg_bit(component, CTRL_IN, AMM_GEN_EN, 0);
}

void AMMGenSetAddr(long addr)
{
    WriteReg(component, AMM_GEN_ADDR, addr);
}

void AMMGenSetBurst(long burst)
{
    WriteReg(component, AMM_GEN_BURST, burst);
}

// ---------------------- //
// Test related functions //
// ---------------------- //

void PrintTestResult(bool rand)
{
    struct AMMProbeData_s probeData;
    struct AMMProbeResults_s results;
    AMMProbeLoadData(&probeData);
    AMMProbeCalcResults(&probeData, &results);
    AMMProbePrintResults(&probeData, &results);
    //printf("Raw CSV:\n");
    //AMMProbePrintDataCSV(&probeData);

    bool success = true;
    // Errors are allowed during random indexing
    if (results.raw.errCnt != 0 && ! rand)
    {
        printf("Found %d wrong words during test\n", results.raw.errCnt);
        success = false;
    }
    if (results.raw.eccErrOcc)
    {
        printf("ECC error occurred during test \n");
        success = false;
    }
    if (results.raw.writeWords != results.raw.readWords)
    {
        printf("Read word cnt do not match written word cnt\n");
        success = false;
    }
    if (results.raw.readWords != results.raw.reqCnt * results.raw.burst)
    {
        printf("Requested and received word counts do not match\n");
        success = false;
    }
    if (results.raw.errOcc && success && ! rand)
    {
        printf("Unknown error occurred (TEST_SUCCESS flag = 0)\n");
        success = false;
    }

    if (success)
        printf("Memory test was successful\n");

    AMMProbeFreeData(&probeData);
}

bool RunTestIntern(struct TestParams_s *testParams)
{
    ToggleBit(component, CTRL_IN, RUN_TEST);

    if (! WaitForBit(component, CTRL_OUT, TEST_DONE, 1, TEST_MAX_ASKS, TEST_ASK_DELAY))
    {
        printf("Test was not finished in time\n");
        return false;
    }

    if (testParams->onlyCSV || testParams->onlyXML)
    {
        struct AMMProbeData_s       probeData;
        struct AMMProbeResults_s    probeResults;

        AMMProbeLoadData(&probeData);
        AMMProbeCalcResults(&probeData, &probeResults);

        if (testParams->onlyCSV)
            AMMProbePrintResultsCSV(&probeResults);
        else
            AMMProbePrintResultsXML(&probeResults);

        AMMProbeFreeData(&probeData);
    }
    else
    {
        PrintTestResult(testParams->type == RANDOM);
    }

    return true;
}

uint32_t GetAddLim(uint32_t burst, uint32_t addrBits, double scale)
{
    //uint32_t maxAddr = pow(2, devConfig.amm_addr_width);
    uint32_t addrLim = 0;
    uint32_t maxAddr = pow(2, addrBits) * scale;
    if (scale >= 1.0)
        maxAddr -= 2 * burst;

    while (addrLim < maxAddr)
        addrLim += burst;

    return addrLim;
}

bool RunTest(struct TestParams_s *testParams)
{
    if (! Reset(false))
        return false;

    // Set test parameters
    WriteReg(component, ADDR_LIM,
        GetAddLim(testParams->burstCnt,
        devConfig.amm_addr_width, testParams->addrLimScale));
    WriteReg(component, BURST_CNT, testParams->burstCnt);
    WriteReg_bit(component, PROBE_CTRL, LATENCY_TO_FIRST,   testParams->latencyToFirst);
    WriteReg_bit(component, CTRL_IN, ONLY_ONE_SIMULT_READ,  testParams->onlyOneSimultRead);
    WriteReg_bit(component, CTRL_IN, AUTO_PRECHARGE_REQ,    testParams->autoPrecharge);

    // Select test type
    if (testParams->type == SEQUENTIAL)
    {
        WriteReg_bit(component, CTRL_IN, RANDOM_ADDR_EN, 0);
        // TODO Handle err
        RunTestIntern(testParams);
    }
    else if (testParams->type == RANDOM)
    {
        WriteReg_bit(component, CTRL_IN, RANDOM_ADDR_EN, 1);
        RunTestIntern(testParams);
    }

    return true;
}

void SetRandomAMMData(uint32_t burstCnt)
{
    for (unsigned d = 0; d < burstCnt; d ++)
    {
        for(uint32_t s = 0; s < devConfig.slicesCnt; s++)
        {
            WriteReg(component, AMM_GEN_ADDR, d * devConfig.slicesCnt + s);
            WriteReg(component, AMM_GEN_DATA, RandMIData());
        }
    }

}

unsigned CmpRandomAMMData(uint32_t burstCnt)
{
    unsigned errCnt = 0;

    for (unsigned d = 0; d < burstCnt; d ++)
    {
        for(uint32_t s = 0; s < devConfig.slicesCnt; s++)
        {
            WriteReg(component, AMM_GEN_ADDR, d * devConfig.slicesCnt + s);
            uint32_t data = ReadReg(component, AMM_GEN_DATA);

            if (data != RandMIData())
                errCnt++;
        }
    }

    return errCnt;
}
