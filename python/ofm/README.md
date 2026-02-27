# Open FPGA Modules package

The OFM package contains modules and tools for NDK FW components and common utilities that are
used also, for example, in the `cocotbext` package.

## Installation
Follow the steps when in the OFM package's directory.
Please note that it is necessary to use Python3.11 or above.

1. Create and enter a virtual environment (recommended)
```
$ python3.11 -m venv my-venv
$ source my-venv/bin/activate
```
2. Source the env.sh script in the root directory to get the enviroment variables
```
$ source ../../env.sh
```
3. Install python development header files (might not be necessary)
```
$ sudo dnf install python3.11-devel
```
If you run into a problem with `GPG signature verification error`, it is possible to avoid this
error by editing the `/etc/yum.repos.d/runner_gitlab-runner.repo` file and setting `enabled` to 0
(for both instances).

4. Finally, install the OFM package
```
$ pip install .
```

## Tools available after installing the OFM package:
 - ofm-frequency-meter
 - ofm-data-logger
 - ofm-mem-logger
 - ofm-mvb-hash-table-simple

## Available modules to import:
 - ofm.comp.base.misc.frequency_meter
 - ofm.comp.debug.data_logger.data_logger
 - ofm.comp.debug.data_logger.mem_logger
 - ofm.comp.mfb_tools.flow.rate_limiter
 - ofm.comp.mfb_tools.flow.timestamp_limiter
 - ofm.comp.mfb_tools.logic.speed_meter
 - ofm.comp.mvb_tools.storage.mvb_hash_table_simple.mvb_hash_table_simple

**Notes**

Please, keep this README up-to-date.
