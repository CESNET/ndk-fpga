# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.7.2] - 2024-10-17

### Fixed

- Fixed missing prefix DMA Medusa jenkins verification script.
- NFB-200G2QL: Fixed missing lock DNA_PORT2E to X0Y1 due to different Chip ID in each SLRs (private submodule).
- NFB-200G2QL: Fixed all PCIE paths for pblock (private submodule).

## [0.7.1] - 2024-10-16

### Fixed

- Fixed PCIE0 path for pblock to SLR1 on Netcope NFB-200G2QL card (private submodule).
- Fixed single-bit input problem on Agilex DSP counters in new Quartus.
- Fixed coding style in lots of files.
- Fixed Modules.tcl paths due to compatibility with new NDK-FPGA in external APPs.
- Fixed verification jenkins files.
- Fixed build jenkins files of APP-Minimal.

## [0.7.0] - 2024-10-09

- Initial release of NDK-FPGA. The changelog for the previous versions of this
  repository (formerly known as ndk-app-minimal) was not maintained,
  so the changelog starts here.
