# RuMono: Fuzz Driver Synthesis for Rust Generic APIs

## Introduction 
This is the repository of RuMono, a tool for synthesizing the fuzz drivers for Rust libraries with support for generic APIs. RuMono aims to automatically synthesize fuzz drivers for every API in your Rust library. RuMono can synthesize valid and comprehensive fuzz drivers by inferring suitable concrete types for generic APIs and synthesize every implementation for generic APIs. Thus, RuMono is capable of detecting inconspicuous bugs within specific monomorphic variants of a generic API. To this end, RuMono employs a two-stage approach, involving reachable monomorphic API search and similarity pruning.

## Build Steps
We recommand you run RuMono on a docker environment. We provide a dockerfile for necessary dependencies to run RuMono. You can build running environment by running `docker/docker-build` script. This script will build an image containing the dependencies of RuMono.  

You should use `docker/docker-run` to start a container for running environment. This script will start a docker container and map the current directory to the container. 

To build our tool, run `scripts/build-in-docker`. This process will build the Rust toolchains as well as RuMono.

## Synthesize Fuzz Drivers for Your Library
1. Run `export PATH="<PROJECT_PATH>/rumono:$PATH"` to set environment variable.
2. Now you can use `rumono` command. Run `rumono gen` at the root of crate to synthesize fuzz drivers for your library. The synthesized fuzz drivers will save at `fuzz_target` directory. You can use `--crate <crate_name>` to specify the crate synthesized for, and use `--dir <dir>` to specify crate directory.
3. Run `./script/install-fuzzing-scripts` to install necessary tool `find_literal` and `afl_scripts`.
4. Run `rumono build` to build cargo project for each fuzz drivers source code.

## Start Fuzzing
1. Run `scripts/enable-afl-on-host`. This script will enable afl to run on host. Running this script requires logging as root. You can run `sudo su` to switch to root. Then `exit` to normal user.
2. Run `cargo install afl --version 0.13.5 --locked` to install specific version of `afl.rs`.
3. Run `rumono fuzz` to start fuzzing all fuzz drivers.