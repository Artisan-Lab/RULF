# RULF+: Fuzz Driver Synthesis for Rust Generic APIs

### Introduction 

This is the protrtype repository of RULF+. RULF+ is a tool aims to automatically synthesize fuzz drivers for generic APIs in Rust. RULF+ can generate multiple monomorphic APIs for a single generic API, to reach a comprehensive and diversity test for the generic API. Thus, RULF+ have the capability of finding the elusive bugs hidden in generic APIs, even it hide in a specific monomorphic API.

### Warning

We are in the process of reformating code, and the present version may encounter build issues when you following the instructions below. We will finish the document and release the docker build environment as soon as possible.

### Workflow

The recommended workflow to use this tool to fuzz a library is as follows: 
1. clone the source and build this tool
2. select a library for fuzzing, the use this tool to generate targets for the selected library.
3. fuzz the library with [afl.rs](https://github.com/rust-fuzz/afl.rs). We provide a command line script to partly automate the process. 

### How to use our tool with Docker
The recommend way to use and develop our tool is through docker.
We prepare a dockerfile and several scripts to manage dependencies of RULF and afl. 

The first three scripts are executed on host machine.
1. Run `docker/docker-build`. This script will build an image containing the dependencies of RULF.  
2. Run `scripts/enable-afl-on-host`. This script will enable afl to run on your machine. Running this script requires logging as root. You can run `sudo su` to switch to root. Then `exit` to normal user.
3. Run `docker/docker-run`. This script will start a docker container and map the current directory to the container.
The following scripts are executed in the container.
4. Run `scripts/build-in-docker`. This script will compile current project and set it as default toolchain with rustup. This scripts may fail several times due to network problem. Just retry it.
5. Run `scripts/install-and-test-afl`. This script will download afl.rs and test whether afl can run on your machine. You should see the output window of afl to continue. Just type Ctrl+C to exit afl.
6. Run `scripts/install-fuzzing-scripts`. This script will download our fuzzing scripts from github. It will also download source files of several test crates we use in our paper. **Note**: Sometimes downloading files from github may fail. You can download this project on host and copy it into the container(One example is `docker/docker-cp`). Then run this script again.

Then you can generate targets and fuzz them.
For example, we want to fuzz url. You can run following commands.
```shell
afl_scripts -p url
afl_scripts -f 500 url
afl_scripts -b url
afl_scripts -fuzz url
```
More options can see documentation of our fuzzing scripts.
