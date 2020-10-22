ARG UBUNTU_VERSION
FROM ubuntu:${UBUNTU_VERSION}

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  bison \
  build-essential \
  clang-10 \
  clang-format-10 \
  clang-tools-10 \
  gcc-multilib \
  g++-7-multilib \
  cmake \
  curl \
  doxygen \
  expect \
  flex \
  git \
  libboost-all-dev \
  libcap-dev \
  libffi-dev \
  libgoogle-perftools-dev \
  libncurses5-dev \
  libsqlite3-dev \
  libssl-dev \
  libtcmalloc-minimal4 \
  lib32stdc++-7-dev \
  libgmp-dev \
  libgmpxx4ldbl \
  lld-10 \
  llvm-10 \
  ncurses-doc \
  ninja-build \
  perl \
  pkg-config \
  python \
  python3 \
  python3-minimal \
  python3-pip \
  subversion \
  sudo \
  unzip \
  wget \
  # Cleanup
  && apt-get clean \
  # Install Python packages
  && pip3 install --no-cache-dir setuptools \
  && pip3 install --no-cache-dir \
    argparse \
    colored \
    lit \
    tabulate \
    termcolor \
    toml \
    wllvm

ARG USERNAME
ARG USER_UID
ARG USER_GID
ARG USER_HOME=/home/${USERNAME}
ARG FUZZ_TARGET_GENERATOR_DIR=${USER_HOME}/Fuzzing-Target-Generator

RUN (groupadd --gid=${USER_GID} ${USERNAME} || true) \
  && (useradd --shell=/bin/bash --uid=${USER_UID} --gid=${USER_GID} --create-home ${USERNAME} || true) \
  && echo "${USERNAME}  ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers

RUN mkdir ${FUZZ_TARGET_GENERATOR_DIR}

WORKDIR ${FUZZ_TARGET_GENERATOR_DIR}
COPY . .
#build cargo first, then rustdoc and fuzz-target-generator
RUN python ./x.py build --stage 2 src/tools/cargo \
    && python3 ./x.py build --stage 2
ENV PATH="${FUZZ_TARGET_GENERATOR_DIR}/build/x86_64-unknown-linux-gnu/stage2/bin:${PATH}"
ENV PATH="${FUZZ_TARGET_GENERATOR_DIR}/build/x86_64-unknown-linux-gnu/stage2-tools-bin:${PATH}"

#install rustup
USER ${USERNAME}
WORKDIR ${USER_HOME}
ENV PATH="${USER_HOME}/.cargo/bin:${PATH}"
RUN curl --location https://sh.rustup.rs > /tmp/rustup \
  && sh /tmp/rustup -y --default-toolchain=none \
  && rustup --version \
  && rm /tmp/rustup

RUN rustup toolchain link stage2 ${FUZZ_TARGET_GENERATOR_DIR}/build/x86*/stage2 \
  && rustup default stage2

#create a .bashrc
RUN echo "export PATH=\"${PATH}\"" >> ${USER_HOME}/.bashrc \
  && echo "ulimit -c0" >> ${USER_HOME}/.bashrc

#install fuzzing scripts
RUN git clone https://github.com/Artisan-Lab/Fuzzing-Scripts \
    && cd Fuzzing-Scripts \
    && cargo install --path afl_scripts \
    && cargo install --path find_literal

#to reduce the final size of docker image 
#RUN cp ${FUZZ_TARGET_GENERATOR_DIR}/build/x86_64-unknown-linux-gnu/stage2/bin/rustdoc ${USER_HOME}/.cargo/bin \
#  && cp ${FUZZ_TARGET_GENERATOR_DIR}/build/x86_64-unknown-linux-gnu/stage2/bin/fuzz-target-generator ${USER_HOME}/.cargo/bin \
#  && cp ${FUZZ_TARGET_GENERATOR_DIR}/build/x86_64-unknown-linux-gnu/stage2-tools-bin/cargo ${USER_HOME}/.cargo/bin \
#  && rm -rf ${FUZZ_TARGET_GENERATOR_DIR} \
#  && rm -rf ${USER_HOME}/Fuzzing-Scripts
