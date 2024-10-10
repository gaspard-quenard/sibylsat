FROM ubuntu:22.04

# Install required packages for building SibylSat and its dependencies
RUN apt-get update && apt-get install -y \
    bash \
    g++ \
    cmake \
    make \
    flex \
    zlib1g-dev \
    wget \
    bison \
    zip \
    gengetopt \
    git \
    && apt-get clean

# Set up working directory
WORKDIR /sibylsat

# Clone the SibylSat repository (including submodules for the IPC benchmarks)
RUN git clone --recurse-submodules https://github.com/gaspard-quenard/sibylsat.git /sibylsat # Clone into the /sibylsat directory

# Create build directory and compile SibylSat
WORKDIR /sibylsat/build
RUN cmake .. -DCMAKE_BUILD_TYPE=RELEASE -DIPASIRSOLVER=glucose4 && make

WORKDIR /sibylsat

# Switch to bash shell when container starts
CMD ["/bin/bash"]
