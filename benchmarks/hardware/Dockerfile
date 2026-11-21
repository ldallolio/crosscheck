# arm-none-eabi-gcc from Ubuntu's signed packages, for run_cycles.py --gcc and hw.py:
#   docker build -t armgcc:local benchmarks/hardware
# (the build needs the network; the compilations then run with --network none)
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends gcc-arm-none-eabi binutils-arm-none-eabi libnewlib-arm-none-eabi && rm -rf /var/lib/apt/lists/*
