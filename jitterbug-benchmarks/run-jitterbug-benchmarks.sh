#!/usr/bin/env bash
set -euo pipefail;

# Run Jitterbug on Rosette 3 benchmarks.
cd jitterbug-rosette3;
env PATH="${PWD}/../rosette3-bin:${PATH}" ./scripts/verif-perf.py ../jitterbug-rosette3-data.csv;


# Run Jitterbug on Rosette 4 benchmarks.
cd ../jitterbug-rosette4;
env PATH="${PWD}/../rosette4-bin:${PATH}" ./scripts/verif-perf.py ../jitterbug-rosette4-data.csv;