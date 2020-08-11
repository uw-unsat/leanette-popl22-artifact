#!/usr/bin/env bash
set -euo pipefail

cd /workspace/rosette-benchmarks-3
raco cross -q --workspace /workspace/rosette-3 racket run.rkt -c "$@" > /workspace/perf/workspace/r3.csv

cd /workspace/rosette-benchmarks-4
raco cross -q --workspace /workspace/rosette-4 racket run.rkt -c "$@" > /workspace/perf/workspace/r4.csv

cd /workspace/perf
raco cross -q --workspace /workspace/rosette-4 racket report.rkt
