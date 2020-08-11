#!/usr/bin/env bash
set -euo pipefail

raco cross --workspace /workspace/rosette-4 racket line-count.rkt rosette-4
raco cross --workspace /workspace/rosette-3 racket line-count.rkt rosette-3
raco cross --workspace /workspace/rosette-4 racket report.rkt
