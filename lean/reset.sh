#!/usr/bin/env bash
set -euo pipefail

find ./src -name *.olean -exec rm -f {} \;
rm -f src/workspace/load-*.lean
