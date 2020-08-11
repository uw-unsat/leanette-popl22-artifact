#!/usr/bin/env bash
set -euo pipefail;

echo "Table 4b:";
./gen-jitterbug-results.py --template jitterbug-perf.tex.template;
echo;
echo "Performance results for the 668 ported and original Jitterbug benchmarks.";


echo;
echo "Table 4c (Jitterbug results only)";
./gen-jitterbug-results.py --template jitterbug-stats.tex.template;
echo;
echo "Performance ratios between the ported and original code for SymPro and Jitterbug benchmarks.";
