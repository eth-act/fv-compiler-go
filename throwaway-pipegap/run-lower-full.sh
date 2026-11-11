#!/bin/bash
# Throwaway: lower-probe --dump on full-v11 (per-function fired rules and ceiling classes).
set -u
cd /home/kev/work/fv-compiler-go-wt/pipegap
export TMPDIR=$PWD/tmp
F=/home/kev/work/gofv-corpus/2aae1000ea1d/full-v11/plain
/usr/bin/time -f "lowerf wall %e s maxrss %M KB" nice -n 10 scripts/memcap.sh tmp/lower-probe --jobs 2 --dump tmp/lower-full.tsv "$F" \
  > tmp/lower-full.out 2> tmp/lower-full.err
echo "lowerf exit $?"
