#!/bin/bash
# Throwaway: lower-probe --dump and rule-fire-probe on quick-v10 (per-function rule data).
set -u
cd /home/kev/work/fv-compiler-go-wt/pipegap
export TMPDIR=$PWD/tmp
Q=/home/kev/work/gofv-corpus/2aae1000ea1d/quick-v10/plain
/usr/bin/time -f "lowerq wall %e s" nice -n 10 scripts/memcap.sh tmp/lower-probe --jobs 2 --dump tmp/lower-quick.tsv "$Q" \
  > tmp/lower-quick.out 2> tmp/lower-quick.err
echo "lower exit $?"
/usr/bin/time -f "fireq wall %e s" nice -n 10 scripts/memcap.sh tmp/rule-fire-probe --jobs 2 "$Q" \
  > tmp/fire-quick.out 2> tmp/fire-quick.err
echo "fire exit $?"
