#!/bin/bash
# Throwaway: quick-v10 --e2e with per-function rows (stock verdict, pipeline verdict, verified-pipeline fields).
set -u
cd /home/kev/work/fv-compiler-go-wt/pipegap
export TMPDIR=$PWD/tmp
Q=/home/kev/work/gofv-corpus/2aae1000ea1d/quick-v10/plain
/usr/bin/time -f "quick wall %e s maxrss %M KB" nice -n 10 scripts/memcap.sh tmp/gofv-ssa-opt-rows \
  --check --verified --e2e --jobs 2 --table tmp/e2e-quick.md --accepted tmp/e2e-quick-accepted.txt \
  --vstats tmp/e2e-quick-rows.tsv "$Q" > tmp/e2e-quick.log 2> tmp/e2e-quick.err
echo "quick exit $?"
