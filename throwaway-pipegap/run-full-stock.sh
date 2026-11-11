#!/bin/bash
# Throwaway: full-v11 --e2e stock column only (GOFV_E2E_STOCK_ONLY: no verified pipeline), per-function rows.
set -u
cd /home/kev/work/fv-compiler-go-wt/pipegap
export TMPDIR=$PWD/tmp
F=/home/kev/work/gofv-corpus/2aae1000ea1d/full-v11/plain
GOFV_E2E_LIST=tmp/full-all-but3.files GOFV_E2E_STOCK_ONLY=1 /usr/bin/time -f "fullstock wall %e s maxrss %M KB" nice -n 10 scripts/memcap.sh \
  tmp/gofv-ssa-opt-rows4 --check --verified --e2e --jobs 2 --table tmp/e2e-full-stock.md \
  --vstats tmp/e2e-full-stock-rows.tsv /dev/null > tmp/e2e-full-stock.log 2> tmp/e2e-full-stock.err
echo "fullstock exit $?"
