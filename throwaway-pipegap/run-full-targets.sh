#!/bin/bash
# Throwaway: the verified pipeline with per-function rows (gen=, low=, lowwhy=, sched=, diff=) on the
# full-v11 functions whose stock back end passes and whose pipeline is not fully verified.
set -u
cd /home/kev/work/fv-compiler-go-wt/pipegap
export TMPDIR=$PWD/tmp
GOFV_E2E_LIST=tmp/full-targets.files /usr/bin/time -f "fulltargets wall %e s maxrss %M KB" nice -n 10 scripts/memcap.sh \
  tmp/gofv-ssa-opt-rows4 --check --verified --e2e --jobs 2 --table tmp/e2e-full-targets.md \
  --vstats tmp/e2e-full-targets.tsv /dev/null > tmp/e2e-full-targets.log 2> tmp/e2e-full-targets.err
echo "fulltargets exit $?"
