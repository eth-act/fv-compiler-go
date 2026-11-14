#!/usr/bin/env bash
# Run a corpus measurement (gofv-ssa-opt / gen-check / lower-probe over full-v11 or quick-v10) in
# one of a few shared measurement slots, so that the agents' corpus runs together stay within what
# the shared machine can hold. Concurrent full-v11 runs were killed by systemd-oomd under
# machine-wide memory pressure (AGENTS.md). Whole-tree builds and audits use gofv-heavy.lock instead.
#
# usage: scripts/measure-slot.sh <cmd> [args...]
#   GOFV_MEASURE_SLOTS  number of slots (default 2)
#   GOFV_MEASURE_MINGB  MemAvailable (GB) needed before starting (default 6)
#
# Memory is polled with no slot held. A slot is a lock file next to the shared Lake cache
# (/home/kev/work/gofv-measure.<i>.lock); once one is taken, memory is checked again, and the slot is
# released and the wait resumed if it dropped. The command runs holding the slot and its exit status
# is returned. Run <cmd> through scripts/memcap.sh as usual.
set -euo pipefail
[ $# -ge 1 ] || { echo "usage: $0 <cmd> [args...]" >&2; exit 2; }
slots=${GOFV_MEASURE_SLOTS:-2}
mingb=${GOFV_MEASURE_MINGB:-6}
dir=/home/kev/work
avail() { free -g | awk '/^Mem:/{print $7}'; }
while :; do
  while [ "$(avail)" -lt "$mingb" ]; do sleep 60; done
  for i in $(seq 1 "$slots"); do
    exec 9>"$dir/gofv-measure.$i.lock"
    if flock -n 9; then
      if [ "$(avail)" -ge "$mingb" ]; then
        echo "measure-slot: slot $i taken $(date +%T) avail=$(avail)G" >&2
        set +e; "$@"; rc=$?; set -e
        flock -u 9; exec 9>&-
        exit $rc
      fi
      flock -u 9
    fi
    exec 9>&-
  done
  sleep 60
done
