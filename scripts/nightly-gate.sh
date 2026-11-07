#!/usr/bin/env bash
# Nightly gate (docs/GATE.md): on the newest origin/main, in the dedicated detached worktree
# ../fv-compiler-go-wt/nightly-gate, run
#   build     lake build of every module (GoFV, GoFVTest) and the executables the gate uses
#   allproof  GoFVTest/Proof/AllProof.lean (regenerated if stale: scripts/gen-allproof.sh) builds:
#             every GoFV/Proof module imports together (no name declared twice)
#   no-sorry  scripts/no-sorry.py
#   reverts   scripts/scan-history-reverts.sh: no recent squash merge silently undid earlier work
#   axioms    scripts/axioms-audit.sh --replay (every constant of GoFV and GoFVTest; kernel replay)
#   ssa-check ssa-check on the full corpus
#   parity    scripts/parity.sh on the full corpus
#   check     whole-pipeline gofv-ssa-opt --check on the full corpus
#   e2e       driver toolchain (rebuilt when patches/go changed) + scripts/driver-e2e.sh --mode full
# and two reports that never turn the gate red (issue #189):
#   verified      gofv-ssa-opt --check --verified on the full corpus (verified pipeline vs stock)
#   e2e-verified  scripts/driver-e2e.sh --verified (programs built with the verified pipeline)
# then append the result to the "Nightly gate" status issue (label nightly-gate; created if
# missing) and, when red, open an issue (label gate-red) for the first failing step, or comment on
# the open one for that step.
#
# usage: scripts/nightly-gate.sh             timer entry: skip if today's gate already ran; skip
#                                            while MemAvailable < $GATE_MIN_FREE_GB (default 20)
#                                            (the hourly timer retries; the attempt at or after
#                                            $GATE_LAST_HOUR, default 06, posts "skipped")
#        scripts/nightly-gate.sh --now       run now even if today's gate ran (memory check kept)
#        scripts/nightly-gate.sh --install   create the gate worktree and install and start the
#                                            systemd --user timer (gofv-nightly-gate.timer)
#        scripts/nightly-gate.sh --stop-scopes  stop scopes left in gofvgate.slice by a stopped or
#                                            timed-out run (the unit's ExecStopPost); no-op while a
#                                            gate run holds ../gofv-gate.lock
#        options: --no-post (write the summary only), --force (no memory check)
#
# Results: <gate worktree>/tmp/gate/<date>T<time>/ (summary.md, one log per step).
# All of the script runs inside main(), so a checkout that replaces this file mid-run is safe.
set -euo pipefail

main() {
  local self root main_root parent wt now=0 post=1 force=0 install=0 steps=0 stop_scopes=0
  self=$(readlink -f "$0")
  root=$(cd "$(dirname "$self")/.." && pwd)
  main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
  parent=$(dirname "$main_root")
  wt=$parent/fv-compiler-go-wt/nightly-gate
  local min_free=${GATE_MIN_FREE_GB:-20} last_hour=${GATE_LAST_HOUR:-06}
  local rev= run=
  while [ $# -gt 0 ]; do
    case $1 in
      --now) now=1; shift ;;
      --no-post) post=0; shift ;;
      --force) force=1; shift ;;
      --install) install=1; shift ;;
      --stop-scopes) stop_scopes=1; shift ;;
      --steps) steps=1; rev=$2; run=$3; shift 3 ;;  # internal: run the steps in this worktree
      *) sed -n '2,33s/^# \{0,1\}//p' "$self" >&2; exit 2 ;;
    esac
  done
  export PATH=$HOME/.elan/bin:$HOME/.local/bin:$PATH

  if [ "$stop_scopes" = 1 ]; then
    gate_stop_scopes "$parent"
    return
  fi
  if [ "$steps" = 1 ]; then
    gate_steps "$root" "$parent" "$rev" "$run" "$post"
    return
  fi
  if [ "$install" = 1 ]; then
    gate_install "$main_root" "$wt"
    return
  fi

  local today state
  today=$(date +%F)
  state=$parent/gofv-gate.state  # "<date> ran <commit>" or "<date> skipped"
  if [ "$now" = 0 ] && [ -f "$state" ] && [ "$(cut -d' ' -f1 "$state")" = "$today" ]; then
    echo "nightly-gate: already ran today ($(cat "$state"))"
    return 0
  fi
  local avail
  avail=$(awk '/^MemAvailable:/ { printf "%d", $2 / 1048576 }' /proc/meminfo)
  if [ "$force" = 0 ] && [ "$avail" -lt "$min_free" ]; then
    echo "nightly-gate: MemAvailable ${avail}G < ${min_free}G, skipping this attempt"
    if [ "$now" = 0 ] && [ "$(date +%H)" -ge "$last_hour" ]; then
      echo "$today skipped" >"$state"
      [ "$post" = 0 ] || gate_post_status "$main_root" \
        "## Nightly gate $today: skipped"$'\n\n'"MemAvailable stayed below ${min_free}G at every attempt up to ${last_hour}:00 (last: ${avail}G)."
    fi
    return 0
  fi

  exec 9>"$parent/gofv-gate.lock"
  flock -n 9 || { echo "nightly-gate: another gate run holds $parent/gofv-gate.lock" >&2; return 1; }
  gate_worktree "$main_root" "$wt"
  rev=$(git -C "$wt" rev-parse HEAD)
  run=$wt/tmp/gate/$(date +%FT%H%M)
  mkdir -p "$run"
  echo "$today ran $rev" >"$state"
  # The steps run from origin/main's version of this script.
  local args=(--steps "$rev" "$run")
  [ "$post" = 1 ] || args=(--no-post "${args[@]}")
  "$wt/scripts/nightly-gate.sh" "${args[@]}"
}

# gate_worktree <main_root> <wt>: the detached gate worktree at the newest origin/main.
gate_worktree() {
  local main_root=$1 wt=$2 d
  git -C "$main_root" fetch -q origin
  if [ ! -e "$wt/.git" ]; then
    git -C "$main_root" worktree add -q --detach "$wt" origin/main
  else
    git -C "$wt" checkout -q -f --detach origin/main
    git -C "$wt" clean -fdq  # untracked files; ignored ones (tmp/, .lake/) stay
  fi
  mkdir -p "$wt/third_party"
  for d in go go-build; do
    if [ -e "$main_root/third_party/$d" ] && [ ! -e "$wt/third_party/$d" ]; then
      ln -s "$main_root/third_party/$d" "$wt/third_party/$d"
    fi
  done
}

# gate_stop_scopes <parent>: when no gate run holds the lock, stop every scope in gofvgate.slice.
# A stopped or timed-out service leaves its memcap.sh scopes running (they are units of their
# own); 2026-11-07 a leftover pass-parity kept running after the service stopped. Steps run with
# the lock fd closed (`9>&-`), so leftovers never hold the lock and the next run is not blocked.
gate_stop_scopes() {
  local parent=$1 u
  exec 9>"$parent/gofv-gate.lock"
  flock -n 9 || { echo "nightly-gate: a gate run holds the lock; leaving its scopes" >&2; return 0; }
  for u in $(systemctl --user list-units --type=scope --no-legend --plain | awk '{print $1}'); do
    if [ "$(systemctl --user show -p Slice --value "$u")" = gofvgate.slice ]; then
      echo "nightly-gate: stopping leftover $u" >&2
      systemctl --user stop "$u" || true
    fi
  done
}

# gate_install <main_root> <wt>: worktree, user units (scripts/systemd/*), timer enabled.
gate_install() {
  local main_root=$1 wt=$2 units=$HOME/.config/systemd/user u
  gate_worktree "$main_root" "$wt"
  mkdir -p "$units"
  [ -f "$units/gofv.slice" ] || cp "$wt/scripts/gofv.slice" "$units/gofv.slice"
  for u in gofvgate.slice gofv-nightly-gate.service gofv-nightly-gate.timer; do
    sed "s|@GATE_WT@|$wt|g" "$wt/scripts/systemd/$u" >"$units/$u"
  done
  systemctl --user daemon-reload
  systemctl --user enable --now gofv-nightly-gate.timer
  systemctl --user list-timers gofv-nightly-gate.timer --no-pager
}

# gh_issue <label> <exact title>: the number of the open issue with that label and title.
gh_issue() {
  gh issue list --state open --label "$1" --limit 100 --json number,title \
    --jq ".[] | select(.title == \"$2\") | .number" | head -n 1
}

gh_label() {
  gh label create "$1" --color "$2" --description "$3" >/dev/null 2>&1 || true
}

# gate_post_status <dir> <markdown>: append to the "Nightly gate" status issue (created if
# missing); prints the comment URL.
gate_post_status() {
  local dir=$1 body=$2 n
  (
    cd "$dir"
    gh_label nightly-gate 0e8a16 "Nightly gate status (scripts/nightly-gate.sh)"
    n=$(gh_issue nightly-gate "Nightly gate")
    if [ -z "$n" ]; then
      n=$(gh issue create --title "Nightly gate" --label nightly-gate --body "$(cat <<'EOF'
Status of the nightly gate (`scripts/nightly-gate.sh`, docs/GATE.md). One comment per night:
build, all-proof import, no-sorry, axioms audit, ssa-check, full-corpus parity, whole-pipeline `--check`, driver
e2e (full mode). A red night opens an issue labelled `gate-red` for its first failure.
EOF
)")
      n=${n##*/}  # the new issue's URL; the issue list lags behind a create
    fi
    gh issue comment "$n" --body "$body"
  )
}

# gate_steps <root> <parent> <rev> <run> <post>: the gate in this worktree (root).
gate_steps() {
  local root=$1 parent=$2 rev=$3 run=$4 post=$5
  cd "$root"
  mkdir -p "$run" tmp
  export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
  # memcap.sh scopes go into the gate's own slice (scripts/systemd/gofvgate.slice)
  export FV_SLICE=gofvgate.slice
  local pin12 corpus cur
  pin12=$(sed -n 's/^pin=\([0-9a-f]\{12\}\).*/\1/p' scripts/build-go.sh)
  corpus=$(readlink -f "$parent/gofv-corpus/$pin12/full/plain" || true)
  cur=$(tr '\n' ' ' <"$parent/gofv-corpus/$pin12/CURRENT" 2>/dev/null || echo -)
  local names=() results=() times=() first= built=1 t0 rc

  # step <name> <command...>: run with its log in $run/<name>.log; records pass/FAIL.
  step() {
    local name=$1; shift
    echo "nightly-gate: $name" >&2
    t0=$(date +%s)
    rc=0
    "$@" >"$run/$name.log" 2>&1 9>&- || rc=$?
    names+=("$name")
    times+=("$(( ($(date +%s) - t0) / 60 ))m")
    if [ "$rc" = 0 ]; then
      results+=(pass)
    else
      results+=("FAIL (exit $rc)")
      [ -n "$first" ] || first=$name
    fi
    return 0
  }
  skip() {
    names+=("$1"); results+=("skipped ($2)"); times+=(-)
  }
  # report <name> <command...>: like step, but the result is "report" (exit status in the
  # table), never a failure.
  report() {
    local name=$1; shift
    echo "nightly-gate: $name (report)" >&2
    t0=$(date +%s)
    rc=0
    "$@" >"$run/$name.log" 2>&1 9>&- || rc=$?
    names+=("$name")
    times+=("$(( ($(date +%s) - t0) / 60 ))m")
    if [ "$rc" = 0 ]; then results+=(report); else results+=("report (exit $rc)"); fi
    return 0
  }

  step build gate_lake GoFV GoFVTest gofv-ssa-opt pass-parity ssa-check
  [ "${results[-1]}" = pass ] || built=0
  step allproof gate_allproof
  step no-sorry python3 scripts/no-sorry.py
  step reverts scripts/scan-history-reverts.sh 80
  if [ "$built" = 1 ]; then
    # the replay checks one module per 4 GB of FV_MEMCAP at a time (scripts/axioms-audit.sh)
    step axioms flock -w 10800 "$parent/gofv-heavy.lock" env FV_MEMCAP="${GATE_BUILD_MEMCAP:-16G}" \
      scripts/axioms-audit.sh --replay --out "$run/axioms"
  else
    skip axioms "build failed"
  fi
  if [ -z "$corpus" ] || [ ! -d "$corpus" ]; then
    for s in ssa-check parity check; do skip "$s" "no full corpus"; done
    [ -n "$first" ] || first=corpus
  elif [ "$built" = 1 ]; then
    step ssa-check scripts/memcap.sh .lake/build/bin/ssa-check "$corpus"
    step parity scripts/parity.sh -o "$run/parity.md" "$corpus"
    step check scripts/memcap.sh .lake/build/bin/gofv-ssa-opt --check --jobs 4 --max-report 20 \
      --table "$run/check.md" "$corpus"
    report verified timeout "${GATE_VERIFIED_TIMEOUT:-6h}" scripts/memcap.sh \
      .lake/build/bin/gofv-ssa-opt --check --verified --jobs 4 --max-report 5 \
      --table "$run/verified.md" "$corpus"
  else
    for s in ssa-check parity check verified; do skip "$s" "build failed"; done
  fi
  if [ "$built" = 1 ]; then
    step e2e gate_e2e "$run"
    if [ -x tmp/go-driver/bin/go ]; then
      report e2e-verified env GOFV_DRIVER_GO="$PWD/tmp/go-driver" scripts/driver-e2e.sh --verified \
        --out "$run/e2e-verified"
    else
      skip e2e-verified "no driver toolchain"
    fi
  else
    skip e2e "build failed"
    skip e2e-verified "build failed"
  fi

  local verdict=GREEN
  [ -z "$first" ] || verdict=RED
  local sum=$run/summary.md i
  {
    echo "## Nightly gate $(basename "$run"): $verdict"
    echo
    echo "- commit: $rev (origin/main)"
    echo "- full corpus: ${corpus:-none} (CURRENT: ${cur% })"
    echo "- results: \`$run\`"
    echo
    echo "| step | result | time |"
    echo "| --- | --- | ---: |"
    for i in "${!names[@]}"; do echo "| ${names[$i]} | ${results[$i]} | ${times[$i]} |"; done
    echo
    gate_details "$run"
  } >"$sum"
  local red_link=
  if [ -n "$first" ] && [ "$post" = 1 ]; then
    red_link=$(gate_red_issue "$first" "$rev" "$run")
    printf '\nFirst failure: `%s` → %s\n' "$first" "$red_link" >>"$sum"
  fi
  cat "$sum"
  if [ "$post" = 1 ]; then
    gate_post_status "$root" "$(cat "$sum")"
  fi
  [ -z "$first" ]
}

# gate_allproof: the import of all proof modules builds (regenerated first when stale, so a
# module its author did not add is covered too; the next run's checkout resets the file).
gate_allproof() {
  scripts/gen-allproof.sh --check || scripts/gen-allproof.sh || return
  gate_lake GoFVTest.Proof.AllProof
}

# gate_lake <targets>: `lake build` at $GATE_BUILD_MEMCAP (default 16G) under ../gofv-heavy.lock
# (AGENTS.md: above 8G only under that lock), with at most $GATE_LEAN_SLOTS (default 4)
# concurrent lean processes (memcap.sh FV_LEAN_SLOTS). At 8G a cold -j4 build of the whole tree
# was memcg-OOM-killed (2026-11-05, #487); after a root change Lake starts ~500 lean at once.
gate_lake() {
  flock -w 10800 "$parent/gofv-heavy.lock" \
    env FV_MEMCAP="${GATE_BUILD_MEMCAP:-16G}" FV_LEAN_SLOTS="${GATE_LEAN_SLOTS:-4}" \
    scripts/memcap.sh lake build "$@"
}

# gate_e2e <run>: the driver toolchain for this commit's patches (rebuilt when they changed),
# the Lean pipeline, then driver-e2e in full mode.
gate_e2e() {
  local run=$1 gob=$PWD/tmp/go-driver sum
  sum=$(cat patches/go/*.patch | sha256sum | cut -c1-16)
  if [ "$(cat "$gob/.gofv-patches" 2>/dev/null)" != "$sum" ] || [ ! -x "$gob/bin/go" ]; then
    # explicit returns: set -e does not apply inside a step (its command runs under ||)
    GOFV_GO_DRIVER=1 GOFV_GO_BUILD=$gob scripts/build-go.sh || return
    echo "$sum" >"$gob/.gofv-patches"
  fi
  GOFV_DRIVER_GO=$gob scripts/driver-e2e.sh --mode full --out "$run/e2e-full"
}

# gate_details <run>: the numbers of each step, from its outputs.
gate_details() {
  local run=$1
  echo "<details><summary>details</summary>"
  echo
  if [ -f "$run/axioms/summary.txt" ]; then
    echo "**axioms**"; echo; sed 's/^/    /' "$run/axioms/summary.txt"; echo
  fi
  if [ -f "$run/no-sorry.log" ]; then
    echo "**no-sorry**: $(tail -n 1 "$run/no-sorry.log")"; echo
  fi
  if [ -f "$run/ssa-check.log" ]; then
    echo "**ssa-check**"; echo; tail -n 5 "$run/ssa-check.log" | sed 's/^/    /'; echo
  fi
  if [ -f "$run/parity.md" ]; then
    echo "**parity** (rows with mismatches or errors, then the corpus lines)"; echo
    head -n 1 "$run/parity.md" | sed 's/^/    /'
    awk -F'|' '$2 !~ /^ *(pass|---) *$/ && NF > 10 && ($8 + 0 > 0 || $9 + 0 > 0)' "$run/parity.md" | sed 's/^/    /'
    grep -E '^(corpus|commit)' "$run/parity.md" | sed 's/^/    /'
    echo
  fi
  if [ -f "$run/check.log" ]; then
    echo "**check**"; echo; grep -v '^|' "$run/check.log" | grep -v '^$' | tail -n 20 | sed 's/^/    /'; echo
  fi
  if [ -f "$run/verified.md" ]; then
    echo "**verified** (report: verified pipeline vs stock)"; echo; grep -v '^|' "$run/verified.md" | grep -v '^$' | sed 's/^/    /'; echo
  elif [ -f "$run/verified.log" ]; then
    echo "**verified**"; echo; tail -n 5 "$run/verified.log" | sed 's/^/    /'; echo
  fi
  if [ -f "$run/e2e-verified/report.md" ]; then
    echo "**e2e (verified, report)**"; echo; grep -v '^#' "$run/e2e-verified/report.md" | grep -v '^$' | sed 's/^/    /'; echo
  fi
  if [ -f "$run/e2e-full/report.md" ]; then
    echo "**e2e (full)**"; echo; grep -v '^#' "$run/e2e-full/report.md" | grep -v '^$' | sed 's/^/    /'; echo
  elif [ -f "$run/e2e.log" ]; then
    echo "**e2e**"; echo; tail -n 15 "$run/e2e.log" | sed 's/^/    /'; echo
  fi
  echo "</details>"
}

# gate_red_issue <step> <rev> <run>: open (or comment on) the gate-red issue for the step;
# prints its URL.
gate_red_issue() {
  local step=$1 rev=$2 run=$3 title n body log=$run/$1.log
  title="Nightly gate red: $step"
  body="First failing step of the nightly gate $(basename "$run") (scripts/nightly-gate.sh, docs/GATE.md): \`$step\`.

- commit: $rev (origin/main)
- log: \`$log\`

\`\`\`
$(tail -n 60 "$log" 2>/dev/null | cut -c1-300)
\`\`\`"
  gh_label gate-red d93f0b "Nightly gate failure (scripts/nightly-gate.sh)"
  n=$(gh_issue gate-red "$title")
  if [ -n "$n" ]; then
    gh issue comment "$n" --body "$body"
  else
    gh issue create --title "$title" --label gate-red --body "$body"
  fi
}

main "$@"; exit
