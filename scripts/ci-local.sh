#!/usr/bin/env bash
# Run the checks of `.github/workflows/lean_action_ci.yml` locally, faster.
#
#   scripts/ci-local.sh [--base REF] [--jobs N] [--no-lint] [--style-only]
#
# 1. Style, before building: every line *added* since REF (default: the merge base with
#    origin/main) in a `.lean` file is at most 100 characters. Only added lines are checked, since
#    some existing files have longer lines, and `scripts/*Test.lean` is skipped, since its expected
#    outputs (`#guard_msgs`) must match messages exactly.
# 2. `lake build`, once.
# 3. The checks of the workflow, in parallel (N at a time, default 4), and `lake lint` unless
#    `--no-lint`. Each writes a log; failing logs are printed at the end.
#
# The list of checks below mirrors the workflow; when a step is added there, add it here too.

set -uo pipefail
cd "$(dirname "$0")/.."

base=""
jobs=4
lint=1
style_only=0
while [ $# -gt 0 ]; do
  case "$1" in
    --base) base="$2"; shift 2 ;;
    --jobs) jobs="$2"; shift 2 ;;
    --no-lint) lint=0; shift ;;
    --style-only) style_only=1; shift ;;
    *) echo "unknown option: $1"; exit 2 ;;
  esac
done
[ -n "$base" ] || base=$(git merge-base HEAD origin/main 2>/dev/null || echo HEAD)

start=$(date +%s)
logs=$(mktemp -d)

# 1. Style: added lines longer than 100 characters, with file and line number.
echo "== style (added lines since $(git rev-parse --short "$base"))"
# Untracked files count as added in full (`git diff` alone does not list them).
{ git diff -U0 "$base" -- '*.lean'
  git ls-files -z --others --exclude-standard -- '*.lean' |
    xargs -0 -r -n1 git diff -U0 --no-index /dev/null || true
} | python3 -c '
import re, sys
bad, path, line = 0, None, 0
for raw in sys.stdin:
    raw = raw.rstrip("\n")
    if raw.startswith("+++ "):
        path = raw[6:] if raw.startswith("+++ b/") else None
        if path and re.fullmatch(r"scripts/.*Test\.lean", path):
            path = None
    elif raw.startswith("@@"):
        line = int(re.search(r"\+(\d+)", raw).group(1))
    elif raw.startswith("+") and path:
        if len(raw) - 1 > 100:
            print(f"{path}:{line}: {len(raw) - 1} characters"); bad += 1
        line += 1
sys.exit(1 if bad else 0)
' || { echo "style: fix the lines above"; exit 1; }
echo "style: ok"
[ "$style_only" = 1 ] && exit 0

# 2. Build.
echo "== lake build"
if ! lake build > "$logs/build.log" 2>&1; then
  grep -E "error" "$logs/build.log" | head -40
  echo "build failed; full log: $logs/build.log"
  exit 1
fi
echo "build: ok ($(( $(date +%s) - start ))s)"

# 3. Checks, in parallel. Each is a name and a command; a command fails by a nonzero exit.
checks=(
  "reductions|lake env lean scripts/CheckReductions.lean"
  "reductions-test|lake env lean scripts/CheckReductionsTest.lean"
  "fun-prop-test|lake env lean scripts/FunPropTest.lean"
  "reduce-from-test|lake env lean scripts/ReduceFromTest.lean"
  "halt-results-test|lake env lean scripts/HaltResultsTest.lean"
  "metaprograms|lake env lean --run scripts/CheckMetaprograms.lean"
  "metaprograms-fixture|out=\$(lake env lean --run scripts/CheckMetaprograms.lean scripts/metaprogram-fixture) && exit 1; for word in run_cmd addDecl modifyEnv declMapExt debug.; do grep -qF \"\\\`\$word\\\`\" <<< \"\$out\" || { echo \"not reported: \$word\"; exit 1; }; done"
  "metaprograms-test|lake env lean scripts/CheckMetaprogramsTest.lean"
  "layering|lake env lean --run scripts/CheckLayering.lean"
  "layering-fixture|out=\$(lake env lean --run scripts/CheckLayering.lean scripts/layering-fixture) && exit 1; grep -qF 'DiagonaLean.Synthetic.Tactic -> DiagonaLean.PCP.Basic' <<< \"\$out\""
)
[ "$lint" = 1 ] && checks+=("lint|lake lint")

echo "== ${#checks[@]} checks, $jobs at a time"
run_check() {
  local name="${1%%|*}" cmd="${1#*|}" logs="$2" t0
  t0=$(date +%s)
  if bash -c "$cmd" > "$logs/$name.log" 2>&1; then
    echo "ok   $name ($(( $(date +%s) - t0 ))s)"
  else
    echo "FAIL $name ($(( $(date +%s) - t0 ))s)"
    touch "$logs/$name.failed"
  fi
}
export -f run_check
# NUL-separated, so that xargs does no quote processing on the commands.
# Each check is the last argument (`-n 1`), not a `-I` replacement, which BSD xargs caps at
# 255 bytes.
export logs
printf '%s\0' "${checks[@]}" | xargs -0 -n 1 -P "$jobs" bash -c 'run_check "$1" "$logs"' _

failed=$(find "$logs" -name '*.failed' | wc -l | tr -d ' ')
for f in "$logs"/*.failed; do
  [ -e "$f" ] || continue
  name=$(basename "$f" .failed)
  echo "---- $name (last 30 lines of $logs/$name.log)"
  tail -30 "$logs/$name.log"
done
echo "== done in $(( $(date +%s) - start ))s: $failed failed; logs in $logs"
[ "$failed" -eq 0 ]
