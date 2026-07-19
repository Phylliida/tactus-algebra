#!/usr/bin/env bash
# Verify tactus-algebra under the Lean backend.
#
# Usage:
#   ./check.sh                 # verify the whole crate (src/lib.rs)
#   ./check.sh <extra args>    # pass extra flags through to verus
#
# Always passes `-V cache` (function-level result cache in target/verus-cache/) so
# unchanged functions are skipped on re-runs, and always tees full output to a log file
# (default /tmp/tactus-algebra-check.log, override with $TACTUS_CHECK_LOG) so a mistaken
# grep/filter never forces a re-run — just read the log.
#
# Requires the tactus verus binary to be built at ../tactus/source/target-verus/release/verus
# (see tactus-tutorial/chapters/00-setup) and Mathlib set up in the tactus install.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
LOG="${TACTUS_CHECK_LOG:-/tmp/tactus-algebra-check.log}"

if [[ ! -x "$VERUS" ]]; then
  echo "error: tactus verus binary not found at $VERUS" >&2
  echo "build it with: cd ../tactus/source && vargo build --release" >&2
  exit 1
fi

# Mathlib on LEAN_PATH: `by (nonlinear_arith)` proofs emit
# `import Mathlib.Tactic.Linarith` into the stmt files, and the verifier's
# spawned `lean` only sees the prelude/defs dirs plus whatever LEAN_PATH we
# export (it prepends its own dirs — see lean_process.rs). Resolved once from
# the tactus lean-project; skipped silently if lake/lean aren't on PATH.
if [[ -z "${LEAN_PATH:-}" && -d "$HERE/../tactus/lean-project" ]]; then
  export LEAN_PATH="$(cd "$HERE/../tactus/lean-project" && lake env printenv LEAN_PATH 2>/dev/null || true)"
fi

# NOTE: do NOT add --emit-lean here — it emits .lean files WITHOUT running
# Lean (a floor-only measurement mode; tactus-group-theory's check.sh carries
# it as a leftover). This script must run the real package-check Lean gate.
"$VERUS" --lean-backend -V cache --crate-type=lib "$HERE/src/lib.rs" "$@" 2>&1 | tee "$LOG"
rc="${PIPESTATUS[0]}"
echo "[check.sh] full output saved to $LOG (exit $rc)" >&2
exit "$rc"
