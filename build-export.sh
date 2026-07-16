#!/usr/bin/env bash
# Build the cross-crate export consumed by tactus-quadratic-extension (and any
# other tactus crate that wants the algebra trait ladder + Rational).
#
# TWO STEPS, because the artifacts have different roles (same pattern as
# tactus-group-theory/build-export.sh):
#   (1) the .vir is the VERIFICATION artifact — built WITH verification.
#       Soundness of every cross-crate lemma lives here.
#   (2) the .rlib is the ghost-ERASED rustc codegen stub used only for
#       cross-crate NAME resolution (--extern). Erased code carries no proofs,
#       so it is built with --no-verify.
#   The two MUST share one source root (src/lib.rs) so their crate hashes
#   match, else the consumer hits `error[E0463]: can't find crate`.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
mkdir -p "$HERE/export"

echo ">>> Step 1/2: verifying + exporting .vir (the verification artifact)..."
"$VERUS" --lean-backend --crate-type=lib -V cache \
  --export "$HERE/export/tactus_algebra.vir" \
  --crate-name tactus_algebra \
  "$HERE/src/lib.rs"

echo ">>> Step 2/2: building .rlib (ghost-erased codegen stub for rustc --extern)..."
"$VERUS" --lean-backend --crate-type=lib --compile --no-verify \
  --crate-name tactus_algebra \
  "$HERE/src/lib.rs" \
  -o "$HERE/export/libtactus_algebra.rlib"

echo ">>> Done. export/tactus_algebra.vir + export/libtactus_algebra.rlib"
