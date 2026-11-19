#!/usr/bin/env zsh
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

if [[ -d "/Users/revenge/code/tmp/pr-review-cleanup" ]]; then
  WORK_DIR="/Users/revenge/code/tmp/pr-review-cleanup/erdos-708-asymptotic-validate"
else
  WORK_DIR="$ROOT_DIR/target/validation-scratch"
fi
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"
cat > "$WORK_DIR/OWNER.md" <<'EOF'
Owner: erdos-708-asymptotic/scripts/validate-all.sh
Purpose: Ephemeral validation binary and log staging for Erdos 708 asymptotic verifier.
Deletion condition: Deleted automatically on script exit via EXIT trap.
EOF
trap 'rm -rf "$WORK_DIR"' EXIT

echo "=== [1/4] Checking SHA-256 manifest (SHA256SUMS.txt) ==="
shasum -a 256 -c SHA256SUMS.txt

echo "=== [2/4] Compiling & Running Zero-Dependency Standalone Rust Verifier ==="
rustc -O --edition 2021 -D warnings scripts/verify_asymptotic_708.rs -o "$WORK_DIR/verify_asymptotic_708"
"$WORK_DIR/verify_asymptotic_708" | tee "$WORK_DIR/check-rs.log"
grep -F "accept (rust-asymptotic-708) cor4_trials=500 m5040_matched=2992 m15120_matched=9457 hinge_c=2.00" "$WORK_DIR/check-rs.log"

echo "=== [3/4] Running Independent TypeScript/Bun BigInt CRT Verifier ==="
bun scripts/check708-asymptotic-independent.ts | tee "$WORK_DIR/check-ts.log"
grep -F "accept (ts-asymptotic-708) cor4_bigint=120 evals=6021 es_lhs=0.0 es_rhs=93.0 m5040_matched=2992 m15120_matched=9457 hinge_c=2.00" "$WORK_DIR/check-ts.log"

echo "=== [4/4] Running Negative Tamper / Mathematical Sharpness Checks ==="
if "$WORK_DIR/verify_asymptotic_708" --tamper-hinge-c 1.8 >/dev/null 2>&1; then
  echo "FAIL: Rust verifier accepted sub-critical hinge constant c=1.8!" >&2
  exit 1
fi
if bun scripts/check708-asymptotic-independent.ts --tamper-hinge-c 1.8 >/dev/null 2>&1; then
  echo "FAIL: TS BigInt verifier accepted sub-critical hinge constant c=1.8!" >&2
  exit 1
fi
echo "Tamper A (sub-critical hinge constant c=1.8 < 2.0 on 32-prime Erdos-Suranyi clique) -> REJECTED by both verifiers (OK)"

if "$WORK_DIR/verify_asymptotic_708" --tamper-pmax-only >/dev/null 2>&1; then
  echo "FAIL: Rust verifier accepted p=p_max(m)-only restriction at M=2520!" >&2
  exit 1
fi
if bun scripts/check708-asymptotic-independent.ts --tamper-pmax-only >/dev/null 2>&1; then
  echo "FAIL: TS BigInt verifier accepted p=p_max(m)-only restriction at M=2520!" >&2
  exit 1
fi
echo "Tamper B (restricting Prop 8(1) to p=p_max(m) only at M=2520 ES_vp1) -> REJECTED by both verifiers (OK)"

echo ""
echo "ALL POSITIVE AND NEGATIVE TAMPER CHECKS PASSED."
