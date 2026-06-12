#!/usr/bin/env bash
# Behavioral test suite for the `cred` certificate-checker CLI.
# Asserts exit codes and output for accept/reject/malformed/usage paths.
set -u

cd "$(dirname "$0")/.." || exit 99
lake build cred >/dev/null 2>&1 || { echo "FAIL: lake build cred"; exit 99; }
BIN=.lake/build/bin/cred
[ -x "$BIN" ] || { echo "FAIL: $BIN not built"; exit 99; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
fails=0

# expect EXPECTED_CODE NEEDLE -- <command...>
expect() {
  local want_code="$1" needle="$2"; shift 3
  local out code
  out="$("$@" 2>&1)"; code=$?
  if [ "$code" != "$want_code" ]; then
    echo "FAIL [$*]: exit $code, wanted $want_code"; fails=$((fails+1)); return
  fi
  if [ -n "$needle" ] && ! printf '%s' "$out" | grep -qF "$needle"; then
    echo "FAIL [$*]: output missing '$needle'"; fails=$((fails+1)); return
  fi
  echo "ok   [$*] -> $code"
}

# Bundled example code is accepted.
"$BIN" examples | tail -1 > "$TMP/good.cert"
expect 0 "accepted" -- "$BIN" check "$TMP/good.cert"
expect 0 "forallElim" -- "$BIN" check --explain "$TMP/good.cert"

# A small numeric code does not decode to a valid certificate: rejected.
echo 7 > "$TMP/bad.cert"
expect 1 "rejected" -- "$BIN" check "$TMP/bad.cert"

# Non-numeric and missing inputs are malformed: exit 2.
echo "not a number" > "$TMP/mal.cert"
expect 2 "does not hold" -- "$BIN" check "$TMP/mal.cert"
expect 2 "missing or does not hold" -- "$BIN" check "$TMP/does_not_exist.cert"

# Unknown subcommand prints usage and exits 2; no args exits 0.
expect 2 "usage" -- "$BIN" frobnicate
expect 0 "checkCodeNat exampleCode = true" -- "$BIN"

if [ "$fails" -eq 0 ]; then
  echo "PASS: all checker CLI tests"
  exit 0
else
  echo "FAIL: $fails checker CLI test(s)"
  exit 1
fi
