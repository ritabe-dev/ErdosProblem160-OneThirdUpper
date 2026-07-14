#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

echo "[1/4] Building the Lean project"
lake build ErdosProblems

echo "[2/4] Checking theorem axioms"
axiom_output="$(lake env lean AxiomAudit.lean 2>&1)"
printf '%s\n' "$axiom_output"
if printf '%s\n' "$axiom_output" | grep -q 'sorryAx'; then
  echo "A sorry axiom was found" >&2
  exit 1
fi
axiom_lines="$(printf '%s\n' "$axiom_output" | tr '\n' ' ' |
  sed "s/'ErdosProblems/\\n'ErdosProblems/g" |
  grep 'depends on axioms:' || true)"
if [ -z "$axiom_lines" ]; then
  echo "No axiom reports were emitted" >&2
  exit 1
fi
unexpected="$(printf '%s\n' "$axiom_lines" | sed -E \
  -e 's/.*depends on axioms: \[//' -e 's/\]//' \
  -e 's/propext//g' -e 's/Classical\.choice//g' -e 's/Quot\.sound//g' \
  -e 's/[ ,]//g' | grep -v '^$' || true)"
if [ -n "$unexpected" ]; then
  echo "Unexpected axiom names: $unexpected" >&2
  exit 1
fi

echo "[3/4] Scanning the Lean sources for placeholders"
if grep -R -n -E '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' ErdosProblems/E160; then
  echo "Lean placeholder found" >&2
  exit 1
fi

echo "[4/4] Verifying source excerpt hashes and PDF"
while IFS=$'\t' read -r expected path; do
  [ -n "$expected" ] || continue
  if command -v sha256sum >/dev/null 2>&1; then
    actual="$(sha256sum "$path" | awk '{print $1}')"
  else
    actual="$(shasum -a 256 "$path" | awk '{print $1}')"
  fi
  if [ "$actual" != "$expected" ]; then
    echo "SHA-256 mismatch: $path" >&2
    exit 1
  fi
done < third_party/e160/SOURCE_SNAPSHOT_MANIFEST.tsv

test -s output/pdf/e160_one_third_upper_review_candidate.pdf || {
  echo "Compiled PDF is missing or empty" >&2
  exit 1
}

echo "All checks passed."
