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
expected_axiom_names=(
  ErdosProblems.E160.siteH_oneThirdPlusSubpower_unified_explicit_rational
  ErdosProblems.E160.explicitUnifiedOneThirdThreshold_eq_displayed
  ErdosProblems.E160.siteH_oneThirdPlusSubpower_unified_displayed
  ErdosProblems.E160.sourceSurjectiveOriginalH_oneThirdPlusSubpower_unified_explicit_rational
  ErdosProblems.E160.siteH_oneThirdPlusEpsilon_unified_isBigO
  ErdosProblems.E160.siteH_le_rpow_oneThird_add_epsilon_eventually
  ErdosProblems.E160.sourceSurjectiveOriginalH_add_one_oneThirdPlusEpsilon_unified_isBigO
  ErdosProblems.E160.betterThanTensorUpper_unified_explicit
  ErdosProblems.E160.sourceSurjectiveOriginalH_literal_distinct_two_characterization
)
expected_axiom_names_sorted="$(printf '%s\n' "${expected_axiom_names[@]}" | sort)"
actual_axiom_names="$(printf '%s\n' "$axiom_lines" |
  awk -F"'" '/depends on axioms:/ { print $2 }' | sort)"
actual_axiom_count="$(printf '%s\n' "$actual_axiom_names" |
  awk 'NF { n++ } END { print n + 0 }')"
if [ "$actual_axiom_count" -ne "${#expected_axiom_names[@]}" ] ||
   [ "$actual_axiom_names" != "$expected_axiom_names_sorted" ]; then
  echo "Audited theorem set does not match the expected nine endpoints" >&2
  diff -u <(printf '%s\n' "$expected_axiom_names_sorted") \
    <(printf '%s\n' "$actual_axiom_names") || true
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

echo "[3/4] Scanning first-party Lean sources"
first_party_lean=(ErdosProblems AxiomAudit.lean ErdosProblems.lean)
if grep -R -n -E --include='*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' \
  "${first_party_lean[@]}"; then
  echo "Lean placeholder found" >&2
  exit 1
fi
if grep -R -n -E --include='*.lean' \
  '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|local)[[:space:]]+)*(axiom|axioms|constant|constants)([[:space:]]|$)' \
  "${first_party_lean[@]}"; then
  echo "First-party primitive declaration found" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

verify_manifest() {
  local manifest="$1"
  local entries=0
  local line=""
  local expected=""
  local path=""
  while IFS= read -r line || [ -n "$line" ]; do
    [ -n "$line" ] || continue
    read -r expected path <<< "$line"
    if ! [[ "$expected" =~ ^[0-9a-f]{64}$ ]] || [ -z "$path" ]; then
      echo "Malformed manifest line in $manifest: $line" >&2
      exit 1
    fi
    if [ ! -f "$path" ]; then
      echo "Manifest file is missing: $path" >&2
      exit 1
    fi
    actual="$(sha256_file "$path")"
    if [ "$actual" != "$expected" ]; then
      echo "SHA-256 mismatch: $path" >&2
      exit 1
    fi
    entries=$((entries + 1))
  done < "$manifest"
  if [ "$entries" -eq 0 ]; then
    echo "Manifest is empty: $manifest" >&2
    exit 1
  fi
}

verify_release_manifest_shape() {
  local manifest="$1"
  local line_count
  line_count="$(awk 'END { print NR + 0 }' "$manifest")"
  if [ "$line_count" -ne 1 ] ||
     ! grep -Eq '^[0-9a-f]{64}  output/pdf/e160_one_third_upper_review_candidate\.pdf$' \
       "$manifest"; then
    echo "Release manifest must contain exactly one PDF hash: $manifest" >&2
    exit 1
  fi
}

echo "[4/4] Verifying source and release manifests"
verify_manifest third_party/e160/SOURCE_SNAPSHOT_MANIFEST.tsv
verify_release_manifest_shape RELEASE_MANIFEST.sha256
verify_manifest RELEASE_MANIFEST.sha256

test -s output/pdf/e160_one_third_upper_review_candidate.pdf || {
  echo "Compiled PDF is missing or empty" >&2
  exit 1
}

echo "All checks passed."
