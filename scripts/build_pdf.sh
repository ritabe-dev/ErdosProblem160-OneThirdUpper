#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

mode="${1:---check}"
case "$mode" in
  --check|--write) ;;
  *)
    echo "Usage: $0 [--check|--write]" >&2
    exit 2
    ;;
esac

required_version="Tectonic 0.16.9"
bundle_url="https://relay.fullyjustified.net/default_bundle_v33.tar"
source_date_epoch="1783987200"
pdf_path="output/pdf/e160_one_third_upper_review_candidate.pdf"
manifest_path="RELEASE_MANIFEST.sha256"

tectonic_bin="${TECTONIC:-$(command -v tectonic || true)}"
if [ -z "$tectonic_bin" ]; then
  echo "Tectonic 0.16.9 is required; set TECTONIC to its executable path" >&2
  exit 1
fi

actual_version="$("$tectonic_bin" --version)"
if [ "$actual_version" != "$required_version" ]; then
  echo "Expected $required_version, found $actual_version" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/e160-pdf.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT

SOURCE_DATE_EPOCH="$source_date_epoch" "$tectonic_bin" -X compile \
  --bundle "$bundle_url" \
  --outdir "$tmp_dir" \
  --outfmt pdf \
  --untrusted \
  paper/main.tex

built_pdf="$tmp_dir/main.pdf"
test -s "$built_pdf" || {
  echo "Tectonic did not produce a nonempty PDF" >&2
  exit 1
}

if [ "$mode" = "--write" ]; then
  mkdir -p "$(dirname "$pdf_path")"
  cp "$built_pdf" "$pdf_path"
  printf '%s  %s\n' "$(sha256_file "$pdf_path")" "$pdf_path" > "$manifest_path"
  echo "Updated $pdf_path and $manifest_path"
  exit 0
fi

test -s "$pdf_path" || {
  echo "Committed PDF is missing or empty: $pdf_path" >&2
  exit 1
}

if ! cmp -s "$built_pdf" "$pdf_path"; then
  echo "Committed PDF does not match the pinned Tectonic build" >&2
  echo "built:     $(sha256_file "$built_pdf")" >&2
  echo "committed: $(sha256_file "$pdf_path")" >&2
  exit 1
fi

echo "Pinned PDF build matches $pdf_path"
