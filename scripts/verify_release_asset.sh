#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

tag="${1:-}"
if [ -z "$tag" ]; then
  echo "Usage: $0 TAG" >&2
  exit 2
fi

command -v gh >/dev/null 2>&1 || {
  echo "GitHub CLI (gh) is required" >&2
  exit 1
}
git rev-parse -q --verify "refs/tags/$tag" >/dev/null || {
  echo "Local tag not found: $tag" >&2
  exit 1
}

local_commit="$(git rev-parse "$tag^{commit}")"
remote_refs="$(git ls-remote --tags origin \
  "refs/tags/$tag" "refs/tags/$tag^{}")"
remote_commit="$(printf '%s\n' "$remote_refs" |
  awk -v ref="refs/tags/$tag^{}" '$2 == ref { print $1 }')"
if [ -z "$remote_commit" ]; then
  remote_commit="$(printf '%s\n' "$remote_refs" |
    awk -v ref="refs/tags/$tag" '$2 == ref { print $1 }')"
fi
if [ -z "$remote_commit" ]; then
  echo "Remote tag not found on origin: $tag" >&2
  exit 1
fi
if [ "$remote_commit" != "$local_commit" ]; then
  echo "Local and remote tags resolve to different commits: $tag" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/e160-release.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT

tag_manifest="$tmp_dir/RELEASE_MANIFEST.sha256"
git show "$tag:RELEASE_MANIFEST.sha256" > "$tag_manifest"
line_count="$(awk 'END { print NR + 0 }' "$tag_manifest")"
if [ "$line_count" -ne 1 ] ||
   ! grep -Eq '^[0-9a-f]{64}  output/pdf/e160_one_third_upper_review_candidate\.pdf$' \
     "$tag_manifest"; then
  echo "Unexpected release manifest in tag $tag" >&2
  exit 1
fi
read -r expected pdf_path < "$tag_manifest"

tag_pdf="$tmp_dir/tag.pdf"
git show "$tag:$pdf_path" > "$tag_pdf"
tag_hash="$(sha256_file "$tag_pdf")"
if [ "$tag_hash" != "$expected" ]; then
  echo "Tagged PDF does not match its manifest" >&2
  exit 1
fi

asset_name="$(basename "$pdf_path")"
mkdir -p "$tmp_dir/release"
gh release download "$tag" --pattern "$asset_name" --dir "$tmp_dir/release"
asset_pdf="$tmp_dir/release/$asset_name"
asset_hash="$(sha256_file "$asset_pdf")"
if [ "$asset_hash" != "$expected" ]; then
  echo "GitHub Release asset does not match tagged PDF" >&2
  echo "tag:   $expected" >&2
  echo "asset: $asset_hash" >&2
  exit 1
fi

echo "Release asset, tagged PDF, and manifest agree: $expected"
