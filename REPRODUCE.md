# Reproduction guide

## Pinned environment

- Lean: `leanprover/lean4:v4.30.0`
- mathlib: `v4.30.0`
- exact transitive dependency revisions: `lake-manifest.json`
- CI runner label: `ubuntu-24.04` (the hosted image contents can still change)
- paper builder: Tectonic `0.16.9`, bundle `default_bundle_v33`
- paper build timestamp: `2026-07-14 00:00 UTC` via `SOURCE_DATE_EPOCH`

## Fresh-clone build

Install `elan`, then run from the repository root:

```bash
lake build ErdosProblems
```

On the first run, Lake downloads the pinned dependencies.  A warm build may
reuse `.lake/`; the checks should also be run once from a fresh clone or a
directory without `.lake/`.

## Verification

```bash
bash scripts/check_release.sh
```

This performs:

1. the Lean library build;
2. exact name, count, and `#print axioms` checks for nine audited endpoints;
3. a lexical scan for `sorry`, `admit`, and conventional standalone `axiom`
   or `constant` declarations in all first-party Lean sources;
4. verification of the short source-excerpt and release SHA-256 manifests.

The accepted axiom output for the public theorems is limited to standard
Lean/mathlib principles such as `propext`, `Classical.choice`, and
`Quot.sound`.  A non-allowlisted axiom in the dependency closure of any of the
nine audited endpoints causes the check to fail.  The separate first-party
lexical guard rejects conventional standalone `axiom` and `constant`
declarations.  The transitive `#print axioms` reports, rather than that lexical
guard, are authoritative for the audited endpoints.

## Paper

The manuscript is compiled separately because TeX is not part of the Lean
trust chain.  Install Tectonic `0.16.9`, then either place it on `PATH` or set
`TECTONIC` to its executable path.  To compare a fresh pinned build with the
committed PDF, run:

```bash
bash scripts/build_pdf.sh --check
```

Maintainers regenerate the canonical PDF and its one-file manifest with:

```bash
bash scripts/build_pdf.sh --write
```

The canonical PDF is committed at
`output/pdf/e160_one_third_upper_review_candidate.pdf`.  For a release, upload
the PDF extracted from the tag rather than a working-tree copy.  After upload,
verify the manifest, tagged blob, and GitHub Release asset together:

```bash
bash scripts/verify_release_asset.sh v0.2.1-review-candidate
```

The Git tag and commit identify the release.  The verification script requires
an authenticated GitHub CLI session.
