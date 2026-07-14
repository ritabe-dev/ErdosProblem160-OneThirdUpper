# Reproduction guide

## Pinned environment

- Lean: `leanprover/lean4:v4.30.0`
- mathlib: `v4.30.0`
- exact transitive dependency revisions: `lake-manifest.json`

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
2. explicit `#print axioms` checks for the listed theorems;
3. a scan for `sorry` and `admit` in the E160 Lean sources;
4. verification of the short source-excerpt SHA-256 manifest and the presence
   of the compiled PDF.

The accepted axiom output for the public theorems is limited to standard
Lean/mathlib principles such as `propext`, `Classical.choice`, and
`Quot.sound`.  `sorryAx` or a project-defined axiom causes the check to fail.

## Paper

The manuscript is compiled separately because TeX is not part of the Lean
trust chain. With Tectonic installed:

```bash
cd paper
tectonic -X compile --outdir . --outfmt pdf --print --untrusted main.tex
```

The compiled PDF is committed at
`output/pdf/e160_one_third_upper_review_candidate.pdf`.  The copy attached to
each GitHub release is identical to the file in the corresponding tagged tree.
The Git tag and commit identify the release.
