# Candidate one-third upper bound for Erdős Problem 160

This repository presents a proof manuscript and Lean 4 formalization for the
following candidate upper bound:

\[
  H(N) \le N^{1/3+o(1)},
\]

where `H` is the least number of colours needed so that every nontrivial
four-term arithmetic progression in `{1, ..., N}` uses at least three
colours.  More precisely, the Lean development proves that for every real
`ε > 0`, eventually

\[
  H(N) \le N^{1/3+\varepsilon}.
\]

This would improve the exponent `log(3)/log(22)` currently recorded on the
maintained Erdős Problems page.  It does **not** solve Problem 160: no matching
lower bound or asymptotic formula is claimed.

## Status

- The stated formal theorem passes the verification checks in the pinned Lean
  environment.
- The source convention, including the possible nonempty-part reading, is
  connected to the maintained colouring convention by proved Lean theorems.
- This preprint has not been peer reviewed.  No claim of priority is made, and
  novelty has not been independently assessed.

The current version is tagged `v0.2.1-review-candidate`.

## Main Lean theorems

The exact natural-power statement is:

```lean
ErdosProblems.E160.siteH_oneThirdPlusSubpower_unified_explicit_rational
```

For every `k > 0` and every `N` above an explicit threshold, it proves

\[
  H(N)^{3k} < 2{,}985{,}984^k N^{k+3}.
\]

The same bound with the sufficient threshold written in elementary form is:

```lean
ErdosProblems.E160.siteH_oneThirdPlusSubpower_unified_displayed
```

It assumes

\[
  N>\max\{2^{(76k)^2},2^{(40k)^4}\}.
\]

The usual real epsilon forms are:

```lean
ErdosProblems.E160.siteH_oneThirdPlusEpsilon_unified_isBigO
ErdosProblems.E160.siteH_le_rpow_oneThird_add_epsilon_eventually
```

The form corresponding to the original nonempty-part convention retains the
exact predecessor shift:

```lean
ErdosProblems.E160.sourceSurjectiveOriginalH_add_one_oneThirdPlusEpsilon_unified_isBigO
```

We write `H(N)` for the maintained least-good-colours quantity and
`h_E(N)` for Erdős's original maximum-bad-partitions quantity.  The Lean
source bridge proves `H(N) = h_E(N) + 1` for `N ≥ 4`, including the literal
reading with two distinct nonempty parts.

Lean's `siteH` is total on natural numbers and has the unused endpoint value
`siteH 0 = 0`; all bounds stated here concern positive `N`.

The dependency and source-statement correspondence is summarized in
[docs/THEOREM_MAP.md](docs/THEOREM_MAP.md).

## Reproduce

With Git, `elan`, and a network connection for the first dependency fetch:

```bash
lake build ErdosProblems
bash scripts/check_release.sh
```

The pinned environment is Lean `v4.30.0` with mathlib `v4.30.0`.  Full
instructions and expected output are in [REPRODUCE.md](REPRODUCE.md).

## Paper and supporting material

- [paper/main.tex](paper/main.tex) is the proof manuscript.
- The compiled PDF is
  [output/pdf/e160_one_third_upper_review_candidate.pdf](output/pdf/e160_one_third_upper_review_candidate.pdf).
- A concise overview is [docs/review/ONE_PAGE_SUMMARY.md](docs/review/ONE_PAGE_SUMMARY.md).
- The documented literature search is
  [docs/review/LITERATURE_SEARCH.md](docs/review/LITERATURE_SEARCH.md).

## Sources and conventions

Short, problem-relevant source excerpts and their hashes are stored under
`third_party/e160/`.  Full copyrighted papers are not redistributed.  The
source audit is [docs/source/source_audit.md](docs/source/source_audit.md).

The proof uses the explicit constructions formalized in this repository.  DTZ
is cited for context but its asymptotic colouring theorem is not a theorem
dependency.

## Author

**Rio Itabe** (`ritabe-dev`).

## LLM assistance

LLMs accessed through ChatGPT Pro and OpenAI Codex, primarily GPT-5.6, were
used during proof exploration, Lean formalization, testing, and editing.  Rio
Itabe is responsible for the manuscript and code; LLM outputs were not treated
as proof or independent review.

## License

The repository's original code and text are available under the MIT License.
Third-party excerpts remain subject to their source terms and are included
only in short audit form.  See [third_party/NOTICE.md](third_party/NOTICE.md).
