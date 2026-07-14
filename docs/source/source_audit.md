# E160 source audit

Retrieval time for this audit: `2026-07-13 18:38:51 JST (UTC+09:00)`.
Only short problem-relevant facts are recorded here; the PDFs are not
redistributed in this repository.

Primary-source payloads and the maintained page were rechecked at
`2026-07-14 05:27:48 JST (UTC+09:00)`. Short audit excerpts, rather than full
copyrighted PDFs, are pinned under `third_party/e160/`; their paths and hashes
are recorded in `third_party/e160/SOURCE_SNAPSHOT_MANIFEST.tsv`.

## Original source

- Source type: primary source.
- URL: https://users.renyi.hu/~p_erdos/1989-35.pdf
- Paul Erdős, *Some Problems and Results on Combinatorial Number Theory*.
- Location: printed page 143, PDF page 12.
- Retrieved payload SHA-256:
  `ce525a816bc16714a8c5b1a1db9f272c5715bfe8b735a515b8d11d39204182dc`.
- Local audit excerpt: `third_party/e160/erdos_1989_problem_excerpt.txt`.
- The original quantity is the largest number of parts for which every
  partition is bad: some union of two parts contains a four-term AP.

The maintained site instead uses the least number of colours for which a good
colouring exists. For `N >= 4`, the compression, refinement, and extremal
arguments formalized below give

\[
  h_{\rm site}(N)=h_{\rm Erdos}(N)+1.
\]

`siteH_eq_sourceOriginalH_add_one` proves this shift in Lean for the
palette-labelled partition convention, where unused labels are allowed. The
primary phrase "decompose ... into h(n) disjoint sets" does not explicitly
say whether every displayed part must be nonempty, so the strict reading was
formalized separately. `sourceGoodPalette_compress_surjective` compresses any
good colouring to its used labels, and
`sourceSurjectiveGoodPalette_mono` refines nonempty fibres one at a time.
Consequently `sourceSurjectiveOriginalH_eq_sourceOriginalH` proves that the
strict nonempty-part and palette-labelled maximum-bad extrema agree for every
`N`; `siteH_eq_sourceSurjectiveOriginalH_add_one` closes the same `+1` bridge
for `N >= 4`. The strict maximum explicitly restricts to `k <= N`, avoiding
vacuous universal claims when no surjection exists.

The literal phrase "two of them" can be read as two distinct parts, whereas
the bad-colouring predicate also includes a progression using only one colour.
For surjective colourings the two predicates agree for every `k >= 2`; the
only predicate-level discrepancy is `k = 1`. For `N >= 4`, the maximum bad
value is at least two, so this discrepancy does not affect the extremum or the
`+1` bridge. More precisely,
`sourceEverySurjectivePartitionBadDistinctTwo_iff` proves the
literal-predicate equivalence for `k >= 2`,
`sourceEverySurjectivePartitionBadDistinctTwo_iff_lt_siteH` identifies its
sharp threshold for `2 <= k <= N`, and
`sourceSurjectiveOriginalH_literal_distinct_two_characterization` proves that
the strict source extremum is the largest relevant literal-distinct-two value
when `N >= 4`.

## Maintained problem page

- Source type: maintained secondary problem record.
- URL: https://www.erdosproblems.com/160
- Retrieved HTML SHA-256:
  `56a6c4a8f4b365634eff97f34ee03cc3d6fa629da053d16b894103128b40ce93`.
- The full HTML was not archived; only the payload hash is recorded.
- Recheck HTML SHA-256 at `2026-07-14 05:27:48 JST (UTC+09:00)`:
  `6935c3837ccd34022fb62b61b10e6501fce7f2c95664ff79b724e0ce41052a84`.
- Local audit excerpt: `third_party/e160/erdosproblems_160_excerpt.txt`.
- Status at retrieval: open; the page states that finite computation cannot
  resolve the problem.
- Current recorded bounds for the site convention are

\[
  \exp(c(\log N)^{1/9})
  \ll h(N)
  \ll N^{\log 3/\log 22+o(1)}.
\]

## Published 22-to-3 symmetric seed

- Source type: primary research paper.
- URL: https://arxiv.org/pdf/2307.06914
- Mingyang Deng, Jonathan Tidor, and Yufei Zhao, *Uniform sets with few
  progressions via colorings*, arXiv v2.
- Retrieved payload SHA-256:
  `7a16abfa4b0a2a48df1dbf3d63dfea4b72063b24c454643881b7f99b1f7e1543`.
- Local audit excerpt: `third_party/e160/dtz_2307.06914_excerpt.txt`.
- Relevant locations: page 2 gives the seed
  `1333221232131211333233`; page 10, Lemma 5.1, gives its digit-tensor lift.

The paper studies the symmetric-colouring problem and proves the relevant seed
and tensor lemma. We found no explicit E160 bound in it.

## E160 upper-bound comment

- Source type: unverified comment lead.
- URL: https://www.erdosproblems.com/forum/thread/160
- Retrieved HTML SHA-256:
  `f82b0d85947d3f6b94527f5b42f36bd2082158dd0bcfee9697ee35e54d3d7f6e`.
- The full HTML was not archived; only the payload hash is recorded.
- The displayed timestamp is `07:23 on 18 Oct 2025`; its timezone is not
  supplied by the page and is therefore not normalized.

The comment sketches a Behrend-style `N^{o(1)}` filter which leaves only a
symmetrically coloured ABBA pattern, then combines it with the published seed
tensor. It does not explicitly state the properness condition `A != B`. The
Lean development proves that condition separately instead of attributing it to
the comment.

## Relation to prior work

DTZ is cited for the digit-and-sphere framework, and Hunter's comment explains
the previously recorded upper bound. Neither is used as a theorem premise.
The Lean development directly constructs the mod-24 no-three/ABAB label, the
dyadic AABB label, and the cubic proper-ABBA label, and proves their
all-horizon palette bounds.

The resulting exact theorem is
`siteH_oneThirdPlusSubpower_unified_explicit_rational`; its strict-source
counterpart is
`sourceSurjectiveOriginalH_oneThirdPlusSubpower_unified_explicit_rational`.
Their dependency chain and real-asymptotic consequences are listed in
`docs/THEOREM_MAP.md`.
