# E160 one-third upper bound: summary

This preprint has not been peer reviewed, and no claim of priority is made.

## Claim

Let `H(N)` be the least number of colours needed so that every nontrivial
four-term arithmetic progression in `{1, ..., N}` uses at least three
colours. The manuscript proves the following bound, formalized in the
accompanying Lean development. For every integer `k ≥ 1`,

\[
N>\max\{2^{(76k)^2},2^{(40k)^4}\}
\Longrightarrow
H(N)^{3k}<2{,}985{,}984^kN^{k+3}.
\]

Consequently, for every `ε > 0`,

\[
H(N)=O_\varepsilon(N^{1/3+\varepsilon}),
\]

and eventually \(H(N)\le N^{1/3+\varepsilon}\). Taking positive roots with
\(k=60\) gives
\[
H(N)<2{,}985{,}984^{1/3}N^{7/20}
\]
whenever the displayed threshold holds with \(k=60\). Since \(22^7<3^{20}\),
we have \(7/20<\log 3/\log 22\), so this is a strictly smaller upper exponent
than the one currently recorded for Erdős Problem 160.

This is an upper bound only. It does not solve Problem 160.

## Construction in four lines

1. A single mod-24 digit/square-norm label excludes every three-equal pattern
   and the `ABAB` pattern with \(N^{o(1)}\) available colours.
2. A dyadic digit/square-norm label independently excludes `AABB`, also with
   \(N^{o(1)}\) available colours.
3. For the product of these two labels, every at-most-two-colour progression
   has the proper pattern `ABBA`.
4. If the remaining `ABBA` equalities also hold in a nine-state carry label,
   the base-\(p\) digit vectors form a nonconstant affine four-term progression
   in \(\mathbf F_p^3\). For the chosen prime \(p>3\), after an
   \(\mathbf F_p\)-linear identification with \(\mathbf F_{p^3}\), the field
   norm cannot take equal values simultaneously on the outer pair and on the
   inner pair. Hence the combined factor is `ABBA`-free and has \(9p\)
   available colours, where \(p=O(N^{1/3})\).

For the norm step, write

\[
\mathcal N(X+tR)=at^3+bt^2+ct+d,\qquad
a=\mathcal N(R).
\]

The two `ABBA` equalities give

\[
27a+9b+3c=0,\qquad 7a+3b+c=0,
\]

so \(6a=0\). For a prime \(p>3\), this forces
\(\mathcal N(R)=0\), hence \(R=0\), contradicting nontriviality.

## Source convention

The manuscript writes `H(N)` for the maintained least-good-colours quantity
and \(h_E(N)\) for Erdős's original maximum-bad-partitions quantity. The Lean
bridge proves

\[
H(N)=h_E(N)+1\qquad(N\ge4),
\]

including the literal reading with two distinct nonempty parts.

## Questions for reviewers

- Is there an obvious mathematical gap in the construction?
- Is the finite-field norm `ABBA` mechanism already known under another name?
- Does the claimed comparison with the recorded E160 upper appear correct?

The proof is in `paper/main.tex` and the compiled PDF. Lean theorem names and
reproduction commands are in `docs/THEOREM_MAP.md` and `REPRODUCE.md`.
