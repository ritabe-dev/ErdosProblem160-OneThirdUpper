# Lean theorem and dependency map

The root module imports the explicit construction, its asymptotic
consequences, and the source-convention bridge.  No conditional or externally
asserted colouring result is imported.

## Statement bridge

| Mathematical role | Lean theorem or definition | File |
| --- | --- | --- |
| Maintained least-good-colours quantity | `siteH` | `Problem.lean` |
| Original maximum-bad quantity | `sourceOriginalH` | `SourceConventionBridge.lean` |
| Strict nonempty-part quantity | `sourceSurjectiveOriginalH` | `SourceConventionBridge.lean` |
| Nonempty and labelled extrema agree | `sourceSurjectiveOriginalH_eq_sourceOriginalH` | `SourceConventionBridge.lean` |
| Exact predecessor shift for `N >= 4` | `siteH_eq_sourceSurjectiveOriginalH_add_one` | `SourceConventionBridge.lean` |
| Literal two-distinct-nonempty-parts predicate | `sourceEverySurjectivePartitionBadDistinctTwo_iff_lt_siteH` | `SourceConventionBridge.lean` |
| Literal source extremum characterization | `sourceSurjectiveOriginalH_literal_distinct_two_characterization` | `SourceConventionBridge.lean` |
| `[0,N)` colouring to `siteH` | `directSiteH_le_card_of_bounded_notAtMostTwo` | `DirectSiteHBridge.lean` |

## Construction

| Component | Lean endpoint | File |
| --- | --- | --- |
| At-most-two pattern classification | `atMostTwo_noThree_aabb_abab_properABBA` | `FilterComposition.lean` |
| Direct shared no-three/ABAB label | `horizonNoThreeMod24Colour_isNoThreeEqualColouring`, `horizonABABMod24Colour_isABABFreeColouring` | `DTZExplicitHorizon.lean` |
| Dyadic AABB factor | `horizonDyadicSquareColour_isAABBFreeColouring` | `AABBAsymptotics.lean` |
| Cubic proper-ABBA factor | `horizonCubicColour_abba_free` | `CubicHorizon.lean` |
| Unified finite colouring | `explicitUnifiedOneThirdColour_notAtMostTwo` | `OneThirdUnifiedExplicit.lean` |
| Unified palette estimate | `siteH_oneThirdPlusSubpower_unified_explicit_rational` | `OneThirdUnifiedExplicit.lean` |
| Displayed threshold equality | `explicitUnifiedOneThirdThreshold_eq_displayed` | `OneThirdUnifiedExplicit.lean` |
| Main estimate with `76k`/`40k` threshold | `siteH_oneThirdPlusSubpower_unified_displayed` | `OneThirdUnifiedExplicit.lean` |
| Strict-source exact power bound with `+1` | `sourceSurjectiveOriginalH_oneThirdPlusSubpower_unified_explicit_rational` | `OneThirdUnifiedExplicit.lean` |

## Main conclusions

| Claim | Lean theorem | File |
| --- | --- | --- |
| Big-O for every positive epsilon | `siteH_oneThirdPlusEpsilon_unified_isBigO` | `RealAsymptotics.lean` |
| Coefficient-one eventual inequality | `siteH_le_rpow_oneThird_add_epsilon_eventually` | `RealAsymptotics.lean` |
| Strict-source Big-O with exact `+1` | `sourceSurjectiveOriginalH_add_one_oneThirdPlusEpsilon_unified_isBigO` | `RealAsymptotics.lean` |
| Fixed `7/20` improvement | `betterThanTensorUpper_unified_explicit` | `RealAsymptotics.lean` |

## Scope of formal verification

The Lean kernel checks the formal theorem chain above.  The correspondence with
the historical statement is documented in `docs/source/source_audit.md` and
proved through the source-convention bridge.  The literature search and the
mathematical exposition have not been independently reviewed.
