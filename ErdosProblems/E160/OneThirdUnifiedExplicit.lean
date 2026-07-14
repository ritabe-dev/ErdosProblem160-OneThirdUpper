import ErdosProblems.E160.AABBAsymptotics
import ErdosProblems.E160.CubicHorizon
import ErdosProblems.E160.DTZExplicitHorizon
import ErdosProblems.E160.DirectSiteHBridge

/-!
# Unified explicit one-third construction

The explicit no-three and ABAB colourings use definitionally the same
mod-24/square label.  This file keeps that label only once, instead of
counting two diagonal copies in the available palette.
-/

namespace ErdosProblems.E160

/-- The dyadic factor has a nonempty finite palette. -/
theorem unifiedHorizonDyadicSquarePalette_card_pos (N : ℕ) :
    0 < Fintype.card
      (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) := by
  apply Fintype.card_pos_iff.mpr
  infer_instance

/-- One shared factor may simultaneously exclude the no-three and ABAB
patterns, while a second factor excludes AABB. -/
theorem sharedNoThreeABAB_aabb_isProperABBAFilter
    {X C D : Type*} (AP : X → X → X → X → Prop)
    (sharedColour : X → C) (aabbColour : X → D)
    (hnoThree : IsNoThreeEqualColouring AP sharedColour)
    (habab : IsABABFreeColouring AP sharedColour)
    (haabb : IsAABBFreeColouring AP aabbColour) :
    IsProperABBAFilter AP (fun x ↦ (sharedColour x, aabbColour x)) := by
  intro x0 x1 x2 x3 hAP htwo
  exact atMostTwo_noThree_aabb_abab_properABBA htwo
    (NoThreeEqual4.of_map
      (fun z : C × D ↦ z.1)
      (hnoThree x0 x1 x2 x3 hAP))
    (AABBFree4.of_map
      (fun z : C × D ↦ z.2)
      (haabb x0 x1 x2 x3 hAP))
    (ABABFree4.of_map
      (fun z : C × D ↦ z.1)
      (habab x0 x1 x2 x3 hAP))

/-- The no-three and ABAB horizon colours are definitionally the same data. -/
theorem horizonNoThree_eq_horizonABAB (N n : ℕ) :
    horizonNoThreeMod24Colour N n = horizonABABMod24Colour N n := by
  rfl

/-- Available palette after keeping only one copy of the common mod-24
factor. -/
abbrev ExplicitUnifiedOneThirdPalette (N : ℕ) :=
  ((NoThreeMod24Palette (aabbBase N) (aabbLowerDigits N) ×
      DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ×
    ((Fin 3 × Fin 3) × ZMod (cubicPrime N)))

/-- Complete all-horizon colouring with one common mod-24 factor. -/
noncomputable def explicitUnifiedOneThirdColour (N n : ℕ) :
    ExplicitUnifiedOneThirdPalette N :=
  ((horizonNoThreeMod24Colour N n, horizonDyadicSquareColour N n),
    horizonCubicColour N n)

/-- The unified colouring still uses at least three values on every
nontrivial bounded four-term progression. -/
theorem explicitUnifiedOneThirdColour_notAtMostTwo (N : ℕ) :
    ∀ n0 n1 n2 n3,
      BoundedIntFourAP4 N n0 n1 n2 n3 →
      ¬ AtMostTwo4
        (explicitUnifiedOneThirdColour N n0)
        (explicitUnifiedOneThirdColour N n1)
        (explicitUnifiedOneThirdColour N n2)
        (explicitUnifiedOneThirdColour N n3) := by
  simpa only [explicitUnifiedOneThirdColour] using
    properABBAFilter_product_not_atMostTwo
      (BoundedIntFourAP4 N)
      (fun n ↦
        (horizonNoThreeMod24Colour N n,
          horizonDyadicSquareColour N n))
      (horizonCubicColour N)
      (sharedNoThreeABAB_aabb_isProperABBAFilter
        (BoundedIntFourAP4 N)
        (horizonNoThreeMod24Colour N)
        (horizonDyadicSquareColour N)
        (horizonNoThreeMod24Colour_isNoThreeEqualColouring N)
        (by simpa only [horizonNoThree_eq_horizonABAB] using
          horizonABABMod24Colour_isABABFreeColouring N)
        (horizonDyadicSquareColour_isAABBFreeColouring N))
      (horizonCubicColour_abba_free N)

/-- Exact cardinality of the unified available palette. -/
theorem explicitUnifiedOneThirdPalette_card (N : ℕ) :
    Fintype.card (ExplicitUnifiedOneThirdPalette N) =
      Fintype.card
          (NoThreeMod24Palette (aabbBase N) (aabbLowerDigits N)) *
        Fintype.card
          (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) *
        (9 * cubicPrime N) := by
  letI : NeZero (cubicPrime N) := ⟨(cubicPrime_prime N).ne_zero⟩
  simp [ExplicitUnifiedOneThirdPalette, Fintype.card_prod]

/-- Two positive subpower factors need only a 2k budget for their product to
have k-th power below the horizon. -/
theorem pairProduct_pow_lt_of_two_mul_powers_lt
    (a b N k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (haN : a ^ (2 * k) < N)
    (hbN : b ^ (2 * k) < N) :
    (a * b) ^ k < N := by
  have hNpos : 0 < N := (Nat.pow_pos ha).trans haN
  have hsquare : ((a * b) ^ k) ^ 2 < N ^ 2 := by
    calc
      ((a * b) ^ k) ^ 2 = a ^ (2 * k) * b ^ (2 * k) := by
        simp only [mul_pow, pow_mul]
        ring
      _ < N * b ^ (2 * k) := by gcongr
      _ < N * N := by gcongr
      _ = N ^ 2 := by ring
  exact (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsquare

/-- Generic final estimate for one shared no-three/ABAB factor and the dyadic
AABB factor. -/
theorem siteH_oneThirdPlusSubpower_of_unified_factors
    {C : Type*} [Fintype C]
    (N k : ℕ) (hk : 0 < k)
    (sharedColour : ℕ → C)
    (hgood : ∀ n0 n1 n2 n3,
      BoundedIntFourAP4 N n0 n1 n2 n3 →
      ¬ AtMostTwo4
        ((sharedColour n0, horizonDyadicSquareColour N n0),
          horizonCubicColour N n0)
        ((sharedColour n1, horizonDyadicSquareColour N n1),
          horizonCubicColour N n1)
        ((sharedColour n2, horizonDyadicSquareColour N n2),
          horizonCubicColour N n2)
        ((sharedColour n3, horizonDyadicSquareColour N n3),
          horizonCubicColour N n3))
    (hcardShared : Fintype.card C ^ (2 * k) < N)
    (hcardDyadic : Fintype.card
      (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ^
        (2 * k) < N)
    (hN : 1 < N) :
    siteH N ^ (3 * k) <
      N ^ 3 * (cubicPaletteCubeConstant * N) ^ k := by
  let cS := Fintype.card C
  let cD := Fintype.card
    (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N))
  have hcSpos : 0 < cS := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨sharedColour 0⟩
  have hcDpos : 0 < cD := unifiedHorizonDyadicSquarePalette_card_pos N
  have hcSpow : cS ^ (2 * k) < N := by
    simpa [cS] using hcardShared
  have hcDpow : cD ^ (2 * k) < N := by
    simpa [cD] using hcardDyadic
  have hfilter : (cS * cD) ^ k < N :=
    pairProduct_pow_lt_of_two_mul_powers_lt
      cS cD N k hcSpos hcDpos hcSpow hcDpow
  have hsite : siteH N ≤ (cS * cD) * (9 * cubicPrime N) := by
    have hle := directSiteH_le_card_of_bounded_notAtMostTwo N
      (fun n ↦ ((sharedColour n, horizonDyadicSquareColour N n),
        horizonCubicColour N n)) hgood
    change siteH N ≤ Fintype.card
      ((C × DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ×
        ((Fin 3 × Fin 3) × ZMod (cubicPrime N))) at hle
    letI : NeZero (cubicPrime N) := ⟨(cubicPrime_prime N).ne_zero⟩
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card] at hle
    simpa [cS, cD] using hle
  have hfilterPow : (cS * cD) ^ (3 * k) < N ^ 3 := by
    calc
      (cS * cD) ^ (3 * k) = (cS * cD) ^ (k * 3) := by
        congr 1
        omega
      _ = ((cS * cD) ^ k) ^ 3 := by rw [pow_mul]
      _ < N ^ 3 := Nat.pow_lt_pow_left hfilter (by norm_num)
  have hcubicCube :
      (9 * cubicPrime N) ^ 3 < cubicPaletteCubeConstant * N :=
    horizonCubicPalette_cube_lt N hN
  have hcubicPow :
      (9 * cubicPrime N) ^ (3 * k) <
        (cubicPaletteCubeConstant * N) ^ k := by
    calc
      (9 * cubicPrime N) ^ (3 * k) =
          ((9 * cubicPrime N) ^ 3) ^ k := by rw [pow_mul]
      _ < (cubicPaletteCubeConstant * N) ^ k :=
        Nat.pow_lt_pow_left hcubicCube hk.ne'
  calc
    siteH N ^ (3 * k) ≤
        ((cS * cD) * (9 * cubicPrime N)) ^ (3 * k) :=
      Nat.pow_le_pow_left hsite (3 * k)
    _ = (cS * cD) ^ (3 * k) *
        (9 * cubicPrime N) ^ (3 * k) := by rw [mul_pow]
    _ < N ^ 3 * (9 * cubicPrime N) ^ (3 * k) :=
      Nat.mul_lt_mul_of_pos_right hfilterPow
        (Nat.pow_pos (by have := three_lt_cubicPrime N; positivity))
    _ < N ^ 3 * (cubicPaletteCubeConstant * N) ^ k :=
      Nat.mul_lt_mul_of_pos_left hcubicPow (Nat.pow_pos hN.bot_lt)

/-- Unified explicit upper bound using `2k`-th-power estimates for the two
subpower factors. -/
theorem siteH_oneThirdPlusSubpower_unified_explicit
    (N k : ℕ) (hk : 0 < k)
    (hNExplicit :
      2 ^ (dtzABABSubpowerThreshold 8 11 0 (2 * k) ^ 2) < N)
    (hNDyadic : 2 ^ ((20 * (2 * k)) ^ 4) < N) :
    siteH N ^ (3 * k) <
      N ^ 3 * (cubicPaletteCubeConstant * N) ^ k := by
  have htwoK : 0 < 2 * k := by omega
  have hcardShared := horizonNoThreeMod24Palette_card_pow_lt
    N (2 * k) htwoK hNExplicit
  have hcardDyadic := horizonDyadicSquarePalette_card_pow_lt
    N (2 * k) htwoK hNDyadic
  have hNone : 1 < N := by
    have : 1 ≤ 2 ^
        (dtzABABSubpowerThreshold 8 11 0 (2 * k) ^ 2) :=
      Nat.one_le_pow _ 2 (by norm_num)
    omega
  exact siteH_oneThirdPlusSubpower_of_unified_factors
    N k hk
    (horizonNoThreeMod24Colour N)
    (by simpa only [explicitUnifiedOneThirdColour] using
      explicitUnifiedOneThirdColour_notAtMostTwo N)
    hcardShared hcardDyadic hNone

/-- Single displayed threshold for the unified construction. -/
def explicitUnifiedOneThirdThreshold (k : ℕ) : ℕ :=
  max
    (2 ^ (dtzABABSubpowerThreshold 8 11 0 (2 * k) ^ 2))
    (2 ^ ((20 * (2 * k)) ^ 4))

/-- Elementary form of the displayed threshold.  Positivity of `k`
removes the auxiliary `max 1` in the generic subpower lemma. -/
theorem explicitUnifiedOneThirdThreshold_eq_displayed
    (k : ℕ) (hk : 0 < k) :
    explicitUnifiedOneThirdThreshold k =
      max (2 ^ ((76 * k) ^ 2)) (2 ^ ((40 * k) ^ 4)) := by
  have hgeneric : dtzABABSubpowerThreshold 8 11 0 (2 * k) =
      76 * k := by
    simp only [dtzABABSubpowerThreshold]
    omega
  rw [explicitUnifiedOneThirdThreshold, hgeneric]
  congr 2
  ring

theorem siteH_oneThirdPlusSubpower_unified_explicit_eventually
    (N k : ℕ) (hk : 0 < k)
    (hN : explicitUnifiedOneThirdThreshold k < N) :
    siteH N ^ (3 * k) <
      N ^ 3 * (cubicPaletteCubeConstant * N) ^ k := by
  apply siteH_oneThirdPlusSubpower_unified_explicit N k hk
  · exact (Nat.le_max_left _ _).trans_lt hN
  · exact (Nat.le_max_right _ _).trans_lt hN

theorem siteH_oneThirdPlusSubpower_unified_explicit_rational
    (N k : ℕ) (hk : 0 < k)
    (hN : explicitUnifiedOneThirdThreshold k < N) :
    siteH N ^ (3 * k) <
      cubicPaletteCubeConstant ^ k * N ^ (k + 3) := by
  calc
    siteH N ^ (3 * k) <
        N ^ 3 * (cubicPaletteCubeConstant * N) ^ k :=
      siteH_oneThirdPlusSubpower_unified_explicit_eventually N k hk hN
    _ = cubicPaletteCubeConstant ^ k * N ^ (k + 3) := by
      rw [mul_pow, pow_add]
      ring

/-- The main natural-power estimate with the sufficient threshold written
entirely in elementary arithmetic. -/
theorem siteH_oneThirdPlusSubpower_unified_displayed
    (N k : ℕ) (hk : 0 < k)
    (hN : max (2 ^ ((76 * k) ^ 2)) (2 ^ ((40 * k) ^ 4)) < N) :
    siteH N ^ (3 * k) <
      cubicPaletteCubeConstant ^ k * N ^ (k + 3) := by
  apply siteH_oneThirdPlusSubpower_unified_explicit_rational N k hk
  rw [explicitUnifiedOneThirdThreshold_eq_displayed k hk]
  exact hN

theorem sourceSurjectiveOriginalH_oneThirdPlusSubpower_unified_explicit_rational
    (N k : ℕ) (hk : 0 < k) (hN4 : 4 ≤ N)
    (hN : explicitUnifiedOneThirdThreshold k < N) :
    (sourceSurjectiveOriginalH N + 1) ^ (3 * k) <
      cubicPaletteCubeConstant ^ k * N ^ (k + 3) := by
  rw [← siteH_eq_sourceSurjectiveOriginalH_add_one hN4]
  exact siteH_oneThirdPlusSubpower_unified_explicit_rational N k hk hN

theorem siteH_sevenTwentieth_unified_power_bound
    (N : ℕ) (hN : explicitUnifiedOneThirdThreshold 60 < N) :
    siteH N ^ 180 <
      cubicPaletteCubeConstant ^ 60 * N ^ 63 := by
  have h := siteH_oneThirdPlusSubpower_unified_explicit_rational
    N 60 (by norm_num) hN
  norm_num only at h ⊢
  exact h

theorem sourceSurjectiveOriginalH_sevenTwentieth_unified_power_bound
    (N : ℕ) (hN4 : 4 ≤ N)
    (hN : explicitUnifiedOneThirdThreshold 60 < N) :
    (sourceSurjectiveOriginalH N + 1) ^ 180 <
      cubicPaletteCubeConstant ^ 60 * N ^ 63 := by
  rw [← siteH_eq_sourceSurjectiveOriginalH_add_one hN4]
  exact siteH_sevenTwentieth_unified_power_bound N hN

/-- Exact algebraic certificate that the displayed `7/20` exponent improves
the previously recorded tensor exponent `log(3) / log(22)`. -/
theorem sevenTwentieth_lt_logThree_div_logTwentyTwo_unified :
    (7 : ℝ) / 20 < Real.log 3 / Real.log 22 := by
  have hpowers : (22 : ℝ) ^ 7 < (3 : ℝ) ^ 20 := by norm_num
  have hx : (22 : ℝ) ^ 7 ∈ Set.Ioi 0 := by
    norm_num [Set.mem_Ioi]
  have hy : (3 : ℝ) ^ 20 ∈ Set.Ioi 0 := by
    norm_num [Set.mem_Ioi]
  have hlogs : Real.log ((22 : ℝ) ^ 7) <
      Real.log ((3 : ℝ) ^ 20) :=
    Real.strictMonoOn_log hx hy hpowers
  rw [Real.log_pow, Real.log_pow] at hlogs
  have hlog22 : 0 < Real.log (22 : ℝ) := Real.log_pos (by norm_num)
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 20) hlog22).2
  norm_num at hlogs ⊢
  nlinarith

end ErdosProblems.E160
