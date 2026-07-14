import ErdosProblems.E160.OneThirdUnifiedExplicit

/-!
# E160 real asymptotic bounds

This file converts the exact natural-power inequality from
`OneThirdUnifiedExplicit` into real `rpow` and `IsBigO` statements, including
the standard epsilon-form of an `N^(1/3+o(1))` upper bound.
-/

open Filter Set

namespace ErdosProblems.E160

/-- Taking the positive `3k`-th root of the exact natural-power inequality
gives the real exponent `1/3 + 1/k` and the fixed factor `C^(1/3)`. -/
theorem siteH_oneThirdPlusInv_unified_real_bound
    (N k : ℕ) (hk : 0 < k)
    (hN : explicitUnifiedOneThirdThreshold k < N) :
    (siteH N : ℝ) <
      (cubicPaletteCubeConstant : ℝ) ^ ((1 : ℝ) / 3) *
        (N : ℝ) ^ ((1 : ℝ) / 3 + (k : ℝ)⁻¹) := by
  have hpowNat :=
    siteH_oneThirdPlusSubpower_unified_explicit_rational N k hk hN
  have hpowReal :
      (siteH N : ℝ) ^ (3 * k : ℕ) <
        (cubicPaletteCubeConstant : ℝ) ^ (k : ℕ) *
          (N : ℝ) ^ (k + 3 : ℕ) := by
    exact_mod_cast hpowNat
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hkR0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hthreeK0 : 3 * k ≠ 0 := mul_ne_zero (by norm_num) hk0
  have hsite : 0 ≤ (siteH N : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ (cubicPaletteCubeConstant : ℝ) := Nat.cast_nonneg _
  have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hCpow : 0 ≤ (cubicPaletteCubeConstant : ℝ) ^ (k : ℕ) := pow_nonneg hC _
  have hNpow : 0 ≤ (N : ℝ) ^ (k + 3 : ℕ) := pow_nonneg hNr _
  calc
    (siteH N : ℝ) =
        ((siteH N : ℝ) ^ (3 * k : ℕ)) ^ (((3 * k : ℕ) : ℝ)⁻¹) := by
      symm
      exact Real.pow_rpow_inv_natCast hsite hthreeK0
    _ < ((cubicPaletteCubeConstant : ℝ) ^ (k : ℕ) *
          (N : ℝ) ^ (k + 3 : ℕ)) ^ (((3 * k : ℕ) : ℝ)⁻¹) :=
      Real.rpow_lt_rpow (pow_nonneg hsite _) hpowReal (by positivity)
    _ = (cubicPaletteCubeConstant : ℝ) ^ ((1 : ℝ) / 3) *
          (N : ℝ) ^ ((1 : ℝ) / 3 + (k : ℝ)⁻¹) := by
      rw [Real.mul_rpow hCpow hNpow]
      rw [← Real.rpow_natCast_mul hC k (((3 * k : ℕ) : ℝ)⁻¹)]
      rw [← Real.rpow_natCast_mul hNr (k + 3) (((3 * k : ℕ) : ℝ)⁻¹)]
      congr 1 <;> norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
      · field_simp
      · field_simp

/-- For each positive integer `k`, the exact power inequality yields the
corresponding real Big-O bound at exponent `1/3 + 1/k`. -/
theorem siteH_oneThirdPlusInv_unified_isBigO
    (k : ℕ) (hk : 0 < k) :
    (fun n ↦ (siteH n : ℝ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ ((1 : ℝ) / 3 + (k : ℝ)⁻¹)) := by
  refine Asymptotics.IsBigO.of_bound
    ((cubicPaletteCubeConstant : ℝ) ^ ((1 : ℝ) / 3)) ?_
  filter_upwards [eventually_gt_atTop (explicitUnifiedOneThirdThreshold k)] with N hN
  have h := siteH_oneThirdPlusInv_unified_real_bound N k hk hN
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact h.le

/-- Quantified real epsilon-form of the unified explicit upper bound. -/
theorem siteH_oneThirdPlusEpsilon_unified_isBigO
    (ε : ℝ) (hε : 0 < ε) :
    (fun n ↦ (siteH n : ℝ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ ((1 : ℝ) / 3 + ε)) := by
  obtain ⟨k, hk, hkinv⟩ := Real.exists_nat_pos_inv_lt hε
  have hO := siteH_oneThirdPlusInv_unified_isBigO k hk
  have hExponent :
      (1 : ℝ) / 3 + (k : ℝ)⁻¹ ≤ (1 : ℝ) / 3 + ε := by
    linarith
  have hGrow :
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 3 + (k : ℝ)⁻¹)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 3 + ε)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hp := Real.rpow_le_rpow_of_exponent_le hbase hExponent
    simpa only [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hp
  exact hO.trans hGrow

/-- Epsilon-form consequence of the explicit construction. -/
theorem oneThirdPlusEpsilonUpper_unified_explicit :
    OneThirdPlusEpsilonUpper := by
  intro ε hε
  exact siteH_oneThirdPlusEpsilon_unified_isBigO ε hε

/-- The same real epsilon-form in the strict nonempty-part source convention,
including the exact `+1` predecessor shift. -/
theorem sourceSurjectiveOriginalH_add_one_oneThirdPlusEpsilon_unified_isBigO
    (ε : ℝ) (hε : 0 < ε) :
    (fun n ↦ ((sourceSurjectiveOriginalH n + 1 : ℕ) : ℝ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ ((1 : ℝ) / 3 + ε)) := by
  have hO := siteH_oneThirdPlusEpsilon_unified_isBigO ε hε
  apply hO.congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop 4] with N hN
  exact_mod_cast siteH_eq_sourceSurjectiveOriginalH_add_one hN

/-- The fixed factor in the root bound can be absorbed into an arbitrarily
small positive exponent.  This coefficient-one eventual form is the usual
quantified reading of the upper estimate `N^(1/3+o(1))`. -/
theorem siteH_le_rpow_oneThird_add_epsilon_eventually
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (siteH N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3 + ε) := by
  obtain ⟨k, hk, hkinv⟩ := Real.exists_nat_pos_inv_lt hε
  let A : ℝ := (cubicPaletteCubeConstant : ℝ) ^ ((1 : ℝ) / 3)
  let δ : ℝ := ε - (k : ℝ)⁻¹
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hAbsorb : ∀ᶠ N : ℕ in atTop, A ≤ (N : ℝ) ^ δ := by
    exact ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop A)
  filter_upwards
      [eventually_gt_atTop (explicitUnifiedOneThirdThreshold k),
        eventually_ge_atTop 1, hAbsorb] with N hN hN1 hAN
  have hroot := siteH_oneThirdPlusInv_unified_real_bound N k hk hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  calc
    (siteH N : ℝ) ≤ A *
        (N : ℝ) ^ ((1 : ℝ) / 3 + (k : ℝ)⁻¹) := hroot.le
    _ ≤ (N : ℝ) ^ δ *
        (N : ℝ) ^ ((1 : ℝ) / 3 + (k : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hAN
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (N : ℝ) ^ (δ + ((1 : ℝ) / 3 + (k : ℝ)⁻¹)) :=
      (Real.rpow_add hNpos δ ((1 : ℝ) / 3 + (k : ℝ)⁻¹)).symm
    _ = (N : ℝ) ^ ((1 : ℝ) / 3 + ε) := by
      congr 1
      dsimp [δ]
      ring

/-- Coefficient-one eventual form in the strict source convention, retaining
the exact predecessor `+1`. -/
theorem sourceSurjectiveOriginalH_add_one_le_rpow_oneThird_add_epsilon_eventually
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((sourceSurjectiveOriginalH N + 1 : ℕ) : ℝ) ≤
        (N : ℝ) ^ ((1 : ℝ) / 3 + ε) := by
  filter_upwards
      [siteH_le_rpow_oneThird_add_epsilon_eventually ε hε,
        eventually_ge_atTop 4] with N hsite hN
  have heq :
      ((sourceSurjectiveOriginalH N + 1 : ℕ) : ℝ) = (siteH N : ℝ) := by
    exact_mod_cast (siteH_eq_sourceSurjectiveOriginalH_add_one hN).symm
  exact heq.trans_le hsite

/-- The `k=60` specialization gives the rational exponent `7/20`. -/
theorem siteH_sevenTwentieth_unified_real_bound
    (N : ℕ) (hN : explicitUnifiedOneThirdThreshold 60 < N) :
    (siteH N : ℝ) <
      (cubicPaletteCubeConstant : ℝ) ^ ((1 : ℝ) / 3) *
        (N : ℝ) ^ ((7 : ℝ) / 20) := by
  have h := siteH_oneThirdPlusInv_unified_real_bound
    N 60 (by norm_num) hN
  norm_num at h ⊢
  exact h

/-- Fixed `7/20` Big-O consequence of the unified construction. -/
theorem siteH_sevenTwentieth_unified_isBigO :
    (fun n ↦ (siteH n : ℝ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ ((7 : ℝ) / 20)) := by
  refine Asymptotics.IsBigO.of_bound
    ((cubicPaletteCubeConstant : ℝ) ^ ((1 : ℝ) / 3)) ?_
  filter_upwards [eventually_gt_atTop (explicitUnifiedOneThirdThreshold 60)] with N hN
  have h := siteH_sevenTwentieth_unified_real_bound N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact h.le

/-- The exponent `7/20` improves on the tensor exponent. -/
theorem betterThanTensorUpper_unified_explicit : BetterThanTensorUpper := by
  refine ⟨(7 : ℝ) / 20,
    sevenTwentieth_lt_logThree_div_logTwentyTwo_unified, ?_⟩
  exact siteH_sevenTwentieth_unified_isBigO

end ErdosProblems.E160
