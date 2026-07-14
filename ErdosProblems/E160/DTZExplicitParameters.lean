import ErdosProblems.E160.DTZSubpowerArithmetic

/-!
# Explicit parameters for the direct DTZ digit filter

The direct digit construction uses

`p = 24 * 2^m + 1`,  `m = aabbDigitCount N`.

The congruence `p = 1 mod 24` is the carry shield.  The same choice covers
the horizon and leaves only an exponentially-linear palette in `m`, hence a
discretely subpower palette in `N`.
-/

namespace ErdosProblems.E160

/-- Base for the explicit mod-24 digit construction. -/
def explicitDTZBase (N : ℕ) : ℕ := 24 * aabbBase N + 1

/-- The base is one modulo 24. -/
theorem explicitDTZBase_eq (N : ℕ) :
    explicitDTZBase N = 24 * aabbBase N + 1 := rfl

theorem explicitDTZBase_pos (N : ℕ) : 0 < explicitDTZBase N := by
  simp [explicitDTZBase]

/-- The power-of-two base is at most the mod-24 base. -/
theorem aabbBase_le_explicitDTZBase (N : ℕ) :
    aabbBase N ≤ explicitDTZBase N := by
  have hpos := aabbBase_pos N
  simp only [explicitDTZBase]
  omega

/-- The explicit base with `m` digits covers every target horizon. -/
theorem explicitDTZ_horizon_cover (N : ℕ) :
    N ≤ explicitDTZBase N ^ (aabbLowerDigits N + 1) := by
  exact (aabb_horizon_cover N).trans <|
    Nat.pow_le_pow_left (aabbBase_le_explicitDTZBase N)
      (aabbLowerDigits N + 1)

/-- A convenient binary upper bound for the explicit base. -/
theorem explicitDTZBase_le_two_pow (N : ℕ) :
    explicitDTZBase N ≤ 2 ^ (aabbDigitCount N + 5) := by
  have hone : 1 ≤ aabbBase N := by
    exact Nat.one_le_pow _ 2 (by norm_num)
  calc
    explicitDTZBase N = 24 * aabbBase N + 1 := rfl
    _ ≤ 25 * aabbBase N := by omega
    _ ≤ 32 * aabbBase N := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (aabbDigitCount N + 5) := by
      simp [aabbBase, pow_add, mul_comm]

/-- Numerical size of a mod-24 residue vector together with a bounded digit
square norm. -/
def explicitDTZPaletteBound (p L : ℕ) : ℕ :=
  24 ^ L * ((L + 1) * p ^ 2 + 1)

/-- The explicit horizon palette is bounded by `2^(8m+11)`. -/
theorem explicitDTZPaletteBound_le_two_pow (N : ℕ) :
    explicitDTZPaletteBound (explicitDTZBase N) (aabbLowerDigits N) ≤
      2 ^ (8 * aabbDigitCount N + 11) := by
  let m := aabbDigitCount N
  let L := aabbLowerDigits N
  let p := explicitDTZBase N
  have hm : 0 < m := by simpa [m] using aabbDigitCount_pos N
  have hLm : L + 1 = m := by
    simp only [L, aabbLowerDigits, m]
    omega
  have hLle : L ≤ m := by omega
  have h24 : 24 ≤ 2 ^ 5 := by norm_num
  have hfirst : 24 ^ L ≤ 2 ^ (5 * m) := by
    calc
      24 ^ L ≤ (2 ^ 5) ^ L := Nat.pow_le_pow_left h24 L
      _ = 2 ^ (5 * L) := by rw [pow_mul]
      _ ≤ 2 ^ (5 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp : p ≤ 2 ^ (m + 5) := by
    simpa [p, m] using explicitDTZBase_le_two_pow N
  have hmPow : m ≤ 2 ^ m :=
    (show m < 2 ^ m from Nat.lt_two_pow_self).le
  have hpSq : p ^ 2 ≤ 2 ^ (2 * m + 10) := by
    calc
      p ^ 2 ≤ (2 ^ (m + 5)) ^ 2 := Nat.pow_le_pow_left hp 2
      _ = 2 ^ ((m + 5) * 2) := (pow_mul 2 (m + 5) 2).symm
      _ = 2 ^ (2 * m + 10) := by congr 1; omega
  have hproduct : m * p ^ 2 ≤ 2 ^ (3 * m + 10) := by
    calc
      m * p ^ 2 ≤ 2 ^ m * 2 ^ (2 * m + 10) :=
        Nat.mul_le_mul hmPow hpSq
      _ = 2 ^ (m + (2 * m + 10)) := (pow_add 2 m (2 * m + 10)).symm
      _ = 2 ^ (3 * m + 10) := by congr 1; omega
  have hsecond : m * p ^ 2 + 1 ≤ 2 ^ (3 * m + 11) := by
    calc
      m * p ^ 2 + 1 ≤
          2 ^ (3 * m + 10) + 2 ^ (3 * m + 10) :=
        Nat.add_le_add hproduct
          (Nat.one_le_pow (3 * m + 10) 2 (by norm_num))
      _ = 2 * 2 ^ (3 * m + 10) := (two_mul _).symm
      _ = 2 ^ 1 * 2 ^ (3 * m + 10) := by norm_num
      _ = 2 ^ (1 + (3 * m + 10)) :=
        (pow_add 2 1 (3 * m + 10)).symm
      _ = 2 ^ (3 * m + 10 + 1) := by congr 1; omega
      _ = 2 ^ (3 * m + 11) := rfl
  change 24 ^ L * ((L + 1) * p ^ 2 + 1) ≤ _
  rw [hLm]
  calc
    24 ^ L * (m * p ^ 2 + 1) ≤
        2 ^ (5 * m) * 2 ^ (3 * m + 11) :=
      Nat.mul_le_mul hfirst hsecond
    _ = 2 ^ (5 * m + (3 * m + 11)) :=
      (pow_add 2 (5 * m) (3 * m + 11)).symm
    _ = 2 ^ (8 * m + 11) := by congr 1; omega

/-- For every fixed positive `k`, the explicit mod-24 square palette is
smaller than `N^(1/k)` after a displayed threshold. -/
theorem explicitDTZPaletteBound_pow_lt
    (N k : ℕ) (hk : 0 < k)
    (hN : 2 ^ (dtzABABSubpowerThreshold 8 11 0 k ^ 2) < N) :
    explicitDTZPaletteBound
        (explicitDTZBase N) (aabbLowerDigits N) ^ k < N := by
  have hbound := explicitDTZPaletteBound_le_two_pow N
  have hpow := Nat.pow_le_pow_left hbound k
  have hlarge := dtzABABPalette_card_pow_lt 8 11 0 N k hk hN
  simp only [Fintype.card_fin] at hlarge
  change (2 ^ (8 * aabbDigitCount N + 11)) ^ k < N at hlarge
  exact hpow.trans_lt hlarge

end ErdosProblems.E160
