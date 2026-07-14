import ErdosProblems.E160.FilterAssembly

/-!
# Horizon parameters for the dyadic AABB factor

The exact AABB-free construction works on `[0,p^(L+1))`.  This file chooses
power-of-two parameters for every horizon `N`, proves the interval cover, and
specializes the finite palette formula.  The final theorem gives an explicit
discrete `N^(o(1))` estimate: for each fixed positive `k`, a displayed
threshold makes the `k`-th power of the palette smaller than `N`.
-/

namespace ErdosProblems.E160

/-- Binary ceiling logarithm of the target horizon. -/
def aabbCeilLog (N : ℕ) : ℕ := Nat.clog 2 N

/-- The number of base digits, chosen as the integer ceiling of the square
root of the binary ceiling logarithm (with the harmless value `1` at zero). -/
def aabbDigitCount (N : ℕ) : ℕ := Nat.sqrt (aabbCeilLog N - 1) + 1

/-- Power-of-two base used by the horizon-level AABB factor. -/
def aabbBase (N : ℕ) : ℕ := 2 ^ aabbDigitCount N

/-- The number of carry-bearing lower digits. -/
def aabbLowerDigits (N : ℕ) : ℕ := aabbDigitCount N - 1

theorem aabbDigitCount_pos (N : ℕ) : 0 < aabbDigitCount N := by
  simp [aabbDigitCount]

theorem aabbBase_pos (N : ℕ) : 0 < aabbBase N := by
  simp [aabbBase]

/-- The ceiling logarithm fits inside the square of the chosen digit count. -/
theorem aabbCeilLog_le_digitCount_sq (N : ℕ) :
    aabbCeilLog N ≤ aabbDigitCount N ^ 2 := by
  by_cases hq : aabbCeilLog N = 0
  · simp [hq]
  · have hpos : 0 < aabbCeilLog N := Nat.pos_of_ne_zero hq
    have hsqrt := Nat.succ_le_succ_sqrt' (aabbCeilLog N - 1)
    have hpred : aabbCeilLog N - 1 + 1 = aabbCeilLog N := by omega
    simpa [aabbDigitCount, hpred] using hsqrt

/-- For a positive ceiling logarithm, the square of the preceding digit count
is still strictly below it. -/
theorem pred_digitCount_sq_lt_aabbCeilLog (N : ℕ)
    (hq : 0 < aabbCeilLog N) :
    (aabbDigitCount N - 1) ^ 2 < aabbCeilLog N := by
  have hsqrt : Nat.sqrt (aabbCeilLog N - 1) ^ 2 ≤
      aabbCeilLog N - 1 := Nat.sqrt_le' _
  have hcount : aabbDigitCount N - 1 =
      Nat.sqrt (aabbCeilLog N - 1) := by
    simp [aabbDigitCount]
  rw [hcount]
  omega

/-- Every horizon lies in the complete base-power interval used by its AABB
colouring. -/
theorem aabb_horizon_cover (N : ℕ) :
    N ≤ aabbBase N ^ (aabbLowerDigits N + 1) := by
  have hlog : N ≤ 2 ^ aabbCeilLog N :=
    Nat.le_pow_clog (by norm_num) N
  have hexponent : aabbCeilLog N ≤ aabbDigitCount N ^ 2 :=
    aabbCeilLog_le_digitCount_sq N
  have hpow : 2 ^ aabbCeilLog N ≤ 2 ^ (aabbDigitCount N ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  calc
    N ≤ 2 ^ aabbCeilLog N := hlog
    _ ≤ 2 ^ (aabbDigitCount N ^ 2) := hpow
    _ = aabbBase N ^ (aabbLowerDigits N + 1) := by
      have hm : aabbLowerDigits N + 1 = aabbDigitCount N := by
        have hpos := aabbDigitCount_pos N
        simp only [aabbLowerDigits]
        omega
      rw [hm]
      simp [aabbBase, pow_two, pow_mul]

/-- Exact specialization of the available palette size to a positive
power-of-two base and `m` digits. -/
theorem dyadicSquarePalette_card_power_two (m : ℕ) (hm : 0 < m) :
    Fintype.card (DyadicSquarePalette (2 ^ m) (m - 1)) =
      (m + 1) ^ (m - 1) * (m * 2 ^ (2 * m) + 1) := by
  rw [dyadicSquarePalette_card, Nat.log_pow (by norm_num)]
  have hpred : m - 1 + 1 = m := by omega
  rw [hpred]
  congr 2
  rw [← pow_mul]
  congr 2
  omega

/-- Elementary domination used to bound the binary ceiling logarithm of the
digit count. -/
theorem succ_sq_le_four_pow (s : ℕ) (hs : 1 ≤ s) :
    (s + 1) ^ 2 ≤ 4 ^ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        norm_num
      · have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs0
        have hprev := ih hspos
        calc
          (s + 1 + 1) ^ 2 ≤ 4 * (s + 1) ^ 2 := by nlinarith
          _ ≤ 4 * 4 ^ s := Nat.mul_le_mul_left 4 hprev
          _ = 4 ^ (s + 1) := by rw [pow_succ]; omega

/-- A direct integer bound for the logarithmic part of the palette. -/
theorem clog_two_succ_le_two_mul_sqrt (m : ℕ) (hm : 0 < m) :
    Nat.clog 2 (m + 1) ≤ 2 * Nat.sqrt m := by
  have hsne : Nat.sqrt m ≠ 0 := by
    intro hs
    exact hm.ne' (Nat.sqrt_eq_zero.mp hs)
  have hspos : 1 ≤ Nat.sqrt m := Nat.one_le_iff_ne_zero.2 hsne
  apply Nat.clog_le_of_le_pow
  calc
    m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := Nat.succ_le_succ_sqrt' m
    _ ≤ 4 ^ Nat.sqrt m := succ_sq_le_four_pow (Nat.sqrt m) hspos
    _ = 2 ^ (2 * Nat.sqrt m) := by
      rw [show 4 = 2 ^ 2 by norm_num, pow_mul]

/-- A binary exponent budget for the power-of-two AABB palette. -/
def aabbPaletteExponentBudget (m : ℕ) : ℕ :=
  m * Nat.clog 2 (m + 1) + 2 * m + 1

/-- The exact finite palette is bounded by a single power of two with exponent
`m log₂(m+1) + 2m + 1`. -/
theorem dyadicSquarePalette_card_le_two_pow_budget
    (m : ℕ) (hm : 0 < m) :
    Fintype.card (DyadicSquarePalette (2 ^ m) (m - 1)) ≤
      2 ^ aabbPaletteExponentBudget m := by
  let r := Nat.clog 2 (m + 1)
  have hbase : m + 1 ≤ 2 ^ r := by
    simpa [r] using Nat.le_pow_clog (by norm_num) (m + 1)
  have hfirst : (m + 1) ^ (m - 1) ≤ 2 ^ (r * (m - 1)) := by
    calc
      (m + 1) ^ (m - 1) ≤ (2 ^ r) ^ (m - 1) :=
        Nat.pow_le_pow_left hbase (m - 1)
      _ = 2 ^ (r * (m - 1)) := by rw [pow_mul]
  have hmBase : m ≤ 2 ^ r := (Nat.le_succ m).trans hbase
  have hterm : m * 2 ^ (2 * m) ≤ 2 ^ (r + 2 * m) := by
    calc
      m * 2 ^ (2 * m) ≤ 2 ^ r * 2 ^ (2 * m) :=
        Nat.mul_le_mul_right (2 ^ (2 * m)) hmBase
      _ = 2 ^ (r + 2 * m) := (pow_add 2 r (2 * m)).symm
  have hsecond : m * 2 ^ (2 * m) + 1 ≤
      2 ^ (r + 2 * m + 1) := by
    calc
      m * 2 ^ (2 * m) + 1 ≤
          2 ^ (r + 2 * m) + 2 ^ (r + 2 * m) := by
        exact Nat.add_le_add hterm
          (Nat.one_le_pow (r + 2 * m) 2 (by norm_num))
      _ = 2 ^ (r + 2 * m + 1) := by rw [pow_succ]; omega
  rw [dyadicSquarePalette_card_power_two m hm]
  calc
    (m + 1) ^ (m - 1) * (m * 2 ^ (2 * m) + 1) ≤
        2 ^ (r * (m - 1)) * 2 ^ (r + 2 * m + 1) :=
      Nat.mul_le_mul hfirst hsecond
    _ = 2 ^ aabbPaletteExponentBudget m := by
      rw [← pow_add]
      congr 1
      have hpred : m - 1 + 1 = m := by omega
      calc
        r * (m - 1) + (r + 2 * m + 1) =
            (r * (m - 1) + r) + (2 * m + 1) := by omega
        _ = r * (m - 1 + 1) + (2 * m + 1) := by rw [Nat.mul_add, mul_one]
        _ = r * m + (2 * m + 1) := by rw [hpred]
        _ = aabbPaletteExponentBudget m := by
          simp only [aabbPaletteExponentBudget]
          change r * m + (2 * m + 1) = m * r + 2 * m + 1
          rw [Nat.mul_comm r m]
          omega

/-- The exponent budget grows at most like `m^(3/2)`, strictly below the
quadratic horizon exponent. -/
theorem aabbPaletteExponentBudget_le_five_mul_sqrt
    (m : ℕ) (hm : 0 < m) :
    aabbPaletteExponentBudget m ≤ 5 * m * Nat.sqrt m := by
  have hsne : Nat.sqrt m ≠ 0 := by
    intro hs
    exact hm.ne' (Nat.sqrt_eq_zero.mp hs)
  have hspos : 1 ≤ Nat.sqrt m := Nat.one_le_iff_ne_zero.2 hsne
  have hlog := clog_two_succ_le_two_mul_sqrt m hm
  have hmul := Nat.mul_le_mul_left m hlog
  simp only [aabbPaletteExponentBudget]
  calc
    m * Nat.clog 2 (m + 1) + 2 * m + 1 ≤
        m * (2 * Nat.sqrt m) + 2 * m + 1 := by omega
    _ ≤ 5 * m * Nat.sqrt m := by nlinarith

/-- The finite dyadic-square colouring with parameters chosen directly from
the target horizon. -/
def horizonDyadicSquareColour (N n : ℕ) :
    DyadicSquarePalette (aabbBase N) (aabbLowerDigits N) :=
  finiteDyadicSquareColour (aabbBase N) (aabbLowerDigits N)
    (aabbBase_pos N) n

/-- For every `N`, the chosen finite colouring excludes AABB on every
nontrivial four-term progression in `[0,N)`. -/
theorem horizonDyadicSquareColour_isAABBFreeColouring (N : ℕ) :
    IsAABBFreeColouring (BoundedIntFourAP4 N)
      (horizonDyadicSquareColour N) := by
  intro n0 n1 n2 n3 hAP
  rcases hAP with ⟨hn0, hn1, hn2, hn3, hfour, hnontrivial⟩
  have hcover := aabb_horizon_cover N
  exact finiteDyadicSquareColour_aabb_free
    (aabbBase N) (aabbLowerDigits N) n0 n1 n2 n3
    (aabbBase_pos N)
    (hn0.trans_le hcover) (hn1.trans_le hcover)
    (hn2.trans_le hcover) (hn3.trans_le hcover)
    hfour hnontrivial

/-- At an arbitrary horizon, only the no-three-equal and ABAB-free factors
remain to complete the proper-ABBA filter. -/
theorem horizonDyadic_threeFactor_isProperABBAFilter
    {C0 C2 : Type*} (N : ℕ)
    (noThreeColour : ℕ → C0)
    (ababColour : ℕ → C2)
    (hnoThree : IsNoThreeEqualColouring
      (BoundedIntFourAP4 N) noThreeColour)
    (habab : IsABABFreeColouring
      (BoundedIntFourAP4 N) ababColour) :
    IsProperABBAFilter
      (BoundedIntFourAP4 N)
      (fun n ↦ (noThreeColour n,
        horizonDyadicSquareColour N n, ababColour n)) := by
  exact threeFactor_isProperABBAFilter
    (BoundedIntFourAP4 N)
    noThreeColour (horizonDyadicSquareColour N) ababColour
    hnoThree (horizonDyadicSquareColour_isAABBFreeColouring N) habab

/-- A coarse integer inequality turning the `m^(3/2)` palette exponent into
a strict saving against a quadratic horizon exponent. -/
theorem five_mul_succ_mul_sqrt_succ_mul_le_sq
    (k s : ℕ) (hk : 0 < k) (hlarge : (20 * k) ^ 2 ≤ s) :
    5 * (s + 1) * Nat.sqrt (s + 1) * k ≤ s ^ 2 := by
  have htwenty_pos : 1 ≤ 20 * k := by omega
  have hsqrt_s_pos : 1 ≤ Nat.sqrt s := by
    have htwenty_le : 20 * k ≤ Nat.sqrt s :=
      (Nat.le_sqrt').2 hlarge
    omega
  have hs_pos : 1 ≤ s := by
    have hsqrt_le : Nat.sqrt s ≤ s := Nat.sqrt_le_self s
    omega
  have hsucc : s + 1 ≤ 2 * s := by omega
  have hsqrt_succ : Nat.sqrt (s + 1) ≤ 2 * Nat.sqrt s := by
    calc
      Nat.sqrt (s + 1) ≤ Nat.sqrt s + 1 :=
        Nat.sqrt_succ_le_succ_sqrt s
      _ ≤ 2 * Nat.sqrt s := by omega
  have htwenty_le : 20 * k ≤ Nat.sqrt s :=
    (Nat.le_sqrt').2 hlarge
  have hsmall : 20 * k * Nat.sqrt s ≤ s := by
    calc
      20 * k * Nat.sqrt s ≤ Nat.sqrt s * Nat.sqrt s :=
        Nat.mul_le_mul_right (Nat.sqrt s) htwenty_le
      _ ≤ s := Nat.sqrt_le s
  calc
    5 * (s + 1) * Nat.sqrt (s + 1) * k ≤
        5 * (2 * s) * (2 * Nat.sqrt s) * k := by gcongr
    _ = s * (20 * k * Nat.sqrt s) := by ring
    _ ≤ s * s := Nat.mul_le_mul_left s hsmall
    _ = s ^ 2 := by ring

/-- Explicit discrete subpower estimate for the horizon AABB palette.  For
each fixed positive `k`, the displayed elementary threshold is sufficient for
the `k`-th power of the palette size to be smaller than the horizon. -/
theorem horizonDyadicSquarePalette_card_pow_lt
    (N k : ℕ) (hk : 0 < k)
    (hN : 2 ^ ((20 * k) ^ 4) < N) :
    Fintype.card
        (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ^ k < N := by
  let q := aabbCeilLog N
  let s := Nat.sqrt (q - 1)
  let m := aabbDigitCount N
  have hthreshold : (20 * k) ^ 4 < q := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num)).2
    simpa [q, aabbCeilLog] using hN
  have hfour : (20 * k) ^ 4 ≤ q - 1 := by omega
  have hlarge : (20 * k) ^ 2 ≤ s := by
    apply (Nat.le_sqrt').2
    calc
      ((20 * k) ^ 2) ^ 2 = (20 * k) ^ 4 := by ring
      _ ≤ q - 1 := hfour
  have hm : m = s + 1 := by
    simp [m, s, q, aabbDigitCount]
  have hmpos : 0 < m := by rw [hm]; omega
  have hbudget : aabbPaletteExponentBudget m ≤
      5 * m * Nat.sqrt m :=
    aabbPaletteExponentBudget_le_five_mul_sqrt m hmpos
  have hcard :
      Fintype.card
          (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ≤
        2 ^ (5 * m * Nat.sqrt m) := by
    have hraw :
        Fintype.card (DyadicSquarePalette (2 ^ m) (m - 1)) ≤
          2 ^ aabbPaletteExponentBudget m :=
      dyadicSquarePalette_card_le_two_pow_budget m hmpos
    have hraw' :
        Fintype.card
            (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ≤
          2 ^ aabbPaletteExponentBudget m := by
      simpa only [aabbBase, aabbLowerDigits, m] using hraw
    exact hraw'.trans (Nat.pow_le_pow_right (by norm_num) hbudget)
  have hexponent : (5 * m * Nat.sqrt m) * k ≤ q - 1 := by
    rw [hm]
    exact (five_mul_succ_mul_sqrt_succ_mul_le_sq k s hk hlarge).trans
      (Nat.sqrt_le' (q - 1))
  have hNone : 1 < N := by
    have hone : 1 ≤ 2 ^ ((20 * k) ^ 4) :=
      Nat.one_le_pow ((20 * k) ^ 4) 2 (by norm_num)
    omega
  calc
    Fintype.card
          (DyadicSquarePalette (aabbBase N) (aabbLowerDigits N)) ^ k ≤
        (2 ^ (5 * m * Nat.sqrt m)) ^ k :=
      Nat.pow_le_pow_left hcard k
    _ = 2 ^ ((5 * m * Nat.sqrt m) * k) :=
      (pow_mul 2 (5 * m * Nat.sqrt m) k).symm
    _ ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) hexponent
    _ < N := by
      simpa [q, aabbCeilLog] using
        (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hNone)

end ErdosProblems.E160
