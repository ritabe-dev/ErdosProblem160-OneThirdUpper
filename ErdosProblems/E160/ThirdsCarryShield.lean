import ErdosProblems.E160.CubicNormRoute

/-!
# A concrete thirds carry shield

This file proves the integer arithmetic behind the base-`p` cubic
construction.  The key point is uniform in `p`: if the outer and inner
residues lie in matching thirds, then a cyclic four-term progression of
residues cannot wrap.
-/

namespace ErdosProblems.E160

/-- The three consecutive intervals cut out by `p` after multiplying a
residue by three.  On residues in `[0,p)`, this is `floor (3r / p)` without
using division in the definition. -/
def thirdsRegion (p r : ℤ) : Fin 3 :=
  if 3 * r < p then 0 else if 3 * r < 2 * p then 1 else 2

/-- Equal thirds colours put two integers in the same one of the three
explicit intervals. -/
theorem thirdsRegion_eq_cases (p x y : ℤ)
    (h : thirdsRegion p x = thirdsRegion p y) :
    (3 * x < p ∧ 3 * y < p) ∨
      (p ≤ 3 * x ∧ 3 * x < 2 * p ∧
        p ≤ 3 * y ∧ 3 * y < 2 * p) ∨
      (2 * p ≤ 3 * x ∧ 2 * p ≤ 3 * y) := by
  by_cases hx0 : 3 * x < p <;>
    by_cases hx1 : 3 * x < 2 * p <;>
    by_cases hy0 : 3 * y < p <;>
    by_cases hy1 : 3 * y < 2 * p <;>
    simp [thirdsRegion, hx0, hx1, hy0, hy1] at h ⊢ <;> omega

/-- Two numbers in `(-p,p)` which are congruent modulo `p` differ by at most
one wrap. -/
theorem eq_or_eq_add_or_eq_sub_of_dvd_sub (p a b : ℤ)
    (hp : 0 < p)
    (haLower : -p < a) (haUpper : a < p)
    (hbLower : -p < b) (hbUpper : b < p)
    (hdiv : p ∣ a - b) :
    a = b ∨ a = b + p ∨ a = b - p := by
  obtain ⟨k, hk⟩ := hdiv
  have habLower : -2 * p < a - b := by omega
  have habUpper : a - b < 2 * p := by omega
  have hkLower : (-2 : ℤ) < k := by
    apply lt_of_mul_lt_mul_left
    · calc
      p * (-2) = -2 * p := by ring
      _ < a - b := habLower
      _ = p * k := hk
    · exact hp.le
  have hkUpper : k < (2 : ℤ) := by
    apply lt_of_mul_lt_mul_left
    · calc
      p * k = a - b := hk.symm
      _ < 2 * p := habUpper
      _ = p * 2 := by ring
    · exact hp.le
  have hkCases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hkCases with hk' | hk' | hk' <;> subst k <;> omega

/-- The genuine one-digit no-wrap lemma.  The three residue differences are
cyclically congruent modulo `p`; matching thirds on the outer and inner pairs
forces the congruences to be equalities in `ℤ`. -/
theorem thirdsRegion_noWrap (p r0 r1 r2 r3 : ℤ)
    (hp : 3 < p)
    (hr0Lower : 0 ≤ r0) (hr0Upper : r0 < p)
    (hr1Lower : 0 ≤ r1) (hr1Upper : r1 < p)
    (hr2Lower : 0 ≤ r2) (hr2Upper : r2 < p)
    (hr3Lower : 0 ≤ r3) (hr3Upper : r3 < p)
    (hcong01 : p ∣ (r1 - r0) - (r2 - r1))
    (hcong23 : p ∣ (r3 - r2) - (r2 - r1))
    (houter : thirdsRegion p r0 = thirdsRegion p r3)
    (hinner : thirdsRegion p r1 = thirdsRegion p r2) :
    r1 - r0 = r2 - r1 ∧ r3 - r2 = r2 - r1 := by
  have hp0 : 0 < p := by omega
  have h01 := eq_or_eq_add_or_eq_sub_of_dvd_sub p
    (r1 - r0) (r2 - r1) hp0 (by omega) (by omega)
      (by omega) (by omega) hcong01
  have h23 := eq_or_eq_add_or_eq_sub_of_dvd_sub p
    (r3 - r2) (r2 - r1) hp0 (by omega) (by omega)
      (by omega) (by omega) hcong23
  have ho := thirdsRegion_eq_cases p r0 r3 houter
  have hi := thirdsRegion_eq_cases p r1 r2 hinner
  rcases h01 with h01 | h01 | h01 <;>
    rcases h23 with h23 | h23 | h23 <;>
    rcases ho with ho | ho | ho <;>
    rcases hi with hi | hi | hi <;> omega

/-- Three signed base-`p` digits.  Valid digits below are restricted to
`[0,p)`; using `ℤ` here keeps all carry identities cast-free. -/
structure Digits3 where
  low : ℤ
  middle : ℤ
  high : ℤ
deriving DecidableEq

namespace Digits3

/-- Each coordinate is a genuine base-`p` digit. -/
def Valid (p : ℤ) (d : Digits3) : Prop :=
  0 ≤ d.low ∧ d.low < p ∧
    0 ≤ d.middle ∧ d.middle < p ∧
    0 ≤ d.high ∧ d.high < p

/-- The quotient after removing the low digit. -/
def upper (p : ℤ) (d : Digits3) : ℤ := d.middle + p * d.high

/-- The integer represented by the three digits. -/
def value (p : ℤ) (d : Digits3) : ℤ := d.low + p * upper p d

/-- Only the two carry-bearing coordinates need thirds colours.  The top
digit is already a quotient progression after the second carry is removed. -/
def carryShield (p : ℤ) (d : Digits3) : Fin 3 × Fin 3 :=
  (thirdsRegion p d.low, thirdsRegion p d.middle)

end Digits3

/-- Equal integer steps descend to equal quotient steps once the residue
steps are known to be equal. -/
theorem quotient_step_eq_of_residue_step_eq
    (p n0 n1 n2 q0 q1 q2 r0 r1 r2 : ℤ)
    (hp : p ≠ 0)
    (hn0 : n0 = r0 + p * q0)
    (hn1 : n1 = r1 + p * q1)
    (hn2 : n2 = r2 + p * q2)
    (hstep : n1 - n0 = n2 - n1)
    (hresidue : r1 - r0 = r2 - r1) :
    q1 - q0 = q2 - q1 := by
  have hmul : p * ((q1 - q0) - (q2 - q1)) = 0 := by
    calc
      p * ((q1 - q0) - (q2 - q1)) =
          ((n1 - n0) - (n2 - n1)) -
            ((r1 - r0) - (r2 - r1)) := by
              rw [hn0, hn1, hn2]
              ring
      _ = 0 := by rw [hstep, hresidue]; ring
  have hzero : (q1 - q0) - (q2 - q1) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hp
  omega

/-- Equal integer steps make the two residue steps congruent modulo the
base. -/
theorem residue_steps_congruent_of_decomposition
    (p n0 n1 n2 q0 q1 q2 r0 r1 r2 : ℤ)
    (hn0 : n0 = r0 + p * q0)
    (hn1 : n1 = r1 + p * q1)
    (hn2 : n2 = r2 + p * q2)
    (hstep : n1 - n0 = n2 - n1) :
    p ∣ (r1 - r0) - (r2 - r1) := by
  refine ⟨(q2 - q1) - (q1 - q0), ?_⟩
  rw [hn0, hn1, hn2] at hstep
  linear_combination hstep

/-- Coordinatewise signed four-term progression for three digits. -/
def Digits3FormFourAP (d0 d1 d2 d3 : Digits3) : Prop :=
  (d1.low - d0.low = d2.low - d1.low ∧
    d3.low - d2.low = d2.low - d1.low) ∧
  (d1.middle - d0.middle = d2.middle - d1.middle ∧
    d3.middle - d2.middle = d2.middle - d1.middle) ∧
  (d1.high - d0.high = d2.high - d1.high ∧
    d3.high - d2.high = d2.high - d1.high)

/-- The concrete arbitrary-base carry theorem.  A four-term progression of
three-digit integers whose two carry-bearing digit colours have the ABBA
pattern becomes a coordinatewise progression with no carries.

The shield has `3^2 = 9` values. After the second carry is removed, the high
digits themselves are an integer progression and need no further shield
coordinate. -/
theorem digits3_fourAP_of_carryShield (p : ℤ) (d0 d1 d2 d3 : Digits3)
    (hp : 3 < p)
    (hv0 : Digits3.Valid p d0) (hv1 : Digits3.Valid p d1)
    (hv2 : Digits3.Valid p d2) (hv3 : Digits3.Valid p d3)
    (hstep01 : Digits3.value p d1 - Digits3.value p d0 =
      Digits3.value p d2 - Digits3.value p d1)
    (hstep23 : Digits3.value p d3 - Digits3.value p d2 =
      Digits3.value p d2 - Digits3.value p d1)
    (houter : Digits3.carryShield p d0 = Digits3.carryShield p d3)
    (hinner : Digits3.carryShield p d1 = Digits3.carryShield p d2) :
    Digits3FormFourAP d0 d1 d2 d3 := by
  rcases hv0 with ⟨h0l0, h0l1, h0m0, h0m1, h0h0, h0h1⟩
  rcases hv1 with ⟨h1l0, h1l1, h1m0, h1m1, h1h0, h1h1⟩
  rcases hv2 with ⟨h2l0, h2l1, h2m0, h2m1, h2h0, h2h1⟩
  rcases hv3 with ⟨h3l0, h3l1, h3m0, h3m1, h3h0, h3h1⟩
  have houterLow : thirdsRegion p d0.low = thirdsRegion p d3.low :=
    congrArg Prod.fst houter
  have hinnerLow : thirdsRegion p d1.low = thirdsRegion p d2.low :=
    congrArg Prod.fst hinner
  have houterMiddle : thirdsRegion p d0.middle = thirdsRegion p d3.middle :=
    congrArg Prod.snd houter
  have hinnerMiddle : thirdsRegion p d1.middle = thirdsRegion p d2.middle :=
    congrArg Prod.snd hinner
  have hlowCong01 :
      p ∣ (d1.low - d0.low) - (d2.low - d1.low) := by
    exact residue_steps_congruent_of_decomposition p
      (Digits3.value p d0) (Digits3.value p d1) (Digits3.value p d2)
      (Digits3.upper p d0) (Digits3.upper p d1) (Digits3.upper p d2)
      d0.low d1.low d2.low (by rfl) (by rfl) (by rfl) hstep01
  have hlowCong23' :
      p ∣ (d2.low - d1.low) - (d3.low - d2.low) := by
    exact residue_steps_congruent_of_decomposition p
      (Digits3.value p d1) (Digits3.value p d2) (Digits3.value p d3)
      (Digits3.upper p d1) (Digits3.upper p d2) (Digits3.upper p d3)
      d1.low d2.low d3.low (by rfl) (by rfl) (by rfl) hstep23.symm
  have hlowCong23 :
      p ∣ (d3.low - d2.low) - (d2.low - d1.low) := by
    obtain ⟨k, hk⟩ := hlowCong23'
    refine ⟨-k, ?_⟩
    linear_combination -hk
  have hlow := thirdsRegion_noWrap p d0.low d1.low d2.low d3.low hp
    h0l0 h0l1 h1l0 h1l1 h2l0 h2l1 h3l0 h3l1
    hlowCong01 hlowCong23 houterLow hinnerLow
  have hp0 : p ≠ 0 := by omega
  have hupper01 : Digits3.upper p d1 - Digits3.upper p d0 =
      Digits3.upper p d2 - Digits3.upper p d1 := by
    exact quotient_step_eq_of_residue_step_eq p
      (Digits3.value p d0) (Digits3.value p d1) (Digits3.value p d2)
      (Digits3.upper p d0) (Digits3.upper p d1) (Digits3.upper p d2)
      d0.low d1.low d2.low hp0 (by rfl) (by rfl) (by rfl)
      hstep01 hlow.1
  have hupper23' : Digits3.upper p d2 - Digits3.upper p d1 =
      Digits3.upper p d3 - Digits3.upper p d2 := by
    exact quotient_step_eq_of_residue_step_eq p
      (Digits3.value p d1) (Digits3.value p d2) (Digits3.value p d3)
      (Digits3.upper p d1) (Digits3.upper p d2) (Digits3.upper p d3)
      d1.low d2.low d3.low hp0 (by rfl) (by rfl) (by rfl)
      hstep23.symm hlow.2.symm
  have hupper23 : Digits3.upper p d3 - Digits3.upper p d2 =
      Digits3.upper p d2 - Digits3.upper p d1 := hupper23'.symm
  have hmiddleCong01 :
      p ∣ (d1.middle - d0.middle) - (d2.middle - d1.middle) := by
    exact residue_steps_congruent_of_decomposition p
      (Digits3.upper p d0) (Digits3.upper p d1) (Digits3.upper p d2)
      d0.high d1.high d2.high d0.middle d1.middle d2.middle
      (by rfl) (by rfl) (by rfl) hupper01
  have hmiddleCong23' :
      p ∣ (d2.middle - d1.middle) - (d3.middle - d2.middle) := by
    exact residue_steps_congruent_of_decomposition p
      (Digits3.upper p d1) (Digits3.upper p d2) (Digits3.upper p d3)
      d1.high d2.high d3.high d1.middle d2.middle d3.middle
      (by rfl) (by rfl) (by rfl) hupper23.symm
  have hmiddleCong23 :
      p ∣ (d3.middle - d2.middle) - (d2.middle - d1.middle) := by
    obtain ⟨k, hk⟩ := hmiddleCong23'
    refine ⟨-k, ?_⟩
    linear_combination -hk
  have hmiddle := thirdsRegion_noWrap p
    d0.middle d1.middle d2.middle d3.middle hp
    h0m0 h0m1 h1m0 h1m1 h2m0 h2m1 h3m0 h3m1
    hmiddleCong01 hmiddleCong23 houterMiddle hinnerMiddle
  have hhigh01 : d1.high - d0.high = d2.high - d1.high := by
    exact quotient_step_eq_of_residue_step_eq p
      (Digits3.upper p d0) (Digits3.upper p d1) (Digits3.upper p d2)
      d0.high d1.high d2.high d0.middle d1.middle d2.middle hp0
      (by rfl) (by rfl) (by rfl) hupper01 hmiddle.1
  have hhigh23' : d2.high - d1.high = d3.high - d2.high := by
    exact quotient_step_eq_of_residue_step_eq p
      (Digits3.upper p d1) (Digits3.upper p d2) (Digits3.upper p d3)
      d1.high d2.high d3.high d1.middle d2.middle d3.middle hp0
      (by rfl) (by rfl) (by rfl) hupper23.symm hmiddle.2.symm
  exact ⟨hlow, hmiddle, hhigh01, hhigh23'.symm⟩

namespace Digits3

/-- The three residue coordinates, viewed as a vector over `ZMod p`. -/
def residueVector (p : ℕ) (d : Digits3) : Fin 3 → ZMod p :=
  ![(d.low : ZMod p), (d.middle : ZMod p), (d.high : ZMod p)]

/-- Integer four-term progressions in the three-digit model. -/
def IsValueFourAP (p : ℤ) (d0 d1 d2 d3 : Digits3) : Prop :=
  Valid p d0 ∧ Valid p d1 ∧ Valid p d2 ∧ Valid p d3 ∧
    value p d1 - value p d0 = value p d2 - value p d1 ∧
    value p d3 - value p d2 = value p d2 - value p d1 ∧
    value p d1 ≠ value p d0

/-- Canonical low-to-high base-`p` digits of a natural number.  The top digit
is not reduced modulo `p`; validity below supplies that bound when `n<p^3`. -/
def ofNat (p n : ℕ) : Digits3 where
  low := (n % p : ℕ)
  middle := ((n / p) % p : ℕ)
  high := (n / (p * p) : ℕ)

/-- Canonical digit extraction reconstructs the original natural number. -/
theorem value_ofNat (p n : ℕ) :
    value (p : ℤ) (ofNat p n) = (n : ℤ) := by
  have hrepr :
      n % p + p * ((n / p) % p + p * (n / (p * p))) = n := by
    rw [← Nat.div_div_eq_div_mul]
    rw [Nat.mod_add_div, Nat.mod_add_div]
  change ((n % p : ℕ) : ℤ) + (p : ℤ) *
      (((n / p) % p : ℕ) + (p : ℤ) * (n / (p * p) : ℕ)) =
    (n : ℤ)
  exact_mod_cast hrepr

/-- Numbers below `p^3` have three valid canonical digits. -/
theorem valid_ofNat (p n : ℕ) (hp : 0 < p) (hn : n < p ^ 3) :
    Valid (p : ℤ) (ofNat p n) := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hhigh : n / (p * p) < p := by
    apply (Nat.div_lt_iff_lt_mul hpp).2
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hn
  change 0 ≤ ((n % p : ℕ) : ℤ) ∧ ((n % p : ℕ) : ℤ) < (p : ℤ) ∧
    0 ≤ (((n / p) % p : ℕ) : ℤ) ∧
      (((n / p) % p : ℕ) : ℤ) < (p : ℤ) ∧
    0 ≤ ((n / (p * p) : ℕ) : ℤ) ∧
      ((n / (p * p) : ℕ) : ℤ) < (p : ℤ)
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_⟩
  · exact_mod_cast Nat.mod_lt n hp
  · exact_mod_cast Nat.mod_lt (n / p) hp
  · exact_mod_cast hhigh

/-- A nontrivial natural-number four-term progression below `p^3` becomes a
valid progression in the canonical three-digit model. -/
theorem isValueFourAP_ofNat (p a d : ℕ)
    (hp : 0 < p) (hd : 0 < d) (hbound : a + 3 * d < p ^ 3) :
    IsValueFourAP (p : ℤ)
      (ofNat p a) (ofNat p (a + d))
      (ofNat p (a + 2 * d)) (ofNat p (a + 3 * d)) := by
  have ha : a < p ^ 3 := by omega
  have ha1 : a + d < p ^ 3 := by omega
  have ha2 : a + 2 * d < p ^ 3 := by omega
  refine ⟨valid_ofNat p a hp ha,
    valid_ofNat p (a + d) hp ha1,
    valid_ofNat p (a + 2 * d) hp ha2,
    valid_ofNat p (a + 3 * d) hp hbound, ?_, ?_, ?_⟩
  · simp only [value_ofNat]
    push_cast
    ring
  · simp only [value_ofNat]
    push_cast
    ring
  · simp only [value_ofNat]
    push_cast
    omega

end Digits3

/-- Two representatives in `[0,p)` with the same image in `ZMod p` are
equal as integers. -/
theorem int_eq_of_zmod_cast_eq_of_mem_Ico (p : ℕ) (x y : ℤ)
    (hx0 : 0 ≤ x) (hxp : x < p) (hy0 : 0 ≤ y) (hyp : y < p)
    (hcast : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have hdiv : (p : ℤ) ∣ y - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mp hcast
  have habs : |y - x| < (p : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
  omega

/-- The 9-state concrete shield satisfies the abstract carry-shield
interface on valid three-digit progressions. -/
theorem digits3_carryShield_isABBA (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) :
    IsABBACarryShield (K := ZMod p)
      (Digits3.IsValueFourAP (p : ℤ))
      (Digits3.residueVector p)
      (Digits3.carryShield (p : ℤ)) := by
  intro d0 d1 d2 d3 hAP houter hinner
  rcases hAP with ⟨hv0, hv1, hv2, hv3, hstep01, hstep23, hnonzero⟩
  have hforms := digits3_fourAP_of_carryShield (p : ℤ)
    d0 d1 d2 d3 (by exact_mod_cast hp) hv0 hv1 hv2 hv3
    hstep01 hstep23 houter hinner
  rcases hforms with ⟨⟨hlow01, hlow23⟩,
    ⟨hmiddle01, hmiddle23⟩, hhigh01, hhigh23⟩
  have hlow2 : d2.low = d0.low + 2 * (d1.low - d0.low) := by omega
  have hmiddle2 : d2.middle = d0.middle +
      2 * (d1.middle - d0.middle) := by omega
  have hhigh2 : d2.high = d0.high + 2 * (d1.high - d0.high) := by omega
  have hlow3 : d3.low = d0.low + 3 * (d1.low - d0.low) := by omega
  have hmiddle3 : d3.middle = d0.middle +
      3 * (d1.middle - d0.middle) := by omega
  have hhigh3 : d3.high = d0.high + 3 * (d1.high - d0.high) := by omega
  let x : Fin 3 → ZMod p := Digits3.residueVector p d0
  let h : Fin 3 → ZMod p :=
    Digits3.residueVector p d1 - Digits3.residueVector p d0
  have hh : h ≠ 0 := by
    intro hz
    have hz0 := congrFun hz (0 : Fin 3)
    have hz1 := congrFun hz (1 : Fin 3)
    have hz2 := congrFun hz (2 : Fin 3)
    have hcastLow : (d1.low : ZMod p) = (d0.low : ZMod p) := by
      apply sub_eq_zero.mp
      simpa [h, Digits3.residueVector] using hz0
    have hcastMiddle : (d1.middle : ZMod p) = (d0.middle : ZMod p) := by
      apply sub_eq_zero.mp
      simpa [h, Digits3.residueVector] using hz1
    have hcastHigh : (d1.high : ZMod p) = (d0.high : ZMod p) := by
      apply sub_eq_zero.mp
      simpa [h, Digits3.residueVector] using hz2
    rcases hv0 with ⟨h0l0, h0l1, h0m0, h0m1, h0h0, h0h1⟩
    rcases hv1 with ⟨h1l0, h1l1, h1m0, h1m1, h1h0, h1h1⟩
    have hlowEq := int_eq_of_zmod_cast_eq_of_mem_Ico p
      d1.low d0.low h1l0 h1l1 h0l0 h0l1 hcastLow
    have hmiddleEq := int_eq_of_zmod_cast_eq_of_mem_Ico p
      d1.middle d0.middle h1m0 h1m1 h0m0 h0m1 hcastMiddle
    have hhighEq := int_eq_of_zmod_cast_eq_of_mem_Ico p
      d1.high d0.high h1h0 h1h1 h0h0 h0h1 hcastHigh
    apply hnonzero
    simp [Digits3.value, Digits3.upper, hlowEq, hmiddleEq, hhighEq]
  refine ⟨x, h, hh, rfl, ?_, ?_, ?_⟩
  · simp [x, h]
  · funext i
    fin_cases i
    · change (d2.low : ZMod p) =
        (d0.low : ZMod p) + (2 : ZMod p) *
          ((d1.low : ZMod p) - (d0.low : ZMod p))
      rw [hlow2]
      push_cast
      ring
    · change (d2.middle : ZMod p) =
        (d0.middle : ZMod p) + (2 : ZMod p) *
          ((d1.middle : ZMod p) - (d0.middle : ZMod p))
      rw [hmiddle2]
      push_cast
      ring
    · change (d2.high : ZMod p) =
        (d0.high : ZMod p) + (2 : ZMod p) *
          ((d1.high : ZMod p) - (d0.high : ZMod p))
      rw [hhigh2]
      push_cast
      ring
  · funext i
    fin_cases i
    · change (d3.low : ZMod p) =
        (d0.low : ZMod p) + (3 : ZMod p) *
          ((d1.low : ZMod p) - (d0.low : ZMod p))
      rw [hlow3]
      push_cast
      ring
    · change (d3.middle : ZMod p) =
        (d0.middle : ZMod p) + (3 : ZMod p) *
          ((d1.middle : ZMod p) - (d0.middle : ZMod p))
      rw [hmiddle3]
      push_cast
      ring
    · change (d3.high : ZMod p) =
        (d0.high : ZMod p) + (3 : ZMod p) *
          ((d1.high : ZMod p) - (d0.high : ZMod p))
      rw [hhigh3]
      push_cast
      ring

end ErdosProblems.E160
