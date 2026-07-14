import ErdosProblems.E160.DTZPatternBridge

/-!
# An explicit finite no-three-equal factor

This file gives the finite-digit part of the construction behind
Deng--Tidor--Zhao Lemma 3.2 for the three weight pairs needed at `k = 4`.
A base congruent to `1` modulo `24` and lower-digit residues modulo `24`
remove carries.  The integer square norm then makes a monochromatic weighted
three-point pattern trivial.

The asymptotic palette estimates are proved in `DTZSubpowerArithmetic`.
-/

namespace ErdosProblems.E160

/-- Bases used by the explicit no-three-equal construction. -/
def noThreeMod24Base (s : ℕ) : ℕ := 24 * s + 1

theorem noThreeMod24Base_pos (s : ℕ) : 0 < noThreeMod24Base s := by
  simp [noThreeMod24Base]

/-- One mod-24 carry-correction step.  For the positive weights whose sum is
at most three, equal mod-24 labels on all three residues expose the exact
weighted relation on the residues and pass it to the base quotients. -/
theorem noThreeMod24_quotient_step
    (s a b x y z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 3)
    (hrel : a * x + b * y = (a + b) * z)
    (hxy : (x % noThreeMod24Base s) % 24 =
      (y % noThreeMod24Base s) % 24)
    (hyz : (y % noThreeMod24Base s) % 24 =
      (z % noThreeMod24Base s) % 24) :
    a * (x % noThreeMod24Base s) +
          b * (y % noThreeMod24Base s) =
        (a + b) * (z % noThreeMod24Base s) ∧
      a * (x / noThreeMod24Base s) +
          b * (y / noThreeMod24Base s) =
        (a + b) * (z / noThreeMod24Base s) := by
  let p := noThreeMod24Base s
  let rx := x % p
  let ry := y % p
  let rz := z % p
  have hp : 0 < p := by simpa [p] using noThreeMod24Base_pos s
  have hrx : rx < p := Nat.mod_lt _ hp
  have hry : ry < p := Nat.mod_lt _ hp
  have hrz : rz < p := Nat.mod_lt _ hp
  have hmodp : a * rx + b * ry ≡ (a + b) * rz [MOD p] := by
    have hx : rx ≡ x [MOD p] := by
      simpa [rx] using Nat.mod_modEq x p
    have hy : ry ≡ y [MOD p] := by
      simpa [ry] using Nat.mod_modEq y p
    have hz : rz ≡ z [MOD p] := by
      simpa [rz] using Nat.mod_modEq z p
    exact (hx.mul_left a).add (hy.mul_left b) |>.trans <|
      (show a * x + b * y ≡ (a + b) * z [MOD p] by rw [hrel]) |>.trans
        (hz.mul_left (a + b)).symm
  have hmod24 : a * rx + b * ry ≡ (a + b) * rz [MOD 24] := by
    have hxy' : rx ≡ ry [MOD 24] := by
      simpa [rx, ry, p] using hxy
    have hyz' : ry ≡ rz [MOD 24] := by
      simpa [ry, rz, p] using hyz
    calc
      a * rx + b * ry ≡ a * rz + b * rz [MOD 24] :=
        ((hxy'.trans hyz').mul_left a).add (hyz'.mul_left b)
      _ = (a + b) * rz := (Nat.add_mul a b rz).symm
  have hpdiv : (p : ℤ) ∣
      ((((a + b) * rz : ℕ) : ℤ) - ((a * rx + b * ry : ℕ) : ℤ)) :=
    hmodp.dvd
  have h24div : (24 : ℤ) ∣
      ((((a + b) * rz : ℕ) : ℤ) - ((a * rx + b * ry : ℕ) : ℤ)) :=
    hmod24.dvd
  have hcoprime : Nat.Coprime p 24 := by
    simp only [p, noThreeMod24Base]
    rw [show 24 * s + 1 = 1 + s * 24 by omega]
    exact (Nat.coprime_add_mul_right_left 1 24 s).2 (by simp)
  have hprod : (p : ℤ) * 24 ∣
      ((((a + b) * rz : ℕ) : ℤ) - ((a * rx + b * ry : ℕ) : ℤ)) :=
    hcoprime.isCoprime.mul_dvd hpdiv h24div
  have hcases :
      (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    omega
  have hbound :
      |((((a + b) * rz : ℕ) : ℤ) - ((a * rx + b * ry : ℕ) : ℤ))| <
        (p : ℤ) * 24 := by
    rw [abs_lt]
    rcases hcases with h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      constructor <;> norm_num at * <;> omega
  have hzero := Int.eq_zero_of_abs_lt_dvd hprod hbound
  have hdigit : a * rx + b * ry = (a + b) * rz := by
    have heq : (a + b) * rz = a * rx + b * ry := by
      exact_mod_cast (sub_eq_zero.mp hzero)
    exact heq.symm
  have hxdec : (x : ℤ) = ((x % p : ℕ) : ℤ) +
      (p : ℤ) * ((x / p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div x p).symm
  have hydec : (y : ℤ) = ((y % p : ℕ) : ℤ) +
      (p : ℤ) * ((y / p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div y p).symm
  have hzdec : (z : ℤ) = ((z % p : ℕ) : ℤ) +
      (p : ℤ) * ((z / p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div z p).symm
  have hrelInt : (a : ℤ) * (x : ℤ) + (b : ℤ) * (y : ℤ) =
      ((a + b : ℕ) : ℤ) * (z : ℤ) := by
    exact_mod_cast hrel
  have hdigitInt : (a : ℤ) * ((x % p : ℕ) : ℤ) +
      (b : ℤ) * ((y % p : ℕ) : ℤ) =
        ((a + b : ℕ) : ℤ) * ((z % p : ℕ) : ℤ) := by
    exact_mod_cast hdigit
  have hquotientInt : (a : ℤ) * ((x / p : ℕ) : ℤ) +
      (b : ℤ) * ((y / p : ℕ) : ℤ) =
        ((a + b : ℕ) : ℤ) * ((z / p : ℕ) : ℤ) := by
    nlinarith
  have hquotient : a * (x / p) + b * (y / p) =
      (a + b) * (z / p) := by
    exact_mod_cast hquotientInt
  simpa [p, rx, ry, rz] using And.intro hdigit hquotient

/-- Iterating the mod-24 correction through the lower `L` digits preserves
the weighted relation in every quotient and exposes it in every lower digit. -/
theorem noThreeMod24_quotient_induction
    (s L a b x y z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 3)
    (hrel : a * x + b * y = (a + b) * z)
    (hxy : ∀ k < L,
      digitAt (noThreeMod24Base s) k x % 24 =
        digitAt (noThreeMod24Base s) k y % 24)
    (hyz : ∀ k < L,
      digitAt (noThreeMod24Base s) k y % 24 =
        digitAt (noThreeMod24Base s) k z % 24) :
    (∀ k ≤ L,
      a * quotientAt (noThreeMod24Base s) k x +
          b * quotientAt (noThreeMod24Base s) k y =
        (a + b) * quotientAt (noThreeMod24Base s) k z) ∧
    (∀ k < L,
      a * digitAt (noThreeMod24Base s) k x +
          b * digitAt (noThreeMod24Base s) k y =
        (a + b) * digitAt (noThreeMod24Base s) k z) := by
  let p := noThreeMod24Base s
  have hquotients : ∀ k ≤ L,
      a * quotientAt p k x + b * quotientAt p k y =
        (a + b) * quotientAt p k z := by
    intro k hk
    induction k with
    | zero => simpa [quotientAt] using hrel
    | succ k ih =>
        have hkL : k < L := by omega
        have hprevious := ih (by omega)
        have hstep := noThreeMod24_quotient_step s a b
          (quotientAt p k x) (quotientAt p k y) (quotientAt p k z)
          ha hb hab hprevious
          (by simpa [p, digitAt] using hxy k hkL)
          (by simpa [p, digitAt] using hyz k hkL)
        simpa [p, quotientAt_succ] using hstep.2
  refine ⟨by simpa [p] using hquotients, ?_⟩
  intro k hk
  have hstep := noThreeMod24_quotient_step s a b
    (quotientAt p k x) (quotientAt p k y) (quotientAt p k z)
    ha hb hab (hquotients k hk.le)
    (by simpa [p, digitAt] using hxy k hk)
    (by simpa [p, digitAt] using hyz k hk)
  simpa [p, digitAt] using hstep.1

/-- The quotient induction plus the top-digit bound exposes the weighted
relation in the complete fixed-length digit vectors. -/
theorem noThreeMod24_all_digits_weighted
    (s L a b x y z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 3)
    (hx : x < noThreeMod24Base s ^ (L + 1))
    (hy : y < noThreeMod24Base s ^ (L + 1))
    (hz : z < noThreeMod24Base s ^ (L + 1))
    (hrel : a * x + b * y = (a + b) * z)
    (hxy : ∀ k < L,
      digitAt (noThreeMod24Base s) k x % 24 =
        digitAt (noThreeMod24Base s) k y % 24)
    (hyz : ∀ k < L,
      digitAt (noThreeMod24Base s) k y % 24 =
        digitAt (noThreeMod24Base s) k z % 24) :
    ∀ k ≤ L,
      a * digitAt (noThreeMod24Base s) k x +
          b * digitAt (noThreeMod24Base s) k y =
        (a + b) * digitAt (noThreeMod24Base s) k z := by
  let p := noThreeMod24Base s
  have hp : 0 < p := by simpa [p] using noThreeMod24Base_pos s
  obtain ⟨hquotients, hdigits⟩ :=
    noThreeMod24_quotient_induction s L a b x y z
      ha hb hab hrel hxy hyz
  intro k hk
  by_cases hkL : k < L
  · exact hdigits k hkL
  · have hkeq : k = L := by omega
    subst k
    have htop := hquotients L le_rfl
    rw [digitAt_top_eq_quotient p L x hp (by simpa [p] using hx),
      digitAt_top_eq_quotient p L y hp (by simpa [p] using hy),
      digitAt_top_eq_quotient p L z hp (by simpa [p] using hz)]
    exact htop

open Matrix

/-- Strict convexity of the integer square norm in the exact integral form
needed here.  Positive weighted barycentric equality plus one common norm
forces both endpoints to equal their target coordinatewise. -/
theorem integerSquareNorm_weighted_three_forces_eq
    {ι : Type*} [Fintype ι]
    (a b : ℕ) (x y z : ι → ℤ)
    (ha : 0 < a) (hb : 0 < b)
    (hrel : ∀ i, (a : ℤ) * x i + (b : ℤ) * y i =
      ((a + b : ℕ) : ℤ) * z i)
    (hxz : integerSquareNorm x = integerSquareNorm z)
    (hyz : integerSquareNorm y = integerSquareNorm z) :
    x = z ∧ y = z := by
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < b := by exact_mod_cast hb
  have hpoint (i : ι) :
      (a : ℤ) * (x i - z i) ^ 2 + (b : ℤ) * (y i - z i) ^ 2 =
        (a : ℤ) * x i ^ 2 + (b : ℤ) * y i ^ 2 -
          ((a + b : ℕ) : ℤ) * z i ^ 2 := by
    have hi := hrel i
    calc
      _ = (a : ℤ) * x i ^ 2 + (b : ℤ) * y i ^ 2 -
          2 * z i * ((a : ℤ) * x i + (b : ℤ) * y i) +
          ((a + b : ℕ) : ℤ) * z i ^ 2 := by
            push_cast
            ring
      _ = _ := by
            rw [hi]
            ring
  have hsum :
      ∑ i : ι, ((a : ℤ) * (x i - z i) ^ 2 +
        (b : ℤ) * (y i - z i) ^ 2) = 0 := by
    calc
      _ = ∑ i : ι, ((a : ℤ) * x i ^ 2 + (b : ℤ) * y i ^ 2 -
          ((a + b : ℕ) : ℤ) * z i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hpoint i
      _ = (a : ℤ) * integerSquareNorm x +
          (b : ℤ) * integerSquareNorm y -
          ((a + b : ℕ) : ℤ) * integerSquareNorm z := by
            unfold integerSquareNorm dotProduct
            simp only [pow_two]
            conv_lhs =>
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 0 := by
            rw [hxz, hyz]
            push_cast
            ring
  have hterm (i : ι) :
      (a : ℤ) * (x i - z i) ^ 2 +
        (b : ℤ) * (y i - z i) ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => by positivity)).mp hsum i (Finset.mem_univ i)
  constructor
  · funext i
    have hi := hterm i
    nlinarith [sq_nonneg (x i - z i), sq_nonneg (y i - z i)]
  · funext i
    have hi := hterm i
    nlinarith [sq_nonneg (x i - z i), sq_nonneg (y i - z i)]

/-- The lower-digit mod-24 labels with their finite range exposed. -/
def noThreeMod24ResidueVector (s L n : ℕ) : Fin L → Fin 24 :=
  fun i ↦ ⟨digitAt (noThreeMod24Base s) i n % 24,
    Nat.mod_lt _ (by norm_num)⟩

/-- The finite palette of the explicit no-three-equal factor. -/
abbrev NoThreeMod24Palette (s L : ℕ) :=
  (Fin L → Fin 24) ×
    Fin ((L + 1) * noThreeMod24Base s ^ 2 + 1)

/-- Mod-24 carry labels together with the full integer digit-square norm,
represented by its finite natural range. -/
def noThreeMod24Colour (s L n : ℕ) : NoThreeMod24Palette s L :=
  (noThreeMod24ResidueVector s L n,
    finiteDigitSquareColour (noThreeMod24Base s) L
      (noThreeMod24Base_pos s) n)

/-- On the complete base-power interval, a positive weighted relation of
weight sum at most three cannot be monochromatic unless all three naturals
are equal. -/
theorem noThreeMod24Colour_eq_forces_eq
    (s L a b x y z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 3)
    (hx : x < noThreeMod24Base s ^ (L + 1))
    (hy : y < noThreeMod24Base s ^ (L + 1))
    (hz : z < noThreeMod24Base s ^ (L + 1))
    (hrel : a * x + b * y = (a + b) * z)
    (hcolourXY : noThreeMod24Colour s L x =
      noThreeMod24Colour s L y)
    (hcolourYZ : noThreeMod24Colour s L y =
      noThreeMod24Colour s L z) :
    x = y ∧ y = z := by
  let p := noThreeMod24Base s
  have hp : 0 < p := by simpa [p] using noThreeMod24Base_pos s
  have hcarryXY := congrArg Prod.fst hcolourXY
  have hcarryYZ := congrArg Prod.fst hcolourYZ
  change noThreeMod24ResidueVector s L x =
    noThreeMod24ResidueVector s L y at hcarryXY
  change noThreeMod24ResidueVector s L y =
    noThreeMod24ResidueVector s L z at hcarryYZ
  have hxyDigits : ∀ k < L,
      digitAt p k x % 24 = digitAt p k y % 24 := by
    intro k hk
    let i : Fin L := ⟨k, hk⟩
    have hi := congrFun hcarryXY i
    have hval := congrArg Fin.val hi
    simpa [noThreeMod24ResidueVector, p, i] using hval
  have hyzDigits : ∀ k < L,
      digitAt p k y % 24 = digitAt p k z % 24 := by
    intro k hk
    let i : Fin L := ⟨k, hk⟩
    have hi := congrFun hcarryYZ i
    have hval := congrArg Fin.val hi
    simpa [noThreeMod24ResidueVector, p, i] using hval
  have hdigitRel := noThreeMod24_all_digits_weighted
    s L a b x y z ha hb hab hx hy hz hrel
      (by simpa [p] using hxyDigits) (by simpa [p] using hyzDigits)
  have hpointwise : ∀ i : Fin (L + 1),
      (a : ℤ) * integerDigitVector p L x i +
        (b : ℤ) * integerDigitVector p L y i =
          ((a + b : ℕ) : ℤ) * integerDigitVector p L z i := by
    intro i
    have hi := hdigitRel i (by omega)
    dsimp [integerDigitVector]
    simp only [p]
    exact_mod_cast hi
  have hsquareXY :=
    congrArg (fun c : NoThreeMod24Palette s L ↦ c.2.val) hcolourXY
  have hsquareYZ :=
    congrArg (fun c : NoThreeMod24Palette s L ↦ c.2.val) hcolourYZ
  change naturalDigitSquareColour p L x =
    naturalDigitSquareColour p L y at hsquareXY
  change naturalDigitSquareColour p L y =
    naturalDigitSquareColour p L z at hsquareYZ
  have hnormXY : integerSquareNorm (integerDigitVector p L x) =
      integerSquareNorm (integerDigitVector p L y) := by
    change digitSquareColour p L x = digitSquareColour p L y
    rw [← naturalDigitSquareColour_cast p L x,
      ← naturalDigitSquareColour_cast p L y]
    exact_mod_cast hsquareXY
  have hnormYZ : integerSquareNorm (integerDigitVector p L y) =
      integerSquareNorm (integerDigitVector p L z) := by
    change digitSquareColour p L y = digitSquareColour p L z
    rw [← naturalDigitSquareColour_cast p L y,
      ← naturalDigitSquareColour_cast p L z]
    exact_mod_cast hsquareYZ
  have hvectors := integerSquareNorm_weighted_three_forces_eq a b
    (integerDigitVector p L x) (integerDigitVector p L y)
    (integerDigitVector p L z) ha hb hpointwise
    (hnormXY.trans hnormYZ) hnormYZ
  have hxz : x = z := by
    apply eq_of_digitAt_eq_of_lt_pow p L x z hp
      (by simpa [p] using hx) (by simpa [p] using hz)
    intro k hk
    let i : Fin (L + 1) := ⟨k, by omega⟩
    have hi := congrFun hvectors.1 i
    change ((digitAt p k x : ℕ) : ℤ) =
      ((digitAt p k z : ℕ) : ℤ) at hi
    exact_mod_cast hi
  have hyz : y = z := by
    apply eq_of_digitAt_eq_of_lt_pow p L y z hp
      (by simpa [p] using hy) (by simpa [p] using hz)
    intro k hk
    let i : Fin (L + 1) := ⟨k, by omega⟩
    have hi := congrFun hvectors.2 i
    change ((digitAt p k y : ℕ) : ℤ) =
      ((digitAt p k z : ℕ) : ℤ) at hi
    exact_mod_cast hi
  exact ⟨hxz.trans hyz.symm, hyz⟩

/-- Bounded DTZ `4` patterns are not monochromatic under the explicit
finite-digit colouring. -/
theorem noThreeMod24Colour_bounded_pattern_not_monochromatic
    (s L a b x y z : ℕ)
    (hx : x < noThreeMod24Base s ^ (L + 1))
    (hy : y < noThreeMod24Base s ^ (L + 1))
    (hz : z < noThreeMod24Base s ^ (L + 1))
    (hpattern : DTZWeightedThreePointPattern 4 a b x y z) :
    ¬ MonochromaticTriple (noThreeMod24Colour s L) x y z := by
  rintro hmono
  rcases hpattern with ⟨ha, hb, hab, hrel, hnontrivial⟩
  have hab3 : a + b ≤ 3 := by omega
  exact hnontrivial <|
    noThreeMod24Colour_eq_forces_eq s L a b x y z
      ha hb hab3 hx hy hz hrel hmono.1 hmono.2

/-- The explicit finite-digit colouring rules out all four ways that three
positions of a nontrivial bounded integer four-term progression can have one
colour. -/
theorem noThreeMod24Colour_isNoThreeEqualColouring (s L : ℕ) :
    IsNoThreeEqualColouring
      (BoundedIntFourAP4 (noThreeMod24Base s ^ (L + 1)))
      (noThreeMod24Colour s L) := by
  intro x0 x1 x2 x3 hAP
  have hpatterns := boundedIntFourAP4_dtzPatterns
    (noThreeMod24Base s ^ (L + 1)) x0 x1 x2 x3 hAP
  rcases hpatterns with ⟨hp012, hp123, hp013, hp023⟩
  rcases hAP with ⟨hx0, hx1, hx2, hx3, _hfour, _hne⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h01, h12⟩
    exact noThreeMod24Colour_bounded_pattern_not_monochromatic
      s L 1 1 x0 x2 x1 hx0 hx2 hx1 hp012
      ⟨h01.trans h12, h12.symm⟩
  · rintro ⟨h01, h13⟩
    exact noThreeMod24Colour_bounded_pattern_not_monochromatic
      s L 2 1 x0 x3 x1 hx0 hx3 hx1 hp013
      ⟨h01.trans h13, h13.symm⟩
  · rintro ⟨h02, h23⟩
    exact noThreeMod24Colour_bounded_pattern_not_monochromatic
      s L 1 2 x0 x3 x2 hx0 hx3 hx2 hp023
      ⟨h02.trans h23, h23.symm⟩
  · rintro ⟨h12, h23⟩
    exact noThreeMod24Colour_bounded_pattern_not_monochromatic
      s L 1 1 x1 x3 x2 hx1 hx3 hx2 hp123
      ⟨h12.trans h23, h23.symm⟩

end ErdosProblems.E160
