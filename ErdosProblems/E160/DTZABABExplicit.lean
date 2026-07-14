import ErdosProblems.E160.AABBFilter

/-!
# An explicit mod-24 ABAB factor

This file specializes the digit construction behind Deng--Tidor--Zhao
Lemma 7.11 to the standard four-term `ABAB` pattern.  A base congruent to
`1` modulo `24` makes the digitwise mod-24 labels correct carries, while the
integer square norm rules out the resulting nontrivial vector progression.
-/

namespace ErdosProblems.E160

/-- Bases used by the explicit standard-ABAB construction. -/
def ababMod24Base (s : ℕ) : ℕ := 24 * s + 1

theorem ababMod24Base_pos (s : ℕ) : 0 < ababMod24Base s := by
  simp [ababMod24Base]

/-- The specialized wrap-correction step.  Congruent residue steps modulo a
base `24s+1`, together with the two `ABAB` congruences modulo `24`, force all
three signed representative steps to agree. -/
theorem ababMod24_noWrap
    (s r0 r1 r2 r3 : ℕ)
    (hr0 : r0 < ababMod24Base s) (hr1 : r1 < ababMod24Base s)
    (hr2 : r2 < ababMod24Base s) (hr3 : r3 < ababMod24Base s)
    (hcong01 : (ababMod24Base s : ℤ) ∣
      ((r1 : ℤ) - r0) - ((r2 : ℤ) - r1))
    (hcong23 : (ababMod24Base s : ℤ) ∣
      ((r3 : ℤ) - r2) - ((r2 : ℤ) - r1))
    (h02 : r0 % 24 = r2 % 24)
    (h13 : r1 % 24 = r3 % 24) :
    (r1 : ℤ) - r0 = (r2 : ℤ) - r1 ∧
      (r3 : ℤ) - r2 = (r2 : ℤ) - r1 := by
  have hpInt : (0 : ℤ) < ababMod24Base s := by
    exact_mod_cast ababMod24Base_pos s
  have hstep01 := eq_or_eq_add_or_eq_sub_of_dvd_sub
    (ababMod24Base s : ℤ)
    ((r1 : ℤ) - r0) ((r2 : ℤ) - r1) hpInt
    (by omega) (by omega) (by omega) (by omega) hcong01
  have hstep23 := eq_or_eq_add_or_eq_sub_of_dvd_sub
    (ababMod24Base s : ℤ)
    ((r3 : ℤ) - r2) ((r2 : ℤ) - r1) hpInt
    (by omega) (by omega) (by omega) (by omega) hcong23
  have h02mod : r0 ≡ r2 [MOD 24] := h02
  have h13mod : r1 ≡ r3 [MOD 24] := h13
  obtain ⟨z02, hz02⟩ := h02mod.dvd
  obtain ⟨z13, hz13⟩ := h13mod.dvd
  simp only [ababMod24Base] at hstep01 hstep23
  rcases hstep01 with hstep01 | hstep01 | hstep01 <;>
    rcases hstep23 with hstep23 | hstep23 | hstep23 <;>
    constructor <;> omega

/-- One mod-24 correction step exposes a digit progression and passes the
integer progression to the next base quotient. -/
theorem ababMod24_quotient_step
    (s q0 q1 q2 q3 : ℕ) (hAP : IntFourAP4 q0 q1 q2 q3)
    (h02 : (q0 % ababMod24Base s) % 24 =
      (q2 % ababMod24Base s) % 24)
    (h13 : (q1 % ababMod24Base s) % 24 =
      (q3 % ababMod24Base s) % 24) :
    IntFourAP4
        (q0 % ababMod24Base s) (q1 % ababMod24Base s)
        (q2 % ababMod24Base s) (q3 % ababMod24Base s) ∧
      IntFourAP4
        (q0 / ababMod24Base s) (q1 / ababMod24Base s)
        (q2 / ababMod24Base s) (q3 / ababMod24Base s) := by
  let p := ababMod24Base s
  have hp : 0 < p := by simpa [p] using ababMod24Base_pos s
  rcases hAP with ⟨hstep01, hstep23⟩
  have hdecomp (q : ℕ) : (q : ℤ) =
      (q % p : ℕ) + (p : ℤ) * (q / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div q p).symm
  have hcong01 : (p : ℤ) ∣
      (((q1 % p : ℕ) : ℤ) - (q0 % p : ℕ)) -
        (((q2 % p : ℕ) : ℤ) - (q1 % p : ℕ)) := by
    exact residue_steps_congruent_of_decomposition (p : ℤ)
      (q0 : ℤ) (q1 : ℤ) (q2 : ℤ)
      (q0 / p : ℕ) (q1 / p : ℕ) (q2 / p : ℕ)
      (q0 % p : ℕ) (q1 % p : ℕ) (q2 % p : ℕ)
      (hdecomp q0) (hdecomp q1) (hdecomp q2) hstep01
  have hcong23' : (p : ℤ) ∣
      (((q2 % p : ℕ) : ℤ) - (q1 % p : ℕ)) -
        (((q3 % p : ℕ) : ℤ) - (q2 % p : ℕ)) := by
    exact residue_steps_congruent_of_decomposition (p : ℤ)
      (q1 : ℤ) (q2 : ℤ) (q3 : ℤ)
      (q1 / p : ℕ) (q2 / p : ℕ) (q3 / p : ℕ)
      (q1 % p : ℕ) (q2 % p : ℕ) (q3 % p : ℕ)
      (hdecomp q1) (hdecomp q2) (hdecomp q3) hstep23.symm
  have hcong23 : (p : ℤ) ∣
      (((q3 % p : ℕ) : ℤ) - (q2 % p : ℕ)) -
        (((q2 % p : ℕ) : ℤ) - (q1 % p : ℕ)) := by
    obtain ⟨c, hc⟩ := hcong23'
    refine ⟨-c, ?_⟩
    linear_combination -hc
  have hdigit := ababMod24_noWrap s
    (q0 % p) (q1 % p) (q2 % p) (q3 % p)
    (Nat.mod_lt q0 hp) (Nat.mod_lt q1 hp)
    (Nat.mod_lt q2 hp) (Nat.mod_lt q3 hp)
    (by simpa [p] using hcong01) (by simpa [p] using hcong23)
    (by simpa [p] using h02) (by simpa [p] using h13)
  have hpInt : (p : ℤ) ≠ 0 := by omega
  have hquotient01 : ((q1 / p : ℕ) : ℤ) - (q0 / p : ℕ) =
      ((q2 / p : ℕ) : ℤ) - (q1 / p : ℕ) := by
    exact quotient_step_eq_of_residue_step_eq (p : ℤ)
      (q0 : ℤ) (q1 : ℤ) (q2 : ℤ)
      (q0 / p : ℕ) (q1 / p : ℕ) (q2 / p : ℕ)
      (q0 % p : ℕ) (q1 % p : ℕ) (q2 % p : ℕ)
      hpInt (hdecomp q0) (hdecomp q1) (hdecomp q2) hstep01 hdigit.1
  have hquotient23' : ((q2 / p : ℕ) : ℤ) - (q1 / p : ℕ) =
      ((q3 / p : ℕ) : ℤ) - (q2 / p : ℕ) := by
    exact quotient_step_eq_of_residue_step_eq (p : ℤ)
      (q1 : ℤ) (q2 : ℤ) (q3 : ℤ)
      (q1 / p : ℕ) (q2 / p : ℕ) (q3 / p : ℕ)
      (q1 % p : ℕ) (q2 % p : ℕ) (q3 % p : ℕ)
      hpInt (hdecomp q1) (hdecomp q2) (hdecomp q3)
      hstep23.symm hdigit.2.symm
  simpa only [p] using
    (show IntFourAP4 (q0 % p) (q1 % p) (q2 % p) (q3 % p) ∧
        IntFourAP4 (q0 / p) (q1 / p) (q2 / p) (q3 / p) from
      ⟨hdigit, hquotient01, hquotient23'.symm⟩)

/-- Iterating the mod-24 shield through the lower `L` digits exposes an
integer progression in each digit and preserves all quotient progressions. -/
theorem ababMod24_quotient_induction
    (s L n0 n1 n2 n3 : ℕ) (hAP : IntFourAP4 n0 n1 n2 n3)
    (h02 : ∀ k < L,
      digitAt (ababMod24Base s) k n0 % 24 =
        digitAt (ababMod24Base s) k n2 % 24)
    (h13 : ∀ k < L,
      digitAt (ababMod24Base s) k n1 % 24 =
        digitAt (ababMod24Base s) k n3 % 24) :
    (∀ k ≤ L, IntFourAP4
      (quotientAt (ababMod24Base s) k n0)
      (quotientAt (ababMod24Base s) k n1)
      (quotientAt (ababMod24Base s) k n2)
      (quotientAt (ababMod24Base s) k n3)) ∧
    (∀ k < L, IntFourAP4
      (digitAt (ababMod24Base s) k n0)
      (digitAt (ababMod24Base s) k n1)
      (digitAt (ababMod24Base s) k n2)
      (digitAt (ababMod24Base s) k n3)) := by
  let p := ababMod24Base s
  have hquotients : ∀ k ≤ L, IntFourAP4
      (quotientAt p k n0) (quotientAt p k n1)
      (quotientAt p k n2) (quotientAt p k n3) := by
    intro k hk
    induction k with
    | zero => simpa [quotientAt] using hAP
    | succ k ih =>
        have hkL : k < L := by omega
        have hprev := ih (by omega)
        have hstep := ababMod24_quotient_step s
          (quotientAt p k n0) (quotientAt p k n1)
          (quotientAt p k n2) (quotientAt p k n3) hprev
          (by simpa [p, digitAt] using h02 k hkL)
          (by simpa [p, digitAt] using h13 k hkL)
        simpa [p, quotientAt_succ] using hstep.2
  refine ⟨by simpa [p] using hquotients, ?_⟩
  intro k hk
  have hstep := ababMod24_quotient_step s
    (quotientAt p k n0) (quotientAt p k n1)
    (quotientAt p k n2) (quotientAt p k n3)
    (hquotients k hk.le)
    (by simpa [p, digitAt] using h02 k hk)
    (by simpa [p, digitAt] using h13 k hk)
  simpa [p, digitAt] using hstep.1

/-- The quotient induction plus the top-digit bound exposes the complete
base-digit vector as an integer four-term progression. -/
theorem ababMod24_all_digits_fourAP
    (s L n0 n1 n2 n3 : ℕ)
    (hn0 : n0 < ababMod24Base s ^ (L + 1))
    (hn1 : n1 < ababMod24Base s ^ (L + 1))
    (hn2 : n2 < ababMod24Base s ^ (L + 1))
    (hn3 : n3 < ababMod24Base s ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3)
    (h02 : ∀ k < L,
      digitAt (ababMod24Base s) k n0 % 24 =
        digitAt (ababMod24Base s) k n2 % 24)
    (h13 : ∀ k < L,
      digitAt (ababMod24Base s) k n1 % 24 =
        digitAt (ababMod24Base s) k n3 % 24) :
    ∀ k ≤ L, IntFourAP4
      (digitAt (ababMod24Base s) k n0)
      (digitAt (ababMod24Base s) k n1)
      (digitAt (ababMod24Base s) k n2)
      (digitAt (ababMod24Base s) k n3) := by
  let p := ababMod24Base s
  have hp : 0 < p := by simpa [p] using ababMod24Base_pos s
  obtain ⟨hquotients, hdigits⟩ :=
    ababMod24_quotient_induction s L n0 n1 n2 n3 hAP h02 h13
  intro k hk
  by_cases hkL : k < L
  · exact hdigits k hkL
  · have hkeq : k = L := by omega
    subst k
    have htop := hquotients L le_rfl
    rw [digitAt_top_eq_quotient p L n0 hp (by simpa [p] using hn0),
      digitAt_top_eq_quotient p L n1 hp (by simpa [p] using hn1),
      digitAt_top_eq_quotient p L n2 hp (by simpa [p] using hn2),
      digitAt_top_eq_quotient p L n3 hp (by simpa [p] using hn3)]
    exact htop

/-- Equal mod-24 carry labels on the `ABAB` pairs turn a bounded integer
progression into a nontrivial affine progression of full digit vectors. -/
theorem ababMod24_digitVector_affine
    (s L n0 n1 n2 n3 : ℕ)
    (hn0 : n0 < ababMod24Base s ^ (L + 1))
    (hn1 : n1 < ababMod24Base s ^ (L + 1))
    (hn2 : n2 < ababMod24Base s ^ (L + 1))
    (hn3 : n3 < ababMod24Base s ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3) (hnontrivial : n1 ≠ n0)
    (h02 : ∀ k < L,
      digitAt (ababMod24Base s) k n0 % 24 =
        digitAt (ababMod24Base s) k n2 % 24)
    (h13 : ∀ k < L,
      digitAt (ababMod24Base s) k n1 % 24 =
        digitAt (ababMod24Base s) k n3 % 24) :
    ∃ x h : Fin (L + 1) → ℤ, h ≠ 0 ∧
      integerDigitVector (ababMod24Base s) L n0 = x ∧
      integerDigitVector (ababMod24Base s) L n1 = x + h ∧
      integerDigitVector (ababMod24Base s) L n2 = x + (2 : ℤ) • h ∧
      integerDigitVector (ababMod24Base s) L n3 = x + (3 : ℤ) • h := by
  let p := ababMod24Base s
  have hp : 0 < p := by simpa [p] using ababMod24Base_pos s
  have hdigits := ababMod24_all_digits_fourAP s L n0 n1 n2 n3
    hn0 hn1 hn2 hn3 hAP h02 h13
  let x : Fin (L + 1) → ℤ := integerDigitVector p L n0
  let h : Fin (L + 1) → ℤ :=
    integerDigitVector p L n1 - integerDigitVector p L n0
  have hh : h ≠ 0 := by
    intro hz
    have hvec : integerDigitVector p L n1 =
        integerDigitVector p L n0 := by
      apply sub_eq_zero.mp
      exact hz
    apply hnontrivial
    apply eq_of_digitAt_eq_of_lt_pow p L n1 n0 hp
      (by simpa [p] using hn1) (by simpa [p] using hn0)
    intro k hk
    let i : Fin (L + 1) := ⟨k, by omega⟩
    have hi := congrFun hvec i
    change ((digitAt p k n1 : ℕ) : ℤ) = digitAt p k n0 at hi
    exact_mod_cast hi
  refine ⟨x, h, hh, by simp [x, p], ?_, ?_, ?_⟩
  · simp [x, h, p]
  · funext i
    have hi := (hdigits i (by omega)).1
    dsimp [x, h, integerDigitVector]
    simp only [p]
    omega
  · funext i
    rcases hdigits i (by omega) with ⟨hi1, hi2⟩
    dsimp [x, h, integerDigitVector]
    simp only [p]
    omega

/-- The two `ABAB` square-norm equalities force an integer vector step to
vanish. -/
theorem integerSquareNorm_abab_forces_step_zero
    {ι : Type*} [Fintype ι] (x h : ι → ℤ)
    (h02 : integerSquareNorm x =
      integerSquareNorm (x + (2 : ℤ) • h))
    (h13 : integerSquareNorm (x + h) =
      integerSquareNorm (x + (3 : ℤ) • h)) :
    h = 0 := by
  have h02' := h02
  have h13' := h13
  rw [integerSquareNorm_line x h 2] at h02'
  rw [show x + h = x + (1 : ℤ) • h by ext i; simp,
    integerSquareNorm_line x h 1,
    integerSquareNorm_line x h 3] at h13'
  have hnorm : integerSquareNorm h = 0 := by
    norm_num at h02' h13'
    omega
  apply dotProduct_self_eq_zero.mp
  simpa [integerSquareNorm] using hnorm

/-- The integer square norm forbids `ABAB` on every nontrivial affine
four-term progression of digit vectors. -/
theorem integerSquareNorm_abab_free
    {ι : Type*} [Fintype ι] (x h : ι → ℤ) (hh : h ≠ 0) :
    integerSquareNorm x ≠
        integerSquareNorm (x + (2 : ℤ) • h) ∨
      integerSquareNorm (x + h) ≠
        integerSquareNorm (x + (3 : ℤ) • h) := by
  by_cases h02 : integerSquareNorm x =
      integerSquareNorm (x + (2 : ℤ) • h)
  · by_cases h13 : integerSquareNorm (x + h) =
        integerSquareNorm (x + (3 : ℤ) • h)
    · exact (hh (integerSquareNorm_abab_forces_step_zero x h h02 h13)).elim
    · exact Or.inr h13
  · exact Or.inl h02

/-- Mod-24 labels on all carry-bearing lower digits. -/
def ababMod24CarryVector (s L n : ℕ) : Fin L → Fin 24 :=
  fun i ↦ Fin.ofNat 24 (digitAt (ababMod24Base s) i n)

/-- The raw explicit `ABAB` colour: carry data and the full integer square
norm. -/
def ababMod24Colour (s L n : ℕ) : (Fin L → Fin 24) × ℤ :=
  (ababMod24CarryVector s L n,
    integerSquareNorm (integerDigitVector (ababMod24Base s) L n))

/-- The raw mod-24/square colouring eliminates `ABAB` on the complete
base-power interval. -/
theorem ababMod24Colour_abab_free
    (s L n0 n1 n2 n3 : ℕ)
    (hn0 : n0 < ababMod24Base s ^ (L + 1))
    (hn1 : n1 < ababMod24Base s ^ (L + 1))
    (hn2 : n2 < ababMod24Base s ^ (L + 1))
    (hn3 : n3 < ababMod24Base s ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3) (hnontrivial : n1 ≠ n0) :
    ababMod24Colour s L n0 ≠ ababMod24Colour s L n2 ∨
      ababMod24Colour s L n1 ≠ ababMod24Colour s L n3 := by
  by_cases h02 : ababMod24Colour s L n0 = ababMod24Colour s L n2
  · by_cases h13 : ababMod24Colour s L n1 = ababMod24Colour s L n3
    · have hshield02 := congrArg Prod.fst h02
      have hshield13 := congrArg Prod.fst h13
      have hcarry02 : ∀ k < L,
          digitAt (ababMod24Base s) k n0 % 24 =
            digitAt (ababMod24Base s) k n2 % 24 := by
        intro k hk
        let i : Fin L := ⟨k, hk⟩
        have hi := congrFun hshield02 i
        exact congrArg Fin.val hi
      have hcarry13 : ∀ k < L,
          digitAt (ababMod24Base s) k n1 % 24 =
            digitAt (ababMod24Base s) k n3 % 24 := by
        intro k hk
        let i : Fin L := ⟨k, hk⟩
        have hi := congrFun hshield13 i
        exact congrArg Fin.val hi
      obtain ⟨x, h, hh, hx0, hx1, hx2, hx3⟩ :=
        ababMod24_digitVector_affine s L n0 n1 n2 n3
          hn0 hn1 hn2 hn3 hAP hnontrivial hcarry02 hcarry13
      have hsquare02 := congrArg Prod.snd h02
      have hsquare13 := congrArg Prod.snd h13
      change integerSquareNorm (integerDigitVector (ababMod24Base s) L n0) =
        integerSquareNorm (integerDigitVector (ababMod24Base s) L n2)
        at hsquare02
      change integerSquareNorm (integerDigitVector (ababMod24Base s) L n1) =
        integerSquareNorm (integerDigitVector (ababMod24Base s) L n3)
        at hsquare13
      rw [hx0, hx2] at hsquare02
      rw [hx1, hx3] at hsquare13
      exact (hh (integerSquareNorm_abab_forces_step_zero
        x h hsquare02 hsquare13)).elim
    · exact Or.inr h13
  · exact Or.inl h02

/-- A finite palette for the explicit mod-24 `ABAB` factor. -/
abbrev ABABMod24Palette (s L : ℕ) :=
  (Fin L → Fin 24) ×
    Fin ((L + 1) * ababMod24Base s ^ 2 + 1)

/-- Finite-codomain form of the mod-24/square colouring. -/
def finiteABABMod24Colour (s L n : ℕ) : ABABMod24Palette s L :=
  (ababMod24CarryVector s L n,
    finiteDigitSquareColour (ababMod24Base s) L
      (ababMod24Base_pos s) n)

/-- Forget the finite range witnesses and recover the raw arithmetic colour. -/
def forgetABABMod24Palette (s L : ℕ) :
    ABABMod24Palette s L → (Fin L → Fin 24) × ℤ :=
  fun c ↦ (c.1, (c.2.val : ℤ))

theorem forget_finiteABABMod24Colour (s L n : ℕ) :
    forgetABABMod24Palette s L (finiteABABMod24Colour s L n) =
      ababMod24Colour s L n := by
  apply Prod.ext
  · rfl
  · simpa [finiteABABMod24Colour, forgetABABMod24Palette,
      ababMod24Colour, digitSquareColour] using
      naturalDigitSquareColour_cast (ababMod24Base s) L n

/-- Exact finite-palette core: on `[0,(24s+1)^(L+1))`, every nontrivial
integer four-term progression violates at least one of the two `ABAB` colour
equalities. -/
theorem finiteABABMod24Colour_abab_free
    (s L n0 n1 n2 n3 : ℕ)
    (hn0 : n0 < ababMod24Base s ^ (L + 1))
    (hn1 : n1 < ababMod24Base s ^ (L + 1))
    (hn2 : n2 < ababMod24Base s ^ (L + 1))
    (hn3 : n3 < ababMod24Base s ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3) (hnontrivial : n1 ≠ n0) :
    finiteABABMod24Colour s L n0 ≠ finiteABABMod24Colour s L n2 ∨
      finiteABABMod24Colour s L n1 ≠ finiteABABMod24Colour s L n3 := by
  rcases ababMod24Colour_abab_free s L n0 n1 n2 n3
      hn0 hn1 hn2 hn3 hAP hnontrivial with h02 | h13
  · left
    intro h
    apply h02
    have := congrArg (forgetABABMod24Palette s L) h
    simpa only [forget_finiteABABMod24Colour] using this
  · right
    intro h
    apply h13
    have := congrArg (forgetABABMod24Palette s L) h
    simpa only [forget_finiteABABMod24Colour] using this

/-- Exact number of available values in the explicit finite palette. -/
theorem ababMod24Palette_card (s L : ℕ) :
    Fintype.card (ABABMod24Palette s L) =
      24 ^ L * ((L + 1) * ababMod24Base s ^ 2 + 1) := by
  simp [ABABMod24Palette]

end ErdosProblems.E160
