import ErdosProblems.E160.ThirdsCarryShield

/-!
# A dyadic carry shield for the adjacent-pair AABB pattern

Equal dyadic buckets on the first adjacent pair and the last adjacent pair
force a cyclic digit progression to have no carry, yielding an AABB-free
factor.
-/

namespace ErdosProblems.E160

/-- The dyadic scale of `r+1`.  Its fibres are the intervals
`[2^k-1, 2^(k+1)-2]`. -/
def dyadicBucket (r : ℕ) : ℕ := Nat.log 2 (r + 1)

/-- Two numbers in one dyadic bucket differ by a factor strictly less than
two after shifting by one. -/
theorem dyadicBucket_eq_closeness (x y : ℕ)
    (h : dyadicBucket x = dyadicBucket y) :
    y + 1 < 2 * (x + 1) ∧ x + 1 < 2 * (y + 1) := by
  have hxLower : 2 ^ Nat.log 2 (x + 1) ≤ x + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hyLower : 2 ^ Nat.log 2 (y + 1) ≤ y + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hxUpper : x + 1 < 2 ^ (Nat.log 2 (x + 1)).succ :=
    Nat.lt_pow_succ_log_self (by omega) (x + 1)
  have hyUpper : y + 1 < 2 ^ (Nat.log 2 (y + 1)).succ :=
    Nat.lt_pow_succ_log_self (by omega) (y + 1)
  change Nat.log 2 (x + 1) = Nat.log 2 (y + 1) at h
  constructor
  · calc
      y + 1 < 2 ^ (Nat.log 2 (y + 1)).succ := hyUpper
      _ = 2 * 2 ^ Nat.log 2 (x + 1) := by rw [← h]; simp [pow_succ, mul_comm]
      _ ≤ 2 * (x + 1) := Nat.mul_le_mul_left 2 hxLower
  · calc
      x + 1 < 2 ^ (Nat.log 2 (x + 1)).succ := hxUpper
      _ = 2 * 2 ^ Nat.log 2 (y + 1) := by rw [h]; simp [pow_succ, mul_comm]
      _ ≤ 2 * (y + 1) := Nat.mul_le_mul_left 2 hyLower

/-- A genuine one-digit no-carry lemma for the AABB equality pattern.
Congruent residue steps together with equal adjacent dyadic buckets force all
three representative steps to be equal in `ℤ`. -/
theorem dyadicBucket_noWrap (p r0 r1 r2 r3 : ℕ)
    (hp : 0 < p)
    (hr0 : r0 < p) (hr1 : r1 < p) (hr2 : r2 < p) (hr3 : r3 < p)
    (hcong01 : (p : ℤ) ∣
      ((r1 : ℤ) - r0) - ((r2 : ℤ) - r1))
    (hcong23 : (p : ℤ) ∣
      ((r3 : ℤ) - r2) - ((r2 : ℤ) - r1))
    (hpair01 : dyadicBucket r0 = dyadicBucket r1)
    (hpair23 : dyadicBucket r2 = dyadicBucket r3) :
    (r1 : ℤ) - r0 = (r2 : ℤ) - r1 ∧
      (r3 : ℤ) - r2 = (r2 : ℤ) - r1 := by
  have hpInt : (0 : ℤ) < p := by exact_mod_cast hp
  have h01 := eq_or_eq_add_or_eq_sub_of_dvd_sub (p : ℤ)
    ((r1 : ℤ) - r0) ((r2 : ℤ) - r1) hpInt
    (by omega) (by omega) (by omega) (by omega) hcong01
  have h23 := eq_or_eq_add_or_eq_sub_of_dvd_sub (p : ℤ)
    ((r3 : ℤ) - r2) ((r2 : ℤ) - r1) hpInt
    (by omega) (by omega) (by omega) (by omega) hcong23
  have hc01 := dyadicBucket_eq_closeness r0 r1 hpair01
  have hc23 := dyadicBucket_eq_closeness r2 r3 hpair23
  rcases h01 with h01 | h01 | h01 <;>
    rcases h23 with h23 | h23 | h23 <;> omega

/-- The quotient after removing `k` base-`p` digits. -/
def quotientAt (p k n : ℕ) : ℕ := n / p ^ k

/-- The `k`-th base-`p` digit. -/
def digitAt (p k n : ℕ) : ℕ := quotientAt p k n % p

/-- Four naturals form a four-term progression when their signed consecutive
differences agree. -/
def IntFourAP4 (a0 a1 a2 a3 : ℕ) : Prop :=
  ((a1 : ℤ) - a0 = (a2 : ℤ) - a1) ∧
    ((a3 : ℤ) - a2 = (a2 : ℤ) - a1)

theorem quotientAt_succ (p k n : ℕ) :
    quotientAt p (k + 1) n = quotientAt p k n / p := by
  simp [quotientAt, pow_succ, Nat.div_div_eq_div_mul]

theorem quotientAt_div (p k n : ℕ) :
    quotientAt p k (n / p) = quotientAt p (k + 1) n := by
  simp [quotientAt, Nat.div_div_eq_div_mul, pow_succ, mul_comm]

theorem digitAt_div (p k n : ℕ) :
    digitAt p k (n / p) = digitAt p (k + 1) n := by
  simp only [digitAt, quotientAt_div]

/-- Below `p^(L+1)`, the quotient after `L` digits is itself a valid top
digit. -/
theorem quotientAt_lt_base (p L n : ℕ) (hp : 0 < p)
    (hn : n < p ^ (L + 1)) : quotientAt p L n < p := by
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos hp)).2
  simpa [quotientAt, pow_succ, mul_comm] using hn

theorem digitAt_top_eq_quotient (p L n : ℕ) (hp : 0 < p)
    (hn : n < p ^ (L + 1)) :
    digitAt p L n = quotientAt p L n := by
  exact Nat.mod_eq_of_lt (quotientAt_lt_base p L n hp hn)

/-- Fixed-length canonical base digits are injective on `[0,p^(L+1))`. -/
theorem eq_of_digitAt_eq_of_lt_pow (p L n m : ℕ)
    (hp : 0 < p) (hn : n < p ^ (L + 1)) (hm : m < p ^ (L + 1))
    (hdigits : ∀ k ≤ L, digitAt p k n = digitAt p k m) :
    n = m := by
  induction L generalizing n m with
  | zero =>
      have hn' : n < p := by simpa using hn
      have hm' : m < p := by simpa using hm
      have h0 := hdigits 0 (by omega)
      simpa [digitAt, quotientAt, Nat.mod_eq_of_lt hn',
        Nat.mod_eq_of_lt hm'] using h0
  | succ L ih =>
      have hpPow : 0 < p ^ (L + 1) := Nat.pow_pos hp
      have hnDiv : n / p < p ^ (L + 1) := by
        apply (Nat.div_lt_iff_lt_mul hp).2
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hn
      have hmDiv : m / p < p ^ (L + 1) := by
        apply (Nat.div_lt_iff_lt_mul hp).2
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hm
      have hdiv : n / p = m / p := by
        apply ih (n / p) (m / p) hnDiv hmDiv
        intro k hk
        rw [digitAt_div, digitAt_div]
        exact hdigits (k + 1) (by omega)
      have hmod : n % p = m % p := by
        have h0 := hdigits 0 (by omega)
        simpa [digitAt, quotientAt] using h0
      calc
        n = n % p + p * (n / p) := (Nat.mod_add_div n p).symm
        _ = m % p + p * (m / p) := by rw [hmod, hdiv]
        _ = m := Nat.mod_add_div m p

/-- One dyadic no-wrap step simultaneously exposes a digit progression and
passes the progression to the next quotient. -/
theorem dyadicBucket_quotient_step (p q0 q1 q2 q3 : ℕ)
    (hp : 0 < p) (hAP : IntFourAP4 q0 q1 q2 q3)
    (hpair01 : dyadicBucket (q0 % p) = dyadicBucket (q1 % p))
    (hpair23 : dyadicBucket (q2 % p) = dyadicBucket (q3 % p)) :
    IntFourAP4 (q0 % p) (q1 % p) (q2 % p) (q3 % p) ∧
      IntFourAP4 (q0 / p) (q1 / p) (q2 / p) (q3 / p) := by
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
  have hdigit := dyadicBucket_noWrap p
    (q0 % p) (q1 % p) (q2 % p) (q3 % p) hp
    (Nat.mod_lt q0 hp) (Nat.mod_lt q1 hp)
    (Nat.mod_lt q2 hp) (Nat.mod_lt q3 hp)
    hcong01 hcong23 hpair01 hpair23
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
  exact ⟨hdigit, hquotient01, hquotient23'.symm⟩

/-- Iterating the dyadic shield through `L` lower digits exposes every digit
progression and preserves a progression in every quotient. -/
theorem dyadicBucket_quotient_induction
    (p L n0 n1 n2 n3 : ℕ)
    (hp : 0 < p) (hAP : IntFourAP4 n0 n1 n2 n3)
    (h01 : ∀ k < L,
      dyadicBucket (digitAt p k n0) = dyadicBucket (digitAt p k n1))
    (h23 : ∀ k < L,
      dyadicBucket (digitAt p k n2) = dyadicBucket (digitAt p k n3)) :
    (∀ k ≤ L, IntFourAP4
      (quotientAt p k n0) (quotientAt p k n1)
      (quotientAt p k n2) (quotientAt p k n3)) ∧
    (∀ k < L, IntFourAP4
      (digitAt p k n0) (digitAt p k n1)
      (digitAt p k n2) (digitAt p k n3)) := by
  have hquotients : ∀ k ≤ L, IntFourAP4
      (quotientAt p k n0) (quotientAt p k n1)
      (quotientAt p k n2) (quotientAt p k n3) := by
    intro k hk
    induction k with
    | zero => simpa [quotientAt] using hAP
    | succ k ih =>
        have hkL : k < L := by omega
        have hprev := ih (by omega)
        have hstep := dyadicBucket_quotient_step p
          (quotientAt p k n0) (quotientAt p k n1)
          (quotientAt p k n2) (quotientAt p k n3) hp hprev
          (h01 k hkL) (h23 k hkL)
        simpa [quotientAt_succ] using hstep.2
  refine ⟨hquotients, ?_⟩
  intro k hk
  have hstep := dyadicBucket_quotient_step p
    (quotientAt p k n0) (quotientAt p k n1)
    (quotientAt p k n2) (quotientAt p k n3) hp
    (hquotients k hk.le) (h01 k hk) (h23 k hk)
  simpa [digitAt] using hstep.1

/-- The fixed-length signed digit vector, including the top digit. -/
def integerDigitVector (p L n : ℕ) : Fin (L + 1) → ℤ :=
  fun i ↦ (digitAt p i n : ℕ)

/-- The quotient induction plus the top-digit bound exposes a progression in
every digit coordinate. -/
theorem dyadicBucket_all_digits_fourAP
    (p L n0 n1 n2 n3 : ℕ) (hp : 0 < p)
    (hn0 : n0 < p ^ (L + 1)) (hn1 : n1 < p ^ (L + 1))
    (hn2 : n2 < p ^ (L + 1)) (hn3 : n3 < p ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3)
    (h01 : ∀ k < L,
      dyadicBucket (digitAt p k n0) = dyadicBucket (digitAt p k n1))
    (h23 : ∀ k < L,
      dyadicBucket (digitAt p k n2) = dyadicBucket (digitAt p k n3)) :
    ∀ k ≤ L, IntFourAP4
      (digitAt p k n0) (digitAt p k n1)
      (digitAt p k n2) (digitAt p k n3) := by
  obtain ⟨hquotients, hdigits⟩ :=
    dyadicBucket_quotient_induction p L n0 n1 n2 n3 hp hAP h01 h23
  intro k hk
  by_cases hkL : k < L
  · exact hdigits k hkL
  · have hkeq : k = L := by omega
    subst k
    have htop := hquotients L le_rfl
    rw [digitAt_top_eq_quotient p L n0 hp hn0,
      digitAt_top_eq_quotient p L n1 hp hn1,
      digitAt_top_eq_quotient p L n2 hp hn2,
      digitAt_top_eq_quotient p L n3 hp hn3]
    exact htop

/-- Equal adjacent dyadic shields turn a bounded integer progression into a
nontrivial affine progression of its full digit vectors. -/
theorem dyadicBucket_digitVector_affine
    (p L n0 n1 n2 n3 : ℕ) (hp : 0 < p)
    (hn0 : n0 < p ^ (L + 1)) (hn1 : n1 < p ^ (L + 1))
    (hn2 : n2 < p ^ (L + 1)) (hn3 : n3 < p ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3) (hnontrivial : n1 ≠ n0)
    (h01 : ∀ k < L,
      dyadicBucket (digitAt p k n0) = dyadicBucket (digitAt p k n1))
    (h23 : ∀ k < L,
      dyadicBucket (digitAt p k n2) = dyadicBucket (digitAt p k n3)) :
    ∃ x h : Fin (L + 1) → ℤ, h ≠ 0 ∧
      integerDigitVector p L n0 = x ∧
      integerDigitVector p L n1 = x + h ∧
      integerDigitVector p L n2 = x + (2 : ℤ) • h ∧
      integerDigitVector p L n3 = x + (3 : ℤ) • h := by
  have hdigits := dyadicBucket_all_digits_fourAP p L n0 n1 n2 n3 hp
    hn0 hn1 hn2 hn3 hAP h01 h23
  let x : Fin (L + 1) → ℤ := integerDigitVector p L n0
  let h : Fin (L + 1) → ℤ :=
    integerDigitVector p L n1 - integerDigitVector p L n0
  have hh : h ≠ 0 := by
    intro hz
    have hvec : integerDigitVector p L n1 = integerDigitVector p L n0 := by
      apply sub_eq_zero.mp
      exact hz
    apply hnontrivial
    apply eq_of_digitAt_eq_of_lt_pow p L n1 n0 hp hn1 hn0
    intro k hk
    let i : Fin (L + 1) := ⟨k, by omega⟩
    have hi := congrFun hvec i
    change ((digitAt p k n1 : ℕ) : ℤ) = (digitAt p k n0 : ℕ) at hi
    exact_mod_cast hi
  refine ⟨x, h, hh, rfl, ?_, ?_, ?_⟩
  · simp [x, h]
  · funext i
    have hi := (hdigits i (by omega)).1
    dsimp [x, h, integerDigitVector]
    omega
  · funext i
    rcases hdigits i (by omega) with ⟨hi1, hi2⟩
    dsimp [x, h, integerDigitVector]
    omega

open Matrix

/-- The integer square norm of a finite digit vector. -/
def integerSquareNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) : ℤ :=
  v ⬝ᵥ v

/-- Exact quadratic expansion of the square norm along an integer affine
line. -/
theorem integerSquareNorm_line {ι : Type*} [Fintype ι]
    (x h : ι → ℤ) (t : ℤ) :
    integerSquareNorm (x + t • h) =
      integerSquareNorm x + 2 * t * (x ⬝ᵥ h) + t ^ 2 * integerSquareNorm h := by
  simp only [integerSquareNorm, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul]
  rw [dotProduct_comm h x]
  simp only [smul_eq_mul]
  ring

/-- Two adjacent-pair square-norm equalities force the vector step to vanish. -/
theorem integerSquareNorm_aabb_forces_step_zero
    {ι : Type*} [Fintype ι] (x h : ι → ℤ)
    (hfirst : integerSquareNorm x = integerSquareNorm (x + h))
    (hsecond : integerSquareNorm (x + (2 : ℤ) • h) =
      integerSquareNorm (x + (3 : ℤ) • h)) :
    h = 0 := by
  have hfirst' := hfirst
  have hsecond' := hsecond
  rw [show x + h = x + (1 : ℤ) • h by ext i; simp] at hfirst'
  rw [integerSquareNorm_line x h 1] at hfirst'
  rw [integerSquareNorm_line x h 2,
    integerSquareNorm_line x h 3] at hsecond'
  have hnorm : integerSquareNorm h = 0 := by
    norm_num at hfirst' hsecond'
    omega
  apply dotProduct_self_eq_zero.mp
  simpa [integerSquareNorm] using hnorm

/-- The square norm forbids the adjacent-pair AABB equality pattern on every
nontrivial integer vector four-term progression. -/
theorem integerSquareNorm_aabb_free {ι : Type*} [Fintype ι]
    (x h : ι → ℤ) (hh : h ≠ 0) :
    integerSquareNorm x ≠ integerSquareNorm (x + h) ∨
      integerSquareNorm (x + (2 : ℤ) • h) ≠
        integerSquareNorm (x + (3 : ℤ) • h) := by
  by_cases hfirst : integerSquareNorm x = integerSquareNorm (x + h)
  · by_cases hsecond : integerSquareNorm (x + (2 : ℤ) • h) =
        integerSquareNorm (x + (3 : ℤ) • h)
    · exact (hh (integerSquareNorm_aabb_forces_step_zero x h
        hfirst hsecond)).elim
    · exact Or.inr hsecond
  · exact Or.inl hfirst

/-- Dyadic buckets on all carry-bearing digits. -/
def dyadicCarryVector (p L n : ℕ) : Fin L → ℕ :=
  fun i ↦ dyadicBucket (digitAt p i n)

/-- The exact digit-square coordinate. -/
def digitSquareColour (p L n : ℕ) : ℤ :=
  integerSquareNorm (integerDigitVector p L n)

/-- The AABB-specific factor: dyadic carry data together with the integer
square norm of the full digit vector. -/
def dyadicSquareColour (p L n : ℕ) : (Fin L → ℕ) × ℤ :=
  (dyadicCarryVector p L n, digitSquareColour p L n)

/-- The dyadic-square factor eliminates every nontrivial adjacent-pair AABB
pattern on `[0,p^(L+1))`. -/
theorem dyadicSquareColour_aabb_free
    (p L n0 n1 n2 n3 : ℕ) (hp : 0 < p)
    (hn0 : n0 < p ^ (L + 1)) (hn1 : n1 < p ^ (L + 1))
    (hn2 : n2 < p ^ (L + 1)) (hn3 : n3 < p ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3) (hnontrivial : n1 ≠ n0) :
    dyadicSquareColour p L n0 ≠ dyadicSquareColour p L n1 ∨
      dyadicSquareColour p L n2 ≠ dyadicSquareColour p L n3 := by
  by_cases hfirst : dyadicSquareColour p L n0 = dyadicSquareColour p L n1
  · by_cases hsecond : dyadicSquareColour p L n2 = dyadicSquareColour p L n3
    · have hshield01 := congrArg Prod.fst hfirst
      have hshield23 := congrArg Prod.fst hsecond
      have h01 : ∀ k < L,
          dyadicBucket (digitAt p k n0) = dyadicBucket (digitAt p k n1) := by
        intro k hk
        let i : Fin L := ⟨k, hk⟩
        exact congrFun hshield01 i
      have h23 : ∀ k < L,
          dyadicBucket (digitAt p k n2) = dyadicBucket (digitAt p k n3) := by
        intro k hk
        let i : Fin L := ⟨k, hk⟩
        exact congrFun hshield23 i
      obtain ⟨x, h, hh, hx0, hx1, hx2, hx3⟩ :=
        dyadicBucket_digitVector_affine p L n0 n1 n2 n3 hp
          hn0 hn1 hn2 hn3 hAP hnontrivial h01 h23
      have hsquare01 := congrArg Prod.snd hfirst
      have hsquare23 := congrArg Prod.snd hsecond
      change integerSquareNorm (integerDigitVector p L n0) =
        integerSquareNorm (integerDigitVector p L n1) at hsquare01
      change integerSquareNorm (integerDigitVector p L n2) =
        integerSquareNorm (integerDigitVector p L n3) at hsquare23
      rw [hx0, hx1] at hsquare01
      rw [hx2, hx3] at hsquare23
      exact (hh (integerSquareNorm_aabb_forces_step_zero
        x h hsquare01 hsquare23)).elim
    · exact Or.inr hsecond
  · exact Or.inl hfirst

/-- A finite palette containing every value of the dyadic-square factor. -/
abbrev DyadicSquarePalette (p L : ℕ) :=
  (Fin L → Fin (Nat.log 2 p + 1)) × Fin ((L + 1) * p ^ 2 + 1)

/-- The carry component with its finite range made explicit. -/
def finiteDyadicCarryColour (p L : ℕ) (hp : 0 < p) (n : ℕ) :
    Fin L → Fin (Nat.log 2 p + 1) := fun i ↦
  ⟨dyadicBucket (digitAt p i n), Nat.lt_succ_of_le <|
    Nat.log_mono_right <| by
      have hdigit : digitAt p i n < p := by
        simpa [digitAt] using Nat.mod_lt (quotientAt p i n) hp
      omega⟩

/-- The same digit-square coordinate computed in `ℕ`. -/
def naturalDigitSquareColour (p L n : ℕ) : ℕ :=
  ∑ i : Fin (L + 1), (digitAt p i n) ^ 2

theorem naturalDigitSquareColour_le (p L n : ℕ) (hp : 0 < p) :
    naturalDigitSquareColour p L n ≤ (L + 1) * p ^ 2 := by
  calc
    naturalDigitSquareColour p L n ≤ ∑ _i : Fin (L + 1), p ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hd : digitAt p i n ≤ p := (Nat.mod_lt _ hp).le
      exact Nat.pow_le_pow_left hd 2
    _ = (L + 1) * p ^ 2 := by simp

/-- The square coordinate with an explicit finite codomain. -/
def finiteDigitSquareColour (p L : ℕ) (hp : 0 < p) (n : ℕ) :
    Fin ((L + 1) * p ^ 2 + 1) :=
  ⟨naturalDigitSquareColour p L n,
    Nat.lt_succ_of_le (naturalDigitSquareColour_le p L n hp)⟩

/-- The fully finite AABB-specific colouring. -/
def finiteDyadicSquareColour (p L : ℕ) (hp : 0 < p) (n : ℕ) :
    DyadicSquarePalette p L :=
  (finiteDyadicCarryColour p L hp n, finiteDigitSquareColour p L hp n)

/-- Forgetting the finite range witnesses recovers the raw arithmetic colour. -/
def forgetDyadicSquarePalette (p L : ℕ) :
    DyadicSquarePalette p L → (Fin L → ℕ) × ℤ :=
  fun c ↦ (fun i ↦ (c.1 i).val, (c.2.val : ℤ))

theorem naturalDigitSquareColour_cast (p L n : ℕ) :
    (naturalDigitSquareColour p L n : ℤ) = digitSquareColour p L n := by
  simp [naturalDigitSquareColour, digitSquareColour, integerSquareNorm,
    integerDigitVector, dotProduct, pow_two]

theorem forget_finiteDyadicSquareColour (p L : ℕ) (hp : 0 < p) (n : ℕ) :
    forgetDyadicSquarePalette p L (finiteDyadicSquareColour p L hp n) =
      dyadicSquareColour p L n := by
  apply Prod.ext
  · funext i
    rfl
  · exact naturalDigitSquareColour_cast p L n

/-- Finite-palette form of the AABB-free theorem. -/
theorem finiteDyadicSquareColour_aabb_free
    (p L n0 n1 n2 n3 : ℕ) (hp : 0 < p)
    (hn0 : n0 < p ^ (L + 1)) (hn1 : n1 < p ^ (L + 1))
    (hn2 : n2 < p ^ (L + 1)) (hn3 : n3 < p ^ (L + 1))
    (hAP : IntFourAP4 n0 n1 n2 n3) (hnontrivial : n1 ≠ n0) :
    finiteDyadicSquareColour p L hp n0 ≠
        finiteDyadicSquareColour p L hp n1 ∨
      finiteDyadicSquareColour p L hp n2 ≠
        finiteDyadicSquareColour p L hp n3 := by
  rcases dyadicSquareColour_aabb_free p L n0 n1 n2 n3 hp
      hn0 hn1 hn2 hn3 hAP hnontrivial with hfirst | hsecond
  · left
    intro h
    apply hfirst
    have := congrArg (forgetDyadicSquarePalette p L) h
    simpa only [forget_finiteDyadicSquareColour] using this
  · right
    intro h
    apply hsecond
    have := congrArg (forgetDyadicSquarePalette p L) h
    simpa only [forget_finiteDyadicSquareColour] using this

/-- Exact size of the available finite palette. -/
theorem dyadicSquarePalette_card (p L : ℕ) :
    Fintype.card (DyadicSquarePalette p L) =
      (Nat.log 2 p + 1) ^ L * ((L + 1) * p ^ 2 + 1) := by
  simp

end ErdosProblems.E160
