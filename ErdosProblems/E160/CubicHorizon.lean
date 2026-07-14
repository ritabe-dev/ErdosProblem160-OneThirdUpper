import ErdosProblems.E160.CubicConstruction
import ErdosProblems.E160.FilterAssembly
import Mathlib.NumberTheory.Bertrand

/-!
# An all-horizon cubic ABBA factor

This file chooses a prime for every horizon without introducing real cube
roots.  A binary ceiling logarithm supplies a three-digit scale, and
Bertrand's postulate supplies a prime within a factor of two.
-/

namespace ErdosProblems.E160

/-- A safe binary exponent for a three-digit base covering `[0,N)`.  The
extra `2` keeps the Bertrand prime strictly above `3`, including small
horizons. -/
def cubicDigitExponent (N : ℕ) : ℕ :=
  (Nat.clog 2 N + 2) / 3 + 2

/-- The pre-prime scale used for the cubic colouring. -/
def cubicScale (N : ℕ) : ℕ := 2 ^ cubicDigitExponent N

theorem cubicScale_pos (N : ℕ) : 0 < cubicScale N := by
  simp [cubicScale]

theorem three_lt_cubicScale (N : ℕ) : 3 < cubicScale N := by
  have he : 2 ≤ cubicDigitExponent N := by
    simp [cubicDigitExponent]
  calc
    3 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ cubicDigitExponent N :=
      Nat.pow_le_pow_right (by norm_num) he

/-- The cube of the binary scale covers the requested horizon. -/
theorem cubicScale_cube_covers (N : ℕ) : N ≤ cubicScale N ^ 3 := by
  have hlog : N ≤ 2 ^ Nat.clog 2 N :=
    Nat.le_pow_clog (by norm_num) N
  have hexponent : Nat.clog 2 N ≤ 3 * cubicDigitExponent N := by
    simp only [cubicDigitExponent]
    omega
  have hpow : 2 ^ Nat.clog 2 N ≤ 2 ^ (3 * cubicDigitExponent N) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  calc
    N ≤ 2 ^ Nat.clog 2 N := hlog
    _ ≤ 2 ^ (3 * cubicDigitExponent N) := hpow
    _ = 2 ^ (cubicDigitExponent N * 3) := by rw [mul_comm]
    _ = (2 ^ cubicDigitExponent N) ^ 3 := by rw [pow_mul]
    _ = cubicScale N ^ 3 := by rfl

/-- A prime base, within twice the binary scale, whose cube covers the
horizon. -/
theorem exists_cubicPrime (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ N ≤ p ^ 3 ∧ p ≤ 2 * cubicScale N := by
  obtain ⟨p, hp, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (cubicScale N)
      (cubicScale_pos N).ne'
  refine ⟨p, hp, (three_lt_cubicScale N).trans hlo, ?_, hhi⟩
  exact (cubicScale_cube_covers N).trans
    (Nat.pow_le_pow_left hlo.le 3)

/-- A canonical choice of prime base for the horizon. -/
noncomputable def cubicPrime (N : ℕ) : ℕ :=
  Classical.choose (exists_cubicPrime N)

theorem cubicPrime_prime (N : ℕ) : (cubicPrime N).Prime :=
  (Classical.choose_spec (exists_cubicPrime N)).1

theorem three_lt_cubicPrime (N : ℕ) : 3 < cubicPrime N :=
  (Classical.choose_spec (exists_cubicPrime N)).2.1

theorem cubicPrime_cube_covers (N : ℕ) : N ≤ cubicPrime N ^ 3 :=
  (Classical.choose_spec (exists_cubicPrime N)).2.2.1

theorem cubicPrime_le_two_mul_scale (N : ℕ) :
    cubicPrime N ≤ 2 * cubicScale N :=
  (Classical.choose_spec (exists_cubicPrime N)).2.2.2

/-- A uniform integer constant for the cube of the available `9p` cubic
palette. -/
def cubicPaletteCubeConstant : ℕ := 2_985_984

/-- The deliberately padded binary scale is still within a fixed cubic
factor of the horizon. -/
theorem cubicScale_cube_lt_512_mul (N : ℕ) (hN : 1 < N) :
    cubicScale N ^ 3 < 512 * N := by
  let q := Nat.clog 2 N
  have hq : 0 < q := by
    have hcover : N ≤ 2 ^ q := by
      simpa [q] using Nat.le_pow_clog (by norm_num) N
    by_contra h
    have : q = 0 := by omega
    simp [this] at hcover
    omega
  have hexponent : 3 * cubicDigitExponent N ≤ q + 8 := by
    simp only [cubicDigitExponent, q]
    omega
  have hpred : 2 ^ (q - 1) < N := by
    simpa [q] using
      (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN)
  have hpow : 2 ^ q < 2 * N := by
    calc
      2 ^ q = 2 ^ (q - 1 + 1) := by congr 1; omega
      _ = 2 ^ (q - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (q - 1) := by omega
      _ < 2 * N := Nat.mul_lt_mul_of_pos_left hpred (by norm_num)
  calc
    cubicScale N ^ 3 = 2 ^ (3 * cubicDigitExponent N) := by
      rw [show 3 * cubicDigitExponent N =
        cubicDigitExponent N * 3 by omega, pow_mul]
      rfl
    _ ≤ 2 ^ (q + 8) := Nat.pow_le_pow_right (by norm_num) hexponent
    _ = 256 * 2 ^ q := by rw [pow_add]; norm_num; ring
    _ < 256 * (2 * N) := Nat.mul_lt_mul_of_pos_left hpow (by norm_num)
    _ = 512 * N := by ring

/-- The selected prime has cube below a fixed multiple of the horizon. -/
theorem cubicPrime_cube_lt_4096_mul (N : ℕ) (hN : 1 < N) :
    cubicPrime N ^ 3 < 4096 * N := by
  calc
    cubicPrime N ^ 3 ≤ (2 * cubicScale N) ^ 3 :=
      Nat.pow_le_pow_left (cubicPrime_le_two_mul_scale N) 3
    _ = 8 * cubicScale N ^ 3 := by ring
    _ < 8 * (512 * N) :=
      Nat.mul_lt_mul_of_pos_left (cubicScale_cube_lt_512_mul N hN)
        (by norm_num)
    _ = 4096 * N := by ring

/-- Cubing the exact available cubic palette costs only one power of the
horizon and a fixed constant. -/
theorem horizonCubicPalette_cube_lt (N : ℕ) (hN : 1 < N) :
    (9 * cubicPrime N) ^ 3 < cubicPaletteCubeConstant * N := by
  calc
    (9 * cubicPrime N) ^ 3 = 729 * cubicPrime N ^ 3 := by ring
    _ < 729 * (4096 * N) :=
      Nat.mul_lt_mul_of_pos_left (cubicPrime_cube_lt_4096_mul N hN)
        (by norm_num)
    _ = cubicPaletteCubeConstant * N := by
      change 729 * (4096 * N) = 2_985_984 * N
      ring

noncomputable instance cubicPrimeFact (N : ℕ) : Fact (cubicPrime N).Prime :=
  ⟨cubicPrime_prime N⟩

/-- The canonical `9p` cubic colour at horizon `N`. -/
noncomputable def horizonCubicColour (N n : ℕ) :
    (Fin 3 × Fin 3) × ZMod (cubicPrime N) :=
  natCubicColour (cubicPrime N) n

private theorem intFourAP_reverse {n0 n1 n2 n3 : ℕ}
    (hAP : IntFourAP4 n0 n1 n2 n3) :
    IntFourAP4 n3 n2 n1 n0 := by
  rcases hAP with ⟨h01, h23⟩
  constructor <;> omega

private theorem horizonCubicColour_abba_free_of_lt
    (N n0 n1 n2 n3 : ℕ)
    (_hn0 : n0 < N) (_hn1 : n1 < N) (_hn2 : n2 < N) (hn3 : n3 < N)
    (hAP : IntFourAP4 n0 n1 n2 n3) (hlt : n0 < n1) :
    horizonCubicColour N n0 ≠ horizonCubicColour N n3 ∨
      horizonCubicColour N n1 ≠ horizonCubicColour N n2 := by
  let d := n1 - n0
  have hd : 0 < d := Nat.sub_pos_of_lt hlt
  have h1 : n1 = n0 + d := by simp [d, Nat.add_sub_of_le hlt.le]
  have h2 : n2 = n0 + 2 * d := by
    rcases hAP with ⟨h01, _h23⟩
    omega
  have h3 : n3 = n0 + 3 * d := by
    rcases hAP with ⟨h01, h23⟩
    omega
  have hbound : n0 + 3 * d < cubicPrime N ^ 3 := by
    rw [← h3]
    exact hn3.trans_le (cubicPrime_cube_covers N)
  simpa [horizonCubicColour, h1, h2, h3] using
    natCubicColour_abba_free (cubicPrime N) (three_lt_cubicPrime N)
      n0 d hd hbound

/-- On every bounded nontrivial integer four-term progression, the canonical
cubic colour excludes ABBA.  Both increasing and decreasing orientations are
covered. -/
theorem horizonCubicColour_abba_free (N : ℕ) :
    ∀ n0 n1 n2 n3,
      BoundedIntFourAP4 N n0 n1 n2 n3 →
      horizonCubicColour N n0 ≠ horizonCubicColour N n3 ∨
        horizonCubicColour N n1 ≠ horizonCubicColour N n2 := by
  intro n0 n1 n2 n3 hbounded
  rcases hbounded with ⟨hn0, hn1, hn2, hn3, hAP, hne⟩
  by_cases hlt : n0 < n1
  · exact horizonCubicColour_abba_free_of_lt N n0 n1 n2 n3
      hn0 hn1 hn2 hn3 hAP hlt
  · have hgt : n1 < n0 := by omega
    have h32 : n3 < n2 := by
      rcases hAP with ⟨h01, h23⟩
      omega
    rcases horizonCubicColour_abba_free_of_lt N n3 n2 n1 n0
      hn3 hn2 hn1 hn0 (intFourAP_reverse hAP) h32 with h30 | h21
    · exact Or.inl (fun h03 ↦ h30 h03.symm)
    · exact Or.inr (fun h12 ↦ h21 h12.symm)

/-- Exact available size of the horizon cubic palette. -/
theorem horizonCubicPalette_card (N : ℕ) :
    Fintype.card ((Fin 3 × Fin 3) × ZMod (cubicPrime N)) =
      9 * cubicPrime N := by
  letI : NeZero (cubicPrime N) := ⟨(cubicPrime_prime N).ne_zero⟩
  exact digits3CubicColour_palette_card (cubicPrime N)

end ErdosProblems.E160
