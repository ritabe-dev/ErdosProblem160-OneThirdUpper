import ErdosProblems.E160.CubicNormRoute
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# The cubic finite-field norm instance

This file instantiates the abstract cubic ABBA theorem with the norm from the
degree-three Galois field extension.  The cubic line expansion is obtained
from the determinant of the left-multiplication matrix.
-/

open Module Matrix Polynomial

namespace ErdosProblems.E160

/-- On a degree-three finite field extension, the algebra norm is cubic on
every affine line and its leading coefficient is the norm of the direction. -/
theorem algebraNorm_hasCubicLineExpansion_of_finrank_eq_three
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 3) :
    HasCubicLineExpansion (Algebra.norm K : L → K) := by
  intro x h
  let bas : Basis (Fin 3) K L := finBasisOfFinrankEq K L hdim
  let A : Matrix (Fin 3) (Fin 3) K := Algebra.leftMulMatrix bas h
  let B : Matrix (Fin 3) (Fin 3) K := Algebra.leftMulMatrix bas x
  let P : K[X] := det ((X : K[X]) • A.map C + B.map C)
  refine ⟨P.coeff 2, P.coeff 1, P.coeff 0, ?_⟩
  intro t
  have hdeg : P.natDegree < 4 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_det_X_add_C_le A B)
    norm_num
  have heval := P.eval_eq_sum_range' hdeg t
  have hlead : P.coeff 3 = Algebra.norm K h := by
    calc
      P.coeff 3 = det A := by
        dsimp [P]
        simpa using Polynomial.coeff_det_X_add_C_card A B
      _ = Algebra.norm K h := (Algebra.norm_eq_matrix_det bas h).symm
  have hP : P.eval t = det (t • A + B) := by
    dsimp [P]
    rw [eval_det]
    congr 1
    ext i j
    simp [mul_comm]
  calc
    Algebra.norm K (x + t • h) =
        det (Algebra.leftMulMatrix bas (x + t • h)) :=
      Algebra.norm_eq_matrix_det bas _
    _ = det (t • A + B) := by
      congr 1
      dsimp [A, B]
      simp [add_comm]
    _ = P.eval t := hP.symm
    _ = Algebra.norm K h * t ^ 3 + P.coeff 2 * t ^ 2 +
          P.coeff 1 * t + P.coeff 0 := by
      rw [heval]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [hlead]
      ring

/-- A field norm vanishes only at zero. -/
theorem algebraNorm_isAnisotropic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    IsAnisotropic (Algebra.norm K : L → K) := by
  intro h hh
  exact Algebra.norm_eq_zero_iff.mp hh

/-- Concrete cubic-line expansion for `F_(p^3) / F_p`. -/
theorem galoisFieldThree_norm_hasCubicLineExpansion
    (p : ℕ) [Fact p.Prime] :
    HasCubicLineExpansion
      (Algebra.norm (ZMod p) : GaloisField p 3 → ZMod p) :=
  algebraNorm_hasCubicLineExpansion_of_finrank_eq_three
    (GaloisField.finrank p (by norm_num))

/-- Concrete norm anisotropy for `F_(p^3) / F_p`. -/
theorem galoisFieldThree_norm_isAnisotropic
    (p : ℕ) [Fact p.Prime] :
    IsAnisotropic
      (Algebra.norm (ZMod p) : GaloisField p 3 → ZMod p) :=
  algebraNorm_isAnisotropic

/-- The coefficient `6` used by cubic ABBA cancellation is nonzero for
primes greater than three. -/
theorem six_ne_zero_zmod_of_three_lt
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (6 : ZMod p) ≠ 0 := by
  change ¬ ((6 : ℕ) : ZMod p) = 0
  rw [ZMod.natCast_eq_zero_iff]
  intro hdiv
  have hmul : p ∣ 2 * 3 := by simpa using hdiv
  rcases (Fact.out : p.Prime).dvd_mul.mp hmul with h2 | h3
  · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
    omega
  · have := Nat.le_of_dvd (by norm_num : 0 < 3) h3
    omega

/-- The degree-three finite-field norm is an ABBA-free colouring of its
additive vector space for every prime `p > 3`. -/
theorem galoisFieldThree_norm_abba_free
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∀ x h : GaloisField p 3, h ≠ 0 →
      Algebra.norm (ZMod p) x ≠
          Algebra.norm (ZMod p) (x + (3 : ZMod p) • h) ∨
        Algebra.norm (ZMod p) (x + h) ≠
          Algebra.norm (ZMod p) (x + (2 : ZMod p) • h) :=
  anisotropic_cubic_abba_free
    (Algebra.norm (ZMod p) : GaloisField p 3 → ZMod p)
    (six_ne_zero_zmod_of_three_lt p hp)
    (galoisFieldThree_norm_hasCubicLineExpansion p)
    (galoisFieldThree_norm_isAnisotropic p)

end ErdosProblems.E160
