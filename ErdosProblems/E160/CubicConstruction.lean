import ErdosProblems.E160.ThirdsCarryShield
import ErdosProblems.E160.FiniteFieldNorm

/-!
# Concrete cubic colouring on three base-`p` digits

This file combines the carry shield with the degree-three finite-field norm,
including canonical digit extraction on `[0,p^3)`.
-/

namespace ErdosProblems.E160

/-- Carry shields are preserved by a linear equivalence of their target
vector spaces. -/
theorem IsABBACarryShield.linearEquiv
    {X S K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (AP : X → X → X → X → Prop)
    (embed : X → V) (shield : X → S)
    (e : V ≃ₗ[K] W)
    (hshield : IsABBACarryShield (K := K) AP embed shield) :
    IsABBACarryShield (K := K) AP (fun x ↦ e (embed x)) shield := by
  intro x0 x1 x2 x3 hAP houter hinner
  obtain ⟨x, h, hh, hx0, hx1, hx2, hx3⟩ :=
    hshield x0 x1 x2 x3 hAP houter hinner
  refine ⟨e x, e h, ?_, ?_, ?_, ?_, ?_⟩
  · intro heh
    apply hh
    apply e.injective
    simpa using heh
  · exact congrArg e hx0
  · calc
      e (embed x1) = e (x + h) := congrArg e hx1
      _ = e x + e h := e.map_add x h
  · calc
      e (embed x2) = e (x + (2 : K) • h) := congrArg e hx2
      _ = e x + (2 : K) • e h := by rw [e.map_add, e.map_smul]
  · calc
      e (embed x3) = e (x + (3 : K) • h) := congrArg e hx3
      _ = e x + (3 : K) • e h := by rw [e.map_add, e.map_smul]

/-- A basis-dependent identification of three residue coordinates with the
degree-three Galois field.  The resulting colour count and ABBA property are
basis-independent. -/
noncomputable def galoisFieldThreeVectorEquiv
    (p : ℕ) [Fact p.Prime] :
    (Fin 3 → ZMod p) ≃ₗ[ZMod p] GaloisField p 3 :=
  (Module.finBasisOfFinrankEq (ZMod p) (GaloisField p 3)
    (GaloisField.finrank p (by norm_num))).equivFun.symm

/-- The 9-state thirds shield maps every valid nontrivial integer digit AP to
a nontrivial affine AP in `F_(p^3)`. -/
theorem digits3_carryShield_galois (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) :
    IsABBACarryShield (K := ZMod p)
      (Digits3.IsValueFourAP (p : ℤ))
      (fun d ↦ galoisFieldThreeVectorEquiv p (Digits3.residueVector p d))
      (Digits3.carryShield (p : ℤ)) :=
  (digits3_carryShield_isABBA p hp).linearEquiv
    (Digits3.IsValueFourAP (p : ℤ))
    (Digits3.residueVector p)
    (Digits3.carryShield (p : ℤ))
    (galoisFieldThreeVectorEquiv p)

/-- The concrete shield/norm product colour on valid three-digit inputs. -/
noncomputable def digits3CubicColour (p : ℕ) [Fact p.Prime]
    (d : Digits3) : (Fin 3 × Fin 3) × ZMod p :=
  (Digits3.carryShield (p : ℤ) d,
    Algebra.norm (ZMod p)
      (galoisFieldThreeVectorEquiv p (Digits3.residueVector p d)))

/-- The concrete cubic colour is ABBA-free on every valid nontrivial
three-digit integer four-term progression. -/
theorem digits3CubicColour_abba_free (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) :
    ∀ d0 d1 d2 d3,
      Digits3.IsValueFourAP (p : ℤ) d0 d1 d2 d3 →
      digits3CubicColour p d0 ≠ digits3CubicColour p d3 ∨
        digits3CubicColour p d1 ≠ digits3CubicColour p d2 := by
  simpa [digits3CubicColour] using
    shield_product_abba_free
      (Digits3.IsValueFourAP (p : ℤ))
      (fun d ↦ galoisFieldThreeVectorEquiv p (Digits3.residueVector p d))
      (Digits3.carryShield (p : ℤ))
      (Algebra.norm (ZMod p) : GaloisField p 3 → ZMod p)
      (digits3_carryShield_galois p hp)
      (galoisFieldThree_norm_abba_free p hp)

/-- The canonical cubic colour of a natural number. -/
noncomputable def natCubicColour (p : ℕ) [Fact p.Prime]
    (n : ℕ) : (Fin 3 × Fin 3) × ZMod p :=
  digits3CubicColour p (Digits3.ofNat p n)

/-- On the entire interval `[0,p^3)`, the canonical `9p`-palette colouring
is ABBA-free on every nontrivial four-term arithmetic progression. -/
theorem natCubicColour_abba_free (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (a d : ℕ) (hd : 0 < d)
    (hbound : a + 3 * d < p ^ 3) :
    natCubicColour p a ≠ natCubicColour p (a + 3 * d) ∨
      natCubicColour p (a + d) ≠ natCubicColour p (a + 2 * d) := by
  exact digits3CubicColour_abba_free p hp
    (Digits3.ofNat p a) (Digits3.ofNat p (a + d))
    (Digits3.ofNat p (a + 2 * d)) (Digits3.ofNat p (a + 3 * d))
    (Digits3.isValueFourAP_ofNat p a d (by omega) hd hbound)

/-- The explicit palette has exactly `9p` available values when `p` is
nonzero. -/
theorem digits3CubicColour_palette_card (p : ℕ) [NeZero p] :
    Fintype.card ((Fin 3 × Fin 3) × ZMod p) = 9 * p := by
  simp

end ErdosProblems.E160
