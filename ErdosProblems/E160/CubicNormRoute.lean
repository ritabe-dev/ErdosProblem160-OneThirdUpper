import ErdosProblems.E160.Problem

/-!
# Cubic colourings and carry shields

This file proves the abstract cubic criterion used by the finite-field norm
colouring and its carry shield.
-/

namespace ErdosProblems.E160

section CubicAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Along every affine line, `Q` is cubic with leading coefficient `Q h`. -/
def HasCubicLineExpansion (Q : V → K) : Prop :=
  ∀ x h, ∃ b c d : K, ∀ t : K,
    Q (x + t • h) = Q h * t ^ 3 + b * t ^ 2 + c * t + d

/-- The only zero of `Q` is the zero vector. -/
def IsAnisotropic (Q : V → K) : Prop :=
  ∀ h, Q h = 0 → h = 0

/-- The two ABBA equalities of a cubic polynomial force its leading
coefficient to vanish whenever `6` is nonzero in the coefficient field. -/
theorem cubic_abba_forces_leading_zero (a b c d : K)
    (h6 : (6 : K) ≠ 0)
    (houter : d = a * (3 : K) ^ 3 + b * (3 : K) ^ 2 + c * 3 + d)
    (hinner : a + b + c + d =
      a * (2 : K) ^ 3 + b * (2 : K) ^ 2 + c * 2 + d) :
    a = 0 := by
  have ho : 27 * a + 9 * b + 3 * c = 0 := by
    linear_combination -houter
  have hi : 7 * a + 3 * b + c = 0 := by
    linear_combination -hinner
  have ha : (6 : K) * a = 0 := by
    linear_combination ho - 3 * hi
  exact (mul_eq_zero.mp ha).resolve_left h6

/-- An anisotropic cubic is an ABBA-free colouring of its additive vector
space.  A finite-field norm from a cubic extension is the intended instance. -/
theorem anisotropic_cubic_abba_free (Q : V → K)
    (h6 : (6 : K) ≠ 0)
    (hcubic : HasCubicLineExpansion Q)
    (hanisotropic : IsAnisotropic Q) :
    ∀ x h : V, h ≠ 0 →
      Q x ≠ Q (x + (3 : K) • h) ∨
        Q (x + h) ≠ Q (x + (2 : K) • h) := by
  intro x h hh
  by_cases houter : Q x = Q (x + (3 : K) • h)
  · by_cases hinner : Q (x + h) = Q (x + (2 : K) • h)
    · exfalso
      obtain ⟨b, c, d, hexp⟩ := hcubic x h
      have h0 : Q x = d := by
        simpa using hexp 0
      have h1 : Q (x + h) = Q h + b + c + d := by
        simpa using hexp 1
      have h2 : Q (x + (2 : K) • h) =
          Q h * (2 : K) ^ 3 + b * (2 : K) ^ 2 + c * 2 + d := by
        simpa using hexp 2
      have h3 : Q (x + (3 : K) • h) =
          Q h * (3 : K) ^ 3 + b * (3 : K) ^ 2 + c * 3 + d := by
        simpa using hexp 3
      have houter' : d =
          Q h * (3 : K) ^ 3 + b * (3 : K) ^ 2 + c * 3 + d := by
        calc
          d = Q x := h0.symm
          _ = Q (x + (3 : K) • h) := houter
          _ = _ := h3
      have hinner' : Q h + b + c + d =
          Q h * (2 : K) ^ 3 + b * (2 : K) ^ 2 + c * 2 + d := by
        calc
          Q h + b + c + d = Q (x + h) := h1.symm
          _ = Q (x + (2 : K) • h) := hinner
          _ = _ := h2
      have hQ : Q h = 0 :=
        cubic_abba_forces_leading_zero (Q h) b c d h6 houter' hinner'
      exact hh (hanisotropic h hQ)
    · exact Or.inr hinner
  · exact Or.inl houter

end CubicAlgebra

section CarryShield

variable {X S K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A shield forces every ABBA-labelled progression in `X` to become a
non-trivial vector-space 4-AP after applying `embed`. -/
def IsABBACarryShield (AP : X → X → X → X → Prop)
    (embed : X → V) (shield : X → S) : Prop :=
  ∀ x0 x1 x2 x3,
    AP x0 x1 x2 x3 →
    shield x0 = shield x3 →
    shield x1 = shield x2 →
    ∃ x h : V, h ≠ 0 ∧
      embed x0 = x ∧
      embed x1 = x + h ∧
      embed x2 = x + (2 : K) • h ∧
      embed x3 = x + (3 : K) • h

/-- Product composition of a carry shield and an ABBA-free vector colouring
is ABBA-free on the original progression space. -/
theorem shield_product_abba_free
    (AP : X → X → X → X → Prop)
    (embed : X → V) (shield : X → S) (Q : V → K)
    (hshield : IsABBACarryShield (K := K) AP embed shield)
    (hQ : ∀ x h : V, h ≠ 0 →
      Q x ≠ Q (x + (3 : K) • h) ∨
        Q (x + h) ≠ Q (x + (2 : K) • h)) :
    ∀ x0 x1 x2 x3,
      AP x0 x1 x2 x3 →
      (shield x0, Q (embed x0)) ≠ (shield x3, Q (embed x3)) ∨
        (shield x1, Q (embed x1)) ≠ (shield x2, Q (embed x2)) := by
  intro x0 x1 x2 x3 hAP
  by_cases houter :
      (shield x0, Q (embed x0)) = (shield x3, Q (embed x3))
  · by_cases hinner :
        (shield x1, Q (embed x1)) = (shield x2, Q (embed x2))
    · exfalso
      obtain ⟨x, h, hh, hx0, hx1, hx2, hx3⟩ :=
        hshield x0 x1 x2 x3 hAP
          (congrArg Prod.fst houter) (congrArg Prod.fst hinner)
      rcases hQ x h hh with hQouter | hQinner
      · apply hQouter
        have := congrArg Prod.snd houter
        simpa [hx0, hx3] using this
      · apply hQinner
        have := congrArg Prod.snd hinner
        simpa [hx1, hx2] using this
    · exact Or.inr hinner
  · exact Or.inl houter

end CarryShield

end ErdosProblems.E160
