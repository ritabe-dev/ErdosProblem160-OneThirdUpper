import Mathlib

/-!
# Erdős Problem #160

This file defines the maintained finite colouring quantity and the two upper
bound statements proved in this development.  The original 1989 wording uses
a shifted extremal convention; the exact bridge is proved in
`SourceConventionBridge`.
-/

open Filter Set

namespace ErdosProblems.E160

/-- A non-degenerate four-term arithmetic progression in `ℕ`. -/
def IsFourTermAP (progression : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    progression = {x | ∃ i : ℕ, i < 4 ∧ x = a + i * d}

/-- The least number of colours needed on `[1, n]` so
that every four-term arithmetic progression receives at least three colours. -/
noncomputable def siteH (n : ℕ) : ℕ :=
  sInf {k | ∃ colouring : Finset.Icc 1 n → Fin k,
    ∀ progression : Set ℕ,
      (progression ⊆ Finset.Icc 1 n ∧ IsFourTermAP progression) →
        3 ≤ (colouring '' {x | (x : ℕ) ∈ progression}).ncard}

/-- Exponent supplied by the `22`-point, three-colour seed and independent
digit tensoring. -/
noncomputable def tensorExponent : ℝ := Real.log 3 / Real.log 22

/-- A fixed improvement over the tensor exponent. -/
def BetterThanTensorUpper : Prop :=
  ∃ β : ℝ, β < tensorExponent ∧
    (fun n ↦ (siteH n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) ^ β)

/-- The standard epsilon-form of an `N^(1/3+o(1))` upper bound. -/
def OneThirdPlusEpsilonUpper : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun n ↦ (siteH n : ℝ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ ((1 : ℝ) / 3 + ε))

end ErdosProblems.E160
