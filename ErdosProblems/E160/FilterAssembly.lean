import ErdosProblems.E160.FilterComposition
import ErdosProblems.E160.AABBFilter

/-!
# Finite proper-ABBA filter

The dyadic AABB factor combines with no-three-equal and ABAB-free colourings to
give a proper-ABBA filter on bounded integer progressions.
-/

namespace ErdosProblems.E160

/-- Nontrivial integer four-term progressions whose four entries lie in
`[0,N)`. -/
def BoundedIntFourAP4 (N n0 n1 n2 n3 : ℕ) : Prop :=
  n0 < N ∧ n1 < N ∧ n2 < N ∧ n3 < N ∧
    IntFourAP4 n0 n1 n2 n3 ∧ n1 ≠ n0

/-- The finite dyadic-square colouring is an AABB-free factor on its complete
base-power interval. -/
theorem finiteDyadicSquareColour_isAABBFreeColouring
    (p L : ℕ) (hp : 0 < p) :
    IsAABBFreeColouring
      (BoundedIntFourAP4 (p ^ (L + 1)))
      (finiteDyadicSquareColour p L hp) := by
  intro n0 n1 n2 n3 hAP
  rcases hAP with ⟨hn0, hn1, hn2, hn3, hfour, hnontrivial⟩
  exact finiteDyadicSquareColour_aabb_free p L n0 n1 n2 n3 hp
    hn0 hn1 hn2 hn3 hfour hnontrivial

/-- Once no-three-equal and ABAB-free factors are supplied on the same
interval, the dyadic factor completes an exact proper-ABBA filter. -/
theorem dyadic_threeFactor_isProperABBAFilter
    {C0 C2 : Type*} (p L : ℕ) (hp : 0 < p)
    (noThreeColour : ℕ → C0)
    (ababColour : ℕ → C2)
    (hnoThree : IsNoThreeEqualColouring
      (BoundedIntFourAP4 (p ^ (L + 1))) noThreeColour)
    (habab : IsABABFreeColouring
      (BoundedIntFourAP4 (p ^ (L + 1))) ababColour) :
    IsProperABBAFilter
      (BoundedIntFourAP4 (p ^ (L + 1)))
      (fun n ↦ (noThreeColour n,
        finiteDyadicSquareColour p L hp n, ababColour n)) := by
  exact threeFactor_isProperABBAFilter
    (BoundedIntFourAP4 (p ^ (L + 1)))
    noThreeColour (finiteDyadicSquareColour p L hp) ababColour
    hnoThree (finiteDyadicSquareColour_isAABBFreeColouring p L hp) habab

end ErdosProblems.E160
