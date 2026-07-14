import ErdosProblems.E160.FilterAssembly
import ErdosProblems.E160.SourceConventionBridge

/-!
# Bounded-colouring bridge to `siteH`

This module translates a colouring of `[0,N)` to the maintained `siteH`
convention on `[1,N]`.
-/

open Set

namespace ErdosProblems.E160

/-- Recover explicit `AtMostTwo4` witnesses from a four-value set of
cardinality at most two. -/
theorem directAtMostTwo4_of_fourSet_ncard_le
    {C : Type*} {c0 c1 c2 c3 : C}
    (hcard : ({c0, c1, c2, c3} : Set C).ncard ≤ 2) :
    AtMostTwo4 c0 c1 c2 c3 := by
  classical
  let s : Set C := {c0, c1, c2, c3}
  have hne : s.ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem (s := s) (a := c0) (by simp [s])
  have hcases : s.ncard = 1 ∨ s.ncard = 2 := by
    have : s.ncard ≤ 2 := by simpa [s] using hcard
    omega
  rcases hcases with hone | htwo
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hone
    have h0 : c0 = a := by
      have : c0 ∈ s := by simp [s]
      simpa [ha] using this
    have h1 : c1 = a := by
      have : c1 ∈ s := by simp [s]
      simpa [ha] using this
    have h2 : c2 = a := by
      have : c2 ∈ s := by simp [s]
      simpa [ha] using this
    have h3 : c3 = a := by
      have : c3 ∈ s := by simp [s]
      simpa [ha] using this
    exact ⟨a, a, Or.inl h0, Or.inl h1, Or.inl h2, Or.inl h3⟩
  · obtain ⟨a, b, _hab, hs⟩ := Set.ncard_eq_two.mp htwo
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · have : c0 ∈ s := by simp [s]
      simpa [hs] using this
    · have : c1 ∈ s := by simp [s]
      simpa [hs] using this
    · have : c2 ∈ s := by simp [s]
      simpa [hs] using this
    · have : c3 ∈ s := by simp [s]
      simpa [hs] using this

/-- A bounded colouring on `[0,N)` which excludes `AtMostTwo4` gives a good
palette on `[1,N]` after the exact predecessor shift. -/
theorem directSourceGoodPalette_of_bounded_notAtMostTwo
    (N : ℕ) {C : Type*} [Fintype C] (colour : ℕ → C)
    (hcolour : ∀ n0 n1 n2 n3,
      BoundedIntFourAP4 N n0 n1 n2 n3 →
      ¬ AtMostTwo4
        (colour n0) (colour n1) (colour n2) (colour n3)) :
    SourceGoodPalette N (Fintype.card C) := by
  classical
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let siteColour : Finset.Icc 1 N → Fin (Fintype.card C) :=
    fun x ↦ e (colour (x.val - 1))
  refine ⟨siteColour, ?_⟩
  intro progression hprogression
  rcases hprogression with ⟨hsub, ⟨a, d, hd, rfl⟩⟩
  let v0 := a + 0 * d
  let v1 := a + 1 * d
  let v2 := a + 2 * d
  let v3 := a + 3 * d
  have hv0mem : v0 ∈ {x | ∃ i : ℕ, i < 4 ∧ x = a + i * d} :=
    ⟨0, by omega, rfl⟩
  have hv1mem : v1 ∈ {x | ∃ i : ℕ, i < 4 ∧ x = a + i * d} :=
    ⟨1, by omega, rfl⟩
  have hv2mem : v2 ∈ {x | ∃ i : ℕ, i < 4 ∧ x = a + i * d} :=
    ⟨2, by omega, rfl⟩
  have hv3mem : v3 ∈ {x | ∃ i : ℕ, i < 4 ∧ x = a + i * d} :=
    ⟨3, by omega, rfl⟩
  have hv0Icc := hsub hv0mem
  have hv1Icc := hsub hv1mem
  have hv2Icc := hsub hv2mem
  have hv3Icc := hsub hv3mem
  have ha : 1 ≤ a := by
    have := (Finset.mem_Icc.mp hv0Icc).1
    simpa [v0] using this
  let x0 : Finset.Icc 1 N := ⟨v0, hv0Icc⟩
  let x1 : Finset.Icc 1 N := ⟨v1, hv1Icc⟩
  let x2 : Finset.Icc 1 N := ⟨v2, hv2Icc⟩
  let x3 : Finset.Icc 1 N := ⟨v3, hv3Icc⟩
  let n0 := v0 - 1
  let n1 := v1 - 1
  let n2 := v2 - 1
  let n3 := v3 - 1
  have hn0 : n0 < N := by
    have := Finset.mem_Icc.mp hv0Icc
    simp only [n0]
    omega
  have hn1 : n1 < N := by
    have := Finset.mem_Icc.mp hv1Icc
    simp only [n1]
    omega
  have hn2 : n2 < N := by
    have := Finset.mem_Icc.mp hv2Icc
    simp only [n2]
    omega
  have hn3 : n3 < N := by
    have := Finset.mem_Icc.mp hv3Icc
    simp only [n3]
    omega
  have hfour : IntFourAP4 n0 n1 n2 n3 := by
    simp only [IntFourAP4, n0, n1, n2, n3, v0, v1, v2, v3]
    constructor <;> omega
  have hne10 : n1 ≠ n0 := by
    simp only [n0, n1, v0, v1]
    omega
  have hnot : ¬ AtMostTwo4
      (colour n0) (colour n1) (colour n2) (colour n3) :=
    hcolour n0 n1 n2 n3 ⟨hn0, hn1, hn2, hn3, hfour, hne10⟩
  have hsiteNot : ¬ AtMostTwo4
      (siteColour x0) (siteColour x1)
      (siteColour x2) (siteColour x3) := by
    intro htwo
    apply hnot
    have hback := htwo.map e.symm
    simpa [siteColour, x0, x1, x2, x3, n0, n1, n2, n3] using hback
  let imageSet : Set (Fin (Fintype.card C)) :=
    siteColour ''
      {x | (x : ℕ) ∈ {y | ∃ i : ℕ, i < 4 ∧ y = a + i * d}}
  have hfourSubset :
      ({siteColour x0, siteColour x1, siteColour x2, siteColour x3} :
          Set (Fin (Fintype.card C))) ⊆ imageSet := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨x0, hv0mem, rfl⟩
    · exact ⟨x1, hv1mem, rfl⟩
    · exact ⟨x2, hv2mem, rfl⟩
    · exact ⟨x3, hv3mem, rfl⟩
  change 3 ≤ imageSet.ncard
  by_contra hthree
  have himageTwo : imageSet.ncard ≤ 2 := by omega
  have hfourTwo :
      ({siteColour x0, siteColour x1, siteColour x2, siteColour x3} :
          Set (Fin (Fintype.card C))).ncard ≤ 2 :=
    (Set.ncard_le_ncard hfourSubset).trans himageTwo
  exact hsiteNot (directAtMostTwo4_of_fourSet_ncard_le hfourTwo)

/-- Numerical `siteH` upper bound supplied by the bounded colouring. -/
theorem directSiteH_le_card_of_bounded_notAtMostTwo
    (N : ℕ) {C : Type*} [Fintype C] (colour : ℕ → C)
    (hcolour : ∀ n0 n1 n2 n3,
      BoundedIntFourAP4 N n0 n1 n2 n3 →
      ¬ AtMostTwo4
        (colour n0) (colour n1) (colour n2) (colour n3)) :
    siteH N ≤ Fintype.card C :=
  siteH_le_of_sourceGoodPalette
    (directSourceGoodPalette_of_bounded_notAtMostTwo N colour hcolour)

end ErdosProblems.E160
