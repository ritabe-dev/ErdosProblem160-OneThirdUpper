import ErdosProblems.E160.CubicNormRoute

/-!
# Proper-ABBA filter composition

This file isolates the exact finite pattern logic needed for a proper-ABBA
filter.  A no-three-equal factor, an AABB-free factor, and an ABAB-free factor
form such a filter.
-/

namespace ErdosProblems.E160

/-- Four values use at most two values.  The witnesses need not themselves
occur among the four entries; this form is convenient under maps. -/
def AtMostTwo4 {C : Type*} (c0 c1 c2 c3 : C) : Prop :=
  ∃ a b, (c0 = a ∨ c0 = b) ∧ (c1 = a ∨ c1 = b) ∧
    (c2 = a ∨ c2 = b) ∧ (c3 = a ∨ c3 = b)

/-- Applying a map cannot increase the number of values used. -/
theorem AtMostTwo4.map {C D : Type*} (f : C → D) {c0 c1 c2 c3 : C}
    (h : AtMostTwo4 c0 c1 c2 c3) :
    AtMostTwo4 (f c0) (f c1) (f c2) (f c3) := by
  obtain ⟨a, b, h0, h1, h2, h3⟩ := h
  exact ⟨f a, f b, h0.elim (fun h ↦ Or.inl (congrArg f h))
      (fun h ↦ Or.inr (congrArg f h)),
    h1.elim (fun h ↦ Or.inl (congrArg f h))
      (fun h ↦ Or.inr (congrArg f h)),
    h2.elim (fun h ↦ Or.inl (congrArg f h))
      (fun h ↦ Or.inr (congrArg f h)),
    h3.elim (fun h ↦ Or.inl (congrArg f h))
      (fun h ↦ Or.inr (congrArg f h))⟩

/-- If the first and fourth entries are distinct in an at-most-two tuple,
every middle entry is one of those two. -/
theorem AtMostTwo4.second_eq_first_or_fourth {C : Type*}
    {c0 c1 c2 c3 : C} (h : AtMostTwo4 c0 c1 c2 c3) (hne : c0 ≠ c3) :
    c1 = c0 ∨ c1 = c3 := by
  obtain ⟨a, b, h0, h1, _, h3⟩ := h
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h3 with h3 | h3 <;> simp_all

/-- Symmetric form: if the middle entries are distinct, the first entry is
one of them. -/
theorem AtMostTwo4.first_eq_second_or_third {C : Type*}
    {c0 c1 c2 c3 : C} (h : AtMostTwo4 c0 c1 c2 c3) (hne : c1 ≠ c2) :
    c0 = c1 ∨ c0 = c2 := by
  obtain ⟨a, b, h0, h1, h2, _⟩ := h
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> simp_all

/-- No three of four entries are equal.  All four triples are included; only
checking consecutive triples would miss the `AABA` and `ABAA` patterns. -/
def NoThreeEqual4 {C : Type*} (c0 c1 c2 c3 : C) : Prop :=
  ¬ (c0 = c1 ∧ c1 = c2) ∧
  ¬ (c0 = c1 ∧ c1 = c3) ∧
  ¬ (c0 = c2 ∧ c2 = c3) ∧
  ¬ (c1 = c2 ∧ c2 = c3)

/-- The adjacent-pair `AABB` equality pattern is absent. -/
def AABBFree4 {C : Type*} (c0 c1 c2 c3 : C) : Prop :=
  c0 ≠ c1 ∨ c2 ≠ c3

/-- The alternating `ABAB` equality pattern is absent. -/
def ABABFree4 {C : Type*} (c0 c1 c2 c3 : C) : Prop :=
  c0 ≠ c2 ∨ c1 ≠ c3

/-- A no-three-equal property detected after applying a map also holds before
the map. -/
theorem NoThreeEqual4.of_map {C D : Type*} (f : C → D)
    {c0 c1 c2 c3 : C}
    (h : NoThreeEqual4 (f c0) (f c1) (f c2) (f c3)) :
    NoThreeEqual4 c0 c1 c2 c3 := by
  rcases h with ⟨h012, h013, h023, h123⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h01, h12⟩
    exact h012 ⟨congrArg f h01, congrArg f h12⟩
  · rintro ⟨h01, h13⟩
    exact h013 ⟨congrArg f h01, congrArg f h13⟩
  · rintro ⟨h02, h23⟩
    exact h023 ⟨congrArg f h02, congrArg f h23⟩
  · rintro ⟨h12, h23⟩
    exact h123 ⟨congrArg f h12, congrArg f h23⟩

/-- An AABB obstruction detected after applying a map also holds before the
map. -/
theorem AABBFree4.of_map {C D : Type*} (f : C → D)
    {c0 c1 c2 c3 : C}
    (h : AABBFree4 (f c0) (f c1) (f c2) (f c3)) :
    AABBFree4 c0 c1 c2 c3 := by
  rcases h with h01 | h23
  · exact Or.inl (fun e ↦ h01 (congrArg f e))
  · exact Or.inr (fun e ↦ h23 (congrArg f e))

/-- An ABAB obstruction detected after applying a map also holds before the
map. -/
theorem ABABFree4.of_map {C D : Type*} (f : C → D)
    {c0 c1 c2 c3 : C}
    (h : ABABFree4 (f c0) (f c1) (f c2) (f c3)) :
    ABABFree4 c0 c1 c2 c3 := by
  rcases h with h02 | h13
  · exact Or.inl (fun e ↦ h02 (congrArg f e))
  · exact Or.inr (fun e ↦ h13 (congrArg f e))

/-- The exhaustive two-value classification: after excluding the four
three-equal patterns, AABB, and ABAB, the only remaining two-value pattern is
proper ABBA. -/
theorem atMostTwo_noThree_aabb_abab_properABBA
    {C : Type*} {c0 c1 c2 c3 : C}
    (htwo : AtMostTwo4 c0 c1 c2 c3)
    (hthree : NoThreeEqual4 c0 c1 c2 c3)
    (haabb : AABBFree4 c0 c1 c2 c3)
    (habab : ABABFree4 c0 c1 c2 c3) :
    c0 = c3 ∧ c1 = c2 ∧ c0 ≠ c1 := by
  obtain ⟨a, b, h0, h1, h2, h3⟩ := htwo
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;>
    simp_all [NoThreeEqual4, AABBFree4, ABABFree4]

/-- A colouring which rules out equality on every triple of positions. -/
def IsNoThreeEqualColouring {X C : Type*}
    (AP : X → X → X → X → Prop) (colour : X → C) : Prop :=
  ∀ x0 x1 x2 x3, AP x0 x1 x2 x3 →
    NoThreeEqual4 (colour x0) (colour x1) (colour x2) (colour x3)

/-- A colouring which rules out the adjacent-pair AABB pattern. -/
def IsAABBFreeColouring {X C : Type*}
    (AP : X → X → X → X → Prop) (colour : X → C) : Prop :=
  ∀ x0 x1 x2 x3, AP x0 x1 x2 x3 →
    AABBFree4 (colour x0) (colour x1) (colour x2) (colour x3)

/-- A colouring which rules out the alternating ABAB pattern. -/
def IsABABFreeColouring {X C : Type*}
    (AP : X → X → X → X → Prop) (colour : X → C) : Prop :=
  ∀ x0 x1 x2 x3, AP x0 x1 x2 x3 →
    ABABFree4 (colour x0) (colour x1) (colour x2) (colour x3)

/-- A filter is proper-ABBA when every progression using at most two filter
values has two distinct values in the outer/inner ABBA pattern. -/
def IsProperABBAFilter {X S : Type*} (AP : X → X → X → X → Prop)
    (filterColour : X → S) : Prop :=
  ∀ x0 x1 x2 x3,
    AP x0 x1 x2 x3 →
    AtMostTwo4 (filterColour x0) (filterColour x1)
      (filterColour x2) (filterColour x3) →
    filterColour x0 = filterColour x3 ∧
      filterColour x1 = filterColour x2 ∧
      filterColour x0 ≠ filterColour x1

/-- Three mechanism-specific factors give a proper-ABBA filter: one rules out
all three-equal patterns, one rules out AABB, and one rules out ABAB. -/
theorem threeFactor_isProperABBAFilter
    {X C0 C1 C2 : Type*} (AP : X → X → X → X → Prop)
    (noThreeColour : X → C0)
    (aabbColour : X → C1)
    (ababColour : X → C2)
    (hnoThree : IsNoThreeEqualColouring AP noThreeColour)
    (haabb : IsAABBFreeColouring AP aabbColour)
    (habab : IsABABFreeColouring AP ababColour) :
    IsProperABBAFilter AP
      (fun x ↦ (noThreeColour x, aabbColour x, ababColour x)) := by
  intro x0 x1 x2 x3 hAP htwo
  exact atMostTwo_noThree_aabb_abab_properABBA htwo
    (NoThreeEqual4.of_map
      (fun z : C0 × C1 × C2 ↦ z.1)
      (hnoThree x0 x1 x2 x3 hAP))
    (AABBFree4.of_map
      (fun z : C0 × C1 × C2 ↦ z.2.1)
      (haabb x0 x1 x2 x3 hAP))
    (ABABFree4.of_map
      (fun z : C0 × C1 × C2 ↦ z.2.2)
      (habab x0 x1 x2 x3 hAP))

/-- A proper-ABBA filter and an ABBA-free colouring form a colouring which
uses at least three product colours on every progression. -/
theorem properABBAFilter_product_not_atMostTwo
    {X S C : Type*} (AP : X → X → X → X → Prop)
    (filterColour : X → S) (abbaColour : X → C)
    (hfilter : IsProperABBAFilter AP filterColour)
    (habba : ∀ x0 x1 x2 x3,
      AP x0 x1 x2 x3 →
      abbaColour x0 ≠ abbaColour x3 ∨
        abbaColour x1 ≠ abbaColour x2) :
    ∀ x0 x1 x2 x3,
      AP x0 x1 x2 x3 →
      ¬ AtMostTwo4
        (filterColour x0, abbaColour x0)
        (filterColour x1, abbaColour x1)
        (filterColour x2, abbaColour x2)
        (filterColour x3, abbaColour x3) := by
  intro x0 x1 x2 x3 hAP htwo
  have hfilterTwo : AtMostTwo4
      (filterColour x0) (filterColour x1)
      (filterColour x2) (filterColour x3) :=
    htwo.map Prod.fst
  obtain ⟨houterFilter, hinnerFilter, hproper⟩ :=
    hfilter x0 x1 x2 x3 hAP hfilterTwo
  rcases habba x0 x1 x2 x3 hAP with houter | hinner
  · have houterProd :
        (filterColour x0, abbaColour x0) ≠
          (filterColour x3, abbaColour x3) := by
      intro h
      exact houter (congrArg Prod.snd h)
    rcases htwo.second_eq_first_or_fourth houterProd with h10 | h13
    · exact hproper (congrArg Prod.fst h10).symm
    · exact hproper (houterFilter.trans (congrArg Prod.fst h13).symm)
  · have hinnerProd :
        (filterColour x1, abbaColour x1) ≠
          (filterColour x2, abbaColour x2) := by
      intro h
      exact hinner (congrArg Prod.snd h)
    rcases htwo.first_eq_second_or_third hinnerProd with h01 | h02
    · exact hproper (congrArg Prod.fst h01)
    · exact hproper ((congrArg Prod.fst h02).trans hinnerFilter.symm)

end ErdosProblems.E160
