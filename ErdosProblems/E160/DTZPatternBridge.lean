import ErdosProblems.E160.FilterAssembly

/-!
# The DTZ `4`-pattern bridge for the no-three-equal factor

This file proves the arithmetic map from a nontrivial integer four-term
progression to the four weighted three-point patterns used by
Deng--Tidor--Zhao. Their colouring-existence theorem is not used here.
-/

namespace ErdosProblems.E160

/-- The witness-explicit form of Deng--Tidor--Zhao Definition 3.1.

The ordered triple `(x, y, z)` has positive weights `(a, b)`, with
`a + b ≤ k - 1`, and satisfies `a*x + b*y = (a+b)*z`.  Definition 3.1
requires the three points to be not all equal, rather than pairwise distinct.
-/
def DTZWeightedThreePointPattern
    (k a b x y z : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a + b ≤ k - 1 ∧
    a * x + b * y = (a + b) * z ∧
    ¬ (x = y ∧ y = z)

/-- The existential-weight form of a DTZ `k`-pattern. -/
def DTZKPattern (k x y z : ℕ) : Prop :=
  ∃ a b, DTZWeightedThreePointPattern k a b x y z

/-- A triple has one colour when its first and second, and its second and
third, colours agree. -/
def MonochromaticTriple {X C : Type*} (colour : X → C)
    (x y z : X) : Prop :=
  colour x = colour y ∧ colour y = colour z

/-- A colouring avoids every DTZ pattern with the indicated explicit
weights. -/
def AvoidsMonochromaticDTZWeightedPattern {C : Type*}
    (k a b : ℕ) (colour : ℕ → C) : Prop :=
  ∀ x y z, DTZWeightedThreePointPattern k a b x y z →
    ¬ MonochromaticTriple colour x y z

/-- The pattern-avoidance property appearing in DTZ Lemma 3.2. -/
def AvoidsMonochromaticDTZKPatterns {C : Type*}
    (k : ℕ) (colour : ℕ → C) : Prop :=
  ∀ x y z, DTZKPattern k x y z →
    ¬ MonochromaticTriple colour x y z

/-! ## The four arithmetic pattern maps -/

/-- Positions `0,1,2`, ordered as `(x0,x2,x1)`, obey the `(1,1)` relation. -/
theorem intFourAP4_dtzRelation012 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) :
    1 * x0 + 1 * x2 = (1 + 1) * x1 := by
  rcases hAP with ⟨h01, _⟩
  norm_num
  omega

/-- Positions `1,2,3`, ordered as `(x1,x3,x2)`, obey the `(1,1)` relation. -/
theorem intFourAP4_dtzRelation123 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) :
    1 * x1 + 1 * x3 = (1 + 1) * x2 := by
  rcases hAP with ⟨_, h23⟩
  norm_num
  omega

/-- Positions `0,1,3`, ordered as `(x0,x3,x1)`, obey the `(2,1)` relation. -/
theorem intFourAP4_dtzRelation013 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) :
    2 * x0 + 1 * x3 = (2 + 1) * x1 := by
  rcases hAP with ⟨h01, h23⟩
  norm_num
  omega

/-- Positions `0,2,3`, ordered as `(x0,x3,x2)`, obey the `(1,2)` relation. -/
theorem intFourAP4_dtzRelation023 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) :
    1 * x0 + 2 * x3 = (1 + 2) * x2 := by
  rcases hAP with ⟨h01, h23⟩
  norm_num
  omega

/-- A nontrivial integer four-term progression gives the DTZ `(1,1)` pattern
on positions `0,1,2`, ordered as `(x0,x2,x1)`. -/
theorem intFourAP4_dtzPattern012 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) (hne : x1 ≠ x0) :
    DTZWeightedThreePointPattern 4 1 1 x0 x2 x1 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    intFourAP4_dtzRelation012 x0 x1 x2 x3 hAP, ?_⟩
  rintro ⟨hx02, hx21⟩
  exact hne (hx21 ▸ hx02.symm)

/-- A nontrivial integer four-term progression gives the DTZ `(1,1)` pattern
on positions `1,2,3`, ordered as `(x1,x3,x2)`. -/
theorem intFourAP4_dtzPattern123 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) (hne : x1 ≠ x0) :
    DTZWeightedThreePointPattern 4 1 1 x1 x3 x2 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    intFourAP4_dtzRelation123 x0 x1 x2 x3 hAP, ?_⟩
  rcases hAP with ⟨h01, _⟩
  rintro ⟨hx13, hx32⟩
  omega

/-- A nontrivial integer four-term progression gives the DTZ `(2,1)` pattern
on positions `0,1,3`, ordered as `(x0,x3,x1)`. -/
theorem intFourAP4_dtzPattern013 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) (hne : x1 ≠ x0) :
    DTZWeightedThreePointPattern 4 2 1 x0 x3 x1 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    intFourAP4_dtzRelation013 x0 x1 x2 x3 hAP, ?_⟩
  rintro ⟨hx03, hx31⟩
  exact hne (hx31 ▸ hx03.symm)

/-- A nontrivial integer four-term progression gives the DTZ `(1,2)` pattern
on positions `0,2,3`, ordered as `(x0,x3,x2)`. -/
theorem intFourAP4_dtzPattern023 (x0 x1 x2 x3 : ℕ)
    (hAP : IntFourAP4 x0 x1 x2 x3) (hne : x1 ≠ x0) :
    DTZWeightedThreePointPattern 4 1 2 x0 x3 x2 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    intFourAP4_dtzRelation023 x0 x1 x2 x3 hAP, ?_⟩
  rcases hAP with ⟨h01, _⟩
  rintro ⟨hx03, hx32⟩
  omega

/-- A bounded progression supplies all four DTZ weighted patterns. The
interval bounds are unused in this arithmetic argument. -/
theorem boundedIntFourAP4_dtzPatterns (N x0 x1 x2 x3 : ℕ)
    (hAP : BoundedIntFourAP4 N x0 x1 x2 x3) :
    DTZWeightedThreePointPattern 4 1 1 x0 x2 x1 ∧
    DTZWeightedThreePointPattern 4 1 1 x1 x3 x2 ∧
    DTZWeightedThreePointPattern 4 2 1 x0 x3 x1 ∧
    DTZWeightedThreePointPattern 4 1 2 x0 x3 x2 := by
  rcases hAP with ⟨_, _, _, _, hfour, hne⟩
  exact ⟨intFourAP4_dtzPattern012 x0 x1 x2 x3 hfour hne,
    intFourAP4_dtzPattern123 x0 x1 x2 x3 hfour hne,
    intFourAP4_dtzPattern013 x0 x1 x2 x3 hfour hne,
    intFourAP4_dtzPattern023 x0 x1 x2 x3 hfour hne⟩

/-! ## Pattern avoidance implies the no-three-equal factor -/

/-- Avoiding the three relevant explicit weight pairs rules out all four
ways for three positions of a bounded nontrivial four-term progression to
receive one colour. -/
theorem dtzWeightedPatternAvoidance_isNoThreeEqualColouring
    {C : Type*} (N : ℕ) (colour : ℕ → C)
    (h11 : AvoidsMonochromaticDTZWeightedPattern 4 1 1 colour)
    (h21 : AvoidsMonochromaticDTZWeightedPattern 4 2 1 colour)
    (h12 : AvoidsMonochromaticDTZWeightedPattern 4 1 2 colour) :
    IsNoThreeEqualColouring (BoundedIntFourAP4 N) colour := by
  intro x0 x1 x2 x3 hAP
  rcases boundedIntFourAP4_dtzPatterns N x0 x1 x2 x3 hAP with
    ⟨hp012, hp123, hp013, hp023⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h01, h12⟩
    exact h11 x0 x2 x1 hp012 ⟨h01.trans h12, h12.symm⟩
  · rintro ⟨h01, h13⟩
    exact h21 x0 x3 x1 hp013 ⟨h01.trans h13, h13.symm⟩
  · rintro ⟨h02, h23⟩
    exact h12 x0 x3 x2 hp023 ⟨h02.trans h23, h23.symm⟩
  · rintro ⟨h12, h23⟩
    exact h11 x1 x3 x2 hp123 ⟨h12.trans h23, h23.symm⟩

/-- Avoiding every DTZ `4`-pattern implies the bounded no-three-equal
property. -/
theorem dtz4PatternAvoidance_isNoThreeEqualColouring
    {C : Type*} (N : ℕ) (colour : ℕ → C)
    (havoid : AvoidsMonochromaticDTZKPatterns 4 colour) :
    IsNoThreeEqualColouring (BoundedIntFourAP4 N) colour := by
  apply dtzWeightedPatternAvoidance_isNoThreeEqualColouring N colour
  · intro x y z hpattern
    exact havoid x y z ⟨1, 1, hpattern⟩
  · intro x y z hpattern
    exact havoid x y z ⟨2, 1, hpattern⟩
  · intro x y z hpattern
    exact havoid x y z ⟨1, 2, hpattern⟩

/-! ## Cyclic-group pattern bridge

DTZ Lemma 3.2 is stated on a cyclic group, rather than on natural numbers.
The following gives the corresponding additive formulation.
-/

/-- Definition 3.1 over an additive abelian group.  Natural-number scalar
multiplication is the weighted linear relation used in the paper. -/
def DTZWeightedAdditiveThreePointPattern
    {G : Type*} [AddCommGroup G]
    (k a b : ℕ) (x y z : G) : Prop :=
  0 < a ∧ 0 < b ∧ a + b ≤ k - 1 ∧
    a • x + b • y = (a + b) • z ∧
    ¬ (x = y ∧ y = z)

/-- Existential-weight DTZ patterns over an additive abelian group. -/
def DTZAdditiveKPattern
    {G : Type*} [AddCommGroup G] (k : ℕ) (x y z : G) : Prop :=
  ∃ a b, DTZWeightedAdditiveThreePointPattern k a b x y z

/-- A colouring of an additive group avoids all monochromatic DTZ
`k`-patterns.  This is the exact conclusion needed from cyclic Lemma 3.2. -/
def AvoidsMonochromaticDTZAdditiveKPatterns
    {G C : Type*} [AddCommGroup G]
    (k : ℕ) (colour : G → C) : Prop :=
  ∀ x y z, DTZAdditiveKPattern k x y z →
    ¬ MonochromaticTriple colour x y z

/-- Cyclic positions `0,1,2`, ordered `(x0,x2,x1)`, give the DTZ
`(1,1)` pattern. -/
theorem additiveFourAP_dtzPattern012
    {G : Type*} [AddCommGroup G] (x d : G) (hd : d ≠ 0) :
    DTZWeightedAdditiveThreePointPattern 4 1 1
      x (x + 2 • d) (x + d) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by abel, ?_⟩
  rintro ⟨_h02, h21⟩
  have htwo : 2 • d = d := add_left_cancel h21
  apply hd
  calc
    d = 2 • d - d := by abel
    _ = d - d := by rw [htwo]
    _ = 0 := sub_self d

/-- Cyclic positions `1,2,3`, ordered `(x1,x3,x2)`, give the DTZ
`(1,1)` pattern. -/
theorem additiveFourAP_dtzPattern123
    {G : Type*} [AddCommGroup G] (x d : G) (hd : d ≠ 0) :
    DTZWeightedAdditiveThreePointPattern 4 1 1
      (x + d) (x + 3 • d) (x + 2 • d) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by abel, ?_⟩
  rintro ⟨_h13, h32⟩
  have hthree : 3 • d = 2 • d := add_left_cancel h32
  apply hd
  calc
    d = 3 • d - 2 • d := by abel
    _ = 0 := by rw [hthree, sub_self]

/-- Cyclic positions `0,1,3`, ordered `(x0,x3,x1)`, give the DTZ
`(2,1)` pattern. -/
theorem additiveFourAP_dtzPattern013
    {G : Type*} [AddCommGroup G] (x d : G) (hd : d ≠ 0) :
    DTZWeightedAdditiveThreePointPattern 4 2 1
      x (x + 3 • d) (x + d) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by abel, ?_⟩
  rintro ⟨h03, h31⟩
  have hzero : 3 • d = 0 := by
    apply add_left_cancel (a := x)
    simpa using h03.symm
  have heq : 3 • d = d := add_left_cancel h31
  exact hd (heq.symm.trans hzero)

/-- Cyclic positions `0,2,3`, ordered `(x0,x3,x2)`, give the DTZ
`(1,2)` pattern. -/
theorem additiveFourAP_dtzPattern023
    {G : Type*} [AddCommGroup G] (x d : G) (hd : d ≠ 0) :
    DTZWeightedAdditiveThreePointPattern 4 1 2
      x (x + 3 • d) (x + 2 • d) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by abel, ?_⟩
  rintro ⟨_h03, h32⟩
  have hthree : 3 • d = 2 • d := add_left_cancel h32
  apply hd
  calc
    d = 3 • d - 2 • d := by abel
    _ = 0 := by rw [hthree, sub_self]

/-- Avoidance of cyclic/group-valued DTZ `4`-patterns excludes every
three-equal colour pattern on a nonzero-step standard four-term AP. -/
theorem dtz4AdditivePatternAvoidance_noThreeEqual
    {G C : Type*} [AddCommGroup G]
    (colour : G → C)
    (havoid : AvoidsMonochromaticDTZAdditiveKPatterns 4 colour) :
    ∀ x d : G, d ≠ 0 →
      NoThreeEqual4
        (colour x) (colour (x + d))
        (colour (x + 2 • d)) (colour (x + 3 • d)) := by
  intro x d hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h01, h12⟩
    exact havoid x (x + 2 • d) (x + d)
      ⟨1, 1, additiveFourAP_dtzPattern012 x d hd⟩
      ⟨h01.trans h12, h12.symm⟩
  · rintro ⟨h01, h13⟩
    exact havoid x (x + 3 • d) (x + d)
      ⟨2, 1, additiveFourAP_dtzPattern013 x d hd⟩
      ⟨h01.trans h13, h13.symm⟩
  · rintro ⟨h02, h23⟩
    exact havoid x (x + 3 • d) (x + 2 • d)
      ⟨1, 2, additiveFourAP_dtzPattern023 x d hd⟩
      ⟨h02.trans h23, h23.symm⟩
  · rintro ⟨h12, h23⟩
    exact havoid (x + d) (x + 3 • d) (x + 2 • d)
      ⟨1, 1, additiveFourAP_dtzPattern123 x d hd⟩
      ⟨h12.trans h23, h23.symm⟩

end ErdosProblems.E160
