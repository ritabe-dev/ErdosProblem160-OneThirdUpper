import ErdosProblems.E160.Problem

/-!
# E160 source-convention bridge

This file separates the finite extremal conventions used for Erdős Problem
160.  A palette is represented by a map to `Fin k`; unused labels are allowed
in the maintained colouring formulation.  The primary text says "disjoint
sets" but does not separately state a nonemptiness condition.  Both readings
are treated here: the final section proves that the labelled and nonempty
(surjective) partition extrema coincide.  The restriction `k ≤ N` in the
surjective maximum is essential, since no surjection exists for `k > N`.

`SourceGoodPalette N k` says that every non-degenerate four-term progression
in `[1,N]` uses at least three labels.  `SourceEveryPartitionBad N k` is the
opposite statement in the original convention: every such labelled partition has a
four-term progression contained in at most two fibres.

The main theorem proves, for `4 ≤ N`, that the least good palette size is one
more than the largest bad palette size.  No asymptotic estimate for either
quantity is proved here.
-/

open Set

namespace ErdosProblems.E160

/-- The exact finite good-colouring predicate, stated independently of the
`sInf` used by `siteH`.  Palette labels need not all be used. -/
def SourceGoodPalette (N k : ℕ) : Prop :=
  ∃ colouring : Finset.Icc 1 N → Fin k,
    ∀ progression : Set ℕ,
      (progression ⊆ Finset.Icc 1 N ∧ IsFourTermAP progression) →
        3 ≤ (colouring '' {x | (x : ℕ) ∈ progression}).ncard

/-- The bad-partition predicate in the original convention. Every palette-labelled
partition has a four-term progression whose points occupy at most two
fibres.  This formulation permits unused labels and so is not a surjectivity
claim about the colouring. -/
def SourceEveryPartitionBad (N k : ℕ) : Prop :=
  ∀ colouring : Finset.Icc 1 N → Fin k,
    ∃ progression : Set ℕ,
      progression ⊆ Finset.Icc 1 N ∧ IsFourTermAP progression ∧
        (colouring '' {x | (x : ℕ) ∈ progression}).ncard ≤ 2

/-- The palette-labelled version of the original extremal convention: the
largest palette size for which every labelled partition is bad.  The theorem
below supplies nonemptiness and boundedness of this set when `4 ≤ N`. -/
noncomputable def sourceOriginalH (N : ℕ) : ℕ :=
  sSup {k | SourceEveryPartitionBad N k}

/-- `siteH` is the infimum of the finite good-colouring predicate. -/
theorem siteH_eq_sInf_sourceGoodPalette (N : ℕ) :
    siteH N = sInf {k | SourceGoodPalette N k} := by
  rfl

/-- A non-degenerate four-term progression has exactly four points. -/
theorem isFourTermAP_ncard {progression : Set ℕ}
    (hprogression : IsFourTermAP progression) :
    progression.ncard = 4 := by
  rcases hprogression with ⟨a, d, hd, rfl⟩
  let f : Fin 4 → ℕ := fun i ↦ a + i.val * d
  have hrange :
      {x | ∃ i : ℕ, i < 4 ∧ x = a + i * d} = Set.range f := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
  rw [hrange, Set.ncard_range_of_injective]
  · exact Nat.card_fin 4
  · intro i j hij
    apply Fin.ext
    apply Nat.eq_of_mul_eq_mul_right hd
    exact Nat.add_left_cancel hij

/-- The explicit source bad predicate is exactly the negation of existence of
a good colouring. -/
theorem sourceEveryPartitionBad_iff_not_good (N k : ℕ) :
    SourceEveryPartitionBad N k ↔ ¬ SourceGoodPalette N k := by
  constructor
  · intro hbad hgood
    rcases hgood with ⟨colouring, hcolouring⟩
    rcases hbad colouring with ⟨progression, hsub, hAP, hcard⟩
    have hthree := hcolouring progression ⟨hsub, hAP⟩
    omega
  · intro hnotgood colouring
    by_contra hcounterexample
    apply hnotgood
    refine ⟨colouring, ?_⟩
    intro progression hprogression
    by_contra hcard
    have hle :
        (colouring '' {x | (x : ℕ) ∈ progression}).ncard ≤ 2 := by
      omega
    exact hcounterexample
      ⟨progression, hprogression.1, hprogression.2, hle⟩

/-- Good colourings are upward closed in the available palette size. -/
theorem sourceGoodPalette_mono {N k l : ℕ} (hkl : k ≤ l)
    (hgood : SourceGoodPalette N k) :
    SourceGoodPalette N l := by
  rcases hgood with ⟨colouring, hcolouring⟩
  let largerColouring : Finset.Icc 1 N → Fin l :=
    fun x ↦ Fin.castLE hkl (colouring x)
  refine ⟨largerColouring, ?_⟩
  intro progression hprogression
  let points : Set (Finset.Icc 1 N) :=
    {x | (x : ℕ) ∈ progression}
  have himage :
      largerColouring '' points =
        Fin.castLE hkl '' (colouring '' points) := by
    simp only [largerColouring, points, Set.image_image]
  rw [himage,
    Set.ncard_image_of_injective _ (Fin.castLE_injective hkl)]
  exact hcolouring progression hprogression

/-- Bad palette sizes form an initial segment. -/
theorem sourceEveryPartitionBad_anti {N k l : ℕ} (hkl : k ≤ l)
    (hbad : SourceEveryPartitionBad N l) :
    SourceEveryPartitionBad N k := by
  rw [sourceEveryPartitionBad_iff_not_good] at hbad ⊢
  exact fun hgood ↦ hbad (sourceGoodPalette_mono hkl hgood)

/-- Every horizon has a good colouring with `N+1` available labels: colour an
integer by itself. -/
theorem sourceGoodPalette_succ (N : ℕ) :
    SourceGoodPalette N (N + 1) := by
  let colouring : Finset.Icc 1 N → Fin (N + 1) := fun x ↦
    ⟨x.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp x.property).2⟩
  have hcolouring : Function.Injective colouring := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Fin.val hxy
  refine ⟨colouring, ?_⟩
  intro progression hprogression
  let points : Set (Finset.Icc 1 N) :=
    {x | (x : ℕ) ∈ progression}
  have hvalImage : Subtype.val '' points = progression := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxInterval := hprogression.1 hx
      exact ⟨⟨x, hxInterval⟩, hx, rfl⟩
  have hpoints : points.ncard = 4 := by
    have hvalCard :=
      Set.ncard_image_of_injective points Subtype.val_injective
    rw [hvalImage, isFourTermAP_ncard hprogression.2] at hvalCard
    exact hvalCard.symm
  have hcolourCard :=
    Set.ncard_image_of_injective points hcolouring
  rw [hcolourCard, hpoints]
  omega

/-- The least good palette size is itself good because the good-palette set is
nonempty. -/
theorem sourceGoodPalette_siteH (N : ℕ) :
    SourceGoodPalette N (siteH N) := by
  rw [siteH_eq_sInf_sourceGoodPalette]
  have hnonempty : Set.Nonempty {k | SourceGoodPalette N k} := by
    refine ⟨N + 1, ?_⟩
    exact sourceGoodPalette_succ N
  exact Nat.sInf_mem hnonempty

/-- Minimality of the site convention. -/
theorem siteH_le_of_sourceGoodPalette {N k : ℕ}
    (hgood : SourceGoodPalette N k) :
    siteH N ≤ k := by
  rw [siteH_eq_sInf_sourceGoodPalette]
  exact Nat.sInf_le hgood

/-- The source bad palette sizes are exactly those strictly below the site
threshold. -/
theorem sourceEveryPartitionBad_iff_lt_siteH (N k : ℕ) :
    SourceEveryPartitionBad N k ↔ k < siteH N := by
  rw [sourceEveryPartitionBad_iff_not_good]
  constructor
  · intro hnotgood
    by_contra hnotlt
    exact hnotgood
      (sourceGoodPalette_mono (Nat.le_of_not_gt hnotlt)
        (sourceGoodPalette_siteH N))
  · intro hlt hgood
    have := siteH_le_of_sourceGoodPalette hgood
    omega

/-- For `N ≥ 4`, two labels cannot be good: the progression
`{1,2,3,4}` already uses at most the whole palette. -/
theorem three_le_siteH {N : ℕ} (hN : 4 ≤ N) :
    3 ≤ siteH N := by
  have hgood := sourceGoodPalette_siteH N
  rcases hgood with ⟨colouring, hcolouring⟩
  let progression : Set ℕ :=
    {x | ∃ i : ℕ, i < 4 ∧ x = 1 + i * 1}
  have hsub : progression ⊆ Finset.Icc 1 N := by
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hAP : IsFourTermAP progression := by
    exact ⟨1, 1, by omega, rfl⟩
  have hthree := hcolouring progression ⟨hsub, hAP⟩
  have hpalette := Set.ncard_le_card
    (colouring '' {x | (x : ℕ) ∈ progression})
  rw [Nat.card_fin] at hpalette
  omega

/-- At `N ≥ 4`, the bad-palette set is nonempty. -/
theorem sourceBadSet_nonempty {N : ℕ} (hN : 4 ≤ N) :
    Set.Nonempty {k | SourceEveryPartitionBad N k} := by
  refine ⟨2, ?_⟩
  change SourceEveryPartitionBad N 2
  rw [sourceEveryPartitionBad_iff_lt_siteH]
  have := three_le_siteH hN
  omega

/-- At every horizon, the bad-palette set is bounded above by the least good
palette size. -/
theorem sourceBadSet_bddAbove (N : ℕ) :
    BddAbove {k | SourceEveryPartitionBad N k} := by
  refine ⟨siteH N, ?_⟩
  intro k hk
  change SourceEveryPartitionBad N k at hk
  rw [sourceEveryPartitionBad_iff_lt_siteH] at hk
  omega

/-- The source extremal value is itself a bad palette size for `N ≥ 4`. -/
theorem sourceOriginalH_bad {N : ℕ} (hN : 4 ≤ N) :
    SourceEveryPartitionBad N (sourceOriginalH N) := by
  exact Nat.sSup_mem (sourceBadSet_nonempty hN) (sourceBadSet_bddAbove N)

/-- Exact comparison in predecessor form. -/
theorem sourceOriginalH_eq_siteH_sub_one {N : ℕ} (hN : 4 ≤ N) :
    sourceOriginalH N = siteH N - 1 := by
  have hsite : 3 ≤ siteH N := three_le_siteH hN
  have horiginalBad := sourceOriginalH_bad hN
  have horiginalLt : sourceOriginalH N < siteH N :=
    (sourceEveryPartitionBad_iff_lt_siteH N (sourceOriginalH N)).mp
      horiginalBad
  have hpredBad : SourceEveryPartitionBad N (siteH N - 1) := by
    rw [sourceEveryPartitionBad_iff_lt_siteH]
    omega
  have hpredLe : siteH N - 1 ≤ sourceOriginalH N :=
    le_csSup (sourceBadSet_bddAbove N) hpredBad
  omega

/-- The maintained least-good convention is exactly one more than the
palette-labelled maximum-bad convention for every nontrivial horizon
`N ≥ 4`. -/
theorem siteH_eq_sourceOriginalH_add_one {N : ℕ} (hN : 4 ≤ N) :
    siteH N = sourceOriginalH N + 1 := by
  rw [sourceOriginalH_eq_siteH_sub_one hN]
  have := three_le_siteH hN
  omega

/-! ## Nonempty/surjective partition convention -/

/-- A good palette which uses every displayed colour.  Its fibres are exactly
the nonempty labelled parts of a partition of `[1,N]`. -/
def SourceSurjectiveGoodPalette (N k : ℕ) : Prop :=
  ∃ colouring : Finset.Icc 1 N → Fin k,
    Function.Surjective colouring ∧
    ∀ progression : Set ℕ,
      (progression ⊆ Finset.Icc 1 N ∧ IsFourTermAP progression) →
        3 ≤ (colouring '' {x | (x : ℕ) ∈ progression}).ncard

/-- Compress an arbitrary good colouring to the finite set of colours it
actually uses.  The compressed colouring is surjective and uses no more
labels. -/
theorem sourceGoodPalette_compress_surjective {N k : ℕ}
    (hgood : SourceGoodPalette N k) :
    ∃ l : ℕ, l ≤ k ∧ SourceSurjectiveGoodPalette N l := by
  classical
  rcases hgood with ⟨colouring, hcolouring⟩
  let R : Set (Fin k) := Set.range colouring
  letI : Fintype R := Fintype.ofFinite R
  let l := Fintype.card R
  let e : R ≃ Fin l := Fintype.equivFin R
  let compressed : Finset.Icc 1 N → Fin l := fun x ↦
    e ⟨colouring x, ⟨x, rfl⟩⟩
  let forget : Fin l → Fin k := fun j ↦ (e.symm j).val
  have hforget (x : Finset.Icc 1 N) :
      forget (compressed x) = colouring x := by
    simp [forget, compressed]
  have hsurj : Function.Surjective compressed := by
    intro j
    rcases (e.symm j).property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      compressed x = e ⟨colouring x, ⟨x, rfl⟩⟩ := rfl
      _ = e (e.symm j) := by
        apply congrArg e
        exact Subtype.ext hx
      _ = j := e.apply_symm_apply j
  have hlk : l ≤ k := by
    simpa [l] using
      (Fintype.card_le_of_injective Subtype.val
        (Subtype.val_injective : Function.Injective (fun x : R ↦ x.val)))
  refine ⟨l, hlk, compressed, hsurj, ?_⟩
  intro progression hprogression
  let points : Set (Finset.Icc 1 N) :=
    {x | (x : ℕ) ∈ progression}
  have hsubset :
      colouring '' points ⊆ forget '' (compressed '' points) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨compressed x, ⟨x, hx, rfl⟩, hforget x⟩
  have hleft : 3 ≤ (colouring '' points).ncard :=
    hcolouring progression hprogression
  have hmiddle :
      (colouring '' points).ncard ≤
        (forget '' (compressed '' points)).ncard :=
    Set.ncard_le_ncard hsubset
  have hright :
      (forget '' (compressed '' points)).ncard ≤
        (compressed '' points).ncard :=
    Set.ncard_image_le
  exact hleft.trans (hmiddle.trans hright)

/-- A palette of minimal size cannot contain an unused label. -/
theorem sourceSurjectiveGoodPalette_siteH (N : ℕ) :
    SourceSurjectiveGoodPalette N (siteH N) := by
  obtain ⟨l, hl, hsurjGood⟩ :=
    sourceGoodPalette_compress_surjective (sourceGoodPalette_siteH N)
  have hsite_le : siteH N ≤ l := by
    rcases hsurjGood with ⟨colouring, _hsurj, hgood⟩
    exact siteH_le_of_sourceGoodPalette ⟨colouring, hgood⟩
  have heq : l = siteH N := by omega
  simpa [heq] using hsurjGood

theorem card_Icc_one_N (N : ℕ) :
    Fintype.card (Finset.Icc 1 N) = N := by
  rw [Fintype.card_coe, Nat.card_Icc]
  omega

/-- Split one duplicated fibre and give one of its points a fresh colour. -/
theorem sourceSurjectiveGoodPalette_succ {N k : ℕ}
    (hkN : k < N) (hgood : SourceSurjectiveGoodPalette N k) :
    SourceSurjectiveGoodPalette N (k + 1) := by
  classical
  rcases hgood with ⟨colouring, hsurj, hcolouring⟩
  have hninj : ¬ Function.Injective colouring := by
    intro hinj
    have hcard := Fintype.card_le_of_injective colouring hinj
    rw [card_Icc_one_N, Fintype.card_fin] at hcard
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hninj
  let refined : Finset.Icc 1 N → Fin (k + 1) := fun z ↦
    if z = x then Fin.last k else Fin.castSucc (colouring z)
  let collapse : Fin (k + 1) → Fin k :=
    Fin.lastCases (colouring x) (fun i ↦ i)
  have hcollapse (z : Finset.Icc 1 N) :
      collapse (refined z) = colouring z := by
    by_cases hz : z = x
    · subst z
      simp [collapse, refined]
    · simp [collapse, refined, hz]
  have hrefinedSurj : Function.Surjective refined := by
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · exact ⟨x, by simp [refined]⟩
    · rcases hsurj i with ⟨z, hz⟩
      by_cases hzx : z = x
      · refine ⟨y, ?_⟩
        have hyx : y ≠ x := Ne.symm hne
        have hcy : colouring y = i := by
          rw [← hxy, ← hzx, hz]
        simp [refined, hyx, hcy]
      · exact ⟨z, by simp [refined, hzx, hz]⟩
  refine ⟨refined, hrefinedSurj, ?_⟩
  intro progression hprogression
  let points : Set (Finset.Icc 1 N) :=
    {z | (z : ℕ) ∈ progression}
  have hsubset :
      colouring '' points ⊆ collapse '' (refined '' points) := by
    intro c hc
    rcases hc with ⟨z, hz, rfl⟩
    exact ⟨refined z, ⟨z, hz, rfl⟩, hcollapse z⟩
  have hleft : 3 ≤ (colouring '' points).ncard :=
    hcolouring progression hprogression
  have hmiddle :
      (colouring '' points).ncard ≤
        (collapse '' (refined '' points)).ncard :=
    Set.ncard_le_ncard hsubset
  have hright :
      (collapse '' (refined '' points)).ncard ≤
        (refined '' points).ncard :=
    Set.ncard_image_le
  exact hleft.trans (hmiddle.trans hright)

/-- Repeated splitting gives a surjective good colouring with every palette
size between the least good size and the number of points. -/
theorem sourceSurjectiveGoodPalette_mono {N k l : ℕ}
    (hkl : k ≤ l) (hlN : l ≤ N)
    (hgood : SourceSurjectiveGoodPalette N k) :
    SourceSurjectiveGoodPalette N l := by
  induction l, hkl using Nat.le_induction with
  | base => exact hgood
  | succ l hkl ih =>
      exact sourceSurjectiveGoodPalette_succ (by omega) (ih (by omega))

/-- Every partition into exactly `k` nonempty labelled parts is bad. -/
def SourceEverySurjectivePartitionBad (N k : ℕ) : Prop :=
  ∀ colouring : Finset.Icc 1 N → Fin k,
    Function.Surjective colouring →
    ∃ progression : Set ℕ,
      progression ⊆ Finset.Icc 1 N ∧ IsFourTermAP progression ∧
        (colouring '' {x | (x : ℕ) ∈ progression}).ncard ≤ 2

/-- Literal nonempty-part reading of the primary phrase "two of them": the
two displayed fibres are required to be distinct, and their union contains
the progression. -/
def SourceEverySurjectivePartitionBadDistinctTwo (N k : ℕ) : Prop :=
  ∀ colouring : Finset.Icc 1 N → Fin k,
    Function.Surjective colouring →
    ∃ i j : Fin k, i ≠ j ∧
      ∃ progression : Set ℕ,
        progression ⊆ Finset.Icc 1 N ∧ IsFourTermAP progression ∧
          colouring '' {x | (x : ℕ) ∈ progression} ⊆ ({i, j} : Set (Fin k))

/-- In a palette with at least two labels, every set of at most two labels is
contained in a pair of distinct labels. -/
theorem exists_distinct_pair_cover_of_ncard_le_two
    {k : ℕ} (hk : 2 ≤ k) (S : Set (Fin k)) (hS : S.ncard ≤ 2) :
    ∃ i j : Fin k, i ≠ j ∧ S ⊆ ({i, j} : Set (Fin k)) := by
  classical
  have hcard : 1 < Fintype.card (Fin k) := by
    simp only [Fintype.card_fin]
    omega
  have hcases : S.ncard = 0 ∨ S.ncard = 1 ∨ S.ncard = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · have hSempty : S = ∅ :=
      (Set.ncard_eq_zero (s := S) (Set.toFinite S)).mp hzero
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hcard
    exact ⟨i, j, hij, by simp [hSempty]⟩
  · obtain ⟨i, hi⟩ := Set.ncard_eq_one.mp hone
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    refine ⟨i, j, Ne.symm hji, ?_⟩
    simp [hi]
  · obtain ⟨i, j, hij, hSij⟩ := Set.ncard_eq_two.mp htwo
    exact ⟨i, j, hij, by simp [hSij]⟩

/-- For every relevant palette size, the at-most-two-colours predicate is
exactly the literal distinct-two-fibre union predicate. -/
theorem sourceEverySurjectivePartitionBadDistinctTwo_iff
    (N k : ℕ) (hk : 2 ≤ k) :
    SourceEverySurjectivePartitionBadDistinctTwo N k ↔
      SourceEverySurjectivePartitionBad N k := by
  constructor
  · intro hliteral colouring hsurj
    rcases hliteral colouring hsurj with
      ⟨i, j, hij, progression, hsub, hAP, hcover⟩
    refine ⟨progression, hsub, hAP, ?_⟩
    calc
      (colouring '' {x | (x : ℕ) ∈ progression}).ncard ≤
          ({i, j} : Set (Fin k)).ncard := Set.ncard_le_ncard hcover
      _ = 2 := Set.ncard_pair hij
  · intro hbad colouring hsurj
    rcases hbad colouring hsurj with ⟨progression, hsub, hAP, hcard⟩
    obtain ⟨i, j, hij, hcover⟩ :=
      exists_distinct_pair_cover_of_ncard_le_two hk
        (colouring '' {x | (x : ℕ) ∈ progression}) hcard
    exact ⟨i, j, hij, progression, hsub, hAP, hcover⟩

theorem sourceEverySurjectivePartitionBad_iff_not_good (N k : ℕ) :
    SourceEverySurjectivePartitionBad N k ↔
      ¬ SourceSurjectiveGoodPalette N k := by
  constructor
  · intro hbad hgood
    rcases hgood with ⟨colouring, hsurj, hcolouring⟩
    rcases hbad colouring hsurj with ⟨progression, hsub, hAP, hcard⟩
    have hthree := hcolouring progression ⟨hsub, hAP⟩
    omega
  · intro hnotgood colouring hsurj
    by_contra hcounterexample
    apply hnotgood
    refine ⟨colouring, hsurj, ?_⟩
    intro progression hprogression
    by_contra hcard
    have hle :
        (colouring '' {x | (x : ℕ) ∈ progression}).ncard ≤ 2 := by
      omega
    exact hcounterexample
      ⟨progression, hprogression.1, hprogression.2, hle⟩

theorem sourceEverySurjectivePartitionBad_iff_lt_siteH
    (N k : ℕ) (hkN : k ≤ N) :
    SourceEverySurjectivePartitionBad N k ↔ k < siteH N := by
  rw [sourceEverySurjectivePartitionBad_iff_not_good]
  constructor
  · intro hnotgood
    by_contra hnotlt
    exact hnotgood <| sourceSurjectiveGoodPalette_mono
      (Nat.le_of_not_gt hnotlt) hkN (sourceSurjectiveGoodPalette_siteH N)
  · intro hlt hsurjGood
    rcases hsurjGood with ⟨colouring, _hsurj, hgood⟩
    have hsite := siteH_le_of_sourceGoodPalette ⟨colouring, hgood⟩
    omega

theorem siteH_le_N (N : ℕ) : siteH N ≤ N := by
  rcases sourceSurjectiveGoodPalette_siteH N with
    ⟨colouring, hsurj, _hgood⟩
  have hcard := Fintype.card_le_of_surjective colouring hsurj
  rw [Fintype.card_fin, card_Icc_one_N] at hcard
  exact hcard

/-- The nonempty-part maximum.  The `k ≤ N` restriction removes the vacuous
truth caused by asking for surjections onto palettes larger than the interval. -/
noncomputable def sourceSurjectiveOriginalH (N : ℕ) : ℕ :=
  sSup {k | k ≤ N ∧ SourceEverySurjectivePartitionBad N k}

theorem sourceSurjectiveBadSet_eq_sourceBadSet (N : ℕ) :
    {k | k ≤ N ∧ SourceEverySurjectivePartitionBad N k} =
      {k | SourceEveryPartitionBad N k} := by
  ext k
  simp only [Set.mem_setOf_eq]
  rw [sourceEveryPartitionBad_iff_lt_siteH]
  constructor
  · rintro ⟨hkN, hbad⟩
    exact (sourceEverySurjectivePartitionBad_iff_lt_siteH N k hkN).mp hbad
  · intro hk
    have hkN : k ≤ N := by
      have := siteH_le_N N
      omega
    exact ⟨hkN,
      (sourceEverySurjectivePartitionBad_iff_lt_siteH N k hkN).mpr hk⟩

/-- The palette-labelled and nonempty-part maximum-bad conventions agree for
every horizon. -/
theorem sourceSurjectiveOriginalH_eq_sourceOriginalH (N : ℕ) :
    sourceSurjectiveOriginalH N = sourceOriginalH N := by
  rw [sourceSurjectiveOriginalH, sourceOriginalH,
    sourceSurjectiveBadSet_eq_sourceBadSet]

/-- Under the strict nonempty-part reading of the primary wording, the same
predecessor relation holds. -/
theorem sourceSurjectiveOriginalH_eq_siteH_sub_one
    {N : ℕ} (hN : 4 ≤ N) :
    sourceSurjectiveOriginalH N = siteH N - 1 := by
  rw [sourceSurjectiveOriginalH_eq_sourceOriginalH,
    sourceOriginalH_eq_siteH_sub_one hN]

/-- Equivalently, the maintained least-good convention is one more than the
strict nonempty-part maximum-bad convention. -/
theorem siteH_eq_sourceSurjectiveOriginalH_add_one
    {N : ℕ} (hN : 4 ≤ N) :
    siteH N = sourceSurjectiveOriginalH N + 1 := by
  rw [sourceSurjectiveOriginalH_eq_sourceOriginalH]
  exact siteH_eq_sourceOriginalH_add_one hN

/-- The literal distinct-two-fibre statement has the same sharp threshold as
the maintained at-most-two-colours statement. -/
theorem sourceEverySurjectivePartitionBadDistinctTwo_iff_lt_siteH
    (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    SourceEverySurjectivePartitionBadDistinctTwo N k ↔ k < siteH N :=
  (sourceEverySurjectivePartitionBadDistinctTwo_iff N k hk).trans
    (sourceEverySurjectivePartitionBad_iff_lt_siteH N k hkN)

/-- For `N ≥ 4`, `sourceSurjectiveOriginalH N` is also the largest relevant
palette size satisfying the literal primary-source reading with two distinct
nonempty parts. -/
theorem sourceSurjectiveOriginalH_literal_distinct_two_characterization
    {N : ℕ} (hN : 4 ≤ N) :
    SourceEverySurjectivePartitionBadDistinctTwo N
        (sourceSurjectiveOriginalH N) ∧
      ∀ k, 2 ≤ k → k ≤ N →
        SourceEverySurjectivePartitionBadDistinctTwo N k →
          k ≤ sourceSurjectiveOriginalH N := by
  have hvalue := sourceSurjectiveOriginalH_eq_siteH_sub_one hN
  have hsite3 := three_le_siteH hN
  have hsiteN := siteH_le_N N
  have htwo : 2 ≤ sourceSurjectiveOriginalH N := by omega
  have hupper : sourceSurjectiveOriginalH N ≤ N := by omega
  constructor
  · apply (sourceEverySurjectivePartitionBadDistinctTwo_iff_lt_siteH
      N (sourceSurjectiveOriginalH N) htwo hupper).2
    omega
  · intro k hk2 hkN hliteral
    have hklt :=
      (sourceEverySurjectivePartitionBadDistinctTwo_iff_lt_siteH
        N k hk2 hkN).1 hliteral
    omega

end ErdosProblems.E160
