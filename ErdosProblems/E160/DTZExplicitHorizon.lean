import ErdosProblems.E160.DTZABABExplicit
import ErdosProblems.E160.DTZNoThreeExplicit
import ErdosProblems.E160.DTZExplicitParameters

/-!
# All-horizon explicit DTZ filters

This file specializes the exact mod-24 digit cores to the parameter choice
`p = 24 * 2^m + 1`, where `m` is the square-root logarithmic digit count of
the target horizon.
-/

namespace ErdosProblems.E160

/-- Explicit no-three-equal factor on the target horizon. -/
def horizonNoThreeMod24Colour (N n : ℕ) :
    NoThreeMod24Palette (aabbBase N) (aabbLowerDigits N) :=
  noThreeMod24Colour (aabbBase N) (aabbLowerDigits N) n

/-- The explicit no-three-equal factor works on every bounded integer
horizon. -/
theorem horizonNoThreeMod24Colour_isNoThreeEqualColouring (N : ℕ) :
    IsNoThreeEqualColouring (BoundedIntFourAP4 N)
      (horizonNoThreeMod24Colour N) := by
  intro n0 n1 n2 n3 hAP
  rcases hAP with ⟨hn0, hn1, hn2, hn3, hfour, hnontrivial⟩
  have hcover := explicitDTZ_horizon_cover N
  apply noThreeMod24Colour_isNoThreeEqualColouring
    (aabbBase N) (aabbLowerDigits N) n0 n1 n2 n3
  exact ⟨
    by simpa [noThreeMod24Base, explicitDTZBase] using hn0.trans_le hcover,
    by simpa [noThreeMod24Base, explicitDTZBase] using hn1.trans_le hcover,
    by simpa [noThreeMod24Base, explicitDTZBase] using hn2.trans_le hcover,
    by simpa [noThreeMod24Base, explicitDTZBase] using hn3.trans_le hcover,
    hfour, hnontrivial⟩

/-- Exact available size of the horizon no-three-equal palette. -/
theorem horizonNoThreeMod24Palette_card (N : ℕ) :
    Fintype.card
        (NoThreeMod24Palette (aabbBase N) (aabbLowerDigits N)) =
      explicitDTZPaletteBound
        (explicitDTZBase N) (aabbLowerDigits N) := by
  change Fintype.card
      (ABABMod24Palette (aabbBase N) (aabbLowerDigits N)) = _
  rw [ababMod24Palette_card]
  rfl

/-- The explicit horizon no-three-equal palette is discretely subpower. -/
theorem horizonNoThreeMod24Palette_card_pow_lt
    (N k : ℕ) (hk : 0 < k)
    (hN : 2 ^ (dtzABABSubpowerThreshold 8 11 0 k ^ 2) < N) :
    Fintype.card
        (NoThreeMod24Palette (aabbBase N) (aabbLowerDigits N)) ^ k < N := by
  rw [horizonNoThreeMod24Palette_card]
  exact explicitDTZPaletteBound_pow_lt N k hk hN

/-- Explicit ABAB factor on the target horizon. -/
def horizonABABMod24Colour (N n : ℕ) :
    ABABMod24Palette (aabbBase N) (aabbLowerDigits N) :=
  finiteABABMod24Colour (aabbBase N) (aabbLowerDigits N) n

/-- The explicit ABAB factor works on every bounded integer horizon. -/
theorem horizonABABMod24Colour_isABABFreeColouring (N : ℕ) :
    IsABABFreeColouring (BoundedIntFourAP4 N)
      (horizonABABMod24Colour N) := by
  intro n0 n1 n2 n3 hAP
  rcases hAP with ⟨hn0, hn1, hn2, hn3, hfour, hnontrivial⟩
  have hcover := explicitDTZ_horizon_cover N
  exact finiteABABMod24Colour_abab_free
    (aabbBase N) (aabbLowerDigits N) n0 n1 n2 n3
    (by simpa [ababMod24Base, explicitDTZBase] using hn0.trans_le hcover)
    (by simpa [ababMod24Base, explicitDTZBase] using hn1.trans_le hcover)
    (by simpa [ababMod24Base, explicitDTZBase] using hn2.trans_le hcover)
    (by simpa [ababMod24Base, explicitDTZBase] using hn3.trans_le hcover)
    hfour hnontrivial

/-- Exact available size of the horizon ABAB palette. -/
theorem horizonABABMod24Palette_card (N : ℕ) :
    Fintype.card
        (ABABMod24Palette (aabbBase N) (aabbLowerDigits N)) =
      explicitDTZPaletteBound
        (explicitDTZBase N) (aabbLowerDigits N) := by
  rw [ababMod24Palette_card]
  rfl

/-- The explicit horizon ABAB palette is discretely subpower. -/
theorem horizonABABMod24Palette_card_pow_lt
    (N k : ℕ) (hk : 0 < k)
    (hN : 2 ^ (dtzABABSubpowerThreshold 8 11 0 k ^ 2) < N) :
    Fintype.card
        (ABABMod24Palette (aabbBase N) (aabbLowerDigits N)) ^ k < N := by
  rw [horizonABABMod24Palette_card]
  exact explicitDTZPaletteBound_pow_lt N k hk hN

end ErdosProblems.E160
