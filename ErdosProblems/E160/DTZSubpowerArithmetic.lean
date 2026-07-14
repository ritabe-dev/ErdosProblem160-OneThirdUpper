import ErdosProblems.E160.AABBAsymptotics

/-!
# Subpower arithmetic for the explicit digit filters

This file proves the horizon-scale and palette estimates used by the explicit
E160 construction.
-/

namespace ErdosProblems.E160

/-- The square-root logarithmic scale used by the digit palettes. -/
def dtzABABScale (H : ℕ) : ℕ := aabbDigitCount H

theorem horizon_le_two_pow_dtzABABScale_sq (H : ℕ) :
    H ≤ 2 ^ (dtzABABScale H ^ 2) := by
  have hlog : H ≤ 2 ^ aabbCeilLog H :=
    Nat.le_pow_clog (by norm_num) H
  have hexponent : aabbCeilLog H ≤ dtzABABScale H ^ 2 := by
    simpa only [dtzABABScale] using aabbCeilLog_le_digitCount_sq H
  exact hlog.trans (Nat.pow_le_pow_right (by norm_num) hexponent)

/-- A threshold making a linear-in-square-root-log palette subpower. -/
def dtzABABSubpowerThreshold (A B t0 k : ℕ) : ℕ :=
  max (max t0 1) (2 * (A + B) * k)

/-- Explicit discrete subpower estimate for a palette of the displayed
size.  This is arithmetic only and has no colouring-existence hypothesis. -/
theorem dtzABABPalette_card_pow_lt
    (A B t0 H k : ℕ) (_hk : 0 < k)
    (hH : 2 ^ (dtzABABSubpowerThreshold A B t0 k ^ 2) < H) :
    Fintype.card
        (Fin (2 ^ (A * dtzABABScale H + B))) ^ k < H := by
  let q := aabbCeilLog H
  let s := Nat.sqrt (q - 1)
  let m := dtzABABScale H
  let T := dtzABABSubpowerThreshold A B t0 k
  have hthreshold : T ^ 2 < q := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num)).2
    simpa [T, q, aabbCeilLog] using hH
  have hT_sq : T ^ 2 ≤ q - 1 := by omega
  have hT_s : T ≤ s := by
    exact (Nat.le_sqrt').2 hT_sq
  have hs_one : 1 ≤ s := by
    have : 1 ≤ T := by
      simp [T, dtzABABSubpowerThreshold]
    omega
  have hm : m = s + 1 := by
    simp [m, s, q, dtzABABScale, aabbDigitCount]
  have hm_one : 1 ≤ m := by rw [hm]; omega
  have hm_two_s : m ≤ 2 * s := by rw [hm]; omega
  have hcoefficient : 2 * (A + B) * k ≤ s := by
    have : 2 * (A + B) * k ≤ T := by
      simp [T, dtzABABSubpowerThreshold]
    exact this.trans hT_s
  have hlinear : A * m + B ≤ (A + B) * m := by
    have hB : B ≤ B * m := by
      calc
        B = B * 1 := by simp
        _ ≤ B * m := Nat.mul_le_mul_left B hm_one
    calc
      A * m + B ≤ A * m + B * m := Nat.add_le_add_left hB (A * m)
      _ = (A + B) * m := by ring
  have hexponent : (A * m + B) * k ≤ q - 1 := by
    calc
      (A * m + B) * k ≤ ((A + B) * m) * k :=
        Nat.mul_le_mul_right k hlinear
      _ ≤ ((A + B) * (2 * s)) * k := by gcongr
      _ = (2 * (A + B) * k) * s := by ring
      _ ≤ s * s := Nat.mul_le_mul_right s hcoefficient
      _ = s ^ 2 := by ring
      _ ≤ q - 1 := by simpa [s, pow_two] using Nat.sqrt_le (q - 1)
  have hH_one : 1 < H := by
    have hone : 1 ≤ 2 ^ (T ^ 2) :=
      Nat.one_le_pow (T ^ 2) 2 (by norm_num)
    have hpowlt : 2 ^ (T ^ 2) < H := by simpa [T] using hH
    omega
  simp only [Fintype.card_fin]
  calc
    (2 ^ (A * dtzABABScale H + B)) ^ k =
        2 ^ ((A * m + B) * k) := by rw [pow_mul]
    _ ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) hexponent
    _ < H := by
      simpa [q, aabbCeilLog] using
        (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hH_one)

end ErdosProblems.E160
