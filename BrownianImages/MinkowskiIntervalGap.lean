/-
Ordering the separated first-level time intervals.

`System.IntervalSeparated` is stated symmetrically through an absolute-distance
lower bound.  The Brownian overlap argument needs an oriented form: for two
different indices, one full affine copy of `[0,1]` lies to the left of the
other, with at least the same gap.  This file supplies that deterministic
conversion.
-/
import BrownianImages.MinkowskiSystem

namespace BrownianImages

open Set

namespace System

variable {iota : Type*} [Fintype iota] (S : System iota)

/-- The left endpoint of a first-level interval is nonnegative. -/
theorem shift_nonneg_of_mapsTo (i : iota) : 0 ≤ S.shift i := by
  simpa [System.map] using
    (S.mapsTo i (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)).1

/-- The right endpoint of a first-level interval is at most one. -/
theorem ratio_add_shift_le_one (i : iota) : S.ratio i + S.shift i ≤ 1 := by
  simpa [System.map] using
    (S.mapsTo i (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)).2

/-- The affine first-level map sends the unit interval exactly to the interval
between its two endpoints. -/
theorem image_map_Icc (i : iota) :
    S.map i '' Set.Icc (0 : ℝ) 1 =
      Set.Icc (S.shift i) (S.ratio i + S.shift i) := by
  have hmono : StrictMono (S.map i) := by
    intro x y hxy
    unfold System.map
    nlinarith [S.ratio_pos i]
  simpa [System.map] using
    (S.continuous_map i).image_Icc_of_strictMono
      (a := (0 : ℝ)) (b := 1) hmono

/-- Oriented version of strong separation on the unit interval.  One of the
two first-level intervals precedes the other, and their endpoint gap is at
least `rho`. -/
theorem StronglySeparated.firstLevel_interval_order
    {rho : ℝ} (hsep : S.StronglySeparated (Set.Icc (0 : ℝ) 1) rho)
    {i j : iota} (hij : i ≠ j) :
    S.ratio i + S.shift i + rho ≤ S.shift j ∨
      S.ratio j + S.shift j + rho ≤ S.shift i := by
  rcases le_total (S.shift i) (S.shift j) with hshift | hshift
  · left
    have hend : S.ratio i + S.shift i < S.shift j := by
      by_contra hnot
      have hjle : S.shift j ≤ S.ratio i + S.shift i := le_of_not_gt hnot
      let x : ℝ := (S.shift j - S.shift i) / S.ratio i
      have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr hshift) (S.ratio_pos i).le
      have hx1 : x ≤ 1 := by
        rw [div_le_one (S.ratio_pos i)]
        linarith
      have hzero := hsep.2 i j hij x ⟨hx0, hx1⟩ 0 (by norm_num)
      have hmaps : S.map i x = S.map j 0 := by
        unfold System.map x
        field_simp [ne_of_gt (S.ratio_pos i)]
        ring
      rw [hmaps, sub_self, abs_zero] at hzero
      linarith [hsep.1]
    have hgap := hsep.2 i j hij 1 (by norm_num) 0 (by norm_num)
    have hsign : S.map i 1 - S.map j 0 ≤ 0 := by
      simp only [System.map]
      linarith
    rw [abs_of_nonpos hsign] at hgap
    simp only [System.map] at hgap
    linarith
  · right
    have hend : S.ratio j + S.shift j < S.shift i := by
      by_contra hnot
      have hile : S.shift i ≤ S.ratio j + S.shift j := le_of_not_gt hnot
      let x : ℝ := (S.shift i - S.shift j) / S.ratio j
      have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr hshift) (S.ratio_pos j).le
      have hx1 : x ≤ 1 := by
        rw [div_le_one (S.ratio_pos j)]
        linarith
      have hzero := hsep.2 j i hij.symm x ⟨hx0, hx1⟩ 0 (by norm_num)
      have hmaps : S.map j x = S.map i 0 := by
        unfold System.map x
        field_simp [ne_of_gt (S.ratio_pos j)]
        ring
      rw [hmaps, sub_self, abs_zero] at hzero
      linarith [hsep.1]
    have hgap := hsep.2 j i hij.symm 1 (by norm_num) 0 (by norm_num)
    have hsign : S.map j 1 - S.map i 0 ≤ 0 := by
      simp only [System.map]
      linarith
    rw [abs_of_nonpos hsign] at hgap
    simp only [System.map] at hgap
    linarith

/-- Every pair in an interval-separated system has the preceding oriented
description for one common positive gap. -/
theorem IntervalSeparated.exists_gap_and_pair_order
    (hsep : S.IntervalSeparated) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ i j : iota, i ≠ j →
      S.ratio i + S.shift i + rho ≤ S.shift j ∨
        S.ratio j + S.shift j + rho ≤ S.shift i := by
  obtain ⟨rho, hstrong⟩ := hsep
  exact ⟨rho, hstrong.1, fun _ _ hij =>
    hstrong.firstLevel_interval_order S hij⟩

end System

end BrownianImages
