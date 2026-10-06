/-
The telescoping bound on the level sums with the Lipschitz hypothesis on the kernel required
only on a set `D` containing every coded point, as in the proof of
`thm:fixed-dimension-analyticity`, where `D` is a neighbourhood of `[0,1]` rather than a
disc of fixed radius.

* `norm_levelSum_succ_sub_le_of_mem`: `|Λ^{(m+1)} - Λ^{(m)}| ≤ 4 L B^{2m+2} ρ^m`.
-/
import BrownianImages.FixedDimension.LevelSums

namespace BrownianImages

open Finset

noncomputable section

/-- The increment of the level sums, with the kernel Lipschitz on a set `D` that contains
every coded point. -/
theorem norm_levelSum_succ_sub_le_of_mem (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (m : ℕ) {z : ℂ}
    {ρ B L : ℝ} {D : Set ℂ} (hb : ‖b z‖ ≤ 1) (hρ : max ‖a z‖ ‖b z‖ ≤ ρ)
    (hB : ‖z‖ + ‖1 - z‖ ≤ B)
    (hD : ∀ (n : ℕ) (ω : ℕ → Fin 2), cpointSeq (a z) (b z) n ω ∈ D) (hL0 : 0 ≤ L)
    (hL : ∀ x y x' y' : ℂ, x ∈ D → y ∈ D → x' ∈ D → y' ∈ D →
      ‖φ z x' y' - φ z x y‖ ≤ L * (‖x' - x‖ + ‖y' - y‖)) :
    ‖levelSum a b φ (m + 1) z - levelSum a b φ m z‖ ≤ 4 * L * B ^ (2 * m + 2) * ρ ^ m := by
  have hρ0 : 0 ≤ ρ := le_trans (le_max_left _ _) hρ |>.trans' (norm_nonneg _)
  have hB0 : 0 ≤ B := le_trans (add_nonneg (norm_nonneg _) (norm_nonneg _)) hB
  rw [levelSum_succ, levelSum_eq_with_letters, ← Finset.sum_sub_distrib]
  set W : (Fin m → Fin 2) → ℂ := fun u => weightSeq z m (extend u) with hW
  set X : (Fin m → Fin 2) → ℂ := fun u => cpointSeq (a z) (b z) m (extend u) with hX
  set Rr : (Fin m → Fin 2) → ℂ := fun u => cratioSeq (a z) (b z) m (extend u) with hR
  have hinner : ∀ u v : Fin m → Fin 2,
      ‖(∑ i : Fin 2, ∑ j : Fin 2, letterWeight z i * letterWeight z j *
          φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j))
        - ∑ i : Fin 2, ∑ j : Fin 2, letterWeight z i * letterWeight z j * φ z (X u) (X v)‖
        ≤ B ^ 2 * (4 * L * ρ ^ m) := by
    intro u v
    rw [← Finset.sum_sub_distrib]
    have hpt : ∀ (w : Fin m → Fin 2) (i : Fin 2), X w + Rr w * cshiftOf (b z) i ∈ D := by
      intro w i
      have := hD (m + 1) (extend (Fin.snoc w i : Fin (m + 1) → Fin 2))
      rw [cpointSeq_extend_snoc] at this
      exact this
    have hpt0 : ∀ w : Fin m → Fin 2, X w ∈ D := fun w => hD m (extend w)
    have hinc : ∀ (w : Fin m → Fin 2) (i : Fin 2), ‖Rr w * cshiftOf (b z) i‖ ≤ 2 * ρ ^ m := by
      intro w i
      rw [norm_mul]
      calc ‖Rr w‖ * ‖cshiftOf (b z) i‖ ≤ ρ ^ m * 2 :=
            mul_le_mul ((norm_cratioSeq_le _ _ _ _).trans (pow_le_pow_left₀ (by positivity) hρ m))
              (norm_cshiftOf_le hb i) (norm_nonneg _) (by positivity)
        _ = 2 * ρ ^ m := by ring
    have hφ : ∀ i j : Fin 2,
        ‖φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j) - φ z (X u) (X v)‖
          ≤ 4 * L * ρ ^ m := by
      intro i j
      calc ‖φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j) - φ z (X u) (X v)‖
          ≤ L * (‖X u + Rr u * cshiftOf (b z) i - X u‖ + ‖X v + Rr v * cshiftOf (b z) j - X v‖) :=
            hL _ _ _ _ (hpt0 u) (hpt0 v) (hpt u i) (hpt v j)
        _ ≤ L * (2 * ρ ^ m + 2 * ρ ^ m) := by
            apply mul_le_mul_of_nonneg_left _ hL0
            simp only [add_sub_cancel_left]
            exact add_le_add (hinc u i) (hinc v j)
        _ = 4 * L * ρ ^ m := by ring
    calc ‖∑ i : Fin 2, (∑ j : Fin 2, letterWeight z i * letterWeight z j *
            φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j)
          - ∑ j : Fin 2, letterWeight z i * letterWeight z j * φ z (X u) (X v))‖
        ≤ ∑ i : Fin 2, ‖∑ j : Fin 2, letterWeight z i * letterWeight z j *
            φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j)
          - ∑ j : Fin 2, letterWeight z i * letterWeight z j * φ z (X u) (X v)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖letterWeight z i‖ * ‖letterWeight z j‖ * (4 * L * ρ ^ m) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [← mul_sub, norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left (hφ i j) (by positivity)
      _ = (∑ i : Fin 2, ‖letterWeight z i‖) * (∑ j : Fin 2, ‖letterWeight z j‖) * (4 * L * ρ ^ m) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ ≤ B ^ 2 * (4 * L * ρ ^ m) := by
          rw [sum_norm_letterWeight]
          have : (‖z‖ + ‖1 - z‖) * (‖z‖ + ‖1 - z‖) ≤ B ^ 2 := by
            rw [pow_two]; exact mul_le_mul hB hB (by positivity) hB0
          exact mul_le_mul_of_nonneg_right this (by positivity)
  calc ‖∑ u, (∑ v, W u * W v * ∑ i, ∑ j, letterWeight z i * letterWeight z j *
          φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j)
        - ∑ v, W u * W v * ∑ i, ∑ j, letterWeight z i * letterWeight z j * φ z (X u) (X v))‖
      ≤ ∑ u, ∑ v, ‖W u‖ * ‖W v‖ * (B ^ 2 * (4 * L * ρ ^ m)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        rw [← mul_sub, norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hinner u v) (by positivity)
    _ = (∑ u, ‖W u‖) * (∑ v, ‖W v‖) * (B ^ 2 * (4 * L * ρ ^ m)) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
    _ ≤ B ^ m * B ^ m * (B ^ 2 * (4 * L * ρ ^ m)) := by
        simp only [hW, sum_norm_weightSeq]
        have : (‖z‖ + ‖1 - z‖) ^ m ≤ B ^ m := pow_le_pow_left₀ (by positivity) hB m
        exact mul_le_mul_of_nonneg_right (mul_le_mul this this (by positivity) (by positivity))
          (by positivity)
    _ = 4 * L * B ^ (2 * m + 2) * ρ ^ m := by ring

end

end BrownianImages
