/-
Expectation-level assembly of the elementary tube-defect estimate.

The deterministic defect is bounded by the sum of all pairwise raw tube
overlaps in `MinkowskiTubeAlgebra`.  This file records the measure-theoretic
step needed in the probabilistic argument: pairwise integrability propagates
through the finite sum, makes the defect integrable, and permits integration
of the pointwise inequality.  No independence or Brownian input is used here.
-/
import BrownianImages.MinkowskiOverlapTranslation

namespace BrownianImages

open MeasureTheory

noncomputable section

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]
variable {P : Measure Omega} {F : iota → Omega → CompactPlane}

local instance : DecidableEq iota := Classical.decEq iota

/-- A pairwise raw-overlap sum is nonnegative. -/
theorem pairwiseTubeOverlapAreaSum_nonneg (r : ℝ) (G : iota → CompactPlane) :
    0 ≤ pairwiseTubeOverlapAreaSum r G := by
  classical
  unfold pairwiseTubeOverlapAreaSum orderedTubeOverlapAreaSum
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => tubeOverlapArea_nonneg r (G i) (G j)
  · norm_num

/-- Integrability of every distinct pair propagates to the ordered finite
overlap sum. -/
theorem integrable_orderedTubeOverlapAreaSum_of_pairwise
    {r : ℝ}
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P) :
    Integrable
      (fun omega => orderedTubeOverlapAreaSum r (fun i => F i omega)) P := by
  classical
  unfold orderedTubeOverlapAreaSum
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact hoverlap i j (Finset.ne_of_mem_erase hj).symm

/-- Integrability of every distinct pair propagates to the unordered finite
overlap sum. -/
theorem integrable_pairwiseTubeOverlapAreaSum_of_pairwise
    {r : ℝ}
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P) :
    Integrable
      (fun omega => pairwiseTubeOverlapAreaSum r (fun i => F i omega)) P := by
  unfold pairwiseTubeOverlapAreaSum
  simpa only [div_eq_mul_inv] using
    (integrable_orderedTubeOverlapAreaSum_of_pairwise hoverlap).mul_const
      (2 : ℝ)⁻¹

/-- Pairwise overlap integrability, together with measurability of the random
compact sets, implies integrability of their tube-mass defect. -/
theorem integrable_tubeDefect_of_pairwise_overlap
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, AEMeasurable (F i) P)
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P) :
    Integrable (fun omega => tubeDefect r (fun i => F i omega)) P := by
  have hpair := integrable_pairwiseTubeOverlapAreaSum_of_pairwise hoverlap
  refine Integrable.mono' hpair
    (aemeasurable_tubeDefect_of_forall hr hF).aestronglyMeasurable ?_
  filter_upwards with omega
  have hdefect := tubeDefect_nonneg hr (fun i => F i omega)
  have hpair_nonneg :=
    pairwiseTubeOverlapAreaSum_nonneg r (fun i => F i omega)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hdefect,
    abs_of_nonneg hpair_nonneg] using
      tubeDefect_le_pairwiseTubeOverlapAreaSum hr (fun i => F i omega)

/-- The pointwise multiple-counting inequality may be integrated once the
distinct pair overlaps are integrable. -/
theorem integral_tubeDefect_le_pairwiseTubeOverlapAreaSum
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, AEMeasurable (F i) P)
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P) :
    (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤
      ∫ omega, pairwiseTubeOverlapAreaSum r (fun i => F i omega) ∂P := by
  exact integral_mono
    (integrable_tubeDefect_of_pairwise_overlap hr hF hoverlap)
    (integrable_pairwiseTubeOverlapAreaSum_of_pairwise hoverlap)
    (fun omega =>
      tubeDefect_le_pairwiseTubeOverlapAreaSum hr (fun i => F i omega))

/-- The expectation of the unordered overlap sum is half the finite ordered
sum of the individual overlap expectations. -/
theorem integral_pairwiseTubeOverlapAreaSum_eq
    {r : ℝ}
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P) :
    (∫ omega, pairwiseTubeOverlapAreaSum r (fun i => F i omega) ∂P) =
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) / 2 := by
  classical
  unfold pairwiseTubeOverlapAreaSum orderedTubeOverlapAreaSum
  rw [integral_div, integral_finsetSum]
  · apply congrArg fun x : ℝ => x / 2
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    intro j hj
    exact hoverlap i j (Finset.ne_of_mem_erase hj).symm
  · intro i _
    apply integrable_finsetSum
    intro j hj
    exact hoverlap i j (Finset.ne_of_mem_erase hj).symm

/-- Fully expanded expectation form of the finite-pair defect estimate. -/
theorem integral_tubeDefect_le_half_sum_pairwise
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, AEMeasurable (F i) P)
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P) :
    (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) / 2 := by
  rw [← integral_pairwiseTubeOverlapAreaSum_eq hoverlap]
  exact integral_tubeDefect_le_pairwiseTubeOverlapAreaSum hr hF hoverlap

/-- A uniform bound for each distinct pair gives a uniform finite-family
defect bound.  The harmless factor `card iota ^ 2 / 2` avoids choosing an
ordering of the unordered pairs. -/
theorem integral_tubeDefect_le_card_sq_mul
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hF : ∀ i, AEMeasurable (F i) P)
    (hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P)
    (hbound : ∀ i j : iota, i ≠ j →
      (∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤ B) :
    (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤
      ((Fintype.card iota : ℝ) ^ 2 / 2) * B := by
  have hsum :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤
        (Fintype.card iota : ℝ) ^ 2 * B := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤
          ∑ _i : iota, ∑ _j : iota, B := by
            apply Finset.sum_le_sum
            intro i _
            calc
              (∑ j ∈ Finset.univ.erase i,
                  ∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤
                  ∑ _j ∈ Finset.univ.erase i, B := by
                    apply Finset.sum_le_sum
                    intro j hj
                    exact hbound i j (Finset.ne_of_mem_erase hj).symm
              _ ≤ ∑ _j : iota, B := by
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.erase_subset i Finset.univ) (fun _ _ _ => hB)
      _ = (Fintype.card iota : ℝ) ^ 2 * B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  calc
    (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) / 2 :=
      integral_tubeDefect_le_half_sum_pairwise hr hF hoverlap
    _ ≤ ((Fintype.card iota : ℝ) ^ 2 * B) / 2 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = ((Fintype.card iota : ℝ) ^ 2 / 2) * B := by ring

/-- Endpoint-shaped finite-family assembly at one radius.  Enlarging the
pairwise constant by the fixed factor
`max 1 ((card iota : ℝ) ^ 2 / 2)` makes the same bound control every pair and
the total multiple-counting defect. -/
theorem pairwise_overlap_and_defect_of_bound
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hF : ∀ i, AEMeasurable (F i) P)
    (hpair : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P ∧
      (∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤ B) :
    (∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P ∧
      (∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤
        max 1 ((Fintype.card iota : ℝ) ^ 2 / 2) * B) ∧
    Integrable (fun omega => tubeDefect r (fun i => F i omega)) P ∧
    (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤
      max 1 ((Fintype.card iota : ℝ) ^ 2 / 2) * B := by
  let D : ℝ := max 1 ((Fintype.card iota : ℝ) ^ 2 / 2)
  have hD_one : 1 ≤ D := le_max_left _ _
  have hD_card : (Fintype.card iota : ℝ) ^ 2 / 2 ≤ D := le_max_right _ _
  have hB_le : B ≤ D * B := by
    nlinarith
  have hoverlap : ∀ i j : iota, i ≠ j →
      Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P :=
    fun i j hij => (hpair i j hij).1
  refine ⟨fun i j hij => ⟨(hpair i j hij).1, (hpair i j hij).2.trans hB_le⟩,
    integrable_tubeDefect_of_pairwise_overlap hr hF hoverlap, ?_⟩
  calc
    (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤
        ((Fintype.card iota : ℝ) ^ 2 / 2) * B :=
      integral_tubeDefect_le_card_sq_mul hr hB hF hoverlap
        (fun i j hij => (hpair i j hij).2)
    _ ≤ D * B := mul_le_mul_of_nonneg_right hD_card hB

/-- Uniform-radius version of `pairwise_overlap_and_defect_of_bound`.  This is
the precise logical bridge from a uniform distinct-pair overlap estimate to
the pair-and-defect conjunction used by the tube-overlap theorem. -/
theorem exists_pairwise_overlap_and_defect_bound
    (hF : ∀ i, AEMeasurable (F i) P) {scale : ℝ → ℝ}
    (hscale : ∀ r : ℝ, 0 < r → r ≤ 1 → 0 ≤ scale r)
    (hpair : ∃ C0 : ℝ, 0 < C0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P ∧
        (∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤
          C0 * scale r) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r (F i omega) (F j omega)) P ∧
        (∫ omega, tubeOverlapArea r (F i omega) (F j omega) ∂P) ≤
          C * scale r) ∧
      Integrable (fun omega => tubeDefect r (fun i => F i omega)) P ∧
      (∫ omega, tubeDefect r (fun i => F i omega) ∂P) ≤ C * scale r := by
  obtain ⟨C0, hC0, hpair⟩ := hpair
  let D : ℝ := max 1 ((Fintype.card iota : ℝ) ^ 2 / 2)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D * C0, mul_pos hD hC0, fun r hr hr1 => ?_⟩
  have h := pairwise_overlap_and_defect_of_bound (P := P) (F := F) hr
    (mul_nonneg hC0.le (hscale r hr hr1)) hF (hpair r hr hr1)
  simpa only [D, mul_assoc] using h

end

end BrownianImages
