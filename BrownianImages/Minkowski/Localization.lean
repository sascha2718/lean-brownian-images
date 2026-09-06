/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: localization of the
normalized smoothed tube measure near a compact set.

The final cylinder argument needs a quantitative version of the elementary fact
that a tube probability around a compact set of small diameter is close to a point
mass.  This file proves that estimate directly, with the exact radius and diameter
appearing in the paper's bounded-Lipschitz argument.

* `tubeProbability_compl_cthickening`: the tube probability is supported by the
  closed radius-`r` thickening.
* `integral_tubeProbability_sub_anchor_le`: a Lipschitz test differs from its value
  at an anchor in the compact set by at most `K (r + diam F)` after tube averaging.
-/
import BrownianImages.Minkowski.TubeAlgebra

namespace BrownianImages

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

/-- A positive-radius tube probability gives zero mass to the complement of the
closed thickening of the same radius. -/
theorem tubeProbability_compl_cthickening {r : ℝ} (hr : 0 < r)
    (F : CompactPlane) :
    (tubeProbability r hr F : Measure Plane)
      (Metric.cthickening r (F : Set Plane))ᶜ = 0 := by
  rw [tubeProbability_apply hr F Metric.isClosed_cthickening.measurableSet.compl]
  suffices ∫⁻ x in (Metric.cthickening r (F : Set Plane))ᶜ,
      ENNReal.ofReal (tubeCutoff r F x) = 0 by simp [this]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem
    Metric.isClosed_cthickening.measurableSet.compl] with x hx
  simp only [Set.mem_compl_iff, mem_cthickening_compactPlane_iff hr.le] at hx
  change ENNReal.ofReal (tubeCutoff r F x) = (0 : ℝ≥0∞)
  have hzero : tubeCutoff r F x = 0 :=
    (tubeCutoff_eq_zero_iff hr F x).2 (le_of_not_ge hx)
  simp [hzero]

/-- Almost every point under a tube probability belongs to the corresponding
closed thickening. -/
theorem ae_mem_cthickening_tubeProbability {r : ℝ} (hr : 0 < r)
    (F : CompactPlane) :
    ∀ᵐ x ∂(tubeProbability r hr F : Measure Plane),
      x ∈ Metric.cthickening r (F : Set Plane) := by
  rw [ae_iff]
  simpa only [show {x : Plane | x ∉ Metric.cthickening r (F : Set Plane)} =
    (Metric.cthickening r (F : Set Plane))ᶜ by rfl] using
      tubeProbability_compl_cthickening hr F

/-- Every point in the closed tube lies within `r + diam F` of any chosen anchor
of `F`. -/
theorem dist_anchor_le_radius_add_diam {r : ℝ} (hr : 0 ≤ r)
    {F : CompactPlane} {x x0 : Plane}
    (hx : x ∈ Metric.cthickening r (F : Set Plane)) (hx0 : x0 ∈ F) :
    dist x x0 ≤ r + Metric.diam (F : Set Plane) := by
  have hinf : Metric.infDist x (F : Set Plane) ≤ r :=
    (mem_cthickening_compactPlane_iff hr F x).mp hx
  exact (Metric.dist_le_infDist_add_diam F.isCompact.isBounded hx0).trans
    (add_le_add hinf le_rfl)

/-- Averaging a Lipschitz function over a tube around `F` changes its value at an
anchor `x0 ∈ F` by at most the Lipschitz constant times `r + diam F`. -/
theorem integral_tubeProbability_sub_anchor_le {K : ℝ≥0}
    (f : BoundedContinuousFunction Plane ℝ) (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 < r)
    {F : CompactPlane} {x0 : Plane} (hx0 : x0 ∈ F) :
    |(∫ x, f x ∂(tubeProbability r hr F : Measure Plane)) - f x0| ≤
      (K : ℝ) * (r + Metric.diam (F : Set Plane)) := by
  let nu : Measure Plane := tubeProbability r hr F
  have hprob : IsProbabilityMeasure nu := inferInstance
  have hfint : Integrable f nu := BoundedContinuousFunction.integrable nu f
  have hcint : Integrable (fun _ : Plane => f x0) nu := integrable_const _
  have hrewrite :
      (∫ x, f x ∂nu) - f x0 = ∫ x, (f x - f x0) ∂nu := by
    rw [integral_sub hfint hcint, integral_const]
    simp
  rw [hrewrite]
  refine (abs_integral_le_integral_abs).trans ?_
  have habsint : Integrable (fun x => |f x - f x0|) nu :=
    (hfint.sub hcint).abs
  have hconstint : Integrable
      (fun _ : Plane => (K : ℝ) * (r + Metric.diam (F : Set Plane))) nu :=
    integrable_const _
  calc
    (∫ x, |f x - f x0| ∂nu) ≤
        ∫ _x : Plane, (K : ℝ) * (r + Metric.diam (F : Set Plane)) ∂nu := by
      apply integral_mono_ae habsint hconstint
      filter_upwards [ae_mem_cthickening_tubeProbability hr F] with x hx
      rw [← Real.dist_eq]
      exact (hf.dist_le_mul x x0).trans
        (mul_le_mul_of_nonneg_left
          (dist_anchor_le_radius_add_diam hr.le hx hx0) K.coe_nonneg)
    _ = (K : ℝ) * (r + Metric.diam (F : Set Plane)) := by simp

end BrownianImages
