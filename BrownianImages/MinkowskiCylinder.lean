/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: the deterministic finite-cylinder
approximation behind the last step of `thm:minkowski-reconstruction`.

This file separates the weak-convergence argument from the stochastic renewal estimates.
It compares the tube probability of a finite union with the tube probabilities of its
pieces and quantifies localization of each piece at a chosen anchor.
-/
import BrownianImages.MinkowskiLocalization

namespace BrownianImages

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

/-- The tube mass of one member of a finite family, normalized by the tube mass of
the union. -/
noncomputable def tubeMassRatio {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℝ) (F : ι → CompactPlane) (i : ι) : ℝ :=
  tubeMass r (F i) / tubeMass r (compactUnion F)

theorem tubeMassRatio_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℝ) (F : ι → CompactPlane) (i : ι) :
    0 ≤ tubeMassRatio r F i :=
  div_nonneg (tubeMass_nonneg r (F i)) (tubeMass_nonneg r (compactUnion F))

/-- Multiplying a tube average by its total tube mass recovers the unnormalized
cut-off integral. -/
theorem tubeMass_mul_integral_tubeProbability {r : ℝ} (hr : 0 < r)
    (F : CompactPlane) (f : Plane → ℝ) :
    tubeMass r F * (∫ x, f x ∂(tubeProbability r hr F : Measure Plane)) =
      ∫ x, tubeCutoff r F x * f x := by
  rw [integral_tubeProbability hr F]
  field_simp [ne_of_gt (tubeMass_pos hr F)]

/-- The normalized multiple-counting defect is the excess of the sum of the
piece mass ratios over one. -/
theorem sum_tubeMassRatio_sub_one {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    (∑ i, tubeMassRatio r F i) - 1 =
      tubeDefect r F / tubeMass r (compactUnion F) := by
  unfold tubeMassRatio tubeDefect
  have hne : tubeMass r (compactUnion F) ≠ 0 :=
    ne_of_gt (tubeMass_pos hr (compactUnion F))
  rw [← Finset.sum_div]
  field_simp

/-- Exact integral form of the finite-union error: replacing the union cut-off by
the sum of the piece cut-offs introduces precisely the normalized defect integrand. -/
theorem sum_tubeMassRatio_mul_integral_sub_integral {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r)
    (F : ι → CompactPlane) (f : BoundedContinuousFunction Plane ℝ) :
    (∑ i, tubeMassRatio r F i *
        ∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)) -
      ∫ x, f x ∂(tubeProbability r hr (compactUnion F) : Measure Plane) =
      (tubeMass r (compactUnion F))⁻¹ *
        ∫ x, tubeDefectIntegrand r F x * f x := by
  classical
  let M : ℝ := tubeMass r (compactUnion F)
  have hM : M ≠ 0 := ne_of_gt (tubeMass_pos hr (compactUnion F))
  have hpiece (i : ι) :
      tubeMassRatio r F i *
          (∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)) =
        M⁻¹ * ∫ x, tubeCutoff r (F i) x * f x := by
    rw [tubeMassRatio, div_eq_mul_inv, mul_assoc,
      integral_tubeProbability hr (F i)]
    field_simp [M, ne_of_gt (tubeMass_pos hr (F i))]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hpiece i), ← Finset.mul_sum,
    integral_tubeProbability hr (compactUnion F)]
  rw [← mul_sub, ← integral_finsetSum]
  · rw [← integral_sub]
    · congr 2
      funext x
      unfold tubeDefectIntegrand
      rw [sub_mul, Finset.sum_mul]
    · apply integrable_finsetSum
      intro i _
      exact (integrable_tubeCutoff hr (F i)).mul_bdd
        f.continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    · exact (integrable_tubeCutoff hr (compactUnion F)).mul_bdd
        f.continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
  · intro i _
    exact (integrable_tubeCutoff hr (F i)).mul_bdd
      f.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)

/-- A bounded test function sees at most its uniform norm times the normalized
multiple-counting defect when the union cut-off is replaced by the sum of the
piece cut-offs. -/
theorem abs_sum_tubeMassRatio_mul_integral_sub_integral_le {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r)
    (F : ι → CompactPlane) (f : BoundedContinuousFunction Plane ℝ) :
    |(∑ i, tubeMassRatio r F i *
        ∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)) -
      ∫ x, f x ∂(tubeProbability r hr (compactUnion F) : Measure Plane)| ≤
      ‖f‖ * (tubeDefect r F / tubeMass r (compactUnion F)) := by
  classical
  rw [sum_tubeMassRatio_mul_integral_sub_integral hr F f]
  have hMpos : 0 < tubeMass r (compactUnion F) :=
    tubeMass_pos hr (compactUnion F)
  have hdint : Integrable (tubeDefectIntegrand r F) :=
    integrable_tubeDefectIntegrand hr F
  have hfmeas : AEStronglyMeasurable (fun x : Plane => f x) :=
    f.continuous.measurable.aestronglyMeasurable
  have hfbound : ∀ᵐ x : Plane, ‖f x‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x
  have hprod : Integrable (fun x => tubeDefectIntegrand r F x * f x) :=
    hdint.mul_bdd hfmeas hfbound
  have hmajor : Integrable (fun x : Plane => tubeDefectIntegrand r F x * ‖f‖) :=
    hdint.mul_const _
  have hintegral :
      |∫ x, tubeDefectIntegrand r F x * f x| ≤
        ‖f‖ * tubeDefect r F := by
    calc
      |∫ x, tubeDefectIntegrand r F x * f x| ≤
          ∫ x, |tubeDefectIntegrand r F x * f x| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x, tubeDefectIntegrand r F x * ‖f‖ := by
        apply integral_mono hprod.abs hmajor
        intro x
        change |tubeDefectIntegrand r F x * f x| ≤
          tubeDefectIntegrand r F x * ‖f‖
        rw [abs_mul, abs_of_nonneg (tubeDefectIntegrand_nonneg hr F x)]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x)
          (tubeDefectIntegrand_nonneg hr F x)
      _ = ‖f‖ * tubeDefect r F := by
        rw [integral_mul_const, ← tubeDefect_eq_integral hr]
        ring
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hMpos.le), div_eq_mul_inv]
  calc
    (tubeMass r (compactUnion F))⁻¹ *
        |∫ x, tubeDefectIntegrand r F x * f x| ≤
      (tubeMass r (compactUnion F))⁻¹ * (‖f‖ * tubeDefect r F) :=
        mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr hMpos.le)
    _ = ‖f‖ * (tubeDefect r F * (tubeMass r (compactUnion F))⁻¹) := by ring

/-- Quantitative finite-cylinder approximation.  The three terms are respectively
the multiple-counting error, localization inside each compact piece, and the error
in the proposed cylinder weights. -/
theorem integral_tubeProbability_sub_weighted_anchors_le {ι : Type*}
    [Fintype ι] [Nonempty ι] {K : ℝ≥0}
    (f : BoundedContinuousFunction Plane ℝ) (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane)
    (x0 : ι → Plane) (hx0 : ∀ i, x0 i ∈ F i) (p : ι → ℝ) :
    |(∫ x, f x ∂(tubeProbability r hr (compactUnion F) : Measure Plane)) -
        ∑ i, p i * f (x0 i)| ≤
      ‖f‖ * (tubeDefect r F / tubeMass r (compactUnion F)) +
      ∑ i, tubeMassRatio r F i *
        ((K : ℝ) * (r + Metric.diam (F i : Set Plane))) +
      ‖f‖ * ∑ i, |tubeMassRatio r F i - p i| := by
  classical
  let I : ℝ := ∫ x, f x ∂(tubeProbability r hr (compactUnion F) : Measure Plane)
  let J : ℝ := ∑ i, tubeMassRatio r F i *
    ∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)
  let A : ℝ := ∑ i, tubeMassRatio r F i * f (x0 i)
  let B : ℝ := ∑ i, p i * f (x0 i)
  have hIJ : |I - J| ≤
      ‖f‖ * (tubeDefect r F / tubeMass r (compactUnion F)) := by
    rw [abs_sub_comm]
    exact abs_sum_tubeMassRatio_mul_integral_sub_integral_le hr F f
  have hJA : |J - A| ≤
      ∑ i, tubeMassRatio r F i *
        ((K : ℝ) * (r + Metric.diam (F i : Set Plane))) := by
    have heq : J - A = ∑ i, tubeMassRatio r F i *
        ((∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)) - f (x0 i)) := by
      dsimp [J, A]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    calc
      |∑ i, tubeMassRatio r F i *
          ((∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)) - f (x0 i))| ≤
          ∑ i, |tubeMassRatio r F i *
            ((∫ x, f x ∂(tubeProbability r hr (F i) : Measure Plane)) - f (x0 i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, tubeMassRatio r F i *
          ((K : ℝ) * (r + Metric.diam (F i : Set Plane))) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (tubeMassRatio_nonneg r F i)]
        exact mul_le_mul_of_nonneg_left
          (integral_tubeProbability_sub_anchor_le f hf hr (hx0 i))
          (tubeMassRatio_nonneg r F i)
  have hAB : |A - B| ≤ ‖f‖ * ∑ i, |tubeMassRatio r F i - p i| := by
    have heq : A - B = ∑ i, (tubeMassRatio r F i - p i) * f (x0 i) := by
      dsimp [A, B]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    calc
      |∑ i, (tubeMassRatio r F i - p i) * f (x0 i)| ≤
          ∑ i, |(tubeMassRatio r F i - p i) * f (x0 i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |tubeMassRatio r F i - p i| * ‖f‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x0 i)) (abs_nonneg _)
      _ = ‖f‖ * ∑ i, |tubeMassRatio r F i - p i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  change |I - B| ≤ _
  calc
    |I - B| = |(I - J) + (J - A) + (A - B)| := by ring_nf
    _ ≤ |I - J| + |J - A| + |A - B| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (‖f‖ * (tubeDefect r F / tubeMass r (compactUnion F))) +
        (∑ i, tubeMassRatio r F i *
          ((K : ℝ) * (r + Metric.diam (F i : Set Plane)))) +
        (‖f‖ * ∑ i, |tubeMassRatio r F i - p i|) :=
      add_le_add (add_le_add hIJ hJA) hAB

/-- The deterministic upper bound in
`integral_tubeProbability_sub_weighted_anchors_le`, packaged as a function of the
radius. -/
noncomputable def cylinderErrorBound {ι : Type*} [Fintype ι] [Nonempty ι]
    (K fNorm r : ℝ) (F : ι → CompactPlane) (p : ι → ℝ) : ℝ :=
  fNorm * (tubeDefect r F / tubeMass r (compactUnion F)) +
    ∑ i, tubeMassRatio r F i *
      (K * (r + Metric.diam (F i : Set Plane))) +
    fNorm * ∑ i, |tubeMassRatio r F i - p i|

/-- If all normalized piece masses converge to prescribed weights summing to one,
then the finite-cylinder error bound converges to the weighted diameter error. -/
theorem tendsto_cylinderErrorBound {ι : Type*} [Fintype ι] [Nonempty ι]
    {rho : ℕ → ℝ} (hrho : ∀ n, 0 < rho n) (hrho0 : Tendsto rho atTop (nhds 0))
    (F : ι → CompactPlane) (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (hratio : ∀ i, Tendsto (fun n => tubeMassRatio (rho n) F i) atTop (nhds (p i)))
    (K fNorm : ℝ) :
    Tendsto (fun n => cylinderErrorBound K fNorm (rho n) F p) atTop
      (nhds (K * ∑ i, p i * Metric.diam (F i : Set Plane))) := by
  have hdefect : Tendsto
      (fun n => tubeDefect (rho n) F / tubeMass (rho n) (compactUnion F))
      atTop (nhds 0) := by
    have hsum : Tendsto (fun n => ∑ i, tubeMassRatio (rho n) F i)
        atTop (nhds (∑ i, p i)) :=
      tendsto_finsetSum Finset.univ fun i _ => hratio i
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hsub : Tendsto
        (fun n => (∑ i, tubeMassRatio (rho n) F i) - 1) atTop
        (nhds ((∑ i, p i) - 1)) := hsum.sub hone
    rw [hp, sub_self] at hsub
    exact hsub.congr'
      (Filter.Eventually.of_forall fun n => sum_tubeMassRatio_sub_one (hrho n) F)
  have hlocal : Tendsto
      (fun n => ∑ i, tubeMassRatio (rho n) F i *
        (K * (rho n + Metric.diam (F i : Set Plane)))) atTop
      (nhds (∑ i, p i * (K * Metric.diam (F i : Set Plane)))) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    have hfactor : Tendsto
        (fun n => K * (rho n + Metric.diam (F i : Set Plane))) atTop
        (nhds (K * Metric.diam (F i : Set Plane))) := by
      simpa only [zero_add] using
        (hrho0.add_const (Metric.diam (F i : Set Plane))).const_mul K
    exact (hratio i).mul hfactor
  have hweight : Tendsto
      (fun n => ∑ i, |tubeMassRatio (rho n) F i - p i|) atTop (nhds 0) := by
    convert tendsto_finsetSum Finset.univ (fun i _ =>
      ((hratio i).sub tendsto_const_nhds).abs) using 1
    simp
  unfold cylinderErrorBound
  have hfconst : Tendsto (fun _ : ℕ => fNorm) atTop (nhds fNorm) :=
    tendsto_const_nhds
  have hleft : Tendsto
      (fun n => fNorm *
        (tubeDefect (rho n) F / tubeMass (rho n) (compactUnion F)))
      atTop (nhds (fNorm * 0)) := hfconst.mul hdefect
  have hright : Tendsto
      (fun n => fNorm * ∑ i, |tubeMassRatio (rho n) F i - p i|)
      atTop (nhds (fNorm * 0)) := hfconst.mul hweight
  have htotal := (hleft.add hlocal).add hright
  have hlocal_limit :
      (∑ i, p i * (K * Metric.diam (F i : Set Plane))) =
        K * ∑ i, p i * Metric.diam (F i : Set Plane) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [mul_zero, zero_add, add_zero, hlocal_limit] using htotal

end BrownianImages
