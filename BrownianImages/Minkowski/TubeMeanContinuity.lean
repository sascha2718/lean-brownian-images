/-
Continuity of the mean normalized Brownian tube profile.

For a fixed compact set the smoothed tube mass is continuous in its positive
radius.  Locally in logarithmic scale, monotonicity in the radius bounds the
whole normalized profile by a fixed multiple of one nearby profile value.
Thus pointwise continuity passes through expectation as soon as the profile is
integrable at every real logarithmic scale.
-/
import BrownianImages.Minkowski.Profile
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace BrownianImages

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

/-- The triangular cutoff is monotone in its positive radius. -/
theorem tubeCutoff_mono_radius {r R : Real} (hr : 0 < r) (hrR : r ≤ R)
    (F : CompactPlane) (x : Plane) :
    tubeCutoff r F x ≤ tubeCutoff R F x := by
  have hR : 0 < R := hr.trans_le hrR
  unfold tubeCutoff
  apply max_le_max_right
  gcongr
  exact Metric.infDist_nonneg

/-- Smoothed tube mass is monotone in its positive radius. -/
theorem tubeMass_mono_radius {r R : Real} (hr : 0 < r) (hrR : r ≤ R)
    (F : CompactPlane) :
    tubeMass r F ≤ tubeMass R F := by
  unfold tubeMass
  exact integral_mono (integrable_tubeCutoff hr F)
    (integrable_tubeCutoff (hr.trans_le hrR) F)
    (tubeCutoff_mono_radius hr hrR F)

/-- For a fixed compact set, smoothed tube mass is continuous at every
positive radius. -/
theorem continuousAt_tubeMass_radius {r : Real} (hr : 0 < r)
    (F : CompactPlane) :
    ContinuousAt (fun R : Real => tubeMass R F) r := by
  let delta : Real := min (r / 2) 1
  have hdelta : 0 < delta := lt_min (by linarith) zero_lt_one
  let K : Set Plane := Metric.cthickening (r + 1) (F : Set Plane)
  let bound : Plane → Real := K.indicator fun _ => 1
  have hK : IsCompact K := F.isCompact.cthickening
  have hbound_integrable : Integrable bound :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  unfold tubeMass
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [Metric.ball_mem_nhds r hdelta] with R hR
    have hRpos : 0 < R := by
      rw [Metric.mem_ball, Real.dist_eq] at hR
      have hdelta_le : delta ≤ r / 2 := min_le_left _ _
      have := (abs_lt.mp hR).1
      linarith
    exact (continuous_tubeCutoff_right R F).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds r hdelta] with R hR
    rw [Metric.mem_ball, Real.dist_eq] at hR
    have hRpos : 0 < R := by
      have hdelta_le : delta ≤ r / 2 := min_le_left _ _
      have := (abs_lt.mp hR).1
      linarith
    have hRupper : R < r + 1 := by
      have hdelta_le : delta ≤ 1 := min_le_right _ _
      have := (abs_lt.mp hR).2
      linarith
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [bound, Set.indicator_of_mem hx, Real.norm_eq_abs,
          abs_of_nonneg (tubeCutoff_nonneg R F x)]
        exact tubeCutoff_le_one hRpos F x
      · have hdist : r + 1 < Metric.infDist x F := by
          have hnot : ¬ Metric.infDist x F ≤ r + 1 := by
            intro hle
            exact hx ((mem_cthickening_compactPlane_iff
              (by linarith : 0 ≤ r + 1) F x).2 hle)
          exact lt_of_not_ge hnot
        have hzero : tubeCutoff R F x = 0 :=
          (tubeCutoff_eq_zero_iff hRpos F x).2 (le_of_lt (hRupper.trans hdist))
        simp [bound, Set.indicator_of_notMem hx, hzero]
  · exact hbound_integrable
  · exact Filter.Eventually.of_forall fun x => by
      unfold tubeCutoff
      exact (continuousAt_const.sub
        (continuousAt_const.div continuousAt_id (ne_of_gt hr))).max
          continuousAt_const

/-- Smoothed tube mass is continuous as a function of its positive radius. -/
theorem continuousOn_tubeMass_radius (F : CompactPlane) :
    ContinuousOn (fun r : Real => tubeMass r F) (Set.Ioi 0) := by
  intro r hr
  exact (continuousAt_tubeMass_radius hr F).continuousWithinAt

/-- For every compact set, its normalized tube profile is continuous in
logarithmic scale. -/
theorem continuous_normalizedTubeMass_logScale (s : Real) (F : CompactPlane) :
    Continuous (fun v : Real => normalizedTubeMass s v F) := by
  unfold normalizedTubeMass
  apply (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).mul
  exact (continuousOn_tubeMass_radius F).comp_continuous
    (Real.continuous_exp.comp continuous_neg)
    (fun v => tubeRadiusReal_pos v)

/-- A local profile value is bounded by a fixed multiple of the value one
logarithmic unit to its left. -/
theorem normalizedTubeMass_le_exp_two_mul_of_mem_ball
    {s v0 v : Real} (hs1 : s < 1) (F : CompactPlane)
    (hv : v ∈ Metric.ball v0 1) :
    normalizedTubeMass s v F ≤
      Real.exp (2 * tubeExponent s) *
        normalizedTubeMass s (v0 - 1) F := by
  have halpha : 0 < tubeExponent s := by
    unfold tubeExponent
    linarith
  have hvbounds : v0 - 1 < v ∧ v < v0 + 1 := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hv
    constructor <;> linarith [hv.1, hv.2]
  have hradius : tubeRadiusReal v ≤ tubeRadiusReal (v0 - 1) := by
    unfold tubeRadiusReal
    exact Real.exp_le_exp.mpr (by linarith)
  have hmass := tubeMass_mono_radius (tubeRadiusReal_pos v) hradius F
  have hexp : Real.exp (tubeExponent s * v) ≤
      Real.exp (2 * tubeExponent s) *
        Real.exp (tubeExponent s * (v0 - 1)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold normalizedTubeMass
  calc
    Real.exp (tubeExponent s * v) * tubeMass (tubeRadiusReal v) F ≤
        (Real.exp (2 * tubeExponent s) *
          Real.exp (tubeExponent s * (v0 - 1))) *
            tubeMass (tubeRadiusReal (v0 - 1)) F :=
      mul_le_mul hexp hmass (tubeMass_nonneg _ _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (2 * tubeExponent s) *
        (Real.exp (tubeExponent s * (v0 - 1)) *
          tubeMass (tubeRadiusReal (v0 - 1)) F) := by ring

/-- Pointwise continuity and all-scale integrability imply continuity of the
mean normalized Brownian tube profile. -/
theorem IsPlanarBrownian.continuous_meanBrownianTubeProfile_of_integrable
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts Real) {s : Real} (hs1 : s < 1)
    (hint : ∀ v : Real, Integrable (brownianTubeProfile W K s v) P) :
    Continuous (meanBrownianTubeProfile W P K s) := by
  rw [continuous_iff_continuousAt]
  intro v0
  unfold meanBrownianTubeProfile
  let bound : Omega → Real := fun omega =>
    Real.exp (2 * tubeExponent s) *
      brownianTubeProfile W K s (v0 - 1) omega
  have hbound : Integrable bound P := (hint (v0 - 1)).const_mul _
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun v =>
      (hW.aemeasurable_brownianTubeProfile K s v).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds v0 zero_lt_one] with v hv
    exact Filter.Eventually.of_forall fun omega => by
      change |normalizedTubeMass s v (brownianImage W K omega)| ≤
        Real.exp (2 * tubeExponent s) *
          normalizedTubeMass s (v0 - 1) (brownianImage W K omega)
      rw [abs_of_nonneg
        (normalizedTubeMass_nonneg s v (brownianImage W K omega))]
      exact normalizedTubeMass_le_exp_two_mul_of_mem_ball hs1 _ hv
  · exact hbound
  · exact Filter.Eventually.of_forall fun omega =>
      (continuous_normalizedTubeMass_logScale s
        (brownianImage W K omega)).continuousAt

end

end BrownianImages
