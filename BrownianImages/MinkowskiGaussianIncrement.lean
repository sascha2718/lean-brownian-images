/-
The bounded-density law of a separating planar Brownian increment.

The overlap argument for two time cylinders isolates their compact Brownian
pieces from the translation between their initial points.  When the initial
times are separated, that translation contains a non-degenerate Brownian
increment.  This file records its exact planar Gaussian density and the
uniform bound by the density at the origin.
-/
import BrownianImages.FourPointBound
import BrownianImages.JointMeasurability

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-! ### Coordinates and planar Lebesgue measure -/

/-- The canonical measurable equivalence from the Euclidean plane to its two
real coordinates. -/
noncomputable def planeProdMeasurableEquiv : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

@[simp]
theorem planeProdMeasurableEquiv_apply (z : Plane) :
    planeProdMeasurableEquiv z = (z 0, z 1) := by
  rfl

/-- Passing from the Euclidean plane to its two coordinates preserves
Lebesgue measure. -/
theorem measurePreserving_planeProdMeasurableEquiv :
    MeasurePreserving planeProdMeasurableEquiv (volume : Measure Plane)
      (volume : Measure (ℝ × ℝ)) := by
  exact (PiLp.volume_preserving_ofLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

/-- A density pulled back through the canonical planar coordinate equivalence
pushes forward to the original density. -/
theorem map_withDensity_comp_planeProdMeasurableEquiv
    {d : (ℝ × ℝ) → ℝ≥0∞} (hd : Measurable d) :
    Measure.map planeProdMeasurableEquiv
        (volume.withDensity fun z : Plane => d (planeProdMeasurableEquiv z)) =
      volume.withDensity d := by
  ext s hs
  rw [planeProdMeasurableEquiv.map_apply,
    withDensity_apply _ (planeProdMeasurableEquiv.measurable hs),
    withDensity_apply _ hs]
  exact measurePreserving_planeProdMeasurableEquiv.setLIntegral_comp_preimage
    hs hd

/-! ### The planar Gaussian density -/

/-- The density of a centred planar Gaussian whose independent coordinates
both have variance `v`. -/
noncomputable def planarGaussianDensity (v : ℝ≥0) (z : Plane) : ℝ :=
  gaussianPDFReal 0 v (z 0) * gaussianPDFReal 0 v (z 1)

/-- The planar Gaussian density is Borel measurable. -/
theorem measurable_planarGaussianDensity (v : ℝ≥0) :
    Measurable (planarGaussianDensity v) := by
  unfold planarGaussianDensity
  fun_prop

/-- The planar Gaussian density is non-negative. -/
theorem planarGaussianDensity_nonneg (v : ℝ≥0) (z : Plane) :
    0 ≤ planarGaussianDensity v z := by
  exact mul_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _)

/-- The density is bounded by its value at the origin, `(2πv)⁻¹`. -/
theorem planarGaussianDensity_le (v : ℝ≥0) (z : Plane) :
    planarGaussianDensity v z ≤ (2 * Real.pi * (v : ℝ))⁻¹ := by
  exact FourPointBound.gaussianPDFReal_prod_le v (z 0) (z 1)

/-- The product of two centred real Gaussians is the pushforward, through
planar coordinates, of the measure having `planarGaussianDensity` as its
Lebesgue density. -/
theorem prod_gaussian_eq_map_planarGaussianDensity {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.map planeProdMeasurableEquiv
        (volume.withDensity fun z : Plane =>
          ENNReal.ofReal (planarGaussianDensity v z)) =
      (gaussianReal 0 v).prod (gaussianReal 0 v) := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    prod_withDensity (measurable_gaussianPDF 0 v)
      (measurable_gaussianPDF 0 v),
    ← Measure.volume_eq_prod]
  have hd :
      (fun q : ℝ × ℝ => gaussianPDF 0 v q.1 * gaussianPDF 0 v q.2) =
        fun z : ℝ × ℝ => ENNReal.ofReal
          (planarGaussianDensity v (planeProdMeasurableEquiv.symm z)) := by
    funext z
    rw [gaussianPDF, gaussianPDF,
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
  rw [hd]
  ext s hs
  rw [planeProdMeasurableEquiv.map_apply,
    withDensity_apply _ (planeProdMeasurableEquiv.measurable hs),
    withDensity_apply _ hs]
  let d : ℝ × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal
      (planarGaussianDensity v (planeProdMeasurableEquiv.symm z))
  have hdmeas : Measurable d :=
    (measurable_planarGaussianDensity v).ennreal_ofReal.comp
      planeProdMeasurableEquiv.symm.measurable
  simpa only [d, MeasurableEquiv.symm_apply_apply] using
    (measurePreserving_planeProdMeasurableEquiv.setLIntegral_comp_preimage
      hs hdmeas)

/-! ### Brownian increments -/

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {W : ℝ≥0 → Omega → Plane}

/-- A non-degenerate planar Brownian increment has the centred planar Gaussian
density of variance `c - b`.  In particular, the preceding lemmas supply the
measurability, non-negativity, and uniform bound required by the probabilistic
tube-overlap estimate. -/
theorem IsPlanarBrownian.map_increment_eq_withDensity
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {b c : ℝ≥0} (hbc : b < c) :
    P.map (fun omega => W c omega - W b omega) =
      volume.withDensity fun z =>
        ENNReal.ofReal (planarGaussianDensity (c - b) z) := by
  have hv : c - b ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hbc)
  apply planeProdMeasurableEquiv.map_measurableEquiv_injective
  have hinc : AEMeasurable (fun omega => W c omega - W b omega) P :=
    (JointMeasurability.aemeasurable_eval hW c).sub
      (JointMeasurability.aemeasurable_eval hW b)
  rw [AEMeasurable.map_map_of_aemeasurable
    planeProdMeasurableEquiv.measurable.aemeasurable hinc,
    prod_gaussian_eq_map_planarGaussianDensity hv]
  have hpair := hW.map_increment b c
  have hvdist : nndist (c : ℝ) (b : ℝ) = c - b := by
    have hbcReal : (b : ℝ) ≤ (c : ℝ) := mod_cast hbc.le
    apply NNReal.eq
    rw [NNReal.coe_sub hbc.le]
    simp [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hbcReal)]
  rw [hvdist] at hpair
  rw [← hpair]
  apply Measure.map_congr
  filter_upwards with omega
  rfl

end BrownianImages
