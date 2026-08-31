/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: notation for the raw and
smoothed Brownian sausages and their logarithmically normalised profiles.

This file is deliberately definitional.  It gives the analytic lemmas of the paper a
single, literal Lean vocabulary while keeping the deterministic Hausdorff-space
construction in `MinkowskiTube` separate from the probabilistic estimates.
-/
import BrownianImages.CompactImage
import BrownianImages.MinkowskiSystem
import BrownianImages.MinkowskiTubeAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Prod

namespace BrownianImages

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology

/-- Lebesgue area of the open `r`-neighbourhood of a compact planar set. -/
noncomputable def tubeArea (r : ℝ) (F : CompactPlane) : ℝ :=
  (volume (Metric.thickening r (F : Set Plane))).toReal

theorem tubeArea_nonneg (r : ℝ) (F : CompactPlane) : 0 ≤ tubeArea r F :=
  ENNReal.toReal_nonneg

/-- At every fixed radius, raw tube area is a Borel function of the compact set. -/
theorem measurable_tubeArea (r : ℝ) : Measurable (tubeArea r) := by
  let g : CompactPlane × Plane → ℝ≥0∞ := fun p =>
    {x | Metric.infDist x (p.1 : Set Plane) < r}.indicator (fun _ => 1) p.2
  have hg : Measurable g := by
    apply Measurable.indicator measurable_const
    exact measurableSet_lt continuous_infDist_compactPlane.measurable measurable_const
  have hmeas : Measurable (fun F : CompactPlane => (∫⁻ x, g (F, x)).toReal) :=
    ENNReal.measurable_toReal.comp hg.lintegral_prod_right'
  convert hmeas using 1
  funext F
  rw [tubeArea]
  congr 1
  change volume (Metric.thickening r (F : Set Plane)) =
    ∫⁻ x : Plane, {x | Metric.infDist x (F : Set Plane) < r}.indicator 1 x
  rw [lintegral_indicator_one]
  · congr 1
    ext x
    exact Metric.mem_thickening_iff_infDist_lt F.nonempty
  · exact (isOpen_lt (Metric.lipschitz_infDist_pt (F : Set Plane)).continuous
      continuous_const).measurableSet

/-- Raw sausage area of a compact Brownian image. -/
noncomputable def brownianTubeArea {Omega : Type*} [MeasurableSpace Omega]
    (W : ℝ≥0 → Omega → Plane) (K : NonemptyCompacts ℝ) (r : ℝ)
    (omega : Omega) : ℝ :=
  tubeArea r (brownianImage W K omega)

/-- The fixed-radius raw Brownian sausage area is almost everywhere measurable. -/
theorem IsPlanarBrownian.aemeasurable_brownianTubeArea
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts ℝ) (r : ℝ) :
    AEMeasurable (brownianTubeArea W K r) P :=
  (measurable_tubeArea r).comp_aemeasurable
    (hW.aemeasurable_brownianImage K)

/-- The logarithmic radius `e⁻ᵛ`. -/
noncomputable def tubeRadiusReal (v : ℝ) : ℝ :=
  Real.exp (-v)

theorem tubeRadiusReal_pos (v : ℝ) : 0 < tubeRadiusReal v :=
  Real.exp_pos _

/-- The normalised smoothed tube mass `e^{(2-2s)v} M_{e^{-v}}(F)`. -/
noncomputable def normalizedTubeMass (s v : ℝ) (F : CompactPlane) : ℝ :=
  Real.exp (tubeExponent s * v) * tubeMass (tubeRadiusReal v) F

theorem normalizedTubeMass_nonneg (s v : ℝ) (F : CompactPlane) :
    0 ≤ normalizedTubeMass s v F :=
  mul_nonneg (Real.exp_pos _).le (tubeMass_nonneg _ _)

/-- At a fixed logarithmic scale the normalised tube mass is continuous in the compact
set. -/
theorem continuous_normalizedTubeMass (s v : ℝ) :
    Continuous (normalizedTubeMass s v) := by
  exact continuous_const.mul (continuous_tubeMass (tubeRadiusReal_pos v))

/-- The random normalised sausage profile `X(v)` of a compact Brownian image. -/
noncomputable def brownianTubeProfile {Omega : Type*} [MeasurableSpace Omega]
    (W : ℝ≥0 → Omega → Plane) (K : NonemptyCompacts ℝ) (s v : ℝ)
    (omega : Omega) : ℝ :=
  normalizedTubeMass s v (brownianImage W K omega)

/-- The fixed-scale Brownian tube profile is almost everywhere measurable. -/
theorem IsPlanarBrownian.aemeasurable_brownianTubeProfile
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts ℝ) (s v : ℝ) :
    AEMeasurable (brownianTubeProfile W K s v) P :=
  (continuous_normalizedTubeMass s v).measurable.comp_aemeasurable
    (hW.aemeasurable_brownianImage K)

/-- The mean sausage profile `m(v) = E X(v)`. -/
noncomputable def meanBrownianTubeProfile {Omega : Type*} [MeasurableSpace Omega]
    (W : ℝ≥0 → Omega → Plane) (P : Measure Omega)
    (K : NonemptyCompacts ℝ) (s v : ℝ) : ℝ :=
  ∫ omega, brownianTubeProfile W K s v omega ∂P

/-- The centred random profile used in the `L²` concentration lemma. -/
noncomputable def centeredBrownianTubeProfile {Omega : Type*} [MeasurableSpace Omega]
    (W : ℝ≥0 → Omega → Plane) (P : Measure Omega)
    (K : NonemptyCompacts ℝ) (s v : ℝ) (omega : Omega) : ℝ :=
  brownianTubeProfile W K s v omega - meanBrownianTubeProfile W P K s v

/-- Non-arithmeticity for the half-logarithmic tube-renewal steps `β_i`. -/
def System.TubeNonArithmetic {iota : Type*} [Fintype iota]
    (S : System iota) : Prop :=
  Dense ((AddSubgroup.closure (Set.range S.halfLogRatio) : AddSubgroup ℝ) : Set ℝ)

/-- Arithmeticity of the tube-renewal steps with span `h`. -/
def System.TubeArithmetic {iota : Type*} [Fintype iota]
    (S : System iota) (h : ℝ) : Prop :=
  AddSubgroup.closure (Set.range S.halfLogRatio) = AddSubgroup.zmultiples h

end BrownianImages
