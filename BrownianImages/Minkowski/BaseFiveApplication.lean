/-
The consequence drawn after `thm:base-five-profiles` in `sec:examples`: the occupation
laws of the two base-five natural measures are mutually singular by `thm:main`, and the
laws of the compact Brownian images of the two attractors are mutually singular through
the Borel reconstruction map of `thm:minkowski-reconstruction`.

* `baseFive_occupationLaw_mutuallySingular`: `Law(BM_* μ₁) ⊥ Law(BM_* μ₂)`, the endpoint
  `audit_base_five_occupation_laws`.
* `baseFive_brownianImageLaw_mutuallySingular`: `Law(BM(K₁)) ⊥ Law(BM(K₂))`, the endpoint
  `audit_base_five_image_laws`.
-/
import BrownianImages.BaseFive
import BrownianImages.MainTheorem
import BrownianImages.Minkowski.FullEndpointAssembly

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace MinkowskiReconstruction

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The first display after `thm:base-five-profiles`: the occupation laws of the two
base-five natural measures are mutually singular.  Both measures are Frostman by the open
set condition, and `thm:main` applies to the profile separation of
`thm:base-five-profiles`. -/
theorem baseFive_occupationLaw_mutuallySingular
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K₁ baseFiveDim μ₁)
    (hμ₂ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K₂ baseFiveDim μ₂) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  have := hμ₁.isProbabilityMeasure
  have := hμ₂.isProbabilityMeasure
  obtain ⟨A₁, hF₁⟩ := System.OpenSetCondition.exists_isFrostman _
    (baseFiveSystem_openSetCondition _ _ baseFiveDigitsA_injective) baseFiveDim_pos.le hμ₁
  obtain ⟨A₂, hF₂⟩ := System.OpenSetCondition.exists_isFrostman _
    (baseFiveSystem_openSetCondition _ _ baseFiveDigitsB_injective) baseFiveDim_pos.le hμ₂
  exact main hW baseFiveDim_pos baseFiveDim_lt_one hF₁ hF₂ (baseFive_profiles hμ₁ hμ₂).2

/-- The second display after `thm:base-five-profiles`: the laws of the compact Brownian
images of the two base-five attractors are mutually singular.  Both systems satisfy the
open set condition, so `thm:minkowski-reconstruction` reconstructs each occupation measure
from the compact image, and the occupation-law singularity descends through the common
Borel reconstruction map. -/
theorem baseFive_brownianImageLaw_mutuallySingular
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K₁ baseFiveDim μ₁)
    (hμ₂ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K₂ baseFiveDim μ₂) :
    (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
      (brownianImageLaw W P hμ₂.compactAttractor) := by
  have := hμ₁.isProbabilityMeasure
  have := hμ₂.isProbabilityMeasure
  have hpath₁ := hμ₁.tubeReconstructsOccupation hW _ baseFiveDim_pos baseFiveDim_lt_one
    ((baseFiveSystem_openSetCondition _ _ baseFiveDigitsA_injective).strongOpenSetCondition _
      hμ₁.attractor) (baseFiveSystem_isDimension _ _)
  have hpath₂ := hμ₂.tubeReconstructsOccupation hW _ baseFiveDim_pos baseFiveDim_lt_one
    ((baseFiveSystem_openSetCondition _ _ baseFiveDigitsB_injective).strongOpenSetCondition _
      hμ₂.attractor) (baseFiveSystem_isDimension _ _)
  exact brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction hW hpath₁ hpath₂
    (baseFive_occupationLaw_mutuallySingular hW hμ₁ hμ₂)

end MinkowskiReconstruction

end

end BrownianImages
