/-
The singularity consequences of `sec:fixed-dimension-family` and
`sec:fixed-dimension-separation`: two parameters of the fixed-dimension family with distinct
means have mutually singular Brownian image-measure laws, by `thm:main`, and mutually
singular compact-image laws, by `thm:minkowski-reconstruction`.  With
`thm:fixed-dimension-separation` this is the final assertion of that theorem, with
`thm:small-dimension-monotone` its second sentence, and with `thm:fixed-dimension-range` the
uncountable subfamily of pairwise singular laws.

* `fixedSystem_profile_separation`: distinct means give separated profiles.
* `fixedSystem_occupationLaw_mutuallySingular`: `Law(BM_*μ_{p₁}) ⊥ Law(BM_*μ_{p₂})`.
* `fixedSystem_brownianImageLaw_mutuallySingular`: `Law(BM(K_{p₁})) ⊥ Law(BM(K_{p₂}))`.
-/
import BrownianImages.FixedDimension.Profiles
import BrownianImages.MainTheorem
import BrownianImages.Minkowski.FullEndpointAssembly
import BrownianImages.TwoContraction.Distinction

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace MinkowskiReconstruction

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Distinct means give separated profiles, `eq:profile-separation`. -/
theorem fixedSystem_profile_separation {s p₁ p₂ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (fixedSystem s p₁ hs hp₁0 hp₁1).IsNatural K₁ s μ₁)
    (hμ₂ : (fixedSystem s p₂ hs hp₂0 hp₂1).IsNatural K₂ s μ₂)
    (hne : fixedMean s p₁ ≠ fixedMean s p₂) :
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t| := by
  have := hμ₁.isProbabilityMeasure
  have := hμ₂.isProbabilityMeasure
  obtain ⟨A₁, hA₁⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp₁0 hp₁1 hμ₁.attractor).exists_isFrostman _ hs.le hμ₁
  obtain ⟨A₂, hA₂⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp₂0 hp₂1 hμ₂.attractor).exists_isFrostman _ hs.le hμ₂
  exact exists_ge_abs_sub_of_tendsto_avg (profile_uniformContinuous hs hs1 hA₁).continuous
    (profile_uniformContinuous hs hs1 hA₂).continuous hne
    (fixedSystem_tendsto_avg_H hs hs1 hp₁0 hp₁1 hμ₁) (fixedSystem_tendsto_avg_H hs hs1 hp₂0 hp₂1 hμ₂)

/-- **`Law(BM_*μ_{p₁}) ⊥ Law(BM_*μ_{p₂})`** for parameters with distinct means, by
`thm:main`: both measures are Frostman by the open set condition. -/
theorem fixedSystem_occupationLaw_mutuallySingular
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {s p₁ p₂ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (fixedSystem s p₁ hs hp₁0 hp₁1).IsNatural K₁ s μ₁)
    (hμ₂ : (fixedSystem s p₂ hs hp₂0 hp₂1).IsNatural K₂ s μ₂)
    (hne : fixedMean s p₁ ≠ fixedMean s p₂) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  have := hμ₁.isProbabilityMeasure
  have := hμ₂.isProbabilityMeasure
  obtain ⟨A₁, hF₁⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp₁0 hp₁1 hμ₁.attractor).exists_isFrostman _ hs.le hμ₁
  obtain ⟨A₂, hF₂⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp₂0 hp₂1 hμ₂.attractor).exists_isFrostman _ hs.le hμ₂
  exact main hW hs hs1 hF₁ hF₂
    (fixedSystem_profile_separation hs hs1 hp₁0 hp₁1 hp₂0 hp₂1 hμ₁ hμ₂ hne)

/-- **`Law(BM(K_{p₁})) ⊥ Law(BM(K_{p₂}))`** for parameters with distinct means: both systems
satisfy the open set condition, so `thm:minkowski-reconstruction` reconstructs each
occupation measure from the compact image, and the occupation-law singularity descends
through the common Borel reconstruction map. -/
theorem fixedSystem_brownianImageLaw_mutuallySingular
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {s p₁ p₂ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (fixedSystem s p₁ hs hp₁0 hp₁1).IsNatural K₁ s μ₁)
    (hμ₂ : (fixedSystem s p₂ hs hp₂0 hp₂1).IsNatural K₂ s μ₂)
    (hne : fixedMean s p₁ ≠ fixedMean s p₂) :
    (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
      (brownianImageLaw W P hμ₂.compactAttractor) := by
  have := hμ₁.isProbabilityMeasure
  have := hμ₂.isProbabilityMeasure
  have hpath₁ := hμ₁.tubeReconstructsOccupation hW _ hs hs1
    ((fixedSystem_openSetCondition hs hs1 hp₁0 hp₁1 hμ₁.attractor).strongOpenSetCondition _
      hμ₁.attractor) (fixedSystem_isDimension hs hp₁0 hp₁1)
  have hpath₂ := hμ₂.tubeReconstructsOccupation hW _ hs hs1
    ((fixedSystem_openSetCondition hs hs1 hp₂0 hp₂1 hμ₂.attractor).strongOpenSetCondition _
      hμ₂.attractor) (fixedSystem_isDimension hs hp₂0 hp₂1)
  exact brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction hW hpath₁ hpath₂
    (fixedSystem_occupationLaw_mutuallySingular hW hs hs1 hp₁0 hp₁1 hp₂0 hp₂1 hμ₁ hμ₂ hne)

end MinkowskiReconstruction

end

end BrownianImages
