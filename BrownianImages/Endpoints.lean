/-
The endpoints of `BrownianImagesComplete.tex` that no single module proves: each is a
composition of results from two or more of the modules above, in the shape
`Challenge.lean` states it.

* `smoothing`, `non_lattice_correlation_limit`: `eq:smoothing` and the `μ_B` conclusion
  of `thm:profile-asymptotics`, the analytic core of `Rescaling` fed with the Stieltjes
  form of `thm:gaussian-reduction`.
* `endpoint_block_mass`, `endpoint_block_mass_dyadic`, `four_point_integral`: the
  variance chain of `sec:variance`, `eq:joint-return-bound` fed through the block bound
  into the dyadic summation.
* `homogeneous_periodic_profile`, `homogeneous_profile_asymptotics_lattice`,
  `thm_smoothing_injective_homogeneous`, `homogeneous_lattice_correlation_oscillation`:
  the periodic profile `G̃_A` of `sec:renewal` for every `0 < λ < 1/2`, built from the
  non-constancy of `HomogeneousNonconstancy`, the internal Frostman regularity result
  and the shift identity `eq:g-recursion`, together with the three results that consume
  it: `eq:ha-asymptotic`, `thm:smoothing-injective` bundled, and the `μ_A` conclusion of
  `thm:profile-asymptotics`.
-/
import BrownianImages.Rescaling
import BrownianImages.Reduction
import BrownianImages.FourPointBound
import BrownianImages.BlockMass
import BrownianImages.FourPointIntegral
import BrownianImages.AhlforsRegular
import BrownianImages.PairDifference
import BrownianImages.HomogeneousNonconstancy

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `eq:smoothing`.  The exact rescaling `S_μ(r) = r^{2s} H_μ(log(1/r))`, for every
`r > 0`. -/
theorem smoothing {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ}
    (hr0 : 0 < r) :
    expCorr W P μ r = r ^ (2 * s) * H s μ (Real.log r⁻¹) :=
  smoothing_of_gaussian_reduction hW hs0 hs1 hμ hr0 (gaussian_reduction hW hs0 hs1 hμ hr0).2

/-- `thm:profile-asymptotics`, the conclusion for `μ_B`: the normalised expected
correlation integral has a finite positive limit. -/
theorem non_lattice_correlation_limit {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s C A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (hCpos : 0 < C) :
    ∃ L > 0, Tendsto (fun r : ℝ => expCorr W P μ r / r ^ (2 * s)) (𝓝[>] 0) (𝓝 L) :=
  non_lattice_correlation_limit_of_gaussian_reduction hW hs0 hs1 hμ hC hCpos
    (fun _r hr => (gaussian_reduction hW hs0 hs1 hμ hr).2)

/-- `thm:endpoint-block-mass`, both halves.
The `μ⁴`-mass of a dyadic block of ordered quadruples, and the joint return probability
on that block.  `μ` sits on `[0,1]`, so reading the times through `Real.toNNReal` is the
identity `μ⁴`-almost everywhere. -/
theorem endpoint_block_mass {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs : 0 < s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ β η : ℝ, 0 < β → β ≤ 1 → 0 < η → η ≤ 1 →
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          β / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ β ∧
          η / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ η}
        ≤ ENNReal.ofReal (C * β ^ s * η ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        β / 2 < x₃ - x₂ → x₃ - x₂ ≤ β →
        η / 2 < (x₂ - x₁) + (x₄ - x₃) → (x₂ - x₁) + (x₄ - x₃) ≤ η →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) :=
  endpoint_block_mass_of_four_point hW hs hμ (fun hr hΔ => gaussian_four_point hW hr hΔ)

/-- `thm:endpoint-block-mass` at the dyadic values `β, η ∈ 𝒟` the paper uses, with both
halves of the lemma. -/
theorem endpoint_block_mass_dyadic {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs : 0 < s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ j l : ℕ,
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
          ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}
        ≤ ENNReal.ofReal (C * (((1:ℝ)/2) ^ j) ^ s * (((1:ℝ)/2) ^ l) ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        ((1:ℝ)/2) ^ j / 2 < x₃ - x₂ → x₃ - x₂ ≤ ((1:ℝ)/2) ^ j →
        ((1:ℝ)/2) ^ l / 2 < (x₂ - x₁) + (x₄ - x₃) →
        (x₂ - x₁) + (x₄ - x₃) ≤ ((1:ℝ)/2) ^ l →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) :=
  endpoint_block_mass_dyadic_of_four_point hW hs hμ
    (fun hr hΔ => gaussian_four_point hW hr hΔ)

/-- `thm:four-point-integral`, `eq:four-point-integral`.  The four dyadic sums, summed:
the joint return probability integrates over the overlap set to `O(V_s(r))`. -/
theorem four_point_integral {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ p : ℝ × ℝ × ℝ × ℝ in {p | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2},
        jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
        ∂(μ.prod (μ.prod (μ.prod μ)))
      ≤ ENNReal.ofReal (C * varScale s r) :=
  four_point_integral_of_block hW hs0 hs1 hμ
    (endpoint_block_mass_dyadic_of_four_point hW hs0 hμ
      (fun hr hΔ => gaussian_four_point hW hr hΔ))

/-- `thm:homogeneous-nonconstancy` and the paragraph following it, on the full range
`0 < λ < 1/2`: the homogeneous natural measure has a positive non-constant periodic
tail profile of period `log(1/λ)`. -/
theorem homogeneous_periodic_profile {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
      (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) ∧
      (∀ x, 0 < g x) ∧ ∃ x y, g x ≠ g y :=
  exists_homogeneous_periodic_profile hlam0 hlam hA

/-- `eq:ha-asymptotic` for the homogeneous system on the full parameter range. -/
theorem homogeneous_profile_asymptotics_lattice {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
      (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
        |H (homogeneousDim lam) μA v - smoothOp (homogeneousDim lam) g v|
          ≤ C * Real.exp (-2 * (1 - homogeneousDim lam) * v) := by
  haveI := hA.isProbabilityMeasure
  obtain ⟨g, hg, hper, hagree, -, -⟩ := homogeneous_periodic_profile hlam0 hlam hA
  obtain ⟨C, hC0, hCbd⟩ := exists_lattice_bound
    (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam)
    (μ := μA) hg (log_inv_pos hlam0 hlam).ne' hper hagree
  exact ⟨g, hg, hper, hagree, C, hC0, hCbd⟩

/-- `thm:smoothing-injective`, including its named conclusion for the homogeneous
periodic profile. -/
theorem thm_smoothing_injective_homogeneous {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    (∀ g₁ g₂ : ℝ → ℝ, Continuous g₁ → Continuous g₂ →
        Function.Periodic g₁ (Real.log lam⁻¹) → Function.Periodic g₂ (Real.log lam⁻¹) →
        (∀ v, smoothOp (homogeneousDim lam) g₁ v = smoothOp (homogeneousDim lam) g₂ v) →
        ∀ x, g₁ x = g₂ x) ∧
      (∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
        (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) ∧
        ∃ v w, smoothOp (homogeneousDim lam) g v ≠ smoothOp (homogeneousDim lam) g w) := by
  refine ⟨fun g₁ g₂ hg₁ hg₂ hper₁ hper₂ h =>
    smoothOp_injective (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam)
      (log_inv_pos hlam0 hlam) hg₁ hg₂ hper₁ hper₂ h, ?_⟩
  obtain ⟨g, hg, hper, hagree, -, hne⟩ := homogeneous_periodic_profile hlam0 hlam hA
  exact ⟨g, hg, hper, hagree,
    smoothOp_nonconstant (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam)
      (log_inv_pos hlam0 hlam) hg hper hne⟩

/-- `thm:profile-asymptotics`, the oscillatory conclusion for the homogeneous measure
for every `0 < λ < 1/2`. -/
theorem homogeneous_lattice_correlation_oscillation {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    ∃ a b : ℝ, a < b ∧
      (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧
        expCorr W P μA r ≤ a * r ^ (2 * homogeneousDim lam)) ∧
      (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧
        b * r ^ (2 * homogeneousDim lam) ≤ expCorr W P μA r) := by
  haveI := hA.isProbabilityMeasure
  obtain ⟨A, hFrost⟩ := AhlforsRegular.exists_isFrostman_of_isNatural
    (homogeneousDim_pos hlam0 hlam)
    (homogeneousSystem_stronglySeparated hlam0 hlam hA.attractor.2.2.1) hA
  exact lattice_correlation_oscillation_of_smoothing hW
    (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam)
    (log_inv_pos hlam0 hlam) (homogeneous_periodic_profile hlam0 hlam hA)
    (fun r hr => smoothing hW (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam) hFrost hr)

end BrownianImages
