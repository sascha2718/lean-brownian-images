/-
`sec:smoothing` of `BrownianImagesComplete.tex`: the `μ_B` conclusion of
`thm:profile-asymptotics` with its constant named.

`eq:gb-limit` is `thm:non-lattice-limit` read at the paired system.  The support of `ϑ`
is `{log 2, log(1/c)}`, so `eq:non-lattice` is exactly the non-arithmetic hypothesis of
that lemma: `pairSystem_nonArithmetic_iff` is the conversion, and
`pairSystem_isDimension`, `pairSystem_stronglySeparated` and the attractor sitting in
`[0,1]` are the remaining inputs.  The bundle `thm:profile-asymptotics` in `NonLattice`
carries the renewal constant `C_B` of `eq:gb-limit` through all three conclusions about
`μ_B`; the piece proved here is the limit of the normalised correlation integral.

* `ProfileAsymptotics.non_lattice_correlation_limit_const`: the `μ_B` conclusion of
  `thm:profile-asymptotics` with the limit named, `C ∫₀^∞ φ` rather than some `L > 0`.
-/
import BrownianImages.Endpoints

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ProfileAsymptotics

/-- `thm:profile-asymptotics`, the conclusion for `μ_B` with the limit named: the
normalised expected correlation integral converges to `C ∫₀^∞ φ`, the same constant
`eq:hb-asymptotic` produces.  `audit_non_lattice_correlation_limit` asserts only that
some positive limit exists; the bundle needs the value, so it is proved here from
`eq:smoothing` and `eq:hb-asymptotic` directly. -/
theorem non_lattice_correlation_limit_const {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s C A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (hCpos : 0 < C) :
    Tendsto (fun r : ℝ => expCorr W P μ r / r ^ (2 * s)) (𝓝[>] 0)
      (𝓝 (C * ∫ η in Set.Ioi (0:ℝ), kern s η)) := by
  obtain ⟨hLpos, hLtend⟩ := profile_asymptotics_nonLattice hs0 hs1 hμ hCpos hC
  have hlog : Tendsto (fun r : ℝ => Real.log r⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  refine Filter.Tendsto.congr' ?_ (hLtend.comp hlog)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  have hrpow : (0:ℝ) < r ^ (2 * s) := Real.rpow_pos_of_pos hr0 _
  rw [Function.comp_apply, (gaussian_reduction hW hs0 hs1 hμ hr0).2,
    Rescaling.integral_ret_pairLaw hs0 hs1 hμ hr0]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hrpow)]

end ProfileAsymptotics

end BrownianImages
