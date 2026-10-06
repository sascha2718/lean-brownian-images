/-
`sec:small-dimension`, the moment `M_p(s) = 𝔼 Z_p^{-s}` with `X`, `Y` independent of law
`μ_p`: the Bernoulli measure with weights `p`, `q` is the code-space measure of the
fixed-dimension system, the law of the coded point is its natural measure `μ_p`, and
`fixedMoment` is the integral of `Z_p^{-s}` against `μ_p ⊗ μ_p`.

* `twoBern_eq_codeLaw_fixed`: the Bernoulli measure is the code-space measure.
* `map_fixedCode_twoBern`: the law of the coded point is `μ_p`, by Hutchinson uniqueness.
* `fixedMoment_eq_natural`: `M_p(s)` against `μ_p`.
-/
import BrownianImages.FixedDimension.System

namespace BrownianImages

open MeasureTheory Filter Hutchinson

noncomputable section

/-- At the weights `a^s = p`, `b^s = q` the Bernoulli measure is the library's code-space
measure of the system. -/
theorem twoBern_eq_codeLaw_fixed {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    twoBern (1 - p) = codeLaw (fixedSystem s p hs hp0 hp1) s := by
  unfold twoBern codeLaw
  congr 1
  funext _
  simp only [twoDigit, digitLaw, Fin.sum_univ_two, fixedSystem_ratio_zero,
    fixedSystem_ratio_one, fixedA_rpow hs hp0, fixedB_rpow hs hp1, sub_sub_cancel]

/-- The law of the coded point under the Bernoulli measure is the natural measure `μ_p`, by
Hutchinson uniqueness. -/
theorem map_fixedCode_twoBern {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) {K : Set ℝ}
    {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    (twoBern (1 - p)).map (fixedCode s p) = μ := by
  have hcode : fixedCode s p = code (fixedSystem s p hs hp0 hp1) :=
    funext (fixedCode_eq hs hp0 hp1)
  rw [twoBern_eq_codeLaw_fixed hs hp0 hp1, hcode]
  show naturalMeasure (fixedSystem s p hs hp0 hp1) s = μ
  have hdim := fixedSystem_isDimension hs hp0 hp1
  have hnat := isNatural_naturalMeasure (fixedSystem s p hs hp0 hp1) hdim
  have := hnat.isProbabilityMeasure
  have := hμ.isProbabilityMeasure
  exact eq_of_selfSimilar _ hdim hnat.selfSimilar hμ.selfSimilar hnat.support_Icc
    hμ.support_Icc

/-- `M_p(s) = 𝔼 Z_p^{-s}` with `X`, `Y` independent of law `μ_p`. -/
theorem fixedMoment_eq_natural {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    fixedMoment s p = ∫ y, ∫ x, fixedCross s p x y ^ (-s) ∂μ ∂μ := by
  have hmap := map_fixedCode_twoBern hs hp0 hp1 hμ
  have hμP := hμ.isProbabilityMeasure
  have hπ := measurable_fixedCode s p
  have hF : Measurable (fun q : ℝ × ℝ => fixedCross s p q.1 q.2 ^ (-s)) :=
    (continuous_fixedCross s p).measurable.pow_const _
  have hG : AEStronglyMeasurable (fun y => ∫ x, fixedCross s p x y ^ (-s) ∂μ) μ :=
    (hF.stronglyMeasurable.integral_prod_left' (μ := μ)).aestronglyMeasurable
  have key : ∀ G : ℝ → ℝ, AEStronglyMeasurable G μ →
      ∫ y, G y ∂μ = ∫ ω, G (fixedCode s p ω) ∂twoBern (1 - p) := by
    intro G hG
    rw [← hmap] at hG ⊢
    exact integral_map hπ.aemeasurable hG
  unfold fixedMoment fixedKernel
  rw [key _ hG]
  refine integral_congr_ae (Eventually.of_forall fun ω' => ?_)
  simp only
  rw [key (fun x => fixedCross s p x (fixedCode s p ω') ^ (-s))
    (((continuous_fixedCross s p).comp (continuous_id.prodMk continuous_const)).measurable.pow_const
      _).aestronglyMeasurable]

end

end BrownianImages
