module

/-
The complete general-kernel lemma `thm:level-sums`: the uniform holomorphic limit,
the exact supremum bound `eq:level-sum-bound`, and the expectation under the natural
measure at every real parameter. The kernel is only assumed holomorphic on its stated
domain; its values outside that domain are irrelevant to the expectation.
-/
public import BrownianImages.FixedDimension.LevelSumsGeneral
public import BrownianImages.FixedDimension.LevelSumsExpectation

@[expose] public section

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- `thm:level-sums`: passage from independent Bernoulli codes to independent
points of natural law, even if the kernel is only continuous on its stated domain. -/
theorem integral_kernel_fixedCode_eq_natural {s p : ℝ} (hs : 0 < s)
    (hp0 : 0 < p) (hp1 : p < 1) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
    {D : Set ℂ} (hDo : IsOpen D) {φ : ℂ → ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun q : ℂ × ℂ => φ p q.1 q.2) (D ×ˢ D))
    (hmem : ∀ᵐ ω ∂twoBern (1 - p), (fixedCode s p ω : ℂ) ∈ D) :
    (∫ ω', ∫ ω, φ p (fixedCode s p ω) (fixedCode s p ω')
      ∂twoBern (1 - p) ∂twoBern (1 - p)) = ∫ y, ∫ x, φ p x y ∂μ ∂μ := by
  classical
  have := hμ.isProbabilityMeasure
  have hmap := map_fixedCode_twoBern hs hp0 hp1 hμ
  have hπ := measurable_fixedCode s p
  have hμmem : ∀ᵐ x : ℝ ∂μ, (x : ℂ) ∈ D := by
    rw [← hmap]
    exact (ae_map_iff hπ.aemeasurable
      (hDo.measurableSet.preimage Complex.measurable_ofReal)).2 hmem
  let E : Set (ℝ × ℝ) := (Complex.ofReal ⁻¹' D) ×ˢ (Complex.ofReal ⁻¹' D)
  let F : ℝ × ℝ → ℂ := E.piecewise (fun q => φ p q.1 q.2) (fun _ => 0)
  have hE : MeasurableSet E :=
    (hDo.measurableSet.preimage Complex.measurable_ofReal).prod
      (hDo.measurableSet.preimage Complex.measurable_ofReal)
  have hFcont : ContinuousOn (fun q : ℝ × ℝ => φ p q.1 q.2) E :=
    hcont.comp ((Complex.continuous_ofReal.comp continuous_fst).prodMk
      (Complex.continuous_ofReal.comp continuous_snd)).continuousOn (fun _ hq => hq)
  have hFmeas : Measurable F := hFcont.measurable_piecewise continuousOn_const hE
  have hFeq : ∀ x y : ℝ, (x : ℂ) ∈ D → (y : ℂ) ∈ D → F (x, y) = φ p x y := by
    intro x y hx hy
    exact Set.piecewise_eq_of_mem E _ _ (show (x, y) ∈ E from ⟨hx, hy⟩)
  have key : ∀ G : ℝ → ℂ, AEStronglyMeasurable G μ →
      ∫ y, G y ∂μ = ∫ ω, G (fixedCode s p ω) ∂twoBern (1 - p) := by
    intro G hG
    rw [← hmap] at hG ⊢
    exact integral_map hπ.aemeasurable hG
  have hmapF : (∫ y, ∫ x, F (x, y) ∂μ ∂μ) =
      ∫ ω', ∫ ω, F (fixedCode s p ω, fixedCode s p ω')
        ∂twoBern (1 - p) ∂twoBern (1 - p) := by
    rw [key _ (hFmeas.stronglyMeasurable.integral_prod_left' (μ := μ)).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω' => ?_)
    exact key _ (hFmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  calc
    _ = ∫ ω', ∫ ω, F (fixedCode s p ω, fixedCode s p ω')
        ∂twoBern (1 - p) ∂twoBern (1 - p) := by
      apply integral_congr_ae
      filter_upwards [hmem] with ω' hω'
      apply integral_congr_ae
      filter_upwards [hmem] with ω hω
      exact (hFeq _ _ hω hω').symm
    _ = ∫ y, ∫ x, F (x, y) ∂μ ∂μ := hmapF.symm
    _ = ∫ y, ∫ x, φ p x y ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμmem] with y hy
      apply integral_congr_ae
      filter_upwards [hμmem] with x hx
      exact hFeq x y hx hy

/-- `thm:level-sums` in full, for the contractions and natural measures of the
fixed-dimension family. `B` is the actual supremum over the open parameter disc.
The theorem holds for every holomorphic kernel with the stated derivative bounds;
boundedness of the convex domain is unnecessary, so the paper's bounded domains
are included without an additional assumption. -/
theorem levelSums {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {φ : ℂ → ℂ → ℂ → ℂ} {z₀ : ℂ} {r ρ L : ℝ} {D : Set ℂ}
    (hr : 0 < r) (hDo : IsOpen D) (hDc : Convex ℝ D)
    (ha : DifferentiableOn ℂ (ca s) (ball z₀ r))
    (hb : DifferentiableOn ℂ (cb s) (ball z₀ r))
    (hρ1 : ρ < 1)
    (hsmall : ρ * (sSup ((fun z : ℂ => ‖z‖ + ‖1 - z‖) '' ball z₀ r)) ^ 2 < 1)
    (hρ : ∀ z ∈ ball z₀ r, max ‖ca s z‖ ‖cb s z‖ ≤ ρ)
    (hD : ∀ z ∈ ball z₀ r, ∀ (m : ℕ) (ω : ℕ → Fin 2),
      cpointSeq (ca s z) (cb s z) m ω ∈ D)
    (hφ : DifferentiableOn ℂ (fun w : ℂ × ℂ × ℂ => φ w.1 w.2.1 w.2.2)
      (ball z₀ r ×ˢ (D ×ˢ D)))
    (hLx : ∀ z ∈ ball z₀ r, ∀ x ∈ D, ∀ y ∈ D,
      ‖deriv (fun t => φ z t y) x‖ ≤ L)
    (hLy : ∀ z ∈ ball z₀ r, ∀ x ∈ D, ∀ y ∈ D,
      ‖deriv (fun t => φ z x t) y‖ ≤ L) :
    TendstoUniformlyOn (levelSum (ca s) (cb s) φ) (limitSum (ca s) (cb s) φ) atTop
      (ball z₀ r) ∧
    DifferentiableOn ℂ (limitSum (ca s) (cb s) φ) (ball z₀ r) ∧
    (∀ z ∈ ball z₀ r, ‖limitSum (ca s) (cb s) φ z - φ z 0 0‖ ≤
      4 * L * (sSup ((fun w : ℂ => ‖w‖ + ‖1 - w‖) '' ball z₀ r)) ^ 2 /
        (1 - ρ * (sSup ((fun w : ℂ => ‖w‖ + ‖1 - w‖) '' ball z₀ r)) ^ 2)) ∧
    ∀ (p : ℝ) (_hpU : (p : ℂ) ∈ ball z₀ r) (hp0 : 0 < p) (hp1 : p < 1)
      (K : Set ℝ) (μ : Measure ℝ),
      (fixedSystem s p hs hp0 hp1).IsNatural K s μ →
      limitSum (ca s) (cb s) φ p = ∫ y, ∫ x, φ p x y ∂μ ∂μ := by
  obtain ⟨hunif, hhol, hbound⟩ :=
    levelSums_holomorphic_disc hr hDo hDc ha hb hρ1 hsmall hρ hD hφ hLx hLy
  refine ⟨hunif, hhol, hbound, ?_⟩
  intro p hpU hp0 hp1 K μ hμ
  have hzero : (0 : ℂ) ∈ D := hD p hpU 0 (fun _ => 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hLx p hpU 0 hzero 0 hzero)
  have hcont : ContinuousOn (fun q : ℂ × ℂ => φ p q.1 q.2) (D ×ˢ D) :=
    (hφ.comp ((differentiableOn_const _).prodMk differentiableOn_id)
      (fun q hq => ⟨hpU, hq⟩)).continuousOn
  have hlimit := tendsto_levelSum_expectation hs hs1 hp0 hp1 hDo hDc (hD p hpU) hL0 hcont
    (fun x hx y hy x' hx' y' hy' =>
      norm_kernel_sub_le_of_deriv_bound hDo hDc hφ hpU (hLx p hpU) (hLy p hpU)
        x y x' y' hx hy hx' hy')
  have hmem : ∀ᵐ ω ∂twoBern (1 - p), (fixedCode s p ω : ℂ) ∈ D := by
    filter_upwards [ae_fixedCode_lt_one hs hs1 hp0 hp1] with ω hω
    exact ofReal_mem_domain_of_cpointSeq hs hp0 hp1 hDc (hD p hpU)
      ⟨(fixedCode_mem_Icc hs hp0 hp1 ω).1, hω⟩
  exact (tendsto_nhds_unique (hunif.tendsto_at hpU) hlimit).trans
    (integral_kernel_fixedCode_eq_natural hs hp0 hp1 hμ hDo hcont hmem)

end

end BrownianImages
