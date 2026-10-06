/-
The level sums at a real parameter, for every `p ∈ (0,1)` and `s ∈ (0,1)`: the cross kernel
at coded points is bounded by `(1 - a - b)^{-s}`, the level sum `Λ^{(m)}(p)` is the double
Bernoulli integral of the kernel at the coded points of the first `m` letters, and
dominated convergence gives `Λ^{(m)}(p) → M_p(s)`.  This is the step "the finite-address
measures converge weakly to `μ_p`" of `thm:fixed-dimension-analyticity`.

* `crossGap`: the gap `1 - a - b`.
* `norm_crossKernelC_ofReal_le`: the kernel bound at real parameters.
* `levelSum_cross_ofReal'`: the level sum as a double integral.
* `tendsto_levelSum_ofReal`: `Λ^{(m)}(p) → M_p(s)`.
-/
import BrownianImages.FixedDimension.SecondDerivative

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- The gap `1 - a - b` of the first-level intervals. -/
def crossGap (s p : ℝ) : ℝ := 1 - fixedA s p - fixedB s p

theorem crossGap_pos {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < crossGap s p := by
  unfold crossGap; linarith [fixedA_add_fixedB_lt_one hs hs1 hp0 hp1]

/-- The base of the cross kernel at a real parameter and real points is the real cross
distance. -/
theorem crossBase_ofReal {s x X Y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    crossBase s (x : ℂ) (X : ℂ) (Y : ℂ) = ((fixedCross s x X Y : ℝ) : ℂ) := by
  unfold crossBase fixedCross
  rw [ca_ofReal hx0, cb_ofReal hx1]
  push_cast
  ring

theorem crossBase_ofReal_mem_slitPlane {s x X Y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1) :
    crossBase s (x : ℂ) (X : ℂ) (Y : ℂ) ∈ Complex.slitPlane := by
  rw [crossBase_ofReal hx0.le hx1.le, Complex.mem_slitPlane_iff]
  left
  rw [Complex.ofReal_re]
  exact fixedCross_pos hs hs1 hx0 hx1 hX hY

/-- The cross kernel at a real parameter and real points of `[0,1]` is bounded by
`(1 - a - b)^{-s}`. -/
theorem norm_crossKernelC_ofReal_le {s x X Y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1) :
    ‖crossKernelC s (x : ℂ) (X : ℂ) (Y : ℂ)‖ ≤ crossGap s x ^ (-s) := by
  rw [crossKernelC_ofReal hs hs1 hx0 hx1 hX hY, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (fixedCross_pos hs hs1 hx0 hx1 hX hY).le _)]
  exact rpow_neg_antitone (crossGap_pos hs hs1 hx0 hx1) (fixedCross_mem hs hx0 hx1 hX hY).1 hs.le

theorem norm_crossSeq_le' {s x : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (m : ℕ) (ω ω' : ℕ → Fin 2) :
    ‖crossSeq s x hs hx0 hx1 m ω ω'‖ ≤ crossGap s x ^ (-s) := by
  unfold crossSeq
  exact norm_crossKernelC_ofReal_le hs hs1 hx0 hx1 (codeSeq_mem_Icc _ ω m) (codeSeq_mem_Icc _ ω' m)

theorem norm_crossCode_le {s x : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (ω ω' : ℕ → Fin 2) :
    ‖crossCode s x hs hx0 hx1 ω ω'‖ ≤ crossGap s x ^ (-s) := by
  unfold crossCode
  exact norm_crossKernelC_ofReal_le hs hs1 hx0 hx1 (code_mem_Icc _ ω) (code_mem_Icc _ ω')

/-- The level sum at a real parameter is the double Bernoulli integral of the kernel at the
coded points of the first `m` letters. -/
theorem levelSum_cross_ofReal' {s x : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (m : ℕ) :
    levelSum (ca s) (cb s) (crossKernelC s) m (x : ℂ)
      = ∫ ω', ∫ ω, crossSeq s x hs hx0 hx1 m ω ω' ∂twoBern (1 - x) ∂twoBern (1 - x) := by
  have hcode : ∀ ω : ℕ → Fin 2, cpointSeq (ca s (x : ℂ)) (cb s (x : ℂ)) m ω
      = ((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ) := fun ω => by
    rw [ca_ofReal hx0.le, cb_ofReal hx1.le, cpointSeq_ofReal hs hx0 hx1]
  have hdep : ∀ ω₁ ω₁' ω₂ ω₂' : ℕ → Fin 2, (∀ k < m, ω₁ k = ω₁' k) → (∀ k < m, ω₂ k = ω₂' k) →
      crossSeq s x hs hx0 hx1 m ω₁ ω₂ = crossSeq s x hs hx0 hx1 m ω₁' ω₂' := by
    intro ω₁ ω₁' ω₂ ω₂' h₁ h₂
    unfold crossSeq
    rw [← hcode, ← hcode, ← hcode ω₁', ← hcode ω₂', cpointSeq_congr _ _ m h₁,
      cpointSeq_congr _ _ m h₂]
  rw [integral_integral_eq_sum_weight hx0.le hx1.le m (measurable_crossSeq hs hx0 hx1 m)
    (fun ω ω' => norm_crossSeq_le' hs hs1 hx0 hx1 m ω ω') hdep]
  unfold levelSum
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [weightSeq_ofReal, weightSeq_ofReal, hcode, hcode]
  rfl

/-- Dominated convergence of the finite-address kernels to the kernel at the coded points. -/
theorem tendsto_integral_cross_codeSeq' {s x : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun m => ∫ ω', ∫ ω, crossSeq s x hs hx0 hx1 m ω ω'
        ∂twoBern (1 - x) ∂twoBern (1 - x)) atTop
      (𝓝 (∫ ω', ∫ ω, crossCode s x hs hx0 hx1 ω ω' ∂twoBern (1 - x) ∂twoBern (1 - x))) := by
  have hprob : IsProbabilityMeasure (twoBern (1 - x)) := isProbabilityMeasure_twoBern_fixed hx0 hx1
  set C := crossGap s x ^ (-s) with hC
  have hpt : ∀ ω ω' : ℕ → Fin 2, Tendsto (fun m => crossSeq s x hs hx0 hx1 m ω ω') atTop
      (𝓝 (crossCode s x hs hx0 hx1 ω ω')) := by
    intro ω ω'
    have h1 : Tendsto (fun m => (((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ),
          ((codeSeq (fixedSystem s x hs hx0 hx1) ω' m : ℝ) : ℂ))) atTop
        (𝓝 (((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ),
          ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ))) :=
      ((Complex.continuous_ofReal.tendsto _).comp (tendsto_codeSeq _ ω)).prodMk_nhds
        ((Complex.continuous_ofReal.tendsto _).comp (tendsto_codeSeq _ ω'))
    have hcont : ContinuousAt (fun q : ℂ × ℂ => crossKernelC s (x : ℂ) q.1 q.2)
        (((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ),
          ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ)) := by
      unfold crossKernelC
      refine ContinuousAt.cpow ?_ continuousAt_const ?_
      · unfold crossBase
        exact ((continuousAt_const.sub continuousAt_const).add
          (continuousAt_const.mul continuousAt_snd)).sub (continuousAt_const.mul continuousAt_fst)
      · exact crossBase_ofReal_mem_slitPlane hs hs1 hx0 hx1 (code_mem_Icc _ ω) (code_mem_Icc _ ω')
    have h2 := hcont.tendsto.comp h1
    unfold crossSeq crossCode
    exact h2
  have hinner : ∀ ω', Tendsto (fun m => ∫ ω, crossSeq s x hs hx0 hx1 m ω ω' ∂twoBern (1 - x))
      atTop (𝓝 (∫ ω, crossCode s x hs hx0 hx1 ω ω' ∂twoBern (1 - x))) := by
    intro ω'
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
      ((integrable_const C : Integrable (fun _ : ℕ → Fin 2 => C) (twoBern (1 - x))))
      (fun m => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => hpt ω ω')
    · exact ((measurable_crossSeq hs hx0 hx1 m).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · exact norm_crossSeq_le' hs hs1 hx0 hx1 m ω ω'
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
    ((integrable_const C : Integrable (fun _ : ℕ → Fin 2 => C) (twoBern (1 - x))))
    (fun m => Eventually.of_forall fun ω' => ?_) (Eventually.of_forall hinner)
  · exact ((measurable_crossSeq hs hx0 hx1 m).stronglyMeasurable.integral_prod_left'
      (μ := twoBern (1 - x))).aestronglyMeasurable
  · have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - x))
      (f := fun ω => crossSeq s x hs hx0 hx1 m ω ω')
      (Eventually.of_forall fun ω => norm_crossSeq_le' hs hs1 hx0 hx1 m ω ω')
    rwa [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at h

/-- The kernel at the coded points integrates to `M_p(s)`. -/
theorem integral_crossCode_eq {s x : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    (∫ ω', ∫ ω, crossCode s x hs hx0 hx1 ω ω' ∂twoBern (1 - x) ∂twoBern (1 - x))
      = ((fixedMoment s x : ℝ) : ℂ) := by
  have hreal : ∀ ω ω' : ℕ → Fin 2,
      crossCode s x hs hx0 hx1 ω ω' = ((fixedKernel s x ω ω' : ℝ) : ℂ) := by
    intro ω ω'
    unfold crossCode fixedKernel
    rw [crossKernelC_ofReal hs hs1 hx0 hx1 (code_mem_Icc _ ω) (code_mem_Icc _ ω'),
      fixedCode_eq hs hx0 hx1, fixedCode_eq hs hx0 hx1]
  have hinner : ∀ ω' : ℕ → Fin 2,
      (∫ ω, crossCode s x hs hx0 hx1 ω ω' ∂twoBern (1 - x))
        = ((∫ ω, fixedKernel s x ω ω' ∂twoBern (1 - x) : ℝ) : ℂ) := by
    intro ω'
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun ω => hreal ω ω')
  rw [integral_congr_ae (Eventually.of_forall hinner), integral_complex_ofReal]
  rfl

/-- **`Λ^{(m)}(p) → M_p(s)`** at every real parameter `p ∈ (0,1)`. -/
theorem tendsto_levelSum_ofReal {s x : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun m => levelSum (ca s) (cb s) (crossKernelC s) m (x : ℂ)) atTop
      (𝓝 ((fixedMoment s x : ℝ) : ℂ)) := by
  have h := tendsto_integral_cross_codeSeq' hs hs1 hx0 hx1
  rw [integral_crossCode_eq hs hs1 hx0 hx1] at h
  refine h.congr fun m => ?_
  rw [levelSum_cross_ofReal' hs hs1 hx0 hx1 m]

end

end BrownianImages
