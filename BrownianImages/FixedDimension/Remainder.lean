/-
`thm:remainder-derivative`: for `0 < s ≤ 1/2` and `0 < p ≤ 1/50`, the moment `M_p(s)` is
differentiable at `p` and `|M_p' - Σ'(p)| ≤ 3000 s (3p/2)^{1/s} p^{-2-s}`.

At a real parameter `x` of the disc, the level sums of the kernel are the Bernoulli double
integrals of `φ_n` at the coded points of the first `m` letters, which converge by dominated
convergence to `g_n`; so `Λ_n(x) = g_n`, `M_x = M_x(s)` by `eq:leading-ones`, `Σ(x)` is the
main term, and `Δ(x) = M_x(s) - Σ(x)`.  Cauchy's estimate for `Δ` then bounds the real
derivative of `M - Σ` at `p`.

* `levelSum_kernel_ofReal`, `tendsto_integral_kernel_codeSeq`, `kernelLimit_ofReal`:
  `Λ_n(x) = g_n`.
* `complexDelta_ofReal`: `Δ(x) = M_x(s) - Σ(x)`.
* `exists_hasDerivAt_sub_mainTerm`, `exists_hasDerivAt_fixedMoment`: the derivative bounds.
-/
import BrownianImages.FixedDimension.RemainderSup
import BrownianImages.FixedDimension.Decomposition

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-! ### Real points of the disc -/

theorem ofReal_mem_discP {p x : ℝ} (hx : x ∈ Icc (p / 2) (3 * p / 2)) : (x : ℂ) ∈ discP p := by
  rw [mem_discP, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem pos_of_mem {p x : ℝ} (hp0 : 0 < p) (hx : x ∈ Icc (p / 2) (3 * p / 2)) : 0 < x := by
  linarith [hx.1]

theorem lt_one_of_mem {p x : ℝ} (hp : p ≤ 1/50) (hx : x ∈ Icc (p / 2) (3 * p / 2)) : x < 1 := by
  linarith [hx.2]

/-- The coded points of a real parameter lie in the unit interval, hence in the bidisc. -/
theorem norm_ofReal_codeSeq_le {s x : ℝ} (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1)
    (ω : ℕ → Fin 2) (m : ℕ) :
    ‖((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ)‖ ≤ 5 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have := codeSeq_mem_Icc (fixedSystem s x hs hx0 hx1) ω m
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem norm_ofReal_code_le {s x : ℝ} (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (ω : ℕ → Fin 2) :
    ‖((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ)‖ ≤ 5 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have := code_mem_Icc (fixedSystem s x hs hx0 hx1) ω
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-- The kernel at the coded points of the first `m` letters, as a function of two words. -/
def kernelSeq (s x : ℝ) (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (n m : ℕ)
    (ω ω' : ℕ → Fin 2) : ℂ :=
  kernelN s n (x : ℂ) ((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ)
    ((codeSeq (fixedSystem s x hs hx0 hx1) ω' m : ℝ) : ℂ)

/-- The kernel at the coded points. -/
def kernelCode (s x : ℝ) (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) (ω ω' : ℕ → Fin 2) : ℂ :=
  kernelN s n (x : ℂ) ((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ)
    ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ)

theorem measurable_kernelN_comp {s x : ℝ} {X Y : (ℕ → Fin 2) × (ℕ → Fin 2) → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (n : ℕ) :
    Measurable fun q => kernelN s n (x : ℂ) (X q : ℂ) (Y q : ℂ) := by
  unfold kernelN kernelBase
  have hX' : Measurable fun q => (X q : ℂ) := Complex.measurable_ofReal.comp hX
  have hY' : Measurable fun q => (Y q : ℂ) := Complex.measurable_ofReal.comp hY
  exact ((measurable_const.sub measurable_const).sub
    (measurable_const.mul (hX'.sub (measurable_const.mul hY')))).pow measurable_const

theorem measurable_kernelSeq {s x : ℝ} (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (n m : ℕ) :
    Measurable (Function.uncurry (kernelSeq s x hs hx0 hx1 n m)) :=
  measurable_kernelN_comp ((continuous_codeSeq _ m).measurable.comp measurable_fst)
    ((continuous_codeSeq _ m).measurable.comp measurable_snd) n

theorem measurable_kernelCode {s x : ℝ} (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    Measurable (Function.uncurry (kernelCode s x hs hx0 hx1 n)) :=
  measurable_kernelN_comp ((measurable_code _).comp measurable_fst)
    ((measurable_code _).comp measurable_snd) n

theorem norm_kernelSeq_le {s p x : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (hx : x ∈ Icc (p / 2) (3 * p / 2)) (n m : ℕ) (ω ω' : ℕ → Fin 2) :
    ‖kernelSeq s x hs (pos_of_mem hp0 hx) (lt_one_of_mem hp hx) n m ω ω'‖
      ≤ ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s) :=
  norm_kernelN_le hs hs1 hp0 hp n (ofReal_mem_discP hx)
    (norm_ofReal_codeSeq_le hs _ _ ω m) (norm_ofReal_codeSeq_le hs _ _ ω' m)

/-- The level sum of the kernel at a real parameter is the Bernoulli double integral of the
kernel at the coded points of the first `m` letters. -/
theorem levelSum_kernel_ofReal {s p x : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) (hx : x ∈ Icc (p / 2) (3 * p / 2)) (n m : ℕ) :
    levelSum (ca s) (cb s) (kernelN s n) m (x : ℂ)
      = ∫ ω', ∫ ω, kernelSeq s x hs (pos_of_mem hp0 hx) (lt_one_of_mem hp hx) n m ω ω'
          ∂twoBern (1 - x) ∂twoBern (1 - x) := by
  have hx0 := pos_of_mem hp0 hx
  have hx1 := lt_one_of_mem hp hx
  have hcode : ∀ ω : ℕ → Fin 2, cpointSeq (ca s (x : ℂ)) (cb s (x : ℂ)) m ω
      = ((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ) := fun ω => by
    rw [ca_ofReal hx0.le, cb_ofReal hx1.le, cpointSeq_ofReal hs hx0 hx1]
  have hdep : ∀ ω₁ ω₁' ω₂ ω₂' : ℕ → Fin 2, (∀ k < m, ω₁ k = ω₁' k) → (∀ k < m, ω₂ k = ω₂' k) →
      kernelSeq s x hs hx0 hx1 n m ω₁ ω₂ = kernelSeq s x hs hx0 hx1 n m ω₁' ω₂' := by
    intro ω₁ ω₁' ω₂ ω₂' h₁ h₂
    unfold kernelSeq
    rw [← hcode, ← hcode, ← hcode ω₁', ← hcode ω₂', cpointSeq_congr _ _ m h₁,
      cpointSeq_congr _ _ m h₂]
  rw [integral_integral_eq_sum_weight hx0.le hx1.le m (measurable_kernelSeq hs hx0 hx1 n m)
    (fun ω ω' => norm_kernelSeq_le hs hs1 hp0 hp hx n m ω ω') hdep]
  unfold levelSum
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [weightSeq_ofReal, weightSeq_ofReal, hcode, hcode]
  rfl

/-- Dominated convergence: the double integrals of the kernel at the first `m` letters
converge to the double integral at the coded points. -/
theorem tendsto_integral_kernel_codeSeq {s p x : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) (hx : x ∈ Icc (p / 2) (3 * p / 2)) (n : ℕ) :
    Tendsto (fun m => ∫ ω', ∫ ω, kernelSeq s x hs (pos_of_mem hp0 hx) (lt_one_of_mem hp hx) n m ω ω'
        ∂twoBern (1 - x) ∂twoBern (1 - x)) atTop
      (𝓝 (∫ ω', ∫ ω, kernelCode s x hs (pos_of_mem hp0 hx) (lt_one_of_mem hp hx) n ω ω'
        ∂twoBern (1 - x) ∂twoBern (1 - x))) := by
  have hx0 := pos_of_mem hp0 hx
  have hx1 := lt_one_of_mem hp hx
  have hprob : IsProbabilityMeasure (twoBern (1 - x)) := isProbabilityMeasure_twoBern_fixed hx0 hx1
  set C := ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s) with hC
  -- pointwise convergence
  have hpt : ∀ ω ω' : ℕ → Fin 2, Tendsto (fun m => kernelSeq s x hs hx0 hx1 n m ω ω') atTop
      (𝓝 (kernelCode s x hs hx0 hx1 n ω ω')) := by
    intro ω ω'
    have h1 : Tendsto (fun m => (((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ),
          ((codeSeq (fixedSystem s x hs hx0 hx1) ω' m : ℝ) : ℂ))) atTop
        (𝓝 (((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ),
          ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ))) :=
      ((Complex.continuous_ofReal.tendsto _).comp (tendsto_codeSeq _ ω)).prodMk_nhds
        ((Complex.continuous_ofReal.tendsto _).comp (tendsto_codeSeq _ ω'))
    have hcont : ContinuousAt (fun q : ℂ × ℂ => kernelN s n (x : ℂ) q.1 q.2)
        (((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ),
          ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ)) := by
      unfold kernelN kernelBase
      refine ContinuousAt.cpow ?_ continuousAt_const ?_
      · exact (continuousAt_const.sub (continuousAt_const.mul (continuousAt_fst.sub
          (continuousAt_const.mul continuousAt_snd))))
      · exact kernelBase_mem_slitPlane hs hs1 hp0 hp n (ofReal_mem_discP hx)
          (norm_ofReal_code_le hs _ _ ω) (norm_ofReal_code_le hs _ _ ω')
    have h2 := hcont.tendsto.comp h1
    unfold kernelSeq kernelCode
    exact h2
  -- the inner integrals converge
  have hinner : ∀ ω', Tendsto (fun m => ∫ ω, kernelSeq s x hs hx0 hx1 n m ω ω' ∂twoBern (1 - x))
      atTop (𝓝 (∫ ω, kernelCode s x hs hx0 hx1 n ω ω' ∂twoBern (1 - x))) := by
    intro ω'
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
      ((integrable_const C : Integrable (fun _ : ℕ → Fin 2 => C) (twoBern (1 - x)))) (fun m => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => hpt ω ω')
    · exact ((measurable_kernelSeq hs hx0 hx1 n m).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · exact norm_kernelSeq_le hs hs1 hp0 hp hx n m ω ω'
  -- the outer integrals converge
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
    ((integrable_const C : Integrable (fun _ : ℕ → Fin 2 => C) (twoBern (1 - x)))) (fun m => Eventually.of_forall fun ω' => ?_)
    (Eventually.of_forall hinner)
  · exact ((measurable_kernelSeq hs hx0 hx1 n m).stronglyMeasurable.integral_prod_left'
      (μ := twoBern (1 - x))).aestronglyMeasurable
  · have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - x))
      (f := fun ω => kernelSeq s x hs hx0 hx1 n m ω ω')
      (Eventually.of_forall fun ω => norm_kernelSeq_le hs hs1 hp0 hp hx n m ω ω')
    rwa [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at h

/-- `Λ_n(x) = g_n` at a real parameter of the disc. -/
theorem kernelLimit_ofReal {s p x : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (hx : x ∈ Icc (p / 2) (3 * p / 2)) (n : ℕ) :
    kernelLimit s n (x : ℂ) = ((leadingTerm s x n : ℝ) : ℂ) := by
  have hx0 := pos_of_mem hp0 hx
  have hx1 := lt_one_of_mem hp hx
  have hs1' : s < 1 := by linarith
  have h1 : Tendsto (fun m => levelSum (ca s) (cb s) (kernelN s n) m (x : ℂ)) atTop
      (𝓝 (kernelLimit s n (x : ℂ))) :=
    tendsto_levelSum (discR_nonneg hp0 hp) (discR_lt_one hs hs1 hp0 hp)
      (incrementBound_kernel hs hs1 hp0 hp n) (ofReal_mem_discP hx)
  have h2 := tendsto_integral_kernel_codeSeq hs hs1 hp0 hp hx n
  simp_rw [← levelSum_kernel_ofReal hs hs1 hp0 hp hx n] at h2
  rw [tendsto_nhds_unique h1 h2]
  -- the double integral of the kernel is the real `g_n`
  have hreal : ∀ ω ω' : ℕ → Fin 2,
      kernelCode s x hs (pos_of_mem hp0 hx) (lt_one_of_mem hp hx) n ω ω'
        = (((1 - fixedB s x ^ (n + 1) - fixedA s x *
            (fixedCode s x ω - fixedB s x ^ (n + 1) * fixedCode s x ω')) ^ (-s) : ℝ) : ℂ) := by
    intro ω ω'
    unfold kernelCode
    rw [kernelN_ofReal hs hs1' hx0 hx1 n (code_mem_Icc _ ω) (code_mem_Icc _ ω'),
      fixedCode_eq hs hx0 hx1, fixedCode_eq hs hx0 hx1]
  have hinner : ∀ ω' : ℕ → Fin 2,
      (∫ ω, kernelCode s x hs (pos_of_mem hp0 hx) (lt_one_of_mem hp hx) n ω ω' ∂twoBern (1 - x))
        = ((∫ ω, (1 - fixedB s x ^ (n + 1) - fixedA s x *
            (fixedCode s x ω - fixedB s x ^ (n + 1) * fixedCode s x ω')) ^ (-s)
              ∂twoBern (1 - x) : ℝ) : ℂ) := by
    intro ω'
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun ω => hreal ω ω')
  rw [integral_congr_ae (Eventually.of_forall hinner), integral_complex_ofReal]
  rfl

/-- `Σ(x)` is the main term at a real parameter of the disc. -/
theorem complexMainTerm_ofReal {s p x : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (hx : x ∈ Icc (p / 2) (3 * p / 2)) :
    complexMainTerm s (x : ℂ) = ((mainTerm s x : ℝ) : ℂ) := by
  have hx0 := pos_of_mem hp0 hx
  have hx1 := lt_one_of_mem hp hx
  unfold complexMainTerm mainTerm
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hb0 := fixedB_pos (s := s) hx1
  have hb1 := fixedB_le_one hs hx0 hx1
  have hbn : fixedB s x ^ (n + 1) ≤ 1 := pow_le_one₀ hb0.le hb1
  have e := Complex.ofReal_cpow (show (0:ℝ) ≤ 1 - fixedB s x ^ (n + 1) by linarith) (-s)
  push_cast at e
  rw [cb_ofReal hx1.le, ← e]
  push_cast
  ring

/-- `Δ(x) = M_x(s) - Σ(x)` at a real parameter of the disc. -/
theorem complexDelta_ofReal {s p x : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (hx : x ∈ Icc (p / 2) (3 * p / 2)) :
    complexDelta s (x : ℂ) = ((fixedMoment s x - mainTerm s x : ℝ) : ℂ) := by
  have hx0 := pos_of_mem hp0 hx
  have hx1 := lt_one_of_mem hp hx
  have hs1' : s < 1 := by linarith
  have hb0 := fixedB_pos (s := s) hx1
  have hb1 := fixedB_le_one hs hx0 hx1
  -- the terms of `Δ` are the real differences
  have hterm : ∀ n : ℕ, (x : ℂ) * (1 - (x : ℂ)) ^ n *
      (kernelLimit s n (x : ℂ) - (1 - cb s (x : ℂ) ^ (n + 1)) ^ (-(s : ℂ)))
      = ((x * (1 - x) ^ n * leadingTerm s x n - x * (1 - x) ^ n * (1 - fixedB s x ^ (n + 1)) ^ (-s)
          : ℝ) : ℂ) := by
    intro n
    have hbn : fixedB s x ^ (n + 1) ≤ 1 := pow_le_one₀ hb0.le hb1
    have e := Complex.ofReal_cpow (show (0:ℝ) ≤ 1 - fixedB s x ^ (n + 1) by linarith) (-s)
    push_cast at e
    rw [kernelLimit_ofReal hs hs1 hp0 hp hx n, cb_ofReal hx1.le, ← e]
    push_cast
    ring
  unfold complexDelta
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum]
  congr 1
  have h1 := hasSum_leadingTerm hs hs1' hx0 hx1
  have h2 := summable_mainTerm_terms hs (by linarith) hx0 hx1
  rw [h1.summable.tsum_sub h2, h1.tsum_eq]
  rfl

/-! ### `thm:remainder-derivative` -/

/-- The real derivative of `M - Σ` at `p` is the real part of `Δ'(p)`. -/
theorem exists_hasDerivAt_sub_mainTerm {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) :
    ∃ D, HasDerivAt (fun x => fixedMoment s x - mainTerm s x) D p ∧
      |D| ≤ 2592 * s * alphaP s p * p ^ (-2 - s) := by
  have hR : 0 < p / 2 := by positivity
  have hdiff : DifferentiableAt ℂ (complexDelta s) (p : ℂ) :=
    (differentiableOn_complexDelta hs hs1 hp0 hp).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hc := hdiff.hasDerivAt
  have hr := hc.real_of_complex
  refine ⟨(deriv (complexDelta s) (p : ℂ)).re, ?_, ?_⟩
  · refine hr.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show p / 2 < p by linarith) (show p < 3 * p / 2 by linarith)]
      with x hx
    rw [complexDelta_ofReal hs hs1 hp0 hp ⟨hx.1.le, hx.2.le⟩, Complex.ofReal_re]
  · exact (Complex.abs_re_le_norm _).trans (norm_deriv_complexDelta_le hs hs1 hp0 hp)

/-- **`thm:remainder-derivative`.**  For `0 < s ≤ 1/2` and `0 < p ≤ 1/50`, `M_p(s)` is
differentiable at `p`, and its derivative differs from that of the main term by at most
`3000 s (3p/2)^{1/s} p^{-2-s}`. -/
theorem exists_hasDerivAt_fixedMoment {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) :
    ∃ D D', HasDerivAt (fixedMoment s) D p ∧ HasDerivAt (mainTerm s) D' p ∧
      |D - D'| ≤ 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) := by
  obtain ⟨E, hE, hEb⟩ := exists_hasDerivAt_sub_mainTerm hs hs1 hp0 hp
  obtain ⟨D', hD', -⟩ := exists_hasDerivAt_mainTerm hs hs1 hp0 hp
  refine ⟨E + D', D', ?_, hD', ?_⟩
  · have := hE.add hD'
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    simp
  · rw [add_sub_cancel_right]
    refine hEb.trans ?_
    unfold alphaP
    have : 0 ≤ s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) := by positivity
    nlinarith

end

end BrownianImages
