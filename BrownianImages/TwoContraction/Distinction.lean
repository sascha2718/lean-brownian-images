/-
`thm:two-contraction-distinction`: along the family `x ↦ x/2`, `x ↦ cx + 1 - c`, the mean
`H̄(c)` of the expected profile, each normalised at its own dimension, is strictly
increasing in `c`.

Parametrise by the dimension `s`, with `c = c(s)` and `q = 1 - 2^{-s}`.  By
`eq:two-contraction-mean-factorisation`, `H̄ = F(s) M(s)` with `M(s) = J(s, c(s), q(s))`.
The three steps of `TwoContraction.Moment` give, for `y` slightly above `s`,
`M(y) ≥ M(s)(1 - (q(y) - q(s)) L̃(s))`, and the same with the roles exchanged below `s`;
the rate `q'(s) L̃(s)` is bounded by `eq:loss-rate-bound`.  The
derivative of `log F` beats it (`logPrefactorDeriv_sub_momentLoss_pos`), so
`log F + log M` is locally strictly increasing on both sides at every point, hence
strictly increasing (`strictMonoOn_of_local`).  This replaces the differentiation of `M`
in the tex by one-sided finite differences.

* `pairWeight`, `momentM`, `lossRate`: `q(s)`, `M(s)` and `L̃(s)`.
* `crossMoment_eq_momentM`, `twoContractionMean_eq`: `H̄ = F(s) M(s)`.
* `momentM_right`, `momentM_left`: the one-sided bounds on `M`.
* `strictMonoOn_logMean`, `twoContractionMean_lt`: strict monotonicity of the mean.
* `exists_ge_abs_sub_of_tendsto_avg`: distinct means force the profiles apart.
-/
import BrownianImages.TwoContraction.Moment
import BrownianImages.TwoContraction.Prefactor
import BrownianImages.TwoContraction.Local

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology ENNReal

noncomputable section

/-- The weight `q(s) = 1 - 2^{-s}` of the second map along the family. -/
def pairWeight (s : ℝ) : ℝ := 1 - (2:ℝ) ^ (-s)

/-- `M(s) = J(s, c(s), q(s)) = 𝔼 Z_{c(s)}^{-s}`. -/
def momentM (s : ℝ) : ℝ := crossJ s (pairRatio s) (pairWeight s)

/-- The loss rate `L̃(s) = 2s c(1-c)/((1/2 - c)(1 - q))` of the weight step at the natural
parameters. -/
def lossRate (s : ℝ) : ℝ :=
  2 * s * pairRatio s * (1 - pairRatio s) / ((1/2 - pairRatio s) * (1 - pairWeight s))

theorem pairWeight_mem {s : ℝ} (hs0 : 0 < s) : 0 < pairWeight s ∧ pairWeight s < 1 := by
  obtain ⟨h0, h1⟩ := two_rpow_neg_mem hs0
  exact ⟨by unfold pairWeight; linarith, by unfold pairWeight; linarith⟩

theorem pairWeight_le {s s' : ℝ} (hss : s ≤ s') : pairWeight s ≤ pairWeight s' := by
  unfold pairWeight
  have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (neg_le_neg hss)
  linarith

theorem hasDerivAt_pairWeight (s : ℝ) :
    HasDerivAt pairWeight (Real.log 2 * (2:ℝ) ^ (-s)) s := by
  have h := (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_two_rpow_neg s)
  exact h.congr_deriv (by ring)

theorem pairRatio_rpow_eq_pairWeight {s : ℝ} (hs0 : 0 < s) :
    pairRatio s ^ s = pairWeight s := pairRatio_rpow hs0

theorem one_le_momentM {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 1 ≤ momentM s :=
  one_le_crossJ hs0.le (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)
    (pairWeight_mem hs0).1.le (pairWeight_mem hs0).2.le

/-! ### `H̄ = F(s) M(s)` -/

/-- At the natural measure, `M_c(s) = M(s)`. -/
theorem crossMoment_eq_momentM {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {K : Set ℝ}
    {μ : Measure ℝ} (hμ : (pairSystem (pairRatio s) (pairRatio_pos hs0)
      (pairRatio_lt_half hs0 hs1)).IsNatural K s μ) :
    crossMoment (pairRatio s) μ s = momentM s := by
  set c := pairRatio s with hc
  have hc0 : 0 < c := pairRatio_pos hs0
  have hch : c < 1/2 := pairRatio_lt_half hs0 hs1
  have hdim := pairSystem_isDimension hs0 hs1
  have hmap := map_twoCode_twoBern hc0 hch hdim hμ
  rw [pairRatio_rpow_eq_pairWeight hs0] at hmap
  have hq := pairWeight_mem hs0
  have := isProbabilityMeasure_twoBern hq.1.le hq.2.le
  set B := twoBern (pairWeight s)
  have hπ := measurable_twoCode c
  have hint : Integrable (fun p : (ℕ → Fin 2) × (ℕ → Fin 2) => crossKernel s c p.1 p.2)
      (B.prod B) :=
    integrable_of_abs_le (measurable_crossKernel s c) (C := (1/2 - c) ^ (-s))
      fun p => abs_crossKernel_le hs0.le hc0 hch p.1 p.2
  unfold crossMoment momentM crossJ
  rw [← hmap, Measure.map_prod_map B B hπ hπ, integral_map (hπ.prodMap hπ).aemeasurable
    ((continuous_crossDist c).measurable.pow_const _).aestronglyMeasurable]
  simp only [Prod.map_fst, Prod.map_snd, ← crossKernel_def]
  exact integral_prod_symm _ hint

/-- **`eq:two-contraction-mean-factorisation`**: `H̄(c(s)) = F(s) M(s)` with
`log F = logPrefactor`. -/
theorem twoContractionMean_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {K : Set ℝ}
    {μ : Measure ℝ} (hμ : (pairSystem (pairRatio s) (pairRatio_pos hs0)
      (pairRatio_lt_half hs0 hs1)).IsNatural K s μ) :
    twoContractionMean (pairRatio s) s μ = Real.exp (logPrefactor s) * momentM s := by
  rw [twoContractionMean, crossMoment_eq_momentM hs0 hs1 hμ]
  set c := pairRatio s with hc
  have hc0 : 0 < c := pairRatio_pos hs0
  obtain ⟨hp0, hp1⟩ := two_rpow_neg_mem hs0
  set p := (2:ℝ) ^ (-s) with hp
  have hq0 : 0 < 1 - p := by linarith
  have hE := prefE_pos hs0
  have hΓ : 0 < Real.Gamma (1 - s) := Real.Gamma_pos_of_pos (by linarith)
  have hhalf : (1/2 : ℝ) ^ s = p := by
    rw [hp, Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
  have hcs : c ^ s = 1 - p := pairRatio_rpow hs0
  have hlogc : s * Real.log c⁻¹ = -Real.log (1 - p) := by
    rw [Real.log_inv, ← hcs, Real.log_rpow hc0]; ring
  have hden : s * ((1/2 : ℝ) ^ s * Real.log 2 + c ^ s * Real.log c⁻¹) = prefE s := by
    rw [hhalf, hcs, prefE, ← hp]
    have : s * (p * Real.log 2 + (1 - p) * Real.log c⁻¹)
        = s * Real.log 2 * p + (1 - p) * (s * Real.log c⁻¹) := by ring
    rw [this, hlogc]; ring
  have hexp : Real.exp (logPrefactor s) = 2 * p ^ 2 * (1 - p) * Real.Gamma (1 - s) / prefE s := by
    unfold logPrefactor
    rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num),
      Real.exp_log hq0, Real.exp_log hΓ, Real.exp_log hE]
    have : Real.exp (2 * s * Real.log 2) = (p ^ 2)⁻¹ := by
      rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos
        (by norm_num), ← Real.exp_neg]
      congr 1; push_cast; ring
    rw [this]
    field_simp
  rw [hden, hexp, hhalf, hcs]
  field_simp

/-! ### The one-sided bounds on `M` -/

/-- **`eq:moment-above`**: `M(y) ≥ M(s)(1 - (q(y) - q(s)) L̃(s))` for `y` slightly larger
than `s`,
by the weight, contraction and exponent steps in turn. -/
theorem momentM_right {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ᶠ y in 𝓝[>] s,
      momentM s * (1 - (pairWeight y - pairWeight s) * lossRate s) ≤ momentM y := by
  have hcont : ContinuousAt (fun y => pairWeight y * (3 - 2 * pairRatio s)) s :=
    ((hasDerivAt_pairWeight s).continuousAt).mul continuousAt_const
  have hlt : pairWeight s * (3 - 2 * pairRatio s) < 1 := pairWeight_mul_lt_one hs0 hs1
  have hev1 : ∀ᶠ y in 𝓝 s, pairWeight y * (3 - 2 * pairRatio s) < 1 :=
    hcont.eventually (gt_mem_nhds hlt)
  have hev2 : ∀ᶠ y in 𝓝 s, y < 1 := Iio_mem_nhds hs1
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
    with y hy1 hy2 hsy
  have hy0 : 0 < y := hs0.trans hsy
  have hc0 := pairRatio_pos hs0
  have hch := pairRatio_lt_half hs0 hs1
  have hc'0 := pairRatio_pos hy0
  have hc'h := pairRatio_lt_half hy0 hy2
  have hcc := (pairRatio_lt_pairRatio hs0 hsy).le
  have hq := pairWeight_mem hs0
  have hq' := pairWeight_mem hy0
  have hqq := pairWeight_le (le_of_lt hsy)
  calc momentM s * (1 - (pairWeight y - pairWeight s) * lossRate s)
      ≤ crossJ s (pairRatio s) (pairWeight y) :=
        crossJ_weight_ge hs0.le hc0 hch hq.1.le hqq hq'.2.le hq.2
    _ ≤ crossJ s (pairRatio y) (pairWeight y) :=
        crossJ_mono_contraction hs0.le hc0 hcc hc'h hq'.1.le hq'.2.le hy1.le
    _ ≤ crossJ y (pairRatio y) (pairWeight y) :=
        crossJ_mono_exponent hs0.le (le_of_lt hsy) hc'0 hc'h hq'.1.le hq'.2.le

/-- **`eq:moment-below`**: `M(s) ≥ M(y)(1 - (q(s) - q(y)) L̃(y))` for `y` slightly smaller
than `s`. -/
theorem momentM_left {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ᶠ y in 𝓝[<] s,
      momentM y * (1 - (pairWeight s - pairWeight y) * lossRate y) ≤ momentM s := by
  have hcont : ContinuousAt (fun y => pairWeight s * (3 - 2 * pairRatio y)) s :=
    continuousAt_const.mul (continuousAt_const.sub
      (continuousAt_const.mul (differentiableAt_pairRatio hs0).continuousAt))
  have hlt : pairWeight s * (3 - 2 * pairRatio s) < 1 := pairWeight_mul_lt_one hs0 hs1
  have hev1 : ∀ᶠ y in 𝓝 s, pairWeight s * (3 - 2 * pairRatio y) < 1 :=
    hcont.eventually (gt_mem_nhds hlt)
  have hev2 : ∀ᶠ y in 𝓝 s, 0 < y := Ioi_mem_nhds hs0
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
    with y hy1 hy0 hys
  have hy1' : y < 1 := hys.trans hs1
  have hc0 := pairRatio_pos hs0
  have hch := pairRatio_lt_half hs0 hs1
  have hc'0 := pairRatio_pos hy0
  have hc'h := pairRatio_lt_half hy0 hy1'
  have hcc := (pairRatio_lt_pairRatio hy0 hys).le
  have hq := pairWeight_mem hs0
  have hq' := pairWeight_mem hy0
  have hqq := pairWeight_le (le_of_lt hys)
  calc momentM y * (1 - (pairWeight s - pairWeight y) * lossRate y)
      ≤ crossJ y (pairRatio y) (pairWeight s) :=
        crossJ_weight_ge hy0.le hc'0 hc'h hq'.1.le hqq hq.2.le hq'.2
    _ ≤ crossJ y (pairRatio s) (pairWeight s) :=
        crossJ_mono_contraction hy0.le hc'0 hcc hch hq.1.le hq.2.le hy1.le
    _ ≤ crossJ s (pairRatio s) (pairWeight s) :=
        crossJ_mono_exponent hy0.le (le_of_lt hys) hc0 hch hq.1.le hq.2.le

/-! ### Strict monotonicity -/

/-- The rate of the weight step at the natural parameters is the moment loss of
`eq:loss-rate-bound`: `q'(s) L̃(s) = 2s log 2 · c(1-c)/(1/2 - c)`. -/
theorem pairWeight_deriv_mul_lossRate {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.log 2 * (2:ℝ) ^ (-s) * lossRate s
      = 2 * s * Real.log 2 * pairRatio s * (1 - pairRatio s) / (1/2 - pairRatio s) := by
  have hch := pairRatio_lt_half hs0 hs1
  have hp0 := (two_rpow_neg_mem hs0).1
  have hd : (1/2 : ℝ) - pairRatio s ≠ 0 := by linarith
  unfold lossRate pairWeight
  rw [show 1 - (1 - (2:ℝ) ^ (-s)) = (2:ℝ) ^ (-s) by ring]
  field_simp

theorem differentiableAt_lossRate {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    DifferentiableAt ℝ lossRate s := by
  have hcd := differentiableAt_pairRatio hs0
  have hqd : DifferentiableAt ℝ pairWeight s := (hasDerivAt_pairWeight s).differentiableAt
  have hch := pairRatio_lt_half hs0 hs1
  have hq := pairWeight_mem hs0
  unfold lossRate
  refine DifferentiableAt.div ?_ ?_ ?_
  · exact ((differentiableAt_const _).mul differentiableAt_id |>.mul hcd).mul
      ((differentiableAt_const _).sub hcd)
  · exact ((differentiableAt_const _).sub hcd).mul ((differentiableAt_const _).sub hqd)
  · exact mul_ne_zero (by linarith) (by linarith [hq.2])

/-- **`log F + log M` is strictly increasing on `(0, 1)`.** -/
theorem strictMonoOn_logMean :
    StrictMonoOn (fun s => logPrefactor s + Real.log (momentM s)) (Ioo 0 1) := by
  refine strictMonoOn_of_local Set.ordConnected_Ioo fun s hs => ?_
  obtain ⟨hs0, hs1⟩ := hs
  set D := -2 * Real.log 2 + Real.log 2 * (2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s))
      - logGammaDeriv (1 - s) - (-(s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s))
        - Real.log 2 * (2:ℝ) ^ (-s) * Real.log (1 - (2:ℝ) ^ (-s))) / prefE s with hD
  have hF := hasDerivAt_logPrefactor hs0 hs1
  have hDpos : 0 < D - Real.log 2 * (2:ℝ) ^ (-s) * lossRate s := by
    rw [hD, logPrefactorDeriv_eq hs0, pairWeight_deriv_mul_lossRate hs0 hs1]
    linarith [logPrefactorDeriv_sub_momentLoss_pos hs0 hs1]
  have hM0 : ∀ y, 0 < y → y < 1 → 0 < momentM y := fun y h0 h1 =>
    zero_lt_one.trans_le (one_le_momentM h0 h1)
  constructor
  · -- to the right
    set K := lossRate s
    have hg : HasDerivAt (fun y => 1 - (pairWeight y - pairWeight s) * K)
        (-(Real.log 2 * (2:ℝ) ^ (-s) * K)) s := by
      have := (hasDerivAt_const s (1:ℝ)).sub
        (((hasDerivAt_pairWeight s).sub (hasDerivAt_const s (pairWeight s))).mul_const K)
      exact this.congr_deriv (by ring)
    have hg1 : (fun y => 1 - (pairWeight y - pairWeight s) * K) s = 1 := by simp
    have hφ := hF.add (hg.log (by simp))
    have hφ' : HasDerivAt (fun y => logPrefactor y +
        Real.log (1 - (pairWeight y - pairWeight s) * K))
        (D - Real.log 2 * (2:ℝ) ^ (-s) * K) s :=
      hφ.congr_deriv (by rw [hD]; simp only [sub_self, zero_mul, sub_zero, div_one]; ring)
    have hloc := (eventually_lt_of_hasDerivAt_pos hφ' hDpos).1
    have hgpos : ∀ᶠ y in 𝓝 s, 0 < 1 - (pairWeight y - pairWeight s) * K :=
      hg.continuousAt.eventually (lt_mem_nhds (by rw [hg1]; norm_num))
    have hlt1 : ∀ᶠ y in 𝓝 s, y < 1 := Iio_mem_nhds hs1
    filter_upwards [hloc, momentM_right hs0 hs1, nhdsWithin_le_nhds hgpos,
      nhdsWithin_le_nhds hlt1, self_mem_nhdsWithin] with y hy hyM hyg hy1 hsy
    have hy0 : 0 < y := hs0.trans hsy
    simp only [sub_self, zero_mul, sub_zero, Real.log_one, add_zero] at hy
    have hMs := hM0 s hs0 hs1
    have hlog : Real.log (momentM s) + Real.log (1 - (pairWeight y - pairWeight s) * K)
        ≤ Real.log (momentM y) := by
      rw [← Real.log_mul hMs.ne' hyg.ne']
      exact Real.log_le_log (mul_pos hMs hyg) hyM
    show logPrefactor s + Real.log (momentM s) < logPrefactor y + Real.log (momentM y)
    linarith
  · -- to the left
    have hKd := (differentiableAt_lossRate hs0 hs1).hasDerivAt
    have hg : HasDerivAt (fun y => 1 - (pairWeight s - pairWeight y) * lossRate y)
        (Real.log 2 * (2:ℝ) ^ (-s) * lossRate s) s := by
      have := (hasDerivAt_const s (1:ℝ)).sub
        (((hasDerivAt_const s (pairWeight s)).sub (hasDerivAt_pairWeight s)).mul hKd)
      exact this.congr_deriv (by simp only [Pi.sub_apply, sub_self, zero_mul]; ring)
    have hg1 : (fun y => 1 - (pairWeight s - pairWeight y) * lossRate y) s = 1 := by simp
    have hφ := hF.sub (hg.log (by simp))
    have hφ' : HasDerivAt (fun y => logPrefactor y -
        Real.log (1 - (pairWeight s - pairWeight y) * lossRate y))
        (D - Real.log 2 * (2:ℝ) ^ (-s) * lossRate s) s :=
      hφ.congr_deriv (by rw [hD]; simp only [sub_self, zero_mul, sub_zero, div_one])
    have hloc := (eventually_lt_of_hasDerivAt_pos hφ' hDpos).2
    have hgpos : ∀ᶠ y in 𝓝 s, 0 < 1 - (pairWeight s - pairWeight y) * lossRate y :=
      hg.continuousAt.eventually (lt_mem_nhds (by rw [hg1]; norm_num))
    have hpos0 : ∀ᶠ y in 𝓝 s, 0 < y := Ioi_mem_nhds hs0
    filter_upwards [hloc, momentM_left hs0 hs1, nhdsWithin_le_nhds hgpos,
      nhdsWithin_le_nhds hpos0, self_mem_nhdsWithin] with y hy hyM hyg hy0 hys
    simp only [sub_self, zero_mul, sub_zero, Real.log_one] at hy
    have hMy := hM0 y hy0 (hys.trans hs1)
    have hlog : Real.log (momentM y)
        + Real.log (1 - (pairWeight s - pairWeight y) * lossRate y) ≤ Real.log (momentM s) := by
      rw [← Real.log_mul hMy.ne' hyg.ne']
      exact Real.log_le_log (mul_pos hMy hyg) hyM
    show logPrefactor y + Real.log (momentM y) < logPrefactor s + Real.log (momentM s)
    linarith

/-- **`thm:two-contraction-distinction`, the monotonicity**: for dimensions
`0 < s₁ < s₂ < 1`, the means of the natural measures of the family are strictly ordered. -/
theorem twoContractionMean_lt {s₁ s₂ : ℝ} (h0 : 0 < s₁) (h12 : s₁ < s₂) (h1 : s₂ < 1)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (pairSystem (pairRatio s₁) (pairRatio_pos h0)
      (pairRatio_lt_half h0 (h12.trans h1))).IsNatural K₁ s₁ μ₁)
    (hμ₂ : (pairSystem (pairRatio s₂) (pairRatio_pos (h0.trans h12))
      (pairRatio_lt_half (h0.trans h12) h1)).IsNatural K₂ s₂ μ₂) :
    twoContractionMean (pairRatio s₁) s₁ μ₁ < twoContractionMean (pairRatio s₂) s₂ μ₂ := by
  rw [twoContractionMean_eq h0 (h12.trans h1) hμ₁, twoContractionMean_eq (h0.trans h12) h1 hμ₂]
  have hM₁ := zero_lt_one.trans_le (one_le_momentM h0 (h12.trans h1))
  have hM₂ := zero_lt_one.trans_le (one_le_momentM (h0.trans h12) h1)
  have h := strictMonoOn_logMean ⟨h0, h12.trans h1⟩ ⟨h0.trans h12, h1⟩ h12
  have := Real.exp_lt_exp.2 h
  simp only [Real.exp_add, Real.exp_log hM₁, Real.exp_log hM₂] at this
  exact this

/-! ### Separation -/

/-- **Distinct means force the profiles apart**: if the Cesàro means of two bounded
continuous functions converge to different limits, then
`limsup |f₁ - f₂| > 0`, in the written-out form of `eq:profile-separation`. -/
theorem exists_ge_abs_sub_of_tendsto_avg {f₁ f₂ : ℝ → ℝ} (hf₁ : Continuous f₁)
    (hf₂ : Continuous f₂) {L₁ L₂ : ℝ} (hne : L₁ ≠ L₂)
    (h₁ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, f₁ t) atTop (𝓝 L₁))
    (h₂ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, f₂ t) atTop (𝓝 L₂)) :
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |f₁ t - f₂ t| := by
  refine ⟨|L₁ - L₂| / 2, by have := abs_pos.2 (sub_ne_zero.2 hne); linarith, fun V => ?_⟩
  by_contra hcon
  push Not at hcon
  set V' := max V 0 with hV'
  set ε := |L₁ - L₂| / 2 with hε
  have hεpos : 0 < ε := by have := abs_pos.2 (sub_ne_zero.2 hne); rw [hε]; linarith
  have hdiff := h₁.sub h₂
  have hint : ∀ T, IntervalIntegrable (fun t => f₁ t - f₂ t) volume 0 T := fun T =>
    (hf₁.sub hf₂).intervalIntegrable 0 T
  have hsplit : ∀ T, (T⁻¹ * ∫ t in (0:ℝ)..T, f₁ t) - T⁻¹ * ∫ t in (0:ℝ)..T, f₂ t
      = T⁻¹ * ((∫ t in (0:ℝ)..V', (f₁ t - f₂ t)) + ∫ t in V'..T, (f₁ t - f₂ t)) := by
    intro T
    rw [← mul_sub, ← intervalIntegral.integral_sub (hf₁.intervalIntegrable 0 T)
      (hf₂.intervalIntegrable 0 T), intervalIntegral.integral_add_adjacent_intervals
        (hint V') ((hint V').symm.trans (hint T))]
  set C := |∫ t in (0:ℝ)..V', (f₁ t - f₂ t)| with hC
  -- the averages of the difference stay within `ε` of `0` in the limit
  have hbound : ∀ T, V' + 1 ≤ T → |(T⁻¹ * ∫ t in (0:ℝ)..T, f₁ t) - T⁻¹ * ∫ t in (0:ℝ)..T, f₂ t|
      ≤ C / T + ε := by
    intro T hT
    have hT0 : 0 < T := by linarith [le_max_right V 0]
    rw [hsplit, abs_mul, abs_of_pos (inv_pos.2 hT0)]
    have htail : |∫ t in V'..T, (f₁ t - f₂ t)| ≤ ε * |T - V'| := by
      rw [← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [Real.norm_eq_abs]
      exact (hcon t (le_trans (le_max_left _ _) ht.1.le)).le
    rw [abs_of_nonneg (show 0 ≤ T - V' by linarith)] at htail
    calc T⁻¹ * |(∫ t in (0:ℝ)..V', (f₁ t - f₂ t)) + ∫ t in V'..T, (f₁ t - f₂ t)|
        ≤ T⁻¹ * (C + ε * (T - V')) :=
          mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add le_rfl htail))
            (inv_pos.2 hT0).le
      _ ≤ C / T + ε := by
          rw [div_eq_inv_mul, mul_add]
          have : T⁻¹ * (ε * (T - V')) ≤ ε := by
            rw [show T⁻¹ * (ε * (T - V')) = ε * ((T - V') / T) by field_simp]
            have : (T - V') / T ≤ 1 := by
              rw [div_le_one hT0]; linarith [le_max_right V 0]
            nlinarith
          linarith
  have hlim : Tendsto (fun T : ℝ => C / T + ε) atTop (𝓝 (0 + ε)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  have hle := le_of_tendsto_of_tendsto (hdiff.abs) hlim
    (eventually_atTop.2 ⟨V' + 1, hbound⟩)
  rw [zero_add, hε] at hle
  have := abs_pos.2 (sub_ne_zero.2 hne)
  linarith

end

end BrownianImages
