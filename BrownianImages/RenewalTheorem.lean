module

/-
The key renewal theorem of `sec:renewal-equation`, for the laws `ϑ = ∑ p_i δ_{α_i}` of
self-similar systems at their similarity dimension, and its half-line consequence
`eq:renewal-shift`.

The paper quotes the theorem for a bounded continuous solution `f = z + ϑ * f` tending to
zero at `-∞`, with a continuous, possibly signed defect `|z(t)| ≤ C e^{-c|t|}`: `f` is the
renewal series `∑ ϑ^{*n} * z`; in the non-lattice case `f(t) → m⁻¹ ∫ z`; in the lattice
case with span `ℓ`, `sup_{t∈[0,ℓ]} |f(t + nℓ) - f̃(t)| → 0` for the periodisation
`f̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t + kℓ)`.  The non-lattice conclusion and the series are the
vendored Fourier-analytic theorem; the lattice conclusion is the discrete renewal theorem
with Tannery's theorem on one period, applied to the cut-off `min{t,1} f(t)`, and the
limit is identified with `f̃` by telescoping the renewal equation along the lattice.
The half-line consequence applies the same cut-off to a function defined on `[0,∞)`.

* `System.continuous_defect`: the defect of a continuous solution is continuous.
* `System.nonlattice_renewal_series`: `f = ∑ ϑ^{*n} * z` in the non-lattice case.
* `System.nonlattice_renewal_limit`: the non-lattice conclusion.
* `System.lattice_renewal_limit`: the lattice conclusion, uniform on one period, with the
  limit `f̃` continuous and `ℓ`-periodic.
* `System.key_renewal_theorem`: both conclusions.
* `System.renewal_shift`: `eq:renewal-shift`.
-/
public import BrownianImages.LatticePeriodisation
public import BrownianImages.LatticeFourier

@[expose] public section

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The defect `z = f - ϑ * f` of a continuous solution is continuous. -/
theorem continuous_defect {s : ℝ} {f z : ℝ → ℝ} (hf : Continuous f)
    (hren : ∀ t, f t = S.renewalConv s f t + z t) : Continuous z := by
  have hz : z = fun t => f t - S.renewalConv s f t := funext fun t => by rw [hren t]; ring
  rw [hz]
  refine hf.sub (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_const.mul (hf.comp (continuous_id.sub continuous_const))

/-- The renewal mean of `ϑ` bounds the convolution of a bounded function. -/
theorem abs_renewalConv_le {s : ℝ} (hdim : S.IsDimension s) {g : ℝ → ℝ} {A : ℝ}
    (hA : ∀ t, |g t| ≤ A) (t : ℝ) : |S.renewalConv s g t| ≤ A := by
  unfold renewalConv
  calc |∑ j, S.ratio j ^ s * g (t - S.logRatio j)|
      ≤ ∑ j, |S.ratio j ^ s * g (t - S.logRatio j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, S.ratio j ^ s * A := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (S.ratio_pos j).le s)]
        exact mul_le_mul_of_nonneg_left (hA _) (Real.rpow_nonneg (S.ratio_pos j).le s)
    _ = A := by rw [← Finset.sum_mul, hdim, one_mul]

variable [Nonempty ι]

open _root_.AbsorptionCutoff.Renewal in
/-- **The renewal series**, `f = ∑_{n≥0} ϑ^{*n} * z`, in the non-lattice case of the key
renewal theorem of `sec:renewal-equation`: a bounded continuous solution of
`f = ϑ * f + z` vanishing at `-∞`, with a continuous defect of two-sided exponential
decay, is the sum of the convolutions of its defect with the convolution powers of `ϑ`. -/
theorem nonlattice_renewal_series {s : ℝ} (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {f z : ℝ → ℝ} {A C c : ℝ} (hf : Continuous f) (hA : ∀ t, |f t| ≤ A)
    (hbot : Tendsto f atBot (𝓝 0)) (hc : 0 < c)
    (hzb : ∀ t, |z t| ≤ C * Real.exp (-c * |t|))
    (hren : ∀ t, f t = S.renewalConv s f t + z t) (y : ℝ) :
    f y = ∑' n, ∫ x, z (y - x) ∂(convPow (S.renewalLaw s) n) := by
  have := S.isProbabilityMeasure_renewalLaw hdim
  obtain ⟨θ, hθ, hlt⟩ := S.exists_expTransform_lt_one hdim
  have hm : 0 < ∫ x, x ∂(S.renewalLaw s) := by
    rw [S.integral_id_renewalLaw]
    exact S.renewalMean_pos s
  have hzc : Continuous z := S.continuous_defect hf hren
  have hzd : driNorm (fun x => ‖z x‖ₑ) ≠ ∞ := driNorm_ne_top_of_exp_decay hc hzb
  obtain ⟨C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_of_expTransform
    (S.fellerNonlattice_renewalLaw hdim hna) (S.memLp_id_renewalLaw hdim) hm hθ hlt 1
  have hzd' : driNorm (fun x => ‖((z x : ℝ) : ℂ)‖ₑ) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hzd
  have hzi : ∀ (n : ℕ) (w : ℝ), Integrable (fun x => z (w - x)) (convPow (S.renewalLaw s) n) := by
    intro n w
    have := integrable_comp_sub_of_driNorm hC₀ ENNReal.ofReal_ne_top
      (Complex.continuous_ofReal.comp hzc) hzd' w n
    simpa using this.re
  have hsum : Summable fun n => ∫ x, z (y - x) ∂(convPow (S.renewalLaw s) n) := by
    rw [← Complex.summable_ofReal]
    refine (summable_integral_comp_sub_of_driNorm hC₀ ENNReal.ofReal_ne_top hzd' y).congr
      fun n => ?_
    rw [integral_complex_ofReal]
  exact KeyRenewalFourier.eq_tsum_integral_comp_sub_of_bounded hθ hlt hf hA hbot hzi
    (fun w => by rw [S.integral_comp_sub_renewalLaw]; exact hren w) hsum

open _root_.AbsorptionCutoff.Renewal in
/-- **The key renewal theorem of `sec:renewal-equation`, non-lattice case.**  A bounded
continuous solution of `f = ϑ * f + z` vanishing at `-∞`, with a defect of two-sided
exponential decay, converges to `m⁻¹ ∫ z` when the log-ratios generate a dense subgroup. -/
theorem nonlattice_renewal_limit {s : ℝ} (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {f z : ℝ → ℝ} {A C c : ℝ} (hf : Continuous f) (hA : ∀ t, |f t| ≤ A)
    (hbot : Tendsto f atBot (𝓝 0)) (hc : 0 < c)
    (hzb : ∀ t, |z t| ≤ C * Real.exp (-c * |t|))
    (hren : ∀ t, f t = S.renewalConv s f t + z t) :
    Tendsto f atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x, z x)) :=
  S.tendsto_of_renewalEquation hdim hna (S.continuous_defect hf hren)
    (driNorm_ne_top_of_exp_decay hc hzb) hf hA hbot hren

/-- **The key renewal theorem of `sec:renewal-equation`, lattice case.**  If the
log-ratios generate `ℓℤ`, a bounded continuous solution of `f = ϑ * f + z` vanishing at
`-∞`, with a defect of two-sided exponential decay, converges uniformly on `[0, ℓ]` along
the lattice to the periodisation `f̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t + kℓ)`, which is continuous
and `ℓ`-periodic; in particular `f(t) - f̃(t) → 0`.  The uniform convergence comes from
the signed arithmetic renewal theorem applied to `f(2v)`, and the limit is identified
with `f̃` by `eq_periodisation_of_periodic_limit`. -/
theorem lattice_renewal_limit {s h : ℝ} (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {f z : ℝ → ℝ} {A C c : ℝ} (hf : Continuous f) (hA : ∀ t, |f t| ≤ A)
    (hbot : Tendsto f atBot (𝓝 0)) (hc : 0 < c)
    (hzb : ∀ t, |z t| ≤ C * Real.exp (-c * |t|))
    (hren : ∀ t, f t = S.renewalConv s f t + z t) :
    Continuous (S.periodisation s h z) ∧ Function.Periodic (S.periodisation s h z) h ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
        |f (t + (n : ℝ) * h) - S.periodisation s h z t| ≤ ε) ∧
      Tendsto (fun t => f t - S.periodisation s h z t) atTop (𝓝 0) := by
  have hC : 0 ≤ C := by
    have h0 := hzb 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h0
    exact (abs_nonneg _).trans h0
  -- the half-scale profile and its signed defect
  let m : ℝ → ℝ := fun v => f (2 * v)
  let d : ℝ → ℝ := fun v => -z (2 * v)
  have hm : Continuous m := hf.comp (continuous_const.mul continuous_id)
  have hmA : ∀ v : ℝ, 0 ≤ v → |m v| ≤ A := fun v _ => hA _
  have hren' : ∀ v : ℝ, (∀ i, S.halfLogRatio i ≤ v) →
      m v = S.tubeRenewalConv s m v - d v := by
    intro v _
    have h2 : ∀ i, 2 * (v - S.halfLogRatio i) = 2 * v - S.logRatio i := by
      intro i
      simp only [halfLogRatio]
      ring
    dsimp only [m, d, tubeRenewalConv, tubeWeight]
    simp_rw [h2]
    rw [hren (2 * v), renewalConv]
    ring
  have hdefect : ∀ v : ℝ, (∀ i, S.halfLogRatio i ≤ v) →
      |d v| ≤ C * Real.exp (-(2 * c) * v) := by
    intro v hv
    have hv0 : 0 ≤ v := (S.halfLogRatio_pos (Classical.arbitrary ι)).le.trans (hv _)
    dsimp only [d]
    rw [abs_neg]
    refine (hzb (2 * v)).trans (le_of_eq ?_)
    rw [abs_of_nonneg (by positivity)]
    ring_nf
  obtain ⟨P, hPc, hPp, hPconv⟩ := S.exists_uniform_periodic_limit_of_tubeArithmetic
    (half_pos hh) (S.tubeArithmetic_of_log_lattice hlat) hdim hm hmA hC
    (by positivity : 0 < 2 * c) hren' hdefect
  -- back to the original scale
  let Q : ℝ → ℝ := fun w => P (w / 2)
  have hQc : Continuous Q := hPc.comp (continuous_id.div_const 2)
  have hQp : Function.Periodic Q h := by
    intro w
    dsimp only [Q]
    rw [add_div, hPp]
  have hQconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
      |f (t + (n : ℝ) * h) - Q t| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hPconv ε hε
    refine ⟨N, fun n hn t ht => ?_⟩
    have ht' : t / 2 ∈ Set.Icc (0 : ℝ) (h / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmt := hN n hn (t / 2) ht'
    have e : t + (n : ℝ) * h = 2 * (t / 2 + (n : ℝ) * (h / 2)) := by ring
    dsimp only [m] at hmt
    dsimp only [Q]
    rw [e]
    exact hmt
  have hQlim : Tendsto (fun w => f w - Q w) atTop (𝓝 0) :=
    tendsto_sub_periodic_of_uniform_lattice hh hQp hQconv
  have hQeq : Q = S.periodisation s h z :=
    funext (S.eq_periodisation_of_periodic_limit hdim hh hlat hbot hc hzb hren hQp hQlim)
  rw [← hQeq]
  exact ⟨hQc, hQp, hQconv, hQlim⟩

/-- **The key renewal theorem of `sec:renewal-equation`**, both cases: for a bounded
continuous solution of `f = ϑ * f + z` vanishing at `-∞` with a defect of two-sided
exponential decay, `f(t) → m⁻¹ ∫ z` if the log-ratios generate a dense subgroup, and if
they generate `ℓℤ` then `f(t + nℓ) → f̃(t)` uniformly on `[0, ℓ]`, for the continuous
`ℓ`-periodic periodisation `f̃`, so that `f - f̃ → 0`. -/
theorem key_renewal_theorem {s : ℝ} (hdim : S.IsDimension s)
    {f z : ℝ → ℝ} {A C c : ℝ} (hf : Continuous f) (hA : ∀ t, |f t| ≤ A)
    (hbot : Tendsto f atBot (𝓝 0)) (hc : 0 < c)
    (hzb : ∀ t, |z t| ≤ C * Real.exp (-c * |t|))
    (hren : ∀ t, f t = S.renewalConv s f t + z t) :
    (S.NonArithmetic → Tendsto f atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x, z x))) ∧
    (∀ h : ℝ, 0 < h →
      AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h →
      Continuous (S.periodisation s h z) ∧ Function.Periodic (S.periodisation s h z) h ∧
        (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
          |f (t + (n : ℝ) * h) - S.periodisation s h z t| ≤ ε) ∧
        Tendsto (fun t => f t - S.periodisation s h z t) atTop (𝓝 0)) :=
  ⟨fun hna => S.nonlattice_renewal_limit hdim hna hf hA hbot hc hzb hren,
    fun _ hh hlat => S.lattice_renewal_limit hdim hh hlat hf hA hbot hc hzb hren⟩

/-- **`eq:renewal-shift`.**  For a bounded continuous `f : [0, ∞) → ℝ` whose defect
`f - ϑ * f` is exponentially small for large `t`, `f(t - α_i) - f(t) → 0` as `t → ∞` for
every atom `α_i` of `ϑ`.  The cut-off `min{t, 1} f(t)`, extended by zero to `t ≤ 0`, is a
bounded continuous solution on `ℝ` vanishing at `-∞` whose defect vanishes on `(-∞, 0]`,
is bounded on a compact interval and agrees with the defect of `f` beyond it, so the key
renewal theorem applies: the constant limit gives the claim in the non-lattice case, and
the uniform periodic approximation gives it in the lattice case since `α_i ∈ ℓℤ`. -/
theorem renewal_shift {s : ℝ} (hdim : S.IsDimension s)
    {f : ℝ → ℝ} {A C c T : ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hA : ∀ t, 0 ≤ t → |f t| ≤ A) (hc : 0 < c)
    (hdef : ∀ t, T ≤ t → |f t - S.renewalConv s f t| ≤ C * Real.exp (-c * t)) (i : ι) :
    Tendsto (fun t => f (t - S.logRatio i) - f t) atTop (𝓝 0) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 le_rfl)
  -- the cut-off function
  let g : ℝ → ℝ := fun t => tubeRenewalCutoff t * f (max t 0)
  have hg : Continuous g := continuous_tubeRenewalCutoff.mul
    (hf.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right _ _)
  have hgA : ∀ t, |g t| ≤ A := by
    intro t
    dsimp only [g]
    rw [abs_mul, abs_of_nonneg (tubeRenewalCutoff_nonneg t)]
    calc tubeRenewalCutoff t * |f (max t 0)| ≤ 1 * A :=
          mul_le_mul (tubeRenewalCutoff_le_one t) (hA _ (le_max_right _ _)) (abs_nonneg _)
            zero_le_one
      _ = A := one_mul A
  have hg0 : ∀ t, t ≤ 0 → g t = 0 := fun t ht => by
    dsimp only [g]
    rw [tubeRenewalCutoff_eq_zero_of_nonpos ht, zero_mul]
  have hg1 : ∀ t, 1 ≤ t → g t = f t := fun t ht => by
    dsimp only [g]
    rw [tubeRenewalCutoff_eq_one_of_one_le ht, one_mul, max_eq_left (by linarith)]
  have hgbot : Tendsto g atBot (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot 0] with t ht
    exact (hg0 t ht).symm
  -- its defect
  let zg : ℝ → ℝ := fun t => g t - S.renewalConv s g t
  have hreng : ∀ t, g t = S.renewalConv s g t + zg t := fun t => by
    dsimp only [zg]
    ring
  set T' : ℝ := max T S.tubeRenewalTailThreshold with hT'
  have hT'1 : 1 ≤ T' := by
    have := S.tubeRenewalTailThreshold_nonneg
    have h1 : 1 ≤ S.tubeRenewalTailThreshold := by
      obtain ⟨j⟩ := ‹Nonempty ι›
      linarith [S.one_add_logRatio_le_tubeRenewalTailThreshold j, S.logRatio_pos j]
    exact h1.trans (le_max_right _ _)
  have hzg_tail : ∀ t, T' ≤ t → zg t = f t - S.renewalConv s f t := by
    intro t ht
    dsimp only [zg]
    rw [hg1 t (hT'1.trans ht)]
    congr 1
    unfold renewalConv
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg1 _ (by linarith [S.one_add_logRatio_le_tubeRenewalTailThreshold j,
      le_max_right T S.tubeRenewalTailThreshold])]
  have hzg_zero : ∀ t, t ≤ 0 → zg t = 0 := by
    intro t ht
    dsimp only [zg]
    rw [hg0 t ht]
    unfold renewalConv
    rw [Finset.sum_eq_zero fun j _ => ?_]
    · ring
    rw [hg0 _ (by linarith [S.logRatio_pos j]), mul_zero]
  have hzg_bdd : ∀ t, |zg t| ≤ 2 * A := by
    intro t
    dsimp only [zg]
    calc |g t - S.renewalConv s g t| ≤ |g t| + |S.renewalConv s g t| := abs_sub _ _
      _ ≤ A + A := add_le_add (hgA t) (S.abs_renewalConv_le hdim hgA t)
      _ = 2 * A := by ring
  -- the two-sided exponential bound on the defect
  set C' : ℝ := max C (2 * A * Real.exp (c * T')) with hC'
  have hzgb : ∀ t, |zg t| ≤ C' * Real.exp (-c * |t|) := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · rw [hzg_zero t ht, abs_zero]
      exact mul_nonneg (le_max_of_le_right (by positivity)) (Real.exp_pos _).le
    rw [abs_of_pos ht]
    rcases le_or_gt T' t with hTt | hTt
    · rw [hzg_tail t hTt]
      exact (hdef t ((le_max_left _ _).trans hTt)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · calc |zg t| ≤ 2 * A := hzg_bdd t
        _ = 2 * A * Real.exp (c * T') * Real.exp (-c * T') := by
            rw [mul_assoc, ← Real.exp_add]
            simp
        _ ≤ 2 * A * Real.exp (c * T') * Real.exp (-c * t) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            nlinarith
        _ ≤ C' * Real.exp (-c * t) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  -- the shift difference of the cut-off function
  have hshift : Tendsto (fun t => g (t - S.logRatio i) - g t) atTop (𝓝 0) := by
    rcases S.nonArithmetic_or_exists_lattice with hna | ⟨h, hh, hlat⟩
    · exact tendsto_sub_shift_sub_of_tendsto_atTop g
        (S.nonlattice_renewal_limit hdim hna hg hgA hgbot hc hzgb hreng)
    · obtain ⟨-, hper, hconv, -⟩ :=
        S.lattice_renewal_limit hdim hh hlat hg hgA hgbot hc hzgb hreng
      refine tendsto_sub_period_sub_of_uniform_lattice hh hper ?_ hconv
      rw [← hlat]
      exact AddSubgroup.subset_closure ⟨i, rfl⟩
  -- the cut-off function is `f` far out
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop (1 + S.logRatio i)] with t ht
  rw [hg1 t (by linarith [S.logRatio_pos i]), hg1 (t - S.logRatio i) (by linarith)]

end System

end

end BrownianImages
