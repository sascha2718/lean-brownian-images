/-
The smoothing kernel of `eq:h-definition`, `K(η) = ½ η^{s-2} exp(-1/(2η))`, and its
logarithmic form `k(x) = e^x K(e^x)`.  These are the estimates the proof of
`thm:profile-uniform-continuity` runs on, and the tail bound
`K(η) ≤ ½ η^{s-2}` is what the proof of `thm:profile-asymptotics` uses.

* `kern_pos`, `logKern_pos`: strict positivity, needed for the positivity of the
  periodic profile `H̃_A`.
* `logKern_eq`: the substitution `η = e^x` in the form `k(x) = e^x K(e^x)`.
* `kern_integrableOn`, `integral_kern_pos`: `sec:setup`'s claim that `K` is integrable,
  "since it decays exponentially at `0` and as `η^{s-2}` at infinity, where `s < 1`",
  and that `∫₀^∞ K > 0`, which is what makes the limit in `eq:hb-asymptotic` positive.
* `logKern_le_exp_neg_mul_abs`: the two-sided domination `k(x) ≤ e^{-c|x|}`,
  `c = min(s, 1-s)`, which is where `0 < s < 1` enters.  Its two halves,
  `logKern_le_of_nonneg` and `logKern_le_of_nonpos`, are the bounds `e^{-t} ≤ 1` and
  `e^{-t} ≤ 1/t`.
-/
import BrownianImages.Defs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace BrownianImages

open Real MeasureTheory

variable {s : ℝ}

/-! ### Positivity -/

/-- The kernel is strictly positive on `(0, ∞)`. -/
theorem kern_pos {η : ℝ} (hη : 0 < η) : 0 < kern s η := by
  have : (0:ℝ) < η ^ (s - 2) := Real.rpow_pos_of_pos hη _
  have := Real.exp_pos (-(2 * η)⁻¹)
  unfold kern; positivity

/-- The logarithmic kernel is strictly positive. -/
theorem logKern_pos (x : ℝ) : 0 < logKern s x := by
  unfold logKern; positivity

/-! ### The substitution `η = e^x` -/

/-- `k(x) = e^x K(e^x)`: the substitution `η = e^x` of the proof of
`thm:profile-uniform-continuity`. -/
theorem logKern_eq (x : ℝ) : logKern s x = Real.exp x * kern s (Real.exp x) := by
  have hrpow : (Real.exp x) ^ (s - 2) = Real.exp (x * (s - 2)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  rw [kern, hrpow, logKern]
  rw [show Real.exp x * (2⁻¹ * Real.exp (x * (s - 2)) * Real.exp (-(2 * Real.exp x)⁻¹))
      = 2⁻¹ * (Real.exp x * Real.exp (x * (s - 2))) * Real.exp (-(2 * Real.exp x)⁻¹) by ring,
    ← Real.exp_add]
  ring_nf

/-! ### The two-sided domination -/

/-- `e^{-t} ≤ 1/t` for `t > 0`. -/
theorem exp_neg_le_inv {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ t⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ ht (by linarith [Real.add_one_le_exp t])

/-- On `[0, ∞)` the kernel is dominated by `½ e^{(s-1)x}`, from `e^{-t} ≤ 1`. -/
theorem logKern_le_of_nonneg (x : ℝ) : logKern s x ≤ 2⁻¹ * Real.exp ((s - 1) * x) := by
  have h : Real.exp (-(2 * Real.exp x)⁻¹) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hpos : (0:ℝ) < 2⁻¹ * Real.exp ((s - 1) * x) := by positivity
  calc logKern s x = (2⁻¹ * Real.exp ((s - 1) * x)) * Real.exp (-(2 * Real.exp x)⁻¹) := by
        unfold logKern; ring
    _ ≤ (2⁻¹ * Real.exp ((s - 1) * x)) * 1 := by
        exact mul_le_mul_of_nonneg_left h hpos.le
    _ = 2⁻¹ * Real.exp ((s - 1) * x) := by ring

/-- On `(-∞, 0]` the kernel is dominated by `e^{sx}`, from `e^{-t} ≤ 1/t`. -/
theorem logKern_le_exp_mul (x : ℝ) : logKern s x ≤ Real.exp (s * x) := by
  have hx : (0:ℝ) < (2 * Real.exp x)⁻¹ := by positivity
  have h : Real.exp (-(2 * Real.exp x)⁻¹) ≤ 2 * Real.exp x := by
    have := exp_neg_le_inv hx
    rwa [inv_inv] at this
  have hpos : (0:ℝ) < 2⁻¹ * Real.exp ((s - 1) * x) := by positivity
  calc logKern s x = (2⁻¹ * Real.exp ((s - 1) * x)) * Real.exp (-(2 * Real.exp x)⁻¹) := by
        unfold logKern; ring
    _ ≤ (2⁻¹ * Real.exp ((s - 1) * x)) * (2 * Real.exp x) := mul_le_mul_of_nonneg_left h hpos.le
    _ = Real.exp ((s - 1) * x) * Real.exp x := by ring
    _ = Real.exp (s * x) := by rw [← Real.exp_add]; ring_nf

/-- The two-sided domination `k(x) ≤ e^{-c|x|}` with `c = min(s, 1-s) > 0`.  This is
where `0 < s < 1` enters: it is what makes `k` integrable on the whole line. -/
theorem logKern_le_exp_neg_mul_abs (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    logKern s x ≤ Real.exp (-min s (1 - s) * |x|) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    refine (logKern_le_of_nonneg x).trans ?_
    have hmin : min s (1 - s) ≤ 1 - s := min_le_right _ _
    have : (s - 1) * x ≤ -min s (1 - s) * x := by nlinarith
    calc 2⁻¹ * Real.exp ((s - 1) * x) ≤ 1 * Real.exp ((s - 1) * x) := by
          have := Real.exp_pos ((s - 1) * x); nlinarith
      _ = Real.exp ((s - 1) * x) := one_mul _
      _ ≤ Real.exp (-min s (1 - s) * x) := Real.exp_le_exp.mpr this
  · rw [abs_of_nonpos hx]
    refine (logKern_le_exp_mul x).trans (Real.exp_le_exp.mpr ?_)
    have hmin : min s (1 - s) ≤ s := min_le_left _ _
    nlinarith


/-! ### Integrability -/

/-- `x ↦ e^{-c|x|}` is integrable on the line for `c > 0`. -/
theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  have hIoi : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).congr_fun
      (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Set.Iio_union_Ici ℝ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hIoi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def, abs_neg] using hIoi

/-- The logarithmic kernel is continuous. -/
theorem continuous_logKern : Continuous (logKern s) := by
  have h : Continuous fun x : ℝ => (2 * Real.exp x)⁻¹ :=
    (continuous_const.mul Real.continuous_exp).inv₀
      (fun x => (by positivity : (0:ℝ) < 2 * Real.exp x).ne')
  unfold logKern
  exact (continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).mul (Real.continuous_exp.comp h.neg)

/-- `k ∈ L¹(ℝ)`, the integrability behind `thm:profile-uniform-continuity`. -/
theorem logKern_integrable (hs0 : 0 < s) (hs1 : s < 1) : Integrable (logKern s) := by
  refine Integrable.mono' (integrable_exp_neg_mul_abs (c := min s (1 - s)) (lt_min hs0 (by linarith)))
    continuous_logKern.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (logKern_pos x)]
  exact logKern_le_exp_neg_mul_abs hs0 hs1 x


/-! ### Integrability of `K` on `(0, ∞)` -/

/-- Near infinity: `e^{-t} ≤ 1` gives `K(η) ≤ ½ η^{s-2}`, and `s - 2 < -1`. -/
theorem kern_le_rpow {η : ℝ} (hη : 0 < η) : kern s η ≤ 2⁻¹ * η ^ (s - 2) := by
  have hexp : Real.exp (-(2 * η)⁻¹) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hpos : (0:ℝ) < 2⁻¹ * η ^ (s - 2) := by
    have := Real.rpow_pos_of_pos hη (s - 2); positivity
  calc kern s η = (2⁻¹ * η ^ (s - 2)) * Real.exp (-(2 * η)⁻¹) := by unfold kern; ring
    _ ≤ (2⁻¹ * η ^ (s - 2)) * 1 := mul_le_mul_of_nonneg_left hexp hpos.le
    _ = 2⁻¹ * η ^ (s - 2) := by ring

/-- Near zero: `e^{-t} ≤ 1/t` gives `K(η) ≤ η^{s-1}`, and `s - 1 > -1`. -/
theorem kern_le_rpow_of_small {η : ℝ} (hη : 0 < η) : kern s η ≤ η ^ (s - 1) := by
  have hx : (0:ℝ) < (2 * η)⁻¹ := by positivity
  have hexp : Real.exp (-(2 * η)⁻¹) ≤ 2 * η := by
    have := exp_neg_le_inv hx; rwa [inv_inv] at this
  have hpos : (0:ℝ) < 2⁻¹ * η ^ (s - 2) := by
    have := Real.rpow_pos_of_pos hη (s - 2); positivity
  have hsplit : η ^ (s - 2) * η = η ^ (s - 1) := by
    nth_rewrite 2 [← Real.rpow_one η]
    rw [← Real.rpow_add hη]
    congr 1
    ring
  calc kern s η = (2⁻¹ * η ^ (s - 2)) * Real.exp (-(2 * η)⁻¹) := by unfold kern; ring
    _ ≤ (2⁻¹ * η ^ (s - 2)) * (2 * η) := mul_le_mul_of_nonneg_left hexp hpos.le
    _ = η ^ (s - 2) * η := by ring
    _ = η ^ (s - 1) := hsplit

theorem continuousOn_kern (s : ℝ) : ContinuousOn (kern s) (Set.Ioi 0) := by
  intro η hη
  have hη' : η ≠ 0 := ne_of_gt hη
  refine ContinuousAt.continuousWithinAt ?_
  have hinv : ContinuousAt (fun x : ℝ => (2 * x)⁻¹) η :=
    (continuousAt_const.mul continuousAt_id).inv₀ (mul_ne_zero two_ne_zero hη')
  have hexp : ContinuousAt (fun x : ℝ => Real.exp (-(2 * x)⁻¹)) η :=
    Real.continuous_exp.continuousAt.comp hinv.neg
  unfold kern
  exact (continuousAt_const.mul (Real.continuousAt_rpow_const η (s - 2) (Or.inl hη'))).mul hexp

/-- `sec:setup`: `K` is integrable on `(0, ∞)` for `0 < s < 1`. -/
theorem kern_integrableOn (hs0 : 0 < s) (hs1 : s < 1) :
    MeasureTheory.IntegrableOn (kern s) (Set.Ioi 0) := by
  have hmeas : ∀ t : Set ℝ, t ⊆ Set.Ioi 0 → MeasurableSet t →
      MeasureTheory.AEStronglyMeasurable (kern s) (MeasureTheory.volume.restrict t) :=
    fun t ht htm => ((continuousOn_kern s).mono ht).aestronglyMeasurable htm
  have hsmall : MeasureTheory.IntegrableOn (kern s) (Set.Ioc 0 1) := by
    have hbase : MeasureTheory.IntegrableOn (fun η : ℝ => η ^ (s - 1)) (Set.Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1)
        (r := s - 1) (by linarith)
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
    refine MeasureTheory.Integrable.mono' hbase
      (hmeas _ Set.Ioc_subset_Ioi_self measurableSet_Ioc) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with η hη
    rw [Real.norm_eq_abs, abs_of_pos (kern_pos hη.1)]
    exact kern_le_rpow_of_small hη.1
  have hlarge : MeasureTheory.IntegrableOn (kern s) (Set.Ioi 1) := by
    have hbase : MeasureTheory.IntegrableOn (fun η : ℝ => 2⁻¹ * η ^ (s - 2)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine MeasureTheory.Integrable.mono' hbase
      (hmeas _ (Set.Ioi_subset_Ioi (by norm_num)) measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with η hη
    have hη0 : (0:ℝ) < η := lt_trans one_pos hη
    rw [Real.norm_eq_abs, abs_of_pos (kern_pos hη0)]
    exact kern_le_rpow hη0
  have := hsmall.union hlarge
  rwa [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)] at this

/-- `∫₀^∞ K > 0`: this is what makes the limit of `eq:hb-asymptotic` strictly
positive. -/
theorem integral_kern_pos (hs0 : 0 < s) (hs1 : s < 1) :
    0 < ∫ η in Set.Ioi (0:ℝ), kern s η := by
  have hint := kern_integrableOn hs0 hs1
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))] kern s := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with η hη
    exact (kern_pos hη).le
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsupp : Function.support (kern s) ∩ Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
    refine Set.inter_eq_right.mpr fun η hη => ?_
    exact ne_of_gt (kern_pos hη)
  rw [hsupp]
  simp


/-! ### Positivity of the smoothing operator -/

/-- `sec:smoothing`: `Tg` is strictly positive when `g` is.  The integrand is positive
and integrable, dominated by `M·K`, and `K` is integrable with `(0,∞)` of positive
measure.  This is the positivity of `H̃_A` the paper records after
`thm:smoothing-injective`. -/
theorem smoothOp_pos (hs0 : 0 < s) (hs1 : s < 1) {g : ℝ → ℝ} (hg : Continuous g)
    (hgpos : ∀ x, 0 < g x) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (v : ℝ) :
    0 < smoothOp s g v := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hlog : ContinuousOn (fun η : ℝ => g (2 * v - Real.log η)) (Set.Ioi 0) :=
    hg.comp_continuousOn (continuousOn_const.sub
      (Real.continuousOn_log.mono (fun η hη => ne_of_gt hη)))
  have hcont : ContinuousOn (fun η : ℝ => kern s η * g (2 * v - Real.log η)) (Set.Ioi 0) :=
    (continuousOn_kern s).mul hlog
  have hint : MeasureTheory.IntegrableOn
      (fun η : ℝ => kern s η * g (2 * v - Real.log η)) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' ((kern_integrableOn hs0 hs1).mul_const M)
      (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with η hη
    have hk := kern_pos (s := s) hη
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hk (hgpos _))]
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hM _)) hk.le
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))]
      fun η : ℝ => kern s η * g (2 * v - Real.log η) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with η hη
    exact (mul_pos (kern_pos (s := s) hη) (hgpos _)).le
  rw [smoothOp, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsupp : Function.support (fun η : ℝ => kern s η * g (2 * v - Real.log η))
      ∩ Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) :=
    Set.inter_eq_right.mpr fun η hη => ne_of_gt (mul_pos (kern_pos (s := s) hη) (hgpos _))
  rw [hsupp]
  simp

end BrownianImages
