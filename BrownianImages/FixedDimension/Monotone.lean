/-
`thm:small-dimension-monotone` and the monotone part of `thm:critical-set-finite`.

By `eq:log-derivative-mean`, the mean `H̄_s(p) = C_s pq M_p / E(p)` has derivative
`C_s (pq/E) (κ M_p + M_p')`, and since `M_p ≥ 1` and `κ > 0` it is positive wherever
`|M_p'| < κ(p)`. For `p ≤ 10⁻⁴` this follows from `thm:entropy-factor`,
`thm:main-term-derivative` and `thm:remainder-derivative`; for `10⁻⁴ ≤ p < 1/2` from
`thm:second-derivative-small-s`, the symmetry `M_{1/2}' = 0` and the mean value theorem, once
`10¹¹ s γ` is below the constant `c` of `thm:entropy-factor`.

* `hasDerivAt_fixedMean`: `eq:log-derivative-mean` in product form.
* `abs_deriv_fixedMoment_lt_kappa_small`, `abs_deriv_fixedMoment_lt_kappa_large`: the two
  regimes.
* `exists_strictMonoOn_fixedMean`: `thm:small-dimension-monotone`.
* `exists_strictMonoOn_fixedMean_small`: `thm:critical-set-finite`, the strict increase on
  `(0, p₀]` for `s ≤ 1/2`.
-/
import BrownianImages.FixedDimension.Symmetry

namespace BrownianImages

open MeasureTheory Filter Set Metric
open scoped Topology

noncomputable section

/-! ### The derivative of the moment on `(0, 1/2]` -/

/-- For `p ≤ 1/50` the moment is differentiable, with
`|M_p'| ≤ 6 p^{-s} + 3000 s (3p/2)^{1/s} p^{-2-s}` by `thm:main-term-derivative` and
`thm:remainder-derivative`. -/
theorem hasDerivAt_fixedMoment_small {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) :
    HasDerivAt (fixedMoment s) (deriv (fixedMoment s) p) p ∧
    |deriv (fixedMoment s) p| ≤
      6 * p ^ (-s) + 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) := by
  obtain ⟨D, D', hD, hD', hb⟩ := exists_hasDerivAt_fixedMoment hs hs1 hp0 hp
  obtain ⟨D'', hD'', hb'⟩ := exists_hasDerivAt_mainTerm hs hs1 hp0 hp
  have e : D' = D'' := hD'.unique hD''
  subst e
  refine ⟨hD.differentiableAt.hasDerivAt, ?_⟩
  rw [hD.deriv]
  have h1 := abs_le.1 hb
  have h2 := abs_le.1 hb'
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The moment is differentiable at every `p ∈ (0, 1/2]` for `s ≤ 2·10⁻⁵`. -/
theorem hasDerivAt_fixedMoment_of_le_half {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 0 < p) (hp1 : p ≤ 1/2) :
    HasDerivAt (fixedMoment s) (deriv (fixedMoment s) p) p := by
  have hR : 0 < radQ := by rw [radQ_eq]; norm_num
  rcases le_or_gt p (1/50) with hp | hp
  · exact (hasDerivAt_fixedMoment_small hs (by linarith) hp0 hp).1
  · exact (fixedMoment_second_derivative hs hsQ (by linarith) hp1).1 p
      ⟨by linarith, by linarith⟩

/-- `|M_p'| ≤ 10¹¹ s γ (1/2 - p)` on `[10⁻⁴, 1/2]`, by `thm:second-derivative-small-s`, the
symmetry `M_{1/2}' = 0` and the mean value theorem. -/
theorem abs_deriv_fixedMoment_le_of_ge {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) :
    |deriv (fixedMoment s) p| ≤ 10 ^ 11 * s * gammaQ s * (1/2 - p) := by
  have hconv : Convex ℝ (Icc (1/10000 : ℝ) (1/2)) := convex_Icc _ _
  have hd : ∀ x ∈ Icc (1/10000 : ℝ) (1/2),
      HasDerivWithinAt (deriv (fixedMoment s)) (deriv (deriv (fixedMoment s)) x)
        (Icc (1/10000 : ℝ) (1/2)) x := by
    intro x hx
    obtain ⟨D, hD, -⟩ := (fixedMoment_second_derivative hs hsQ hx.1 hx.2).2
    exact hD.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hb : ∀ x ∈ Icc (1/10000 : ℝ) (1/2),
      ‖deriv (deriv (fixedMoment s)) x‖ ≤ 10 ^ 11 * s * gammaQ s := by
    intro x hx
    obtain ⟨D, hD, hDb⟩ := (fixedMoment_second_derivative hs hsQ hx.1 hx.2).2
    rw [Real.norm_eq_abs, hD.deriv]; exact hDb
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (mem_Icc.2 ⟨hp0, hp1⟩)
    (mem_Icc.2 ⟨by norm_num, le_rfl⟩)
  rw [deriv_fixedMoment_half hs hsQ, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ 1/2 - p by linarith)] at h
  exact h

/-! ### The derivative of the mean -/

theorem fixedMean_const_pos {s : ℝ} (hs1 : s < 1) :
    0 < (2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.Gamma_pos_of_pos (by linarith))

/-- `eq:log-derivative-mean` in product form: `H̄_s' = C_s (pq/E) (κ M_p + M_p')`. -/
theorem hasDerivAt_fixedMean {s p D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hM : HasDerivAt (fixedMoment s) D p) :
    HasDerivAt (fixedMean s)
      ((2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) * (p * (1 - p) / entropy p) *
        (kappa p * fixedMoment s p + D)) p := by
  have hF := hasDerivAt_entropyFactor hp0 hp1
  have h := (hF.mul hM).const_mul ((2:ℝ) ^ (1 - s) * Real.Gamma (1 - s))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [fixedMean, Pi.mul_apply]; ring
  · ring

/-- The derivative of the mean is positive wherever `|M_p'| < κ(p)`, since `M_p ≥ 1`. -/
theorem deriv_fixedMean_pos {s p D : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp : p < 1/2) (hM : HasDerivAt (fixedMoment s) D p) (hD : |D| < kappa p) :
    0 < deriv (fixedMean s) p := by
  rw [(hasDerivAt_fixedMean hp0 (by linarith) hM).deriv]
  have hC := fixedMean_const_pos hs1
  have hF : 0 < p * (1 - p) / entropy p :=
    div_pos (mul_pos hp0 (by linarith)) (entropy_pos hp0 (by linarith))
  have hκ := kappa_pos hp0 hp
  have hM1 := one_le_fixedMoment hs hs1 hp0 (by linarith)
  have h1 : kappa p ≤ kappa p * fixedMoment s p := le_mul_of_one_le_right hκ.le hM1
  have h2 := (abs_lt.1 hD).1
  exact mul_pos (mul_pos hC hF) (by linarith)

/-! ### The regime `p ≤ 10⁻⁴` -/

/-- `log 100 ≤ 4.66`. -/
theorem log_hundred_le : Real.log 100 ≤ 4.66 := by
  have h2 := Real.log_two_lt_d9
  have h5 : Real.log (5/4 : ℝ) ≤ 1/4 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 5/4 by norm_num); linarith
  have e : Real.log (100 : ℝ) = 6 * Real.log 2 + 2 * Real.log (5/4) := by
    rw [show (100 : ℝ) = 2 ^ 6 * (5/4) ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e]; linarith

/-- `√p (1 - log p) ≤ 0.124` for `0 < p ≤ 10⁻⁴`. -/
theorem sqrt_mul_one_sub_log_le {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 10000) :
    Real.sqrt p * (1 - Real.log p) ≤ 0.124 := by
  set u := Real.sqrt p with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hp0
  have hu1 : u ≤ 1/100 := by
    rw [hu]
    calc Real.sqrt p ≤ Real.sqrt (1/10000) := Real.sqrt_le_sqrt hp
      _ = 1/100 := by
          rw [show (1/10000 : ℝ) = (1/100) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hp' : p = u ^ 2 := (Real.sq_sqrt hp0.le).symm
  have hlog : Real.log p = 2 * Real.log u := by rw [hp', Real.log_pow]; push_cast; ring
  have h1 : Real.log (1 / (100 * u)) ≤ 1 / (100 * u) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (1 / (100 * u)) = -Real.log u - Real.log 100 := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hu0.ne']; ring
  have h3 := log_hundred_le
  have h4 : -Real.log u ≤ 1 / (100 * u) - 1 + 4.66 := by linarith
  have h5 : u * (1 / (100 * u)) = 1 / 100 := by field_simp
  have h6 : u * (-Real.log u) ≤ 1 / 100 - u + 4.66 * u := by
    have := mul_le_mul_of_nonneg_left h4 hu0.le
    rw [mul_add, mul_sub, h5] at this
    linarith
  rw [hlog]
  nlinarith

/-- Regime B of `thm:small-dimension-monotone`: `|M_p'| < κ(p)` for `s ≤ 1/4` and
`p ≤ 10⁻⁴`. -/
theorem abs_deriv_fixedMoment_lt_kappa_small {s p : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hp0 : 0 < p) (hp : p ≤ 1 / 10000) : |deriv (fixedMoment s) p| < kappa p := by
  have hp1 : p < 1 := by linarith
  have hp50 : p ≤ 1/50 := by linarith
  have hL : 0 < 1 - Real.log p := by have := Real.log_neg hp0 hp1; linarith
  have hκ := kappa_ge_of_le hp0 hp50
  obtain ⟨-, hb⟩ := hasDerivAt_fixedMoment_small hs (by linarith) hp0 hp50
  have hps : p ^ (1 - s) ≤ Real.sqrt p := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le (by linarith)
  have hsq := sqrt_mul_one_sub_log_le hp0 hp
  have h4s : (4:ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]; linarith
  have h34 : (3 * p / 2) ^ s⁻¹ ≤ (3 * p / 2) ^ (4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) h4s
  have e1 : p ^ (-s) * p = p ^ (1 - s) := by
    rw [show (1 - s) = -s + 1 by ring, Real.rpow_add hp0, Real.rpow_one]
  have e2 : p ^ (4:ℕ) * p ^ (-2 - s) * p = p ^ (3 - s) := by
    calc p ^ (4:ℕ) * p ^ (-2 - s) * p = p ^ ((4:ℕ):ℝ) * p ^ (-2 - s) * p ^ (1:ℝ) := by
          rw [Real.rpow_natCast, Real.rpow_one]
      _ = p ^ (((4:ℕ):ℝ) + (-2 - s) + 1) := by rw [Real.rpow_add hp0, Real.rpow_add hp0]
      _ = p ^ (3 - s) := by congr 1; push_cast; ring
  have e3 : p ^ (5/2 : ℝ) = p ^ (2:ℕ) * Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hp0]
    congr 1; push_cast; norm_num
  have hpL : 0 < p * (1 - Real.log p) := mul_pos hp0 hL
  have t1 : 6 * p ^ (-s) * (p * (1 - Real.log p)) ≤ 6 * 0.124 := by
    calc 6 * p ^ (-s) * (p * (1 - Real.log p)) = 6 * ((p ^ (-s) * p) * (1 - Real.log p)) := by
          ring
      _ = 6 * (p ^ (1 - s) * (1 - Real.log p)) := by rw [e1]
      _ ≤ 6 * (Real.sqrt p * (1 - Real.log p)) := by
          gcongr
      _ ≤ 6 * 0.124 := by gcongr
  have t2 : 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) * (p * (1 - Real.log p)) ≤ 0.01 := by
    have hA : 0 ≤ p ^ (-2 - s) * (p * (1 - Real.log p)) := by positivity
    have hq : p ^ (3 - s) ≤ p ^ (5/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le (by linarith)
    have hp2 : p ^ (2:ℕ) ≤ (1/10000) ^ (2:ℕ) := pow_le_pow_left₀ hp0.le hp 2
    calc 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) * (p * (1 - Real.log p))
        = 3000 * s * (3 * p / 2) ^ s⁻¹ * (p ^ (-2 - s) * (p * (1 - Real.log p))) := by ring
      _ ≤ 3000 * s * (3 * p / 2) ^ (4:ℝ) * (p ^ (-2 - s) * (p * (1 - Real.log p))) := by
          gcongr
      _ = 3000 * s * (81/16) * (p ^ (4:ℕ) * p ^ (-2 - s) * p) * (1 - Real.log p) := by
          rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
      _ = 3000 * s * (81/16) * p ^ (3 - s) * (1 - Real.log p) := by rw [e2]
      _ ≤ 3000 * s * (81/16) * p ^ (5/2 : ℝ) * (1 - Real.log p) := by
          gcongr
      _ = 3000 * s * (81/16) * p ^ (2:ℕ) * (Real.sqrt p * (1 - Real.log p)) := by
          rw [e3]; ring
      _ ≤ 3000 * (1/4) * (81/16) * (1/10000) ^ (2:ℕ) * 0.124 := by
          gcongr
      _ ≤ 0.01 := by norm_num
  have key : (6 * p ^ (-s) + 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s)) *
      (p * (1 - Real.log p)) < 0.88 := by
    calc (6 * p ^ (-s) + 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s)) * (p * (1 - Real.log p))
        = 6 * p ^ (-s) * (p * (1 - Real.log p)) +
            3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) * (p * (1 - Real.log p)) := by ring
      _ ≤ 6 * 0.124 + 0.01 := add_le_add t1 t2
      _ < 0.88 := by norm_num
  calc |deriv (fixedMoment s) p| ≤ _ := hb
    _ < 0.88 / (p * (1 - Real.log p)) := by rw [lt_div_iff₀ hpL]; exact key
    _ ≤ kappa p := hκ

/-! ### The regime `10⁻⁴ ≤ p < 1/2` -/

/-- Regime A of `thm:small-dimension-monotone`: `|M_p'| < κ(p)` on `[10⁻⁴, 1/2)` once
`10¹¹ s γ < c`. -/
theorem abs_deriv_fixedMoment_lt_kappa_large {s p c : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hc : ∀ p ∈ Ico (1/10000 : ℝ) (1/2), c * (1/2 - p) ≤ kappa p)
    (hsc : 10 ^ 11 * s * gammaQ s < c) (hp0 : 1 / 10000 ≤ p) (hp : p < 1/2) :
    |deriv (fixedMoment s) p| < kappa p := by
  have h1 := abs_deriv_fixedMoment_le_of_ge hs hsQ hp0 hp.le
  have h2 := hc p ⟨hp0, hp⟩
  have hd : 0 < 1/2 - p := by linarith
  calc |deriv (fixedMoment s) p| ≤ 10 ^ 11 * s * gammaQ s * (1/2 - p) := h1
    _ < c * (1/2 - p) := mul_lt_mul_of_pos_right hsc hd
    _ ≤ kappa p := h2

/-- `γ ≤ 2 s² / r²`, so that `s γ → 0` as `s → 0`. -/
theorem gammaQ_le_sq {s : ℝ} (hs : 0 < s) : gammaQ s ≤ 2 * s ^ 2 / radQ ^ 2 := by
  unfold gammaQ
  have hr : 0 < radQ := by rw [radQ_eq]; norm_num
  have h1 : 1 - radQ ≤ Real.exp (-radQ) := by
    have := Real.add_one_le_exp (-radQ); linarith
  have h2 : (1 - radQ) ^ s⁻¹ ≤ Real.exp (-radQ) ^ s⁻¹ :=
    Real.rpow_le_rpow (by rw [radQ_eq]; norm_num) h1 (inv_nonneg.2 hs.le)
  have h3 : Real.exp (-radQ) ^ s⁻¹ = Real.exp (-(radQ / s)) := by
    rw [← Real.exp_mul]; congr 1; ring
  have h4 : (radQ / s) ^ 2 / 2 ≤ Real.exp (radQ / s) := by
    have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ radQ / s by positivity)
    linarith [show 0 ≤ radQ / s by positivity]
  have h5 : Real.exp (-(radQ / s)) ≤ 2 * s ^ 2 / radQ ^ 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    calc radQ ^ 2 / (2 * s ^ 2) = (radQ / s) ^ 2 / 2 := by field_simp
      _ ≤ _ := h4
  rw [h3] at h2
  exact h2.trans h5

/-- **`thm:small-dimension-monotone`.**  There is `s₀ ∈ (0, 1)` such that for every
`s ∈ (0, s₀]` the mean `p ↦ H̄_s(p)` is strictly increasing on `(0, 1/2]`. -/
theorem exists_strictMonoOn_fixedMean :
    ∃ s₀ ∈ Ioo (0:ℝ) 1, ∀ s ∈ Ioc (0:ℝ) s₀, StrictMonoOn (fixedMean s) (Ioc 0 (1/2)) := by
  obtain ⟨c, hc0, hc⟩ := kappa_ge_of_ge (p₁ := 1/10000) (by norm_num) (by norm_num)
  refine ⟨min (2/100000) (c / 10 ^ 11),
    ⟨lt_min (by norm_num) (by positivity), (min_le_left _ _).trans_lt (by norm_num)⟩, ?_⟩
  intro s hs
  have hs0 : 0 < s := hs.1
  have hsQ : s ≤ 2/100000 := hs.2.trans (min_le_left _ _)
  have hsc' : s ≤ c / 10 ^ 11 := hs.2.trans (min_le_right _ _)
  have hsc : 10 ^ 11 * s * gammaQ s < c := by
    have hγ := gammaQ_le_sq hs0
    have hγ0 := gammaQ_nonneg s
    have h1 : 10 ^ 11 * s * gammaQ s ≤ 10 ^ 11 * s * (2 * s ^ 2 / radQ ^ 2) := by
      gcongr
    have h2 : (10:ℝ) ^ 11 * s * (2 * s ^ 2 / radQ ^ 2) = 8 * 10 ^ 19 * s ^ 3 := by
      rw [radQ_eq]; ring
    have h3 : s ^ 3 ≤ (2/100000) ^ 2 * s := by
      have : s ^ 2 ≤ (2/100000) ^ 2 := pow_le_pow_left₀ hs0.le hsQ 2
      nlinarith
    have h4 : s * 10 ^ 11 ≤ c := by rwa [le_div_iff₀ (by norm_num)] at hsc'
    nlinarith
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
  · intro p hp
    exact (hasDerivAt_fixedMean hp.1 (by linarith [hp.2])
      (hasDerivAt_fixedMoment_of_le_half hs0 hsQ hp.1 hp.2)).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    have hM := hasDerivAt_fixedMoment_of_le_half hs0 hsQ hp.1 hp.2.le
    refine deriv_fixedMean_pos hs0 (by linarith) hp.1 hp.2 hM ?_
    rcases le_or_gt p (1/10000) with hp' | hp'
    · exact abs_deriv_fixedMoment_lt_kappa_small hs0 (by linarith) hp.1 hp'
    · exact abs_deriv_fixedMoment_lt_kappa_large hs0 hsQ hc hsc hp'.le hp.2

/-! ### `thm:critical-set-finite` -/

/-- `√p (1 - log p) ≤ 5 p^{1/4}` for `p > 0`. -/
theorem sqrt_mul_one_sub_log_le_rpow {p : ℝ} (hp0 : 0 < p) :
    Real.sqrt p * (1 - Real.log p) ≤ 5 * p ^ (1/4 : ℝ) := by
  set v := p ^ (1/4 : ℝ) with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos hp0 _
  have hpv : p = v ^ 4 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hsq : Real.sqrt p = v ^ 2 := by
    rw [hpv, show v ^ 4 = (v ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log p = 4 * Real.log v := by rw [hpv, Real.log_pow]; push_cast; ring
  have h1 : Real.log (1 / v) ≤ 1 / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [one_div, Real.log_inv] at h1
  have h2 : v ^ 2 * (-Real.log v) ≤ v ^ 2 * (v⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : v ^ 2 * v⁻¹ = v := by field_simp
  rw [hsq, hlog]
  nlinarith [h2, h3, hv0, sq_nonneg v]

/-- `|M_p'| (p log(e/p)) ≤ C √p log(e/p)` for `0 < p ≤ 1/50` and `s ≤ 1/2`, with
`C = 6 + 3000 s (3/2)^{1/s}`. -/
theorem abs_deriv_fixedMoment_mul_le {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) :
    |deriv (fixedMoment s) p| * (p * (1 - Real.log p)) ≤
      (6 + 3000 * s * (3/2 : ℝ) ^ s⁻¹) * (Real.sqrt p * (1 - Real.log p)) := by
  have hp1 : p < 1 := by linarith
  have hL : 0 < 1 - Real.log p := by have := Real.log_neg hp0 hp1; linarith
  obtain ⟨-, hb⟩ := hasDerivAt_fixedMoment_small hs hs1 hp0 hp
  have hpL : 0 ≤ p * (1 - Real.log p) := by positivity
  have hps : p ^ (1 - s) ≤ Real.sqrt p := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le (by linarith)
  have hs2 : (2:ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]; linarith
  have hpq : p ^ (s⁻¹ - 1 - s) ≤ Real.sqrt p := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le (by linarith)
  have e1 : p ^ (-s) * p = p ^ (1 - s) := by
    rw [show (1 - s) = -s + 1 by ring, Real.rpow_add hp0, Real.rpow_one]
  have e2 : (3 * p / 2) ^ s⁻¹ = (3/2 : ℝ) ^ s⁻¹ * p ^ s⁻¹ := by
    rw [show 3 * p / 2 = 3/2 * p by ring, Real.mul_rpow (by norm_num) hp0.le]
  have e3 : p ^ s⁻¹ * p ^ (-2 - s) * p = p ^ (s⁻¹ - 1 - s) := by
    calc p ^ s⁻¹ * p ^ (-2 - s) * p = p ^ s⁻¹ * p ^ (-2 - s) * p ^ (1:ℝ) := by rw [Real.rpow_one]
      _ = p ^ (s⁻¹ + (-2 - s) + 1) := by rw [Real.rpow_add hp0, Real.rpow_add hp0]
      _ = p ^ (s⁻¹ - 1 - s) := by congr 1; ring
  have h32 : 0 ≤ (3/2 : ℝ) ^ s⁻¹ := by positivity
  calc |deriv (fixedMoment s) p| * (p * (1 - Real.log p))
      ≤ (6 * p ^ (-s) + 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s)) * (p * (1 - Real.log p)) :=
        mul_le_mul_of_nonneg_right hb hpL
    _ = 6 * (p ^ (-s) * p) * (1 - Real.log p) +
        3000 * s * (3/2 : ℝ) ^ s⁻¹ * (p ^ s⁻¹ * p ^ (-2 - s) * p) * (1 - Real.log p) := by
        rw [e2]; ring
    _ = 6 * p ^ (1 - s) * (1 - Real.log p) +
        3000 * s * (3/2 : ℝ) ^ s⁻¹ * p ^ (s⁻¹ - 1 - s) * (1 - Real.log p) := by rw [e1, e3]
    _ ≤ 6 * Real.sqrt p * (1 - Real.log p) +
        3000 * s * (3/2 : ℝ) ^ s⁻¹ * Real.sqrt p * (1 - Real.log p) := by
        gcongr
    _ = (6 + 3000 * s * (3/2 : ℝ) ^ s⁻¹) * (Real.sqrt p * (1 - Real.log p)) := by ring

/-- The derivative bound `|M_p'| < κ(p)` on `(0, p₀)` for `s ≤ 1/2`, with
`p₀ = min(1/50, (0.17/C)⁴)`, `C = 6 + 3000 s (3/2)^{1/s}`. -/
theorem exists_abs_deriv_fixedMoment_lt_kappa_small {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) :
    ∃ p₀ ∈ Ioc (0:ℝ) (1/50), ∀ p ∈ Ioo (0:ℝ) p₀, |deriv (fixedMoment s) p| < kappa p := by
  set C := 6 + 3000 * s * (3/2 : ℝ) ^ s⁻¹ with hC
  have hC0 : 0 < C := by positivity
  set p₀ := min (1/50 : ℝ) ((0.17 / C) ^ (4:ℕ)) with hp₀
  have hp₀0 : 0 < p₀ := lt_min (by norm_num) (by positivity)
  have hp₀1 : p₀ ≤ 1/50 := min_le_left _ _
  refine ⟨p₀, ⟨hp₀0, hp₀1⟩, ?_⟩
  intro p hp
  have hp0 := hp.1
  have hpp : p ≤ 1/50 := by linarith [hp.2]
  have hp1 : p < 1 := by linarith
  have hL : 0 < 1 - Real.log p := by have := Real.log_neg hp0 hp1; linarith
  have hpL : 0 < p * (1 - Real.log p) := mul_pos hp0 hL
  have hκ := kappa_ge_of_le hp0 hpp
  have h1 := abs_deriv_fixedMoment_mul_le hs hs1 hp0 hpp
  have h2 := sqrt_mul_one_sub_log_le_rpow hp0
  have h3 : p ^ (1/4 : ℝ) ≤ 0.17 / C := by
    have hp₀2 : p ≤ (0.17 / C) ^ (4:ℕ) := hp.2.le.trans (min_le_right _ _)
    calc p ^ (1/4 : ℝ) ≤ ((0.17 / C) ^ (4:ℕ)) ^ (1/4 : ℝ) :=
          Real.rpow_le_rpow hp0.le hp₀2 (by norm_num)
      _ = 0.17 / C := by
          rw [show (1/4 : ℝ) = ((4:ℕ):ℝ)⁻¹ by norm_num,
            Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have h4 : C * (Real.sqrt p * (1 - Real.log p)) ≤ 0.85 := by
    calc C * (Real.sqrt p * (1 - Real.log p)) ≤ C * (5 * p ^ (1/4 : ℝ)) := by gcongr
      _ ≤ C * (5 * (0.17 / C)) := by gcongr
      _ = 0.85 := by field_simp; ring
  have key : |deriv (fixedMoment s) p| * (p * (1 - Real.log p)) < 0.88 := by linarith
  calc |deriv (fixedMoment s) p| < 0.88 / (p * (1 - Real.log p)) := by
        rw [lt_div_iff₀ hpL]; exact key
    _ ≤ kappa p := hκ

/-- The derivative of the mean is positive on `(0, p₀)` for `s ≤ 1/2`. -/
theorem exists_deriv_fixedMean_pos_small {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) :
    ∃ p₀ ∈ Ioc (0:ℝ) (1/50), ∀ p ∈ Ioo (0:ℝ) p₀, 0 < deriv (fixedMean s) p := by
  obtain ⟨p₀, hp₀, hkey⟩ := exists_abs_deriv_fixedMoment_lt_kappa_small hs hs1
  refine ⟨p₀, hp₀, fun p hp => ?_⟩
  have hpp : p ≤ 1/50 := hp.2.le.trans hp₀.2
  exact deriv_fixedMean_pos hs (by linarith) hp.1 (by linarith [hp.2])
    (hasDerivAt_fixedMoment_small hs hs1 hp.1 hpp).1 (hkey p hp)

/-- **`thm:critical-set-finite`**, the monotone part: for every `s ∈ (0, 1/2]` there is
`p₀ ∈ (0, 1/2)` such that the mean is strictly increasing on `(0, p₀]`. -/
theorem exists_strictMonoOn_fixedMean_small {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) :
    ∃ p₀ ∈ Ioo (0:ℝ) (1/2), StrictMonoOn (fixedMean s) (Ioc 0 p₀) := by
  obtain ⟨p₀, hp₀, hpos⟩ := exists_deriv_fixedMean_pos_small hs hs1
  refine ⟨p₀, ⟨hp₀.1, by linarith [hp₀.2]⟩, ?_⟩
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
  · intro p hp
    have hpp : p ≤ 1/50 := hp.2.trans hp₀.2
    exact (hasDerivAt_fixedMean hp.1 (by linarith)
      (hasDerivAt_fixedMoment_small hs hs1 hp.1 hpp).1).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    exact hpos p hp

end

end BrownianImages
