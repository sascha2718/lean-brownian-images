/-
`thm:entropy-factor` of `sec:small-dimension`: the logarithmic derivative `κ` of the
entropy factor `pq/E(p)`, its positivity on `(0, 1/2)`, the bound `κ ≥ 0.88/(p log(e/p))`
on `(0, 1/50]`, and the bound `κ ≥ c (1/2 - p)` near `1/2`, together with the derivative
identity `eq:log-derivative-mean` for the entropy factor.

* `entropy_pos`, `hasDerivAt_entropy`, `entropy_le_log_two`: `E > 0`, `E' = log(q/p)`,
  `E ≤ log 2`.
* `kappaNum`, `hasDerivAt_kappaNum`, `strictConcaveOn_kappaNum`: `Φ = q² log(1/q) - p² log(1/p)`, with
  `Φ' = 1 - 2E`, is strictly concave on `[0, 1/2]` and vanishes at both ends.
* `kappa_pos`, `kappa_ge_of_le`, `kappa_ge_of_ge`: the three claims of
  `thm:entropy-factor`.
* `hasDerivAt_entropyFactor`: `(pq/E)' = (pq/E) κ`, which is `eq:log-derivative-mean`.
-/
import BrownianImages.FixedDimension.System
import Mathlib.Analysis.Complex.ExponentialBounds

namespace BrownianImages

open Filter Set
open scoped Topology

noncomputable section

/-! ### The entropy -/

theorem entropy_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < entropy p := by
  have h1 : Real.log p < 0 := Real.log_neg hp0 hp1
  have h2 : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  unfold entropy
  nlinarith

/-- The derivative of `x ↦ (1 - x) log(1 - x)`. -/
theorem hasDerivAt_one_sub_mul_log {p : ℝ} (hp1 : p < 1) :
    HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      ((-1) * Real.log (1 - p) + (1 - p) * ((1 - p)⁻¹ * (-1))) p := by
  have hq : (0:ℝ) < 1 - p := by linarith
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((1 - p)⁻¹ * (-1)) p :=
    (Real.hasDerivAt_log hq.ne').comp p ((hasDerivAt_id p).const_sub 1)
  exact ((hasDerivAt_id p).const_sub 1).mul hlog

theorem hasDerivAt_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt entropy (Real.log (1 - p) - Real.log p) p := by
  have hq : (1:ℝ) - p ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log p + 1) p :=
    Real.hasDerivAt_mul_log hp0.ne'
  have h := h1.neg.sub (hasDerivAt_one_sub_mul_log hp1)
  exact h.congr_deriv (by field_simp; ring)

/-- `E ≤ log 2`, by `log x ≤ x - 1` at `x = 1/(2p)` and `x = 1/(2q)`. -/
theorem entropy_le_log_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : entropy p ≤ Real.log 2 := by
  have hq0 : 0 < 1 - p := by linarith
  have h1 : Real.log (2 * p)⁻¹ ≤ (2 * p)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (2 * (1 - p))⁻¹ ≤ (2 * (1 - p))⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv, Real.log_mul (by norm_num) hp0.ne'] at h1
  rw [Real.log_inv, Real.log_mul (by norm_num) hq0.ne'] at h2
  have h1' : p * (-(Real.log 2 + Real.log p)) ≤ p * ((2 * p)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left h1 hp0.le
  have h2' : (1 - p) * (-(Real.log 2 + Real.log (1 - p)))
      ≤ (1 - p) * ((2 * (1 - p))⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left h2 hq0.le
  have e1 : p * ((2 * p)⁻¹ - 1) = 1/2 - p := by field_simp
  have e2 : (1 - p) * ((2 * (1 - p))⁻¹ - 1) = 1/2 - (1 - p) := by field_simp
  rw [e1] at h1'
  rw [e2] at h2'
  unfold entropy
  nlinarith

/-! ### The numerator `Φ` -/

/-- `Φ(p) = q² log(1/q) - p² log(1/p)`, the numerator of `κ`. -/
def kappaNum (p : ℝ) : ℝ := (1 - p) ^ 2 * Real.log (1 - p)⁻¹ - p ^ 2 * Real.log p⁻¹

theorem kappaNum_eq (p : ℝ) :
    kappaNum p = -((1 - p) * ((1 - p) * Real.log (1 - p))) + p * (p * Real.log p) := by
  unfold kappaNum
  rw [Real.log_inv, Real.log_inv]
  ring

theorem kappaNum_zero : kappaNum 0 = 0 := by simp [kappaNum]

theorem kappaNum_half : kappaNum (1/2) = 0 := by
  unfold kappaNum
  norm_num

theorem continuous_kappaNum : Continuous kappaNum := by
  have h : kappaNum = fun p => -((1 - p) * ((1 - p) * Real.log (1 - p))) + p * (p * Real.log p) :=
    funext kappaNum_eq
  rw [h]
  exact (((continuous_const.sub continuous_id).mul
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).neg).add
    (continuous_id.mul Real.continuous_mul_log)

theorem hasDerivAt_kappaNum {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt kappaNum (1 - 2 * entropy p) p := by
  have hq : (1:ℝ) - p ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log p + 1) p :=
    Real.hasDerivAt_mul_log hp0.ne'
  have h2 := hasDerivAt_one_sub_mul_log hp1
  have h3 : HasDerivAt (fun x : ℝ => (1 - x) * ((1 - x) * Real.log (1 - x)))
      ((-1) * ((1 - p) * Real.log (1 - p)) +
        (1 - p) * ((-1) * Real.log (1 - p) + (1 - p) * ((1 - p)⁻¹ * (-1)))) p :=
    ((hasDerivAt_id p).const_sub 1).mul h2
  have h4 : HasDerivAt (fun x : ℝ => x * (x * Real.log x))
      (1 * (p * Real.log p) + p * (Real.log p + 1)) p :=
    (hasDerivAt_id p).mul h1
  have h := (h3.neg).add h4
  have hfun : kappaNum = fun x => -((1 - x) * ((1 - x) * Real.log (1 - x))) + x * (x * Real.log x) :=
    funext kappaNum_eq
  rw [hfun]
  refine h.congr_deriv ?_
  unfold entropy
  field_simp
  ring

theorem deriv_kappaNum {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : deriv kappaNum p = 1 - 2 * entropy p :=
  (hasDerivAt_kappaNum hp0 hp1).deriv

/-- `Φ` is strictly concave on `[0, 1/2]`, since `Φ'' = -2E' < 0` there. -/
theorem strictConcaveOn_kappaNum : StrictConcaveOn ℝ (Icc (0:ℝ) (1/2)) kappaNum := by
  refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuous_kappaNum.continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  obtain ⟨hx0, hx1⟩ := hx
  have hx1' : x < 1 := by linarith
  have hev : deriv kappaNum =ᶠ[𝓝 x] fun y => 1 - 2 * entropy y := by
    filter_upwards [Ioo_mem_nhds hx0 hx1'] with y hy
    exact deriv_kappaNum hy.1 hy.2
  have hd : HasDerivAt (fun y => 1 - 2 * entropy y)
      (-(2 * (Real.log (1 - x) - Real.log x))) x := by
    have := ((hasDerivAt_entropy hx0 hx1').const_mul 2).const_sub 1
    simpa using this
  show deriv (deriv kappaNum) x < 0
  rw [hev.deriv_eq, hd.deriv]
  have : Real.log x < Real.log (1 - x) := Real.log_lt_log hx0 (by linarith)
  linarith

/-- `Φ > 0` on `(0, 1/2)`: a strictly concave function vanishing at `0` and `1/2`. -/
theorem kappaNum_pos {p : ℝ} (hp0 : 0 < p) (hp : p < 1/2) : 0 < kappaNum p := by
  have h := strictConcaveOn_kappaNum.2 (show (0:ℝ) ∈ Icc (0:ℝ) (1/2) by simp)
    (show (1/2:ℝ) ∈ Icc (0:ℝ) (1/2) by simp) (by norm_num)
    (show (0:ℝ) < 1 - 2 * p by linarith) (show (0:ℝ) < 2 * p by linarith) (by ring)
  simp only [smul_eq_mul, kappaNum_zero, kappaNum_half, mul_zero, add_zero] at h
  convert h using 2
  ring

/-! ### The three claims of `thm:entropy-factor` -/

theorem kappa_eq (p : ℝ) : kappa p = kappaNum p / (p * (1 - p) * entropy p) := rfl

theorem kappa_pos {p : ℝ} (hp0 : 0 < p) (hp : p < 1/2) : 0 < kappa p := by
  rw [kappa_eq]
  exact div_pos (kappaNum_pos hp0 hp)
    (mul_pos (mul_pos hp0 (by linarith)) (entropy_pos hp0 (by linarith)))

/-- `log(1/(1-p)) ≥ p`. -/
theorem log_one_sub_inv_ge {p : ℝ} (hp1 : p < 1) : p ≤ Real.log (1 - p)⁻¹ := by
  rw [Real.log_inv]
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - p by linarith)
  linarith

/-- `(1-p) log(1/(1-p)) ≤ p`. -/
theorem one_sub_mul_log_le {p : ℝ} (hp1 : p < 1) :
    (1 - p) * Real.log (1 - p)⁻¹ ≤ p := by
  have hq : (0:ℝ) < 1 - p := by linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hq)
  have h2 : (1 - p) * Real.log (1 - p)⁻¹ ≤ (1 - p) * ((1 - p)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left this hq.le
  calc (1 - p) * Real.log (1 - p)⁻¹ ≤ (1 - p) * ((1 - p)⁻¹ - 1) := h2
    _ = p := by field_simp; ring

/-- `E(p) ≤ p log(e/p) = p (1 - log p)`. -/
theorem entropy_le {p : ℝ} (hp1 : p < 1) :
    entropy p ≤ p * (1 - Real.log p) := by
  have h := one_sub_mul_log_le hp1
  rw [Real.log_inv] at h
  unfold entropy
  linarith

/-- `p log(1/p) ≤ p (log 50 - 1) + 1/50 ≤ 0.08` for `0 < p ≤ 1/50`. -/
theorem mul_log_inv_le {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/50) : p * Real.log p⁻¹ ≤ 0.08 := by
  have h50 : Real.log 50 ≤ 3.94 := by
    have h2 := Real.log_two_lt_d9
    -- `log(5/4) ≤ 2 log(1.1181) ≤ 2 · 0.1181`, since `5/4 ≤ 1.1181²`
    have h54 : Real.log (5/4) ≤ 0.2362 := by
      have hle : Real.log (5/4) ≤ Real.log ((1.1181:ℝ) ^ 2) :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h1 : Real.log (1.1181:ℝ) ≤ 1.1181 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [Real.log_pow] at hle
      push_cast at hle
      linarith
    have e : Real.log 50 = 5 * Real.log 2 + 2 * Real.log (5/4) := by
      rw [show (50:ℝ) = 2 ^ 5 * (5/4) ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [e]
    linarith
  have hx : 0 < (50 * p)⁻¹ := by positivity
  have h1 : Real.log (50 * p)⁻¹ ≤ (50 * p)⁻¹ - 1 := Real.log_le_sub_one_of_pos hx
  have e1 : Real.log p⁻¹ = Real.log (50 * p)⁻¹ + Real.log 50 := by
    rw [Real.log_inv, Real.log_inv, Real.log_mul (by norm_num) hp0.ne']
    ring
  rw [e1]
  have h2 : p * Real.log (50 * p)⁻¹ ≤ p * ((50 * p)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left h1 hp0.le
  have e2 : p * ((50 * p)⁻¹ - 1) = 1/50 - p := by field_simp
  rw [e2] at h2
  have h3 : p * Real.log 50 ≤ p * 3.94 := mul_le_mul_of_nonneg_left h50 hp0.le
  nlinarith

/-- `thm:entropy-factor`, second claim: `κ(p) ≥ 0.88/(p log(e/p))` for `0 < p ≤ 1/50`. -/
theorem kappa_ge_of_le {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/50) :
    0.88 / (p * (1 - Real.log p)) ≤ kappa p := by
  have hp1 : p < 1 := by linarith
  have hq0 : (0:ℝ) < 1 - p := by linarith
  have hE := entropy_pos hp0 hp1
  have hlog : 0 < 1 - Real.log p := by
    have := Real.log_neg hp0 hp1; linarith
  -- `Φ ≥ p (q² - p log(1/p))`
  have hΦ : p * ((1 - p) ^ 2 - p * Real.log p⁻¹) ≤ kappaNum p := by
    unfold kappaNum
    have := log_one_sub_inv_ge hp1
    nlinarith [sq_nonneg (1 - p)]
  have hnum : 0.88 ≤ (1 - p) ^ 2 - p * Real.log p⁻¹ := by
    have := mul_log_inv_le hp0 hp
    nlinarith
  have hden : p * (1 - p) * entropy p ≤ p * (p * (1 - Real.log p)) := by
    have h1 := entropy_le hp1
    have h2 : p * (1 - p) * entropy p ≤ p * entropy p := by
      have : p * (1 - p) ≤ p := by nlinarith
      exact mul_le_mul_of_nonneg_right this hE.le
    have h3 : p * entropy p ≤ p * (p * (1 - Real.log p)) :=
      mul_le_mul_of_nonneg_left h1 hp0.le
    linarith
  rw [kappa_eq]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 0.88 * (p * (1 - p) * entropy p) ≤ 0.88 * (p * (p * (1 - Real.log p))) := by
        exact mul_le_mul_of_nonneg_left hden (by norm_num)
    _ ≤ ((1 - p) ^ 2 - p * Real.log p⁻¹) * (p * (p * (1 - Real.log p))) := by
        exact mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = p * ((1 - p) ^ 2 - p * Real.log p⁻¹) * (p * (1 - Real.log p)) := by ring
    _ ≤ kappaNum p * (p * (1 - Real.log p)) :=
        mul_le_mul_of_nonneg_right hΦ (by positivity)

/-- `thm:entropy-factor`, third claim: for every `0 < p₁ < 1/2` there is `c > 0` with
`κ(p) ≥ c (1/2 - p)` on `[p₁, 1/2)`, from the concavity of `Φ`. -/
theorem kappa_ge_of_ge {p₁ : ℝ} (hp₁0 : 0 < p₁) (hp₁ : p₁ < 1/2) :
    ∃ c > 0, ∀ p ∈ Ico p₁ (1/2), c * (1/2 - p) ≤ kappa p := by
  have hΦ₁ := kappaNum_pos hp₁0 hp₁
  have hl2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hd : 0 < 1/2 - p₁ := by linarith
  have hden0 : 0 < (1/2 - p₁) * (1/4 * Real.log 2) := mul_pos hd (by positivity)
  refine ⟨kappaNum p₁ / ((1/2 - p₁) * (1/4 * Real.log 2)), div_pos hΦ₁ hden0, fun p hp => ?_⟩
  obtain ⟨hp1, hp2⟩ := hp
  have hp0 : 0 < p := hp₁0.trans_le hp1
  have hE := entropy_pos hp0 (by linarith)
  -- the chord from `(p₁, Φ(p₁))` to `(1/2, 0)` lies below `Φ`
  have hchord : kappaNum p₁ * ((1/2 - p) / (1/2 - p₁)) ≤ kappaNum p := by
    have hconc := strictConcaveOn_kappaNum.concaveOn
    have hmem₁ : p₁ ∈ Icc (0:ℝ) (1/2) := ⟨hp₁0.le, hp₁.le⟩
    have hmemh : (1/2 : ℝ) ∈ Icc (0:ℝ) (1/2) := ⟨by norm_num, le_rfl⟩
    set a := (1/2 - p) / (1/2 - p₁) with ha
    have hd : 0 < 1/2 - p₁ := by linarith
    have ha0 : 0 ≤ a := div_nonneg (by linarith) hd.le
    have ha1 : a ≤ 1 := by rw [ha, div_le_one hd]; linarith
    have hb0 : 0 ≤ 1 - a := by linarith
    have h := hconc.2 hmem₁ hmemh ha0 hb0 (by ring)
    have hpt : a * p₁ + (1 - a) * (1/2) = p := by
      have : a * (1/2 - p₁) = 1/2 - p := by rw [ha, div_mul_cancel₀ _ hd.ne']
      linear_combination -this
    simp only [smul_eq_mul, kappaNum_half, mul_zero, add_zero, hpt] at h
    linarith
  -- the denominator of `κ` is at most `(1/4) log 2`
  have hden : p * (1 - p) * entropy p ≤ 1/4 * Real.log 2 := by
    have h1 : p * (1 - p) ≤ 1/4 := by nlinarith [sq_nonneg (p - 1/2)]
    have h2 := entropy_le_log_two hp0 (by linarith)
    calc p * (1 - p) * entropy p ≤ 1/4 * entropy p :=
          mul_le_mul_of_nonneg_right h1 hE.le
      _ ≤ 1/4 * Real.log 2 := mul_le_mul_of_nonneg_left h2 (by norm_num)
  rw [kappa_eq, le_div_iff₀ (mul_pos (mul_pos hp0 (by linarith)) hE)]
  calc kappaNum p₁ / ((1/2 - p₁) * (1/4 * Real.log 2)) * (1/2 - p) * (p * (1 - p) * entropy p)
      ≤ kappaNum p₁ / ((1/2 - p₁) * (1/4 * Real.log 2)) * (1/2 - p) * (1/4 * Real.log 2) := by
        apply mul_le_mul_of_nonneg_left hden
        apply mul_nonneg (div_nonneg hΦ₁.le hden0.le) (by linarith)
    _ = kappaNum p₁ * ((1/2 - p) / (1/2 - p₁)) := by field_simp
    _ ≤ kappaNum p := hchord

/-! ### `eq:log-derivative-mean` -/

/-- `eq:log-derivative-mean`: the entropy factor `F(p) = pq/E(p)` satisfies `F' = F κ`. -/
theorem hasDerivAt_entropyFactor {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun x => x * (1 - x) / entropy x) (p * (1 - p) / entropy p * kappa p) p := by
  have hE := entropy_pos hp0 hp1
  have hnum : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 * (1 - p) + p * (-1)) p :=
    (hasDerivAt_id p).mul ((hasDerivAt_id p).const_sub 1)
  have h := hnum.div (hasDerivAt_entropy hp0 hp1) hE.ne'
  convert h using 1
  have hp : p ≠ 0 := hp0.ne'
  have hq : (1:ℝ) - p ≠ 0 := by linarith
  have hE' : entropy p ≠ 0 := hE.ne'
  rw [kappa_eq]
  field_simp
  unfold kappaNum entropy
  rw [Real.log_inv, Real.log_inv]
  ring

end

end BrownianImages
