/-
The improper integrals of the proof of `thm:main-term-derivative`, for `T > 0`:
`∫_T^∞ |f'| = f(T)`, `∫_T^∞ x f'' = f(T) + |g(T)|`, `∫_T^∞ g = -T f(T) - ∫_T^∞ f`,
`∫_T^∞ |g'| ≤ 2 f(T) + |g(T)|`, and the bound `s ∫_T^∞ f ≤ 2.3` for `s ≤ 1/2`, through
`f ≤ x^{-s}` on `(T, 1]` and `f ≤ (1 - e^{-1})^{-s} e^{-sx}` on `[1, ∞)`.

* `integrableOn_mainF`, `integrableOn_mainF'`, `integrableOn_mainG`,
  `integrableOn_mul_mainF''`, `integrableOn_mainG'`: integrability on `(T, ∞)`.
* `integral_abs_mainF'`, `integral_mul_mainF''`, `integral_mainG`,
  `integral_abs_mainG'_le`: the four integrals.
* `mul_integral_mainF_le`: `s ∫_T^∞ f ≤ 2.3`.
-/
import BrownianImages.FixedDimension.MainTermF
import BrownianImages.FixedDimension.RiemannSum

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

/-! ### Integrability -/

/-- `(1 + x) e^{-sx} ≤ (2/s) e^{-sx/2}` for `0 < s ≤ 2`, `x ≥ 0`. -/
theorem one_add_mul_exp_le {s x : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (_hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(s * x)) ≤ 2 / s * Real.exp (-(s / 2 * x)) := by
  have h1 : 1 + s / 2 * x ≤ Real.exp (s / 2 * x) := by
    have := Real.add_one_le_exp (s / 2 * x); linarith
  have hpos : 0 < Real.exp (s / 2 * x) := Real.exp_pos _
  have e : Real.exp (-(s * x)) = Real.exp (-(s / 2 * x)) * Real.exp (-(s / 2 * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : (1 + x) * s ≤ 2 * (1 + s / 2 * x) := by nlinarith
  have hkey : (1 + x) * Real.exp (-(s / 2 * x)) ≤ 2 / s := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hpos hs]
    linarith
  calc (1 + x) * Real.exp (-(s * x))
      = ((1 + x) * Real.exp (-(s / 2 * x))) * Real.exp (-(s / 2 * x)) := by rw [e]; ring
    _ ≤ 2 / s * Real.exp (-(s / 2 * x)) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

/-- A function continuous on `(0, ∞)` and bounded by `A e^{-cx}` on `(T, ∞)` is integrable
there. -/
theorem integrableOn_Ioi_of_exp_bound {h : ℝ → ℝ} {T A c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hcont : ContinuousOn h (Ioi 0)) (hb : ∀ x ∈ Ioi T, |h x| ≤ A * Real.exp (-(c * x))) :
    IntegrableOn h (Ioi T) := by
  have hmeas : AEStronglyMeasurable h (volume.restrict (Ioi T)) :=
    (hcont.mono (Ioi_subset_Ioi hT.le)).aestronglyMeasurable measurableSet_Ioi
  have hexp : IntegrableOn (fun x => A * Real.exp (-(c * x))) (Ioi T) := by
    have := (exp_neg_integrableOn_Ioi T hc).const_mul A
    exact this.congr (Eventually.of_forall fun x => by simp [neg_mul])
  exact Integrable.mono' hexp hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
      rw [Real.norm_eq_abs]; exact hb x hx)

/-- `(1 + x) f(x)` is integrable on `(T, ∞)`. -/
theorem integrableOn_one_add_mul_mainF {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    IntegrableOn (fun x => (1 + x) * mainF s x) (Ioi T) := by
  refine integrableOn_Ioi_of_exp_bound hT (half_pos hs)
    ((continuousOn_const.add continuousOn_id).mul (continuousOn_mainF s))
    (A := (1 - Real.exp (-T)) ^ (-s) * (2 / s)) fun x hx => ?_
  have hx : T < x := hx
  have hx0 : 0 < x := hT.trans hx
  rw [abs_of_nonneg (mul_nonneg (by linarith) (mainF_pos hx0).le)]
  calc (1 + x) * mainF s x ≤ (1 + x) * ((1 - Real.exp (-T)) ^ (-s) * Real.exp (-(s * x))) :=
        mul_le_mul_of_nonneg_left (mainF_le_exp hs.le hT hx.le) (by linarith)
    _ = (1 - Real.exp (-T)) ^ (-s) * ((1 + x) * Real.exp (-(s * x))) := by ring
    _ ≤ (1 - Real.exp (-T)) ^ (-s) * (2 / s * Real.exp (-(s / 2 * x))) := by
        apply mul_le_mul_of_nonneg_left (one_add_mul_exp_le hs hs2 hx0.le)
        have : 0 < 1 - Real.exp (-T) := by
          have := Real.exp_lt_one_iff.2 (neg_lt_zero.2 hT); linarith
        positivity
    _ = (1 - Real.exp (-T)) ^ (-s) * (2 / s) * Real.exp (-(s / 2 * x)) := by ring

/-- Integrability of a function continuous on `(0, ∞)` and bounded by `K (1 + x) f(x)` on
`(T, ∞)`. -/
theorem integrableOn_of_le_mainF {h : ℝ → ℝ} {s T K : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T)
    (hcont : ContinuousOn h (Ioi 0)) (hb : ∀ x ∈ Ioi T, |h x| ≤ K * ((1 + x) * mainF s x)) :
    IntegrableOn h (Ioi T) := by
  have hmeas : AEStronglyMeasurable h (volume.restrict (Ioi T)) :=
    (hcont.mono (Ioi_subset_Ioi hT.le)).aestronglyMeasurable measurableSet_Ioi
  exact Integrable.mono' ((integrableOn_one_add_mul_mainF hs hs2 hT).const_mul K) hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
      rw [Real.norm_eq_abs]; exact hb x hx)

theorem integrableOn_mainF {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    IntegrableOn (mainF s) (Ioi T) :=
  integrableOn_of_le_mainF hs hs2 hT (continuousOn_mainF s) (K := 1) fun x hx => by
    have hx0 : 0 < x := hT.trans hx
    rw [abs_of_pos (mainF_pos hx0), one_mul]
    have := mainF_pos (s := s) hx0
    nlinarith

theorem integrableOn_mainG {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    IntegrableOn (mainG s) (Ioi T) :=
  integrableOn_of_le_mainF hs hs2 hT (continuousOn_id.mul (continuousOn_mainF' s)) (K := s)
    fun x hx => by
      have hx0 : 0 < x := hT.trans hx
      have := abs_mainG_le hs hx0
      linarith [show s * (1 + x) * mainF s x = s * ((1 + x) * mainF s x) by ring]

/-- `|f'(x)| ≤ s (1 + 1/T) f(x)` on `(T, ∞)`, from `|g| ≤ s (1 + x) f`. -/
theorem abs_mainF'_le {s T x : ℝ} (hs : 0 < s) (hT : 0 < T) (hx : T < x) :
    |mainF' s x| ≤ s * (1 + T⁻¹) * ((1 + x) * mainF s x) := by
  have hx0 : 0 < x := hT.trans hx
  have hg := abs_mainG_le hs hx0
  have hg' : |mainG s x| = x * |mainF' s x| := by
    unfold mainG; rw [abs_mul, abs_of_pos hx0]
  rw [hg'] at hg
  have hF := (mainF_pos (s := s) hx0).le
  have h1 : |mainF' s x| ≤ s * (1 + x) * mainF s x / x := by
    rw [le_div_iff₀ hx0]; linarith
  have h2 : s * (1 + x) * mainF s x / x ≤ s * (1 + T⁻¹) * ((1 + x) * mainF s x) := by
    rw [div_le_iff₀ hx0]
    have hTx : 1 ≤ T⁻¹ * x := by rw [← div_eq_inv_mul, one_le_div hT]; exact hx.le
    have : 0 ≤ s * ((1 + x) * mainF s x) := by positivity
    nlinarith
  exact h1.trans h2

theorem integrableOn_mainF' {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    IntegrableOn (mainF' s) (Ioi T) :=
  integrableOn_of_le_mainF hs hs2 hT (continuousOn_mainF' s) fun _ hx =>
    abs_mainF'_le hs hT hx

/-- `x f''(x) ≤ s (1 + x) (s + (s + 1)/(e^T - 1)) f(x)` on `(T, ∞)`. -/
theorem mul_mainF''_le {s T x : ℝ} (hs : 0 < s) (hT : 0 < T) (hx : T < x) :
    x * mainF'' s x ≤ s * (s + (s + 1) / (Real.exp T - 1)) * ((1 + x) * mainF s x) := by
  have hx0 : 0 < x := hT.trans hx
  have hpos := exp_sub_one_pos hx0
  have hposT := exp_sub_one_pos hT
  have hne := hpos.ne'
  -- `(eˣ - 1)^{-s-2} = (eˣ - 1)^{-s} / (eˣ - 1)²`
  have e : (Real.exp x - 1) ^ (-s - 2) = (Real.exp x - 1) ^ (-s) / (Real.exp x - 1) ^ 2 := by
    rw [show (-s - 2) = (-s) - (2:ℕ) by norm_num, Real.rpow_sub_natCast hne]
  have hF := mainF_pos (s := s) hx0
  unfold mainF'' mainF
  rw [e]
  have h1 : x * Real.exp x ≤ (1 + x) * (Real.exp x - 1) := by
    have := Real.add_one_le_exp x; nlinarith
  have hmono : Real.exp T - 1 ≤ Real.exp x - 1 := by
    have := Real.exp_le_exp.2 hx.le; linarith
  have h2 : (s * Real.exp x + 1) / (Real.exp x - 1) ≤ s + (s + 1) / (Real.exp T - 1) := by
    rw [div_le_iff₀ hpos]
    have h3 : (s + 1) / (Real.exp T - 1) * (Real.exp x - 1) ≥ s + 1 := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hposT]
      exact mul_le_mul_of_nonneg_left hmono (by linarith)
    nlinarith
  have hFpos := Real.rpow_pos_of_pos hpos (-s)
  rw [show x * (s * Real.exp x * ((Real.exp x - 1) ^ (-s) / (Real.exp x - 1) ^ 2) *
      (s * Real.exp x + 1)) = s * (Real.exp x - 1) ^ (-s) *
      ((x * Real.exp x / (Real.exp x - 1)) * ((s * Real.exp x + 1) / (Real.exp x - 1))) by
      field_simp]
  rw [show s * (s + (s + 1) / (Real.exp T - 1)) * ((1 + x) * (Real.exp x - 1) ^ (-s))
      = s * (Real.exp x - 1) ^ (-s) * ((1 + x) * (s + (s + 1) / (Real.exp T - 1))) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h4 : x * Real.exp x / (Real.exp x - 1) ≤ 1 + x := by rw [div_le_iff₀ hpos]; exact h1
  have h5 : 0 ≤ (s * Real.exp x + 1) / (Real.exp x - 1) := by positivity
  exact mul_le_mul h4 h2 h5 (by linarith)

theorem integrableOn_mul_mainF'' {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    IntegrableOn (fun x => x * mainF'' s x) (Ioi T) :=
  integrableOn_of_le_mainF hs hs2 hT (continuousOn_id.mul (continuousOn_mainF'' s))
    (K := s * (s + (s + 1) / (Real.exp T - 1))) fun x hx => by
      have hx0 : 0 < x := hT.trans hx
      rw [abs_of_nonneg (mul_nonneg hx0.le (mainF''_pos hs hx0).le)]
      exact mul_mainF''_le hs hT hx

theorem integrableOn_mainG' {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    IntegrableOn (mainG' s) (Ioi T) :=
  (integrableOn_mainF' hs hs2 hT).add (integrableOn_mul_mainF'' hs hs2 hT)

/-! ### The four integrals -/

/-- `∫_T^∞ |f'| = f(T)`. -/
theorem integral_abs_mainF' {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    ∫ x in Ioi T, |mainF' s x| = mainF s T := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := mainF s) (f' := mainF' s) (a := T)
    (hasDerivAt_mainF s hT).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_mainF s (hT.trans hx)) (integrableOn_mainF' hs hs2 hT)
    (tendsto_mainF hs)
  rw [zero_sub] at h
  have habs : ∀ x ∈ Ioi T, |mainF' s x| = -mainF' s x := fun x hx =>
    abs_of_neg (mainF'_neg hs (hT.trans hx))
  rw [setIntegral_congr_fun measurableSet_Ioi habs, integral_neg, h, neg_neg]

/-- `∫_T^∞ x f''(x) dx = f(T) + |g(T)|`. -/
theorem integral_mul_mainF'' {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    ∫ x in Ioi T, x * mainF'' s x = mainF s T + |mainG s T| := by
  -- the antiderivative `g - f`
  have hd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y => mainG s y - mainF s y) (x * mainF'' s x) x := by
    intro x hx0
    have := (hasDerivAt_mainG s hx0).sub (hasDerivAt_mainF s hx0)
    exact this.congr_deriv (by unfold mainG'; ring)
  have hlim : Tendsto (fun y => mainG s y - mainF s y) atTop (𝓝 (0 - 0)) :=
    (tendsto_mainG hs).sub (tendsto_mainF hs)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := T)
    (hd T hT).continuousAt.continuousWithinAt (fun x hx => hd x (hT.trans hx))
    (integrableOn_mul_mainF'' hs hs2 hT) hlim
  have h' : ∫ x in Ioi T, x * mainF'' s x = -(mainG s T - mainF s T) := by
    rw [h]; ring
  rw [h', abs_of_neg (by
    have := mainF'_neg hs hT
    unfold mainG; exact mul_neg_of_pos_of_neg hT this)]
  ring

/-- `∫_T^∞ g = -T f(T) - ∫_T^∞ f`. -/
theorem integral_mainG {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    ∫ x in Ioi T, mainG s x = -(T * mainF s T) - ∫ x in Ioi T, mainF s x := by
  -- the antiderivative `x f(x)` of `f + g`
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun y => y * mainF s y) (mainF s x + mainG s x) x := by
    intro x hx0
    have := (hasDerivAt_id x).mul (hasDerivAt_mainF s hx0)
    exact this.congr_deriv (by unfold mainG; simp)
  have hlim : Tendsto (fun y => y * mainF s y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y => (1 + y) * mainF s y) atTop (𝓝 0) := by
      have hC : Tendsto (fun x : ℝ => (1 - Real.exp (-1)) ^ (-s) * ((1 + x) * Real.exp (-(s * x))))
          atTop (𝓝 ((1 - Real.exp (-1)) ^ (-s) * 0)) := (tendsto_one_add_mul_exp hs).const_mul _
      rw [mul_zero] at hC
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with x hx
        exact mul_nonneg (by linarith) (mainF_pos hx).le
      · filter_upwards [eventually_ge_atTop 1] with x hx
        calc (1 + x) * mainF s x
            ≤ (1 + x) * ((1 - Real.exp (-1)) ^ (-s) * Real.exp (-(s * x))) :=
              mul_le_mul_of_nonneg_left (mainF_le_exp hs.le one_pos hx) (by linarith)
          _ = _ := by ring
    have h2 := h1.sub (tendsto_mainF hs)
    rw [sub_zero] at h2
    refine h2.congr fun y => ?_
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := T)
    (hd T hT).continuousAt.continuousWithinAt (fun x hx => hd x (hT.trans hx))
    ((integrableOn_mainF hs hs2 hT).add (integrableOn_mainG hs hs2 hT)) hlim
  rw [integral_add (integrableOn_mainF hs hs2 hT) (integrableOn_mainG hs hs2 hT)] at h
  have h' : (∫ x in Ioi T, mainF s x) + ∫ x in Ioi T, mainG s x = -(T * mainF s T) := by
    rw [h]; ring
  linarith

/-- `∫_T^∞ |g'| ≤ 2 f(T) + |g(T)|`. -/
theorem integral_abs_mainG'_le {s T : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hT : 0 < T) :
    ∫ x in Ioi T, |mainG' s x| ≤ 2 * mainF s T + |mainG s T| := by
  have hle : ∀ x ∈ Ioi T, |mainG' s x| ≤ |mainF' s x| + x * mainF'' s x := by
    intro x hx
    have hx0 : 0 < x := hT.trans hx
    unfold mainG'
    calc |mainF' s x + x * mainF'' s x| ≤ |mainF' s x| + |x * mainF'' s x| := abs_add_le _ _
      _ = |mainF' s x| + x * mainF'' s x := by
          rw [abs_of_nonneg (mul_nonneg hx0.le (mainF''_pos hs hx0).le)]
  calc ∫ x in Ioi T, |mainG' s x|
      ≤ ∫ x in Ioi T, (|mainF' s x| + x * mainF'' s x) :=
        setIntegral_mono_on (integrableOn_mainG' hs hs2 hT).abs
          ((integrableOn_mainF' hs hs2 hT).abs.add (integrableOn_mul_mainF'' hs hs2 hT))
          measurableSet_Ioi hle
    _ = mainF s T + (mainF s T + |mainG s T|) := by
        rw [integral_add (integrableOn_mainF' hs hs2 hT).abs (integrableOn_mul_mainF'' hs hs2 hT),
          integral_abs_mainF' hs hs2 hT, integral_mul_mainF'' hs hs2 hT]
    _ = 2 * mainF s T + |mainG s T| := by ring

/-! ### The bound on `s ∫ f` -/

/-- `(1 - e^{-1})^{-s} ≤ 1.26` for `0 ≤ s ≤ 1/2`. -/
theorem one_sub_exp_neg_one_rpow_le {s : ℝ} (hs : s ≤ 1/2) :
    (1 - Real.exp (-1)) ^ (-s) ≤ 1.26 := by
  have he := Real.exp_one_gt_d9
  have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h1 : Real.exp (-1) ≤ 0.3701 := by
    rw [hinv, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hb : (1:ℝ) ≤ (1 - Real.exp (-1))⁻¹ := by
    rw [one_le_inv_iff₀]
    constructor <;> linarith [Real.exp_pos (-1)]
  have hpos : 0 < 1 - Real.exp (-1) := by linarith
  rw [Real.rpow_neg hpos.le, ← Real.inv_rpow hpos.le]
  calc (1 - Real.exp (-1))⁻¹ ^ s ≤ (1 - Real.exp (-1))⁻¹ ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb hs
    _ = Real.sqrt (1 - Real.exp (-1))⁻¹ := by rw [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (1.26 ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [inv_le_comm₀ hpos (by norm_num)]
        linarith
    _ = 1.26 := Real.sqrt_sq (by norm_num)

/-- `∫_1^∞ (1 - e^{-1})^{-s} e^{-sx} dx = (1 - e^{-1})^{-s} e^{-s} / s`. -/
theorem integral_exp_tail {s : ℝ} (hs : 0 < s) :
    ∫ x in Ioi (1:ℝ), Real.exp (-(s * x)) = Real.exp (-s) / s := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y => -(Real.exp (-(s * y))) / s)
      (Real.exp (-(s * x))) x := by
    intro x
    have := ((Real.hasDerivAt_exp (-(s * x))).comp x
      (((hasDerivAt_id x).const_mul s).neg)).neg.div_const s
    refine this.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun y => -(Real.exp (-(s * y))) / s) atTop (𝓝 (-0 / s)) :=
    ((tendsto_exp_neg_mul hs).neg).div_const s
  have hint : IntegrableOn (fun x => Real.exp (-(s * x))) (Ioi (1:ℝ)) := by
    have := exp_neg_integrableOn_Ioi (1:ℝ) hs
    exact this.congr (Eventually.of_forall fun x => by simp [neg_mul])
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 1)
    (hd 1).continuousAt.continuousWithinAt (fun x _ => hd x) hint hlim
  rw [h]
  field_simp
  ring

/-- `s ∫_T^∞ f ≤ 2.3` for `0 < s ≤ 1/2` and `T > 0`. -/
theorem mul_integral_mainF_le {s T : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hT : 0 < T) :
    s * ∫ x in Ioi T, mainF s x ≤ 2.3 := by
  have hs2 : s ≤ 2 := by linarith
  have hC := one_sub_exp_neg_one_rpow_le hs1
  have hCpos : 0 < (1 - Real.exp (-1)) ^ (-s) := by
    apply Real.rpow_pos_of_pos
    have := Real.exp_lt_one_iff.2 (show (-1:ℝ) < 0 by norm_num); linarith
  -- the tail integral from `max T 1`
  have htail : ∀ a : ℝ, 1 ≤ a → s * ∫ x in Ioi a, mainF s x ≤ 1.26 := by
    intro a ha
    have h1 : ∫ x in Ioi a, mainF s x ≤ ∫ x in Ioi a, (1 - Real.exp (-1)) ^ (-s) * Real.exp (-(s * x)) := by
      refine setIntegral_mono_on (integrableOn_mainF hs hs2 (by linarith)) ?_ measurableSet_Ioi
        fun x hx => mainF_le_exp hs.le one_pos (le_trans ha (le_of_lt hx))
      have := (exp_neg_integrableOn_Ioi a hs).const_mul ((1 - Real.exp (-1)) ^ (-s))
      exact this.congr (Eventually.of_forall fun x => by simp [neg_mul])
    have h2 : ∫ x in Ioi a, Real.exp (-(s * x)) ≤ ∫ x in Ioi (1:ℝ), Real.exp (-(s * x)) := by
      apply setIntegral_mono_set
      · have := exp_neg_integrableOn_Ioi (1:ℝ) hs
        exact this.congr (Eventually.of_forall fun x => by simp [neg_mul])
      · exact Eventually.of_forall fun x => (Real.exp_pos _).le
      · exact Eventually.of_forall (Ioi_subset_Ioi ha)
    rw [integral_const_mul] at h1
    rw [integral_exp_tail hs] at h2
    have h3 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc s * ∫ x in Ioi a, mainF s x
        ≤ s * ((1 - Real.exp (-1)) ^ (-s) * (Real.exp (-s) / s)) := by
          apply mul_le_mul_of_nonneg_left _ hs.le
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hCpos.le)
      _ = (1 - Real.exp (-1)) ^ (-s) * Real.exp (-s) := by field_simp
      _ ≤ 1.26 * 1 := mul_le_mul hC h3 (Real.exp_pos _).le (by norm_num)
      _ = 1.26 := by ring
  rcases le_or_gt 1 T with h1T | hT1
  · linarith [htail T h1T]
  · -- split `(T, ∞) = (T, 1] ∪ (1, ∞)`
    have hsplit : ∫ x in Ioi T, mainF s x
        = (∫ x in Ioc T 1, mainF s x) + ∫ x in Ioi (1:ℝ), mainF s x := by
      rw [← Ioc_union_Ioi_eq_Ioi hT1.le]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((integrableOn_mainF hs hs2 hT).mono_set Ioc_subset_Ioi_self)
        (integrableOn_mainF hs hs2 one_pos)
    -- the singular piece: `∫_T^1 x^{-s} ≤ 1/(1-s)`
    have hpiece : ∫ x in Ioc T 1, mainF s x ≤ 1 / (1 - s) := by
      have hrp : ∫ x in Ioc T 1, x ^ (-s) = (1 - T ^ (-s + 1)) / (-s + 1) := by
        rw [← intervalIntegral.integral_of_le hT1.le, integral_rpow (Or.inr ⟨by linarith,
          fun h => by rw [uIcc_of_le hT1.le] at h; exact absurd h.1 (not_le.2 hT)⟩)]
        simp
      have hmono : ∫ x in Ioc T 1, mainF s x ≤ ∫ x in Ioc T 1, x ^ (-s) := by
        refine setIntegral_mono_on ((integrableOn_mainF hs hs2 hT).mono_set Ioc_subset_Ioi_self)
          ?_ measurableSet_Ioc fun x hx => mainF_le_rpow hs.le (hT.trans hx.1)
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
        exact continuousOn_id.rpow_const fun x hx => Or.inl (by linarith [hx.1] : x ≠ 0)
      rw [hrp] at hmono
      have hT' : 0 ≤ T ^ (-s + 1) := Real.rpow_nonneg hT.le _
      have hden : 0 < -s + 1 := by linarith
      calc ∫ x in Ioc T 1, mainF s x ≤ (1 - T ^ (-s + 1)) / (-s + 1) := hmono
        _ ≤ 1 / (-s + 1) := by
            apply div_le_div_of_nonneg_right _ hden.le; linarith
        _ = 1 / (1 - s) := by ring_nf
    have htail1 := htail 1 le_rfl
    have hs1' : s * (1 / (1 - s)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]; linarith
    rw [hsplit, mul_add]
    have := mul_le_mul_of_nonneg_left hpiece hs.le
    linarith

end

end BrownianImages
