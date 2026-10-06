/-
The function `f(x) = (eˣ - 1)^{-s}` of the proof of `thm:main-term-derivative`, with
`g(x) = x f'(x)`: positivity and monotonicity, the bounds `f ≤ x^{-s}` and
`f ≤ (1 - e^{-T})^{-s} e^{-sx}`, the derivatives `f'`, `f''`, `g'`, the bound
`|g| ≤ s(1 + x) f`, and the decay of `f`, `g` and `x f'` at infinity.

* `mainF`, `mainF'`, `mainF''`, `mainG`, `mainG'`: the functions.
* `hasDerivAt_mainF`, `hasDerivAt_mainF'`, `hasDerivAt_mainG`: the derivatives.
* `mainF_le_rpow`, `mainF_le_exp`, `abs_mainG_le`: the pointwise bounds.
* `tendsto_mainF`, `tendsto_mainG`: the decay.
-/
import BrownianImages.FixedDimension.System

namespace BrownianImages

open Filter Set
open scoped Topology

noncomputable section

/-- `f(x) = (eˣ - 1)^{-s}`. -/
def mainF (s x : ℝ) : ℝ := (Real.exp x - 1) ^ (-s)

/-- `f'(x) = -s eˣ (eˣ - 1)^{-s-1}`. -/
def mainF' (s x : ℝ) : ℝ := -s * Real.exp x * (Real.exp x - 1) ^ (-s - 1)

/-- `f''(x) = s eˣ (eˣ - 1)^{-s-2} (s eˣ + 1)`. -/
def mainF'' (s x : ℝ) : ℝ :=
  s * Real.exp x * (Real.exp x - 1) ^ (-s - 2) * (s * Real.exp x + 1)

/-- `g(x) = x f'(x)`. -/
def mainG (s x : ℝ) : ℝ := x * mainF' s x

/-- `g'(x) = f'(x) + x f''(x)`. -/
def mainG' (s x : ℝ) : ℝ := mainF' s x + x * mainF'' s x

theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have := Real.one_lt_exp_iff.2 hx; linarith

theorem le_exp_sub_one (x : ℝ) : x ≤ Real.exp x - 1 := by
  have := Real.add_one_le_exp x; linarith

theorem mainF_pos {s x : ℝ} (hx : 0 < x) : 0 < mainF s x :=
  Real.rpow_pos_of_pos (exp_sub_one_pos hx) _

theorem mainF'_neg {s x : ℝ} (hs : 0 < s) (hx : 0 < x) : mainF' s x < 0 := by
  unfold mainF'
  have h := mul_pos (mul_pos hs (Real.exp_pos x)) (Real.rpow_pos_of_pos (exp_sub_one_pos hx) (-s - 1))
  linarith

theorem mainF''_pos {s x : ℝ} (hs : 0 < s) (hx : 0 < x) : 0 < mainF'' s x := by
  unfold mainF''
  have := Real.rpow_pos_of_pos (exp_sub_one_pos hx) (-s - 2)
  have := Real.exp_pos x
  positivity

/-! ### Derivatives -/

theorem hasDerivAt_mainF (s : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (mainF s) (mainF' s x) x := by
  have h := ((Real.hasDerivAt_exp x).sub_const 1).rpow_const
    (p := -s) (Or.inl (exp_sub_one_pos hx).ne')
  exact h.congr_deriv (by unfold mainF'; ring)

theorem hasDerivAt_mainF' (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (mainF' s) (mainF'' s x) x := by
  have hne := (exp_sub_one_pos hx).ne'
  have h1 := ((Real.hasDerivAt_exp x).sub_const 1).rpow_const
    (p := -s - 1) (Or.inl hne)
  have hexp : HasDerivAt (fun y => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
  have h := (hexp.mul h1).const_mul (-s)
  have hfun : mainF' s = fun y => -s * (Real.exp y * (Real.exp y - 1) ^ (-s - 1)) := by
    funext y; unfold mainF'; ring
  rw [hfun]
  refine h.congr_deriv ?_
  have e : (Real.exp x - 1) ^ (-s - 1) = (Real.exp x - 1) ^ (-s - 2) * (Real.exp x - 1) := by
    rw [← Real.rpow_add_one hne]; ring_nf
  have e2 : (Real.exp x - 1) ^ (-s - 1 - 1) = (Real.exp x - 1) ^ (-s - 2) := by ring_nf
  rw [e2, mainF'', e]
  ring

theorem hasDerivAt_mainG (s : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (mainG s) (mainG' s x) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_mainF' s hx)
  exact h.congr_deriv (by unfold mainG'; simp)

theorem continuousOn_mainF (s : ℝ) : ContinuousOn (mainF s) (Ioi 0) := fun _ hx =>
  (hasDerivAt_mainF s hx).continuousAt.continuousWithinAt

theorem continuousOn_mainF' (s : ℝ) : ContinuousOn (mainF' s) (Ioi 0) := fun _ hx =>
  (hasDerivAt_mainF' s hx).continuousAt.continuousWithinAt

theorem continuousOn_mainF'' (s : ℝ) : ContinuousOn (mainF'' s) (Ioi 0) := by
  unfold mainF''
  refine ContinuousOn.mul (ContinuousOn.mul (continuousOn_const.mul Real.continuous_exp.continuousOn)
    ?_) (continuousOn_const.mul Real.continuous_exp.continuousOn |>.add continuousOn_const)
  exact (Real.continuous_exp.continuousOn.sub continuousOn_const).rpow_const
    fun x hx => Or.inl (exp_sub_one_pos hx).ne'

theorem continuousOn_mainG' (s : ℝ) : ContinuousOn (mainG' s) (Ioi 0) :=
  (continuousOn_mainF' s).add (continuousOn_id.mul (continuousOn_mainF'' s))

/-! ### Pointwise bounds -/

/-- `f(x) ≤ x^{-s}`, since `eˣ - 1 ≥ x`. -/
theorem mainF_le_rpow {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) : mainF s x ≤ x ^ (-s) :=
  rpow_neg_antitone hx (le_exp_sub_one x) hs

/-- `f(x) ≤ (1 - e^{-T})^{-s} e^{-sx}` for `x ≥ T > 0`. -/
theorem mainF_le_exp {s T x : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (hx : T ≤ x) :
    mainF s x ≤ (1 - Real.exp (-T)) ^ (-s) * Real.exp (-(s * x)) := by
  have hx0 : 0 < x := hT.trans_le hx
  have h1 : 0 < 1 - Real.exp (-T) := by
    have := Real.exp_lt_one_iff.2 (neg_lt_zero.2 hT); linarith
  have h2 : 1 - Real.exp (-T) ≤ 1 - Real.exp (-x) := by
    have := Real.exp_le_exp.2 (neg_le_neg hx); linarith
  have e : Real.exp x - 1 = Real.exp x * (1 - Real.exp (-x)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; simp
  unfold mainF
  rw [e, Real.mul_rpow (Real.exp_pos x).le (by linarith), ← Real.exp_mul, mul_comm]
  rw [show x * -s = -(s * x) by ring]
  exact mul_le_mul_of_nonneg_right (rpow_neg_antitone h1 h2 hs) (Real.exp_pos _).le

theorem mainF_antitoneOn {s : ℝ} (hs : 0 ≤ s) : AntitoneOn (mainF s) (Ioi 0) := by
  intro x hx y _ hxy
  unfold mainF
  exact rpow_neg_antitone (exp_sub_one_pos hx) (by linarith [Real.exp_le_exp.2 hxy]) hs

/-- `|g(x)| ≤ s (1 + x) f(x)`, by `x eˣ ≤ (1 + x)(eˣ - 1)`. -/
theorem abs_mainG_le {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    |mainG s x| ≤ s * (1 + x) * mainF s x := by
  have hne := (exp_sub_one_pos hx).ne'
  have hpos := exp_sub_one_pos hx
  have hneg := mainF'_neg hs hx
  have habs : |mainG s x| = -(x * mainF' s x) := by
    unfold mainG
    rw [abs_of_neg (mul_neg_of_pos_of_neg hx hneg)]
  rw [habs]
  have e : (Real.exp x - 1) ^ (-s - 1) = (Real.exp x - 1) ^ (-s) / (Real.exp x - 1) := by
    rw [← Real.rpow_sub_one hne]
  unfold mainF' mainF
  rw [e]
  have hineq : x * Real.exp x ≤ (1 + x) * (Real.exp x - 1) := by
    have := Real.add_one_le_exp x
    nlinarith
  have hF := Real.rpow_pos_of_pos hpos (-s)
  rw [show -(x * (-s * Real.exp x * ((Real.exp x - 1) ^ (-s) / (Real.exp x - 1))))
      = s * (Real.exp x - 1) ^ (-s) * (x * Real.exp x / (Real.exp x - 1)) by field_simp]
  rw [show s * (1 + x) * (Real.exp x - 1) ^ (-s) = s * (Real.exp x - 1) ^ (-s) * (1 + x) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff₀ hpos]
  exact hineq

/-! ### Decay at infinity -/

theorem tendsto_exp_neg_mul {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => Real.exp (-(s * x))) atTop (𝓝 0) := by
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hs)
  exact this

theorem tendsto_mainF {s : ℝ} (hs : 0 < s) : Tendsto (mainF s) atTop (𝓝 0) := by
  have hC : Tendsto (fun x : ℝ => (1 - Real.exp (-1)) ^ (-s) * Real.exp (-(s * x))) atTop
      (𝓝 ((1 - Real.exp (-1)) ^ (-s) * 0)) := (tendsto_exp_neg_mul hs).const_mul _
  rw [mul_zero] at hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx using (mainF_pos hx).le
  · filter_upwards [eventually_ge_atTop 1] with x hx using mainF_le_exp hs.le one_pos hx

/-- `(1 + x) e^{-sx} → 0`. -/
theorem tendsto_one_add_mul_exp {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => (1 + x) * Real.exp (-(s * x))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := h1.comp (tendsto_id.const_mul_atTop hs)
  have h3 : Tendsto (fun x : ℝ => s⁻¹ * (s * x * Real.exp (-(s * x)))) atTop (𝓝 (s⁻¹ * 0)) :=
    h2.const_mul _
  rw [mul_zero] at h3
  have h4 := h3.add (tendsto_exp_neg_mul hs)
  rw [add_zero] at h4
  refine h4.congr fun x => ?_
  field_simp
  ring

theorem tendsto_mainG {s : ℝ} (hs : 0 < s) : Tendsto (mainG s) atTop (𝓝 0) := by
  have hC : Tendsto (fun x : ℝ => s * (1 - Real.exp (-1)) ^ (-s) * ((1 + x) * Real.exp (-(s * x))))
      atTop (𝓝 (s * (1 - Real.exp (-1)) ^ (-s) * 0)) := (tendsto_one_add_mul_exp hs).const_mul _
  rw [mul_zero] at hC
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC ?_ ?_
  · exact Eventually.of_forall fun x => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    calc |mainG s x| ≤ s * (1 + x) * mainF s x := abs_mainG_le hs hx0
      _ ≤ s * (1 + x) * ((1 - Real.exp (-1)) ^ (-s) * Real.exp (-(s * x))) := by
          apply mul_le_mul_of_nonneg_left (mainF_le_exp hs.le one_pos hx)
          positivity
      _ = s * (1 - Real.exp (-1)) ^ (-s) * ((1 + x) * Real.exp (-(s * x))) := by ring

end

end BrownianImages
