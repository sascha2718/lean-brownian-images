/-
The parametrisation of the two-contraction family by its dimension, in the proof of
`thm:two-contraction-distinction`: `p = 2^{-s}`, `q = 1 - p` and `c(s) = q^{1/s}`, the
library's `pairRatio`.

* `pairRatio_lt_pairRatio`, `differentiableAt_pairRatio`: `c(s)` is strictly increasing
  and differentiable on `(0, 1)`.
* `dimension_facts`: `2^{-s} + c^s = 1` with `0 < c < 1/2` forces `0 < s < 1` and
  `c = c(s)`.
* `exists_unique_twoContractionDim`: for every `0 < c < 1/2` the dimension `s(c)` exists
  and is unique.
* `pairWeight_mul_lt_one`: `q(3 - 2c) < 1`, which is `q(1-c) < p/2`, by strict concavity
  of `x ↦ x^s` on `r = 2c < 1 < 2`.
* `log_two_rpow_sub_one_lt`: `log(2^s - 1) + 2 log 2 · s(1-s) < 0` on `(0, 1)`.
* `momentLoss_lt`: `2s log 2 · c(1-c)/(1/2 - c) < s/(1-s)`.
-/
import BrownianImages.SelfSimilar
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace BrownianImages

open Real Set

/-- `c(s) = (1 - 2^{-s})^{1/s}` is strictly increasing in the dimension. -/
theorem pairRatio_lt_pairRatio {s s' : ℝ} (hs0 : 0 < s) (hss : s < s') :
    pairRatio s < pairRatio s' := by
  have hs'0 : 0 < s' := hs0.trans hss
  have hx0 : 0 < 1 - (2:ℝ) ^ (-s) := one_sub_two_rpow_pos hs0
  have hx1 : 1 - (2:ℝ) ^ (-s) < 1 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (-s); linarith
  have hxx : 1 - (2:ℝ) ^ (-s) < 1 - (2:ℝ) ^ (-s') := by
    have : (2:ℝ) ^ (-s') < (2:ℝ) ^ (-s) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  unfold pairRatio
  calc (1 - (2:ℝ) ^ (-s)) ^ s⁻¹ < (1 - (2:ℝ) ^ (-s)) ^ s'⁻¹ :=
        Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 (inv_strictAnti₀ hs0 hss)
    _ < (1 - (2:ℝ) ^ (-s')) ^ s'⁻¹ :=
        Real.rpow_lt_rpow hx0.le hxx (inv_pos.2 hs'0)

/-- `c(s)` is differentiable on `(0, ∞)`. -/
theorem differentiableAt_pairRatio {s : ℝ} (hs0 : 0 < s) :
    DifferentiableAt ℝ pairRatio s := by
  have h2 : DifferentiableAt ℝ (fun t : ℝ => (2:ℝ) ^ (-t)) s :=
    (differentiableAt_const _).rpow differentiableAt_id.neg (by norm_num)
  exact ((differentiableAt_const _).sub h2).rpow (differentiableAt_inv hs0.ne')
    (one_sub_two_rpow_pos hs0).ne'

/-- The dimension equation `2^{-s} + c^s = 1` with `0 < c < 1/2` forces `0 < s < 1` and
`c = c(s)`. -/
theorem dimension_facts {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hs : (2:ℝ) ^ (-s) + c ^ s = 1) : 0 < s ∧ s < 1 ∧ c = pairRatio s := by
  have hcpos : 0 < c ^ s := Real.rpow_pos_of_pos hc0 s
  have hs0 : 0 < s := by
    by_contra h
    push Not at h
    have : 1 ≤ (2:ℝ) ^ (-s) := Real.one_le_rpow (by norm_num) (by linarith)
    linarith
  have hs1 : s < 1 := by
    by_contra h
    push Not at h
    have h1 : (2:ℝ) ^ (-s) ≤ 1/2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
        (show -s ≤ -1 by linarith)
      rwa [Real.rpow_neg_one, ← one_div] at this
    have h2 : c ^ s ≤ c := by
      have := Real.rpow_le_rpow_of_exponent_ge hc0 (by linarith) h
      rwa [Real.rpow_one] at this
    linarith
  refine ⟨hs0, hs1, ?_⟩
  have hcs : c ^ s = 1 - (2:ℝ) ^ (-s) := by linarith
  unfold pairRatio
  rw [← hcs, ← Real.rpow_mul hc0.le, mul_inv_cancel₀ hs0.ne', Real.rpow_one]

/-- `(2c)^s = 2^s - 1` along the family. -/
theorem two_mul_pairRatio_rpow {s : ℝ} (hs0 : 0 < s) :
    (2 * pairRatio s) ^ s = (2:ℝ) ^ s - 1 := by
  rw [Real.mul_rpow (by norm_num) (pairRatio_pos hs0).le, pairRatio_rpow hs0, mul_sub,
    mul_one, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]

/-- **`eq:natural-weight-bound`: `q(3 - 2c) < 1`**, the inequality `q(1-c) < p/2` behind `𝔼 Y < 1/2` at the natural
parameters.  With `r = 2c`, strict concavity of `x ↦ x^s` on `r < 1 < 2` gives
`(1 - r^s)/(1 - r) > 2^s - 1 = r^s`, that is `r^s(2 - r) < 1`. -/
theorem pairWeight_mul_lt_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - (2:ℝ) ^ (-s)) * (3 - 2 * pairRatio s) < 1 := by
  set c := pairRatio s with hc
  have hc0 := pairRatio_pos hs0
  have hch := pairRatio_lt_half hs0 hs1
  set r := 2 * c with hr
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by linarith
  have hrs := two_mul_pairRatio_rpow hs0
  rw [← hc, ← hr] at hrs
  have hconc := (Real.strictConcaveOn_rpow hs0 hs1).slope_anti_adjacent
    (x := r) (y := 1) (z := 2) (mem_Ici.2 hr0.le) (mem_Ici.2 (by norm_num)) hr1 (by norm_num)
  simp only [Real.one_rpow] at hconc
  rw [show (2:ℝ) - 1 = 1 by norm_num, div_one, lt_div_iff₀ (by linarith), hrs] at hconc
  -- `hconc : (2^s - 1)(1 - r) < 1 - (2^s - 1)`
  have hA : (2:ℝ) ^ (-s) = ((2:ℝ) ^ s)⁻¹ := Real.rpow_neg (by norm_num) s
  have hApos : 0 < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  rw [hA]
  have hcr : 3 - 2 * c = 3 - r := by rw [hr]
  rw [hcr, show (1 - ((2:ℝ) ^ s)⁻¹) = ((2:ℝ) ^ s - 1) / (2:ℝ) ^ s by field_simp,
    div_mul_eq_mul_div, div_lt_one hApos]
  nlinarith

/-- `log(2^s - 1) + 2 log 2 · s(1-s) < 0` on `(0, 1)`: the function is strictly increasing
on `(0, 1]`, where its derivative `log 2 · (1 - (2^s - 1)(4s - 3))/(2^s - 1)` is positive,
and vanishes at `s = 1`. -/
theorem log_two_rpow_sub_one_lt {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.log ((2:ℝ) ^ s - 1) + 2 * Real.log 2 * (s * (1 - s)) < 0 := by
  set f : ℝ → ℝ := fun t => Real.log ((2:ℝ) ^ t - 1) + 2 * Real.log 2 * (t * (1 - t)) with hf
  have hA : ∀ t : ℝ, 0 < t → 1 < (2:ℝ) ^ t := fun t ht => Real.one_lt_rpow (by norm_num) ht
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f ((2:ℝ) ^ t * Real.log 2 / ((2:ℝ) ^ t - 1)
      + 2 * Real.log 2 * (1 - 2 * t)) t := by
    intro t ht
    have h1 := (Real.hasStrictDerivAt_const_rpow (show (0:ℝ) < 2 by norm_num) t).hasDerivAt
    have h2 := (h1.sub_const 1).log (by linarith [hA t ht])
    have h3 : HasDerivAt (fun t : ℝ => 2 * Real.log 2 * (t * (1 - t)))
        (2 * Real.log 2 * (1 - 2 * t)) t := by
      have h := ((hasDerivAt_id' t).mul ((hasDerivAt_const t (1:ℝ)).sub
        (hasDerivAt_id' t))).const_mul (2 * Real.log 2)
      convert h using 1
      simp only [Pi.sub_apply]
      ring
    exact h2.add h3
  have hcont : ContinuousOn f (Ioc 0 1) := fun t ht =>
    (hderiv t ht.1).continuousAt.continuousWithinAt
  have hpos : ∀ t ∈ interior (Ioc (0:ℝ) 1), 0 < deriv f t := by
    intro t ht
    rw [interior_Ioc] at ht
    rw [(hderiv t ht.1).deriv]
    have hAt := hA t ht.1
    have hA2 : (2:ℝ) ^ t < 2 := by
      have := Real.rpow_lt_rpow_of_exponent_lt (show (1:ℝ) < 2 by norm_num) ht.2
      rwa [Real.rpow_one] at this
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkey : ((2:ℝ) ^ t - 1) * (4 * t - 3) < 1 := by
      rcases le_or_gt (4 * t - 3) 0 with h | h
      · nlinarith
      · nlinarith [ht.2]
    have hden : 0 < (2:ℝ) ^ t - 1 := by linarith
    have : (2:ℝ) ^ t * Real.log 2 / ((2:ℝ) ^ t - 1) + 2 * Real.log 2 * (1 - 2 * t)
        = Real.log 2 * (1 - ((2:ℝ) ^ t - 1) * (4 * t - 3)) / ((2:ℝ) ^ t - 1) := by
      field_simp; ring
    rw [this]
    exact div_pos (mul_pos hl (by linarith)) hden
  have hmono := strictMonoOn_of_deriv_pos (convex_Ioc 0 1) hcont hpos
  have h := hmono ⟨hs0, hs1.le⟩ ⟨one_pos, le_rfl⟩ hs1
  have hf1 : f 1 = 0 := by
    show Real.log ((2:ℝ) ^ (1:ℝ) - 1) + 2 * Real.log 2 * (1 * (1 - 1)) = 0
    norm_num
  rw [hf1] at h
  exact h

/-- **`eq:loss-rate-bound`: the moment-loss rate is below `s/(1-s)`**: `2s log 2 · c(1-c)/(1/2 - c) < s/(1-s)`.
With `r = 2c`, the left side is `s log 2 · r(2-r)/(1-r) < 2 s log 2 · r/(1-r)`, and
`log_two_rpow_sub_one_lt` gives `r < e^{-2 log 2 (1-s)}`, whence
`r/(1-r) < 1/(2 log 2 (1-s))`. -/
theorem momentLoss_lt {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    2 * s * Real.log 2 * pairRatio s * (1 - pairRatio s) / (1/2 - pairRatio s)
      < s / (1 - s) := by
  set c := pairRatio s with hc
  have hc0 := pairRatio_pos hs0
  have hch := pairRatio_lt_half hs0 hs1
  set r := 2 * c with hr
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by linarith
  have hrs := two_mul_pairRatio_rpow hs0
  rw [← hc, ← hr] at hrs
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set x := 2 * Real.log 2 * (1 - s) with hx
  have hx0 : 0 < x := by positivity
  -- `r < e^{-x}`
  have hlogr : Real.log r < -x := by
    have h := log_two_rpow_sub_one_lt hs0 hs1
    rw [← hrs, Real.log_rpow hr0] at h
    have : s * Real.log r < s * -x := by rw [hx]; nlinarith
    exact lt_of_mul_lt_mul_left this hs0.le
  have hrexp : r < Real.exp (-x) := by
    rwa [← Real.log_lt_log_iff hr0 (Real.exp_pos _), Real.log_exp]
  -- `r/(1-r) < 1/x`
  have hinv : x < (1 - r) / r := by
    have h1 : Real.exp x < 1 / r := by
      rw [lt_one_div (Real.exp_pos _) hr0, one_div, ← Real.exp_neg]; exact hrexp
    have h2 := Real.add_one_le_exp x
    rw [sub_div, div_self hr0.ne']
    linarith
  have hfrac : r / (1 - r) < 1 / x := by
    rw [div_lt_div_iff₀ (by linarith) hx0]
    rw [lt_div_iff₀ hr0] at hinv
    linarith
  have hlhs : 2 * s * Real.log 2 * c * (1 - c) / (1/2 - c)
      = s * Real.log 2 * (r * (2 - r) / (1 - r)) := by
    rw [hr]; field_simp
  rw [hlhs]
  calc s * Real.log 2 * (r * (2 - r) / (1 - r)) < s * Real.log 2 * (2 * (r / (1 - r))) := by
        refine mul_lt_mul_of_pos_left ?_ (by positivity)
        rw [mul_div_assoc', div_lt_div_iff_of_pos_right (by linarith)]
        nlinarith
    _ < s * Real.log 2 * (2 * (1 / x)) := by
        refine mul_lt_mul_of_pos_left ?_ (by positivity)
        linarith
    _ = s / (1 - s) := by rw [hx]; field_simp

/-- For every `0 < c < 1/2` the dimension `s(c)`, with `2^{-s(c)} + c^{s(c)} = 1`, exists
and is unique: `s ↦ 2^{-s} + c^s` is continuous and strictly decreasing, with value `2`
at `0` and `1/2 + c < 1` at `1`. -/
theorem exists_unique_twoContractionDim {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    ∃! s : ℝ, (2:ℝ) ^ (-s) + c ^ s = 1 := by
  set f : ℝ → ℝ := fun s => (2:ℝ) ^ (-s) + c ^ s with hf
  have hanti : StrictAnti f := by
    intro s s' hss
    have h1 : (2:ℝ) ^ (-s') < (2:ℝ) ^ (-s) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have h2 : c ^ s' < c ^ s := Real.rpow_lt_rpow_of_exponent_gt hc0 (by linarith) hss
    simp only [hf]
    linarith
  have hcont : Continuous f := by
    simp only [hf]
    exact (continuous_const.rpow continuous_neg fun _ => Or.inl (by norm_num)).add
      (continuous_const.rpow continuous_id fun _ => Or.inl hc0.ne')
  have hf0 : f 0 = 2 := by simp [hf]; norm_num
  have hf1 : f 1 = 1/2 + c := by simp [hf, Real.rpow_neg_one]
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num)
    hcont.continuousOn (show (1:ℝ) ∈ Icc (f 1) (f 0) by rw [hf0, hf1]; constructor <;> linarith)
  exact ⟨s, hs, fun s' hs' => hanti.injective (hs'.trans hs.symm)⟩

end BrownianImages
