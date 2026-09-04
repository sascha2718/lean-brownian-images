/-
`sec:reconstruction`: the final scalar ratio argument behind
`eq:cylinder-neighbourhood-ratio`.

The stochastic estimates compare a cylinder profile and the full profile with two
deterministic mean profiles.  If both random errors vanish, the two means become
asymptotically equal, and the denominator mean stays uniformly positive, then the
quotient tends to one.  This file isolates that argument from both renewal theory and
Brownian scaling.
-/
import BrownianImages.MinkowskiProfile

namespace BrownianImages

open Filter
open scoped Topology

namespace MinkowskiRatio

/-- Two profiles with vanishing centred errors have asymptotic ratio one when their
means become equal and the denominator mean stays bounded away from zero. -/
theorem tendsto_div_one_of_centered_errors
    (x y mx my : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hx : Tendsto (fun n => x n - mx n) atTop (nhds 0))
    (hy : Tendsto (fun n => y n - my n) atTop (nhds 0))
    (hm : Tendsto (fun n => my n - mx n) atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, c ≤ mx n) :
    Tendsto (fun n => y n / x n) atTop (nhds 1) := by
  have hdiff : Tendsto (fun n => y n - x n) atTop (nhds 0) := by
    have h := (hy.add hm).sub hx
    convert h using 1
    · funext n
      ring_nf
    · simp
  have hxclose : ∀ᶠ n in atTop, |x n - mx n| < c / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx (c / 2) (by positivity)
    filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with n hn
    simpa only [Real.dist_eq, sub_zero] using hn
  have hxpos : ∀ᶠ n in atTop, c / 2 < x n := by
    filter_upwards [hxclose, hlower] with n hn hmn
    have hleft : -(c / 2) < x n - mx n := (abs_lt.mp hn).1
    linarith
  refine Metric.tendsto_atTop.2 fun epsilon hepsilon => ?_
  have hscale : 0 < epsilon * (c / 2) := mul_pos hepsilon (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdiff _ hscale
  obtain ⟨Npos, hNpos⟩ := (eventually_atTop.1 hxpos)
  refine ⟨max N Npos, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnPos : Npos ≤ n := (le_max_right _ _).trans hn
  have hnum : |y n - x n| < epsilon * (c / 2) := by
    simpa only [Real.dist_eq, sub_zero] using hN n hnN
  have hxposn : c / 2 < x n := hNpos n hnPos
  have hxabs : c / 2 ≤ |x n| := by
    rw [abs_of_pos (lt_of_lt_of_le (by positivity : 0 < c / 2) hxposn.le)]
    exact hxposn.le
  have hxne : x n ≠ 0 := ne_of_gt (lt_trans (by positivity : 0 < c / 2) hxposn)
  change dist (y n / x n) 1 < epsilon
  rw [Real.dist_eq, div_sub_one hxne, abs_div]
  calc
    |y n - x n| / |x n| ≤ |y n - x n| / (c / 2) := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hxabs
    _ < epsilon := by
      rw [div_lt_iff₀ (by positivity : 0 < c / 2)]
      simpa [mul_comm] using hnum

/-- Multiplying the numerator by a fixed cylinder weight gives convergence to that
weight. -/
theorem tendsto_weight_mul_div_of_centered_errors
    (x y mx my : ℕ → ℝ) (p : ℝ) {c : ℝ} (hc : 0 < c)
    (hx : Tendsto (fun n => x n - mx n) atTop (nhds 0))
    (hy : Tendsto (fun n => y n - my n) atTop (nhds 0))
    (hm : Tendsto (fun n => my n - mx n) atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, c ≤ mx n) :
    Tendsto (fun n => p * y n / x n) atTop (nhds p) := by
  have hratio := tendsto_div_one_of_centered_errors x y mx my hc hx hy hm hlower
  have hmul : Tendsto (fun n => p * (y n / x n)) atTop (nhds (p * 1)) :=
    tendsto_const_nhds.mul hratio
  simpa only [mul_div_assoc, mul_one] using hmul

/-- A numerator centered at a weighted mean has asymptotic ratio equal to that
weight.  This is the form used for a Brownian generation cylinder: its mean is
`p * my`, while the full image has mean `mx`. -/
theorem tendsto_div_of_weighted_centered_errors
    (x y mx my : ℕ → ℝ) (p : ℝ) {c : ℝ} (hc : 0 < c)
    (hp : p ≠ 0)
    (hx : Tendsto (fun n => x n - mx n) atTop (nhds 0))
    (hy : Tendsto (fun n => y n - p * my n) atTop (nhds 0))
    (hm : Tendsto (fun n => my n - mx n) atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, c ≤ mx n) :
    Tendsto (fun n => y n / x n) atTop (nhds p) := by
  let y' : ℕ → ℝ := fun n => y n / p
  have hy' : Tendsto (fun n => y' n - my n) atTop (nhds 0) := by
    have hscaled := hy.div_const p
    convert hscaled using 1
    · funext n
      dsimp only [y']
      field_simp [hp]
    · simp
  have hratio := tendsto_weight_mul_div_of_centered_errors
    x y' mx my p hc hx hy' hm hlower
  convert hratio using 1
  funext n
  dsimp only [y']
  field_simp [hp]

end MinkowskiRatio

end BrownianImages
