/-
`sec:variance`: the deterministic geometry behind the four-point estimate.

After sorting the four time endpoints as `x₁ < x₂ < x₃ < x₄` and writing
`a = x₂ - x₁`, `b = x₃ - x₂`, `c = x₄ - x₃`, `h = a + c`, only two of the three
pairings overlap.  Their covariance determinants are computed here, together with the
lower bounds on a dyadic block `E_{β,η}` that `thm:endpoint-block-mass` feeds into
`eq:joint-return-bound`.

* `crossing_det`, `crossing_det_ge`: `eq:crossing-determinant`.
* `nested_det`: `eq:nested-determinant`.
* `det_ge_block`, `length_ge_block`: the two lower bounds `Δ ≥ βη/4` and
  `(b+h)/2 ≥ (β+η)/4` valid on `E_{β,η}`.
* `varScale_div_tendsto_zero`: the last assertion of `thm:variance`, that each of the
  three variance scales `eq:variance-scale` is `o(r^{4s})`.
-/
import BrownianImages.Defs

namespace BrownianImages

/-! ### The two overlapping pairings -/

/-- `eq:crossing-determinant`: for the crossing pairing `[x₁,x₃]`, `[x₂,x₄]` the
covariance determinant is `ab + ac + bc`. -/
theorem crossing_det (a b c : ℝ) : (a + b) * (b + c) - b ^ 2 = a * b + a * c + b * c := by
  ring

/-- `eq:crossing-determinant`: the crossing determinant is at least `bh`. -/
theorem crossing_det_ge {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    b * (a + c) ≤ (a + b) * (b + c) - b ^ 2 := by
  rw [crossing_det]; nlinarith

/-- `eq:nested-determinant`: for the nested pairing `[x₁,x₄]`, `[x₂,x₃]` the covariance
determinant is exactly `bh`. -/
theorem nested_det (a b c : ℝ) : b * (a + b + c) - b ^ 2 = b * (a + c) := by ring

/-! ### The dyadic block bounds -/

/-- On the block `E_{β,η}`, where `β/2 < b` and `η/2 < h`, the determinant `bh` is at
least `βη/4`. -/
theorem det_ge_block {β η b h : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hb : β / 2 < b) (hh : η / 2 < h) : β * η / 4 ≤ b * h := by
  nlinarith

/-- On the block `E_{β,η}` the half-sum `(b+h)/2`, a lower bound for the length of the
longer of the two intervals, is at least `(β+η)/4`. -/
theorem length_ge_block {β η b h : ℝ} (hb : β / 2 < b) (hh : η / 2 < h) :
    (β + η) / 4 ≤ (b + h) / 2 := by
  linarith

/-! ### The variance scale is `o(r^{4s})` -/

/-- `x ↦ x^a` tends to `0` at `0` from the right, for `a > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun x : ℝ => x ^ a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Filter.Tendsto (fun x : ℝ => x ^ a) (nhds 0) (nhds ((0:ℝ) ^ a)) :=
    (Real.continuous_rpow_const ha.le).tendsto 0
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `thm:variance`, the final assertion: each of the three variance scales of
`eq:variance-scale` is `o(r^{4s})`.  The three cases are `r^{2s}`, `r(1 - log r)` and
`r^{2-2s}`, and `0 < s < 1` makes each exponent positive. -/
theorem varScale_div_tendsto_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Filter.Tendsto (fun r : ℝ => varScale s r / r ^ (4 * s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rcases lt_trichotomy s 2⁻¹ with h | h | h
  · have hcongr : (fun r : ℝ => varScale s r / r ^ (4 * s))
        =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] fun r : ℝ => r ^ (2 * s) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [varScale, if_pos h, ← Real.rpow_sub hr, show 6 * s - 4 * s = 2 * s by ring]
    exact Filter.Tendsto.congr' hcongr.symm (tendsto_rpow_nhdsGT_zero (by linarith))
  · have h4 : 4 * s = 2 := by rw [h]; norm_num
    have hcongr : (fun r : ℝ => varScale s r / r ^ (4 * s))
        =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] fun r : ℝ => r - Real.log r * r := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0:ℝ) < r := hr
      rw [varScale, if_neg (by rw [h]; norm_num), if_pos h, h4,
        show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show (3:ℝ) = ((3:ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.log_inv]
      field_simp
      ring
    refine Filter.Tendsto.congr' hcongr.symm ?_
    have h1 : Filter.Tendsto (fun r : ℝ => r) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun r : ℝ => Real.log r * r)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    simpa using h1.sub h2
  · have hcongr : (fun r : ℝ => varScale s r / r ^ (4 * s))
        =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] fun r : ℝ => r ^ (2 - 2 * s) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [varScale, if_neg (by linarith), if_neg (by linarith), ← Real.rpow_sub hr,
        show 2 * s + 2 - 4 * s = 2 - 2 * s by ring]
    exact Filter.Tendsto.congr' hcongr.symm (tendsto_rpow_nhdsGT_zero (by linarith))

end BrownianImages
