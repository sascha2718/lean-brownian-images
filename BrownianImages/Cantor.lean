/-
`thm:cantor-values` of `sec:renewal`: the exact pair-distance values of the
middle-thirds Cantor measure and the non-constancy they force on the periodic
profile `G_A`.

The two probabilistic inputs, `Φ_A(1/3) = 1/2` and `Φ_A(1/6) = 3/10`, enter as
hypotheses; everything downstream of them is proved here.

* `sCantor`: the exponent `s = log 2 / log 3`, with `rpow_three_sCantor : 3^s = 2`.
* `halfMass_eq`: the fixed-point computation `q = (1-q)/4`, hence `q = 1/5` and
  `Φ_A(1/2) = 1 - 2q = 3/5`.
* `G_log_three`, `G_log_six`: the two values `G_A(log 3) = 1` and
  `G_A(log 6) = (3/5)·2^s` of the proof of `thm:cantor-values`.
* `G_log_six_lt_G_log_three`: the numeric separation `(3/5)·2^s < 1`, which is the
  non-constancy of the periodic profile.
-/
import BrownianImages.Periodic

namespace BrownianImages

open Real MeasureTheory

/-! ### The Cantor exponent -/

/-- The similarity dimension `s = log 2 / log 3` of the middle-thirds Cantor set. -/
noncomputable def sCantor : ℝ := Real.log 2 / Real.log 3

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem sCantor_pos : 0 < sCantor := div_pos log_two_pos log_three_pos

/-- `3^s = 2`, the defining property of the Cantor exponent. -/
theorem rpow_three_sCantor : (3 : ℝ) ^ sCantor = 2 := by
  rw [sCantor, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), mul_div_assoc', mul_comm,
    mul_div_assoc, div_self log_three_pos.ne', mul_one, Real.exp_log (by norm_num)]

/-- `s < 2/3`, proved from `8 < 9` as in the paper. -/
theorem sCantor_lt_two_thirds : sCantor < 2 / 3 := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlt : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [h8, h9] at hlt
  rw [sCantor, div_lt_iff₀ log_three_pos]
  linarith

theorem sCantor_lt_one : sCantor < 1 := by
  have := sCantor_lt_two_thirds; linarith

/-- `2^{2/3} < 5/3`, proved from `108 < 125` as in the paper. -/
theorem two_rpow_two_thirds_lt : (2 : ℝ) ^ ((2:ℝ)/3) < 5 / 3 := by
  have hcube : ((2:ℝ) ^ ((2:ℝ)/3)) ^ (3:ℕ) = 4 := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 3 (by norm_num) ?_
  rw [hcube]; norm_num

/-- The numeric separation `(3/5)·2^s < 1` of `thm:cantor-values`. -/
theorem three_fifths_two_rpow_lt_one : (3/5 : ℝ) * (2:ℝ) ^ sCantor < 1 := by
  have h1 : (2:ℝ) ^ sCantor < (2:ℝ) ^ ((2:ℝ)/3) :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr sCantor_lt_two_thirds
  have h2 := two_rpow_two_thirds_lt
  linarith

/-! ### The mass of the far half -/

/-- The fixed-point computation of the proof of `thm:cantor-values`: the mass
`q = P(X - Y ≥ 1/2)` satisfies `q = (1-q)/4`, hence `q = 1/5` and `Φ_A(1/2) = 1 - 2q`
equals `3/5`. -/
theorem halfMass_eq {q : ℝ} (hq : q = (1 - q) / 4) : q = 1/5 ∧ 1 - 2 * q = 3/5 := by
  constructor <;> linarith

/-! ### The two profile values -/

variable {μ : Measure ℝ}

/-- `G_A(log 3) = 3^s Φ_A(1/3) = 1`. -/
theorem G_log_three (h : Phi μ (1/3) = 1/2) : G sCantor μ (Real.log 3) = 1 := by
  have hexp : Real.exp (-Real.log 3) = 1/3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [G, hexp, h, mul_comm sCantor, ← Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3),
    rpow_three_sCantor]
  norm_num

/-- `G_A(log 6) = 6^s Φ_A(1/6) = (3/5)·2^s`. -/
theorem G_log_six (h : Phi μ (1/6) = 3/10) :
    G sCantor μ (Real.log 6) = (3/5) * (2:ℝ) ^ sCantor := by
  have hexp : Real.exp (-Real.log 6) = 1/6 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hsix : (6:ℝ) ^ sCantor = 2 * (2:ℝ) ^ sCantor := by
    rw [show (6:ℝ) = 3 * 2 by norm_num,
      Real.mul_rpow (by norm_num) (by norm_num), rpow_three_sCantor]
  rw [G, hexp, h, mul_comm sCantor, ← Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 6), hsix]
  ring

/-- The periodic profile is non-constant: its values at `log 6` and at `log 3` differ. -/
theorem G_log_six_lt_G_log_three (h3 : Phi μ (1/3) = 1/2) (h6 : Phi μ (1/6) = 3/10) :
    G sCantor μ (Real.log 6) < G sCantor μ (Real.log 3) := by
  rw [G_log_three h3, G_log_six h6]
  exact three_fifths_two_rpow_lt_one


/-! ### Non-constancy on every period -/

/-- The shift identity of `eq:g-recursion` iterates upward: `G(w + np) = G(w)` for
`w > 0`. -/
theorem G_add_nsmul_period {p : ℝ} (hp : 0 < p)
    (hper : ∀ w, p < w → G sCantor μ w = G sCantor μ (w - p))
    {w : ℝ} (hw : 0 < w) : ∀ n : ℕ, G sCantor μ (w + n * p) = G sCantor μ w := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hcast : w + ((n + 1 : ℕ) : ℝ) * p = (w + (n : ℝ) * p) + p := by push_cast; ring
      have hgt : p < (w + (n : ℝ) * p) + p := by
        have hn : (0:ℝ) ≤ (n : ℝ) * p := by positivity
        linarith
      rw [hcast, hper _ hgt, add_sub_cancel_right]
      exact ih

/-- `thm:cantor-values`, the stated consequence: the periodic profile `G_A` is
non-constant on every period.  The two exact values enter as hypotheses, and the shift
identity `eq:g-recursion` for the middle-thirds system enters as `hper`. -/
theorem G_nonconstant_on_period (h3 : Phi μ (1/3) = 1/2) (h6 : Phi μ (1/6) = 3/10)
    (hper : ∀ w, Real.log 3 < w → G sCantor μ w = G sCantor μ (w - Real.log 3))
    {w : ℝ} (hw : Real.log 3 ≤ w) :
    ∃ w₁ ∈ Set.Icc w (w + Real.log 3), ∃ w₂ ∈ Set.Icc w (w + Real.log 3),
      G sCantor μ w₁ ≠ G sCantor μ w₂ := by
  have hp : (0:ℝ) < Real.log 3 := log_three_pos
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog6 : Real.log 6 = Real.log 3 + Real.log 2 := by
    rw [show (6:ℝ) = 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h6pos : (0:ℝ) < Real.log 6 := by rw [hlog6]; linarith [log_two_pos]
  obtain ⟨n, hn⟩ := exists_period_representative (a := Real.log 3) (w := w) hp (by linarith)
  obtain ⟨m, hm⟩ := exists_period_representative (a := Real.log 6) (w := w) hp
    (by rw [hlog6]; linarith)
  refine ⟨Real.log 6 + m * Real.log 3, hm, Real.log 3 + n * Real.log 3, hn, ?_⟩
  rw [G_add_nsmul_period hp hper h6pos m, G_add_nsmul_period hp hper hp n]
  exact (G_log_six_lt_G_log_three h3 h6).ne

end BrownianImages
