/-
The prefactor `F(s) = 2p²qΓ(1-s)/E(s)` of `eq:two-contraction-mean-factorisation` in the
proof of `thm:two-contraction-distinction`, with `p = 2^{-s}`, `q = 1 - p` and the binary
entropy `E(s) = -p log p - q log q = s m`.

The proof runs on `log F`.  Its derivative is
`-2 log 2 - ψ(1-s) + s (log 2)² p/(qE)`, as in the tex, and it exceeds the moment-loss
rate `2s log 2 · c(1-c)/(1/2 - c)` of `eq:loss-rate-bound`: the digamma bound
gives `-ψ(1-s) ≥ γ + s/(1-s) + s(π²/6 - 1)`, the entropy bound `E ≤ log 2` and
`e^x - 1 ≤ x + x²` give `s (log 2)² p/(qE) ≥ 1 - s log 2`, and `momentLoss_lt` bounds the
rate by `s/(1-s)`; what is left is `1 + γ - 2 log 2 + s(π²/6 - 1 - log 2) > 0`.

* `prefE`, `logPrefactor`: `E(s)` and `log F(s)`.
* `hasDerivAt_logPrefactor`: the derivative of `log F`.
* `logPrefactorDeriv_sub_momentLoss_pos`: the derivative beats the moment-loss rate.
-/
import BrownianImages.TwoContraction.Parameter
import BrownianImages.TwoContraction.Digamma
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace BrownianImages

open Real Set Filter
open scoped Topology

noncomputable section

/-- The entropy `E(s) = s log 2 · p - q log q = -p log p - q log q`, with `p = 2^{-s}` and
`q = 1 - p`. -/
def prefE (s : ℝ) : ℝ :=
  s * Real.log 2 * (2:ℝ) ^ (-s) - (1 - (2:ℝ) ^ (-s)) * Real.log (1 - (2:ℝ) ^ (-s))

/-- `log F(s) = log 2 - 2s log 2 + log q + log Γ(1-s) - log E(s)`. -/
def logPrefactor (s : ℝ) : ℝ :=
  Real.log 2 - 2 * s * Real.log 2 + Real.log (1 - (2:ℝ) ^ (-s)) + Real.log (Real.Gamma (1 - s))
    - Real.log (prefE s)

/-- `E(s)` is the binary entropy of `p = 2^{-s}`. -/
theorem prefE_eq_binEntropy (s : ℝ) : prefE s = binEntropy ((2:ℝ) ^ (-s)) := by
  unfold prefE binEntropy
  rw [Real.log_inv, Real.log_inv, Real.log_rpow (by norm_num)]
  ring

theorem two_rpow_neg_mem {s : ℝ} (hs0 : 0 < s) : 0 < (2:ℝ) ^ (-s) ∧ (2:ℝ) ^ (-s) < 1 :=
  ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

theorem prefE_pos {s : ℝ} (hs0 : 0 < s) : 0 < prefE s := by
  rw [prefE_eq_binEntropy]
  exact binEntropy_pos (two_rpow_neg_mem hs0).1 (two_rpow_neg_mem hs0).2

theorem prefE_le_log_two (s : ℝ) : prefE s ≤ Real.log 2 := by
  rw [prefE_eq_binEntropy]; exact binEntropy_le_log_two

/-- The derivative of `p = 2^{-s}` is `-log 2 · p`. -/
theorem hasDerivAt_two_rpow_neg (s : ℝ) :
    HasDerivAt (fun t : ℝ => (2:ℝ) ^ (-t)) (-(Real.log 2 * (2:ℝ) ^ (-s))) s := by
  have h := ((Real.hasStrictDerivAt_const_rpow (show (0:ℝ) < 2 by norm_num) (-s)).hasDerivAt).comp
    s (hasDerivAt_neg s)
  exact h.congr_deriv (by ring)

/-- The derivative of `E(s)` is `-s (log 2)² p - log 2 · p log q`. -/
theorem hasDerivAt_prefE {s : ℝ} (hs0 : 0 < s) :
    HasDerivAt prefE (-(s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s))
      - Real.log 2 * (2:ℝ) ^ (-s) * Real.log (1 - (2:ℝ) ^ (-s))) s := by
  have hp := hasDerivAt_two_rpow_neg s
  have hq : HasDerivAt (fun t : ℝ => 1 - (2:ℝ) ^ (-t)) (Real.log 2 * (2:ℝ) ^ (-s)) s := by
    convert (hasDerivAt_const s (1:ℝ)).sub hp using 1; ring
  have hq0 : 0 < 1 - (2:ℝ) ^ (-s) := by linarith [(two_rpow_neg_mem hs0).2]
  have h1 : HasDerivAt (fun t : ℝ => t * Real.log 2 * (2:ℝ) ^ (-t))
      (1 * Real.log 2 * (2:ℝ) ^ (-s) + s * Real.log 2 * -(Real.log 2 * (2:ℝ) ^ (-s))) s :=
    ((hasDerivAt_id' s).mul_const (Real.log 2)).mul hp
  have h2 := hq.mul (hq.log hq0.ne')
  have h := h1.sub h2
  unfold prefE
  convert h using 1
  field_simp
  ring

/-- **The derivative of `log F`**: `-2 log 2 + log 2 · p/q - ψ(1-s) - E'(s)/E(s)`. -/
theorem hasDerivAt_logPrefactor {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt logPrefactor (-2 * Real.log 2
      + Real.log 2 * (2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s)) - logGammaDeriv (1 - s)
      - (-(s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s))
          - Real.log 2 * (2:ℝ) ^ (-s) * Real.log (1 - (2:ℝ) ^ (-s))) / prefE s) s := by
  have hp := hasDerivAt_two_rpow_neg s
  have hq : HasDerivAt (fun t : ℝ => 1 - (2:ℝ) ^ (-t)) (Real.log 2 * (2:ℝ) ^ (-s)) s := by
    convert (hasDerivAt_const s (1:ℝ)).sub hp using 1; ring
  have hq0 : 0 < 1 - (2:ℝ) ^ (-s) := by linarith [(two_rpow_neg_mem hs0).2]
  have hG : HasDerivAt (fun t : ℝ => Real.log (Real.Gamma (1 - t)))
      (logGammaDeriv (1 - s) * -1) s := by
    have := (differentiableAt_logGamma (show 0 < 1 - s by linarith)).hasDerivAt.comp s
      ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id' s))
    exact this.congr_deriv (by unfold logGammaDeriv; ring)
  have hlin : HasDerivAt (fun t : ℝ => Real.log 2 - 2 * t * Real.log 2) (-2 * Real.log 2) s := by
    convert (hasDerivAt_const s (Real.log 2)).sub
      (((hasDerivAt_id' s).const_mul 2).mul_const (Real.log 2)) using 1
    ring
  have h := ((hlin.add (hq.log hq0.ne')).add hG).sub
    ((hasDerivAt_prefE hs0).log (prefE_pos hs0).ne')
  unfold logPrefactor
  convert h using 1
  ring

/-- The derivative of `log F` in the form of the tex:
`-2 log 2 - ψ(1-s) + s (log 2)² p/(qE)`. -/
theorem logPrefactorDeriv_eq {s : ℝ} (hs0 : 0 < s) :
    -2 * Real.log 2 + Real.log 2 * (2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s)) - logGammaDeriv (1 - s)
      - (-(s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s))
          - Real.log 2 * (2:ℝ) ^ (-s) * Real.log (1 - (2:ℝ) ^ (-s))) / prefE s
    = -2 * Real.log 2 - logGammaDeriv (1 - s)
      + s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s) / ((1 - (2:ℝ) ^ (-s)) * prefE s) := by
  have hq0 : 0 < 1 - (2:ℝ) ^ (-s) := by linarith [(two_rpow_neg_mem hs0).2]
  have hE := prefE_pos hs0
  have hEdef : prefE s = s * Real.log 2 * (2:ℝ) ^ (-s)
      - (1 - (2:ℝ) ^ (-s)) * Real.log (1 - (2:ℝ) ^ (-s)) := rfl
  field_simp
  rw [hEdef]
  ring

/-- `s (log 2)² p/(qE) ≥ 1 - s log 2`: the entropy is at most `log 2`, `p/q = 1/(2^s - 1)`
and `2^s - 1 = e^{s log 2} - 1 ≤ s log 2 + (s log 2)²`. -/
theorem entropy_term_ge {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 - s * Real.log 2
      ≤ s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s) / ((1 - (2:ℝ) ^ (-s)) * prefE s) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  obtain ⟨hp0, hp1⟩ := two_rpow_neg_mem hs0
  have hq0 : 0 < 1 - (2:ℝ) ^ (-s) := by linarith
  have hE := prefE_pos hs0
  have hEl := prefE_le_log_two s
  set x := s * Real.log 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx]; nlinarith
  -- `2^s = e^x` and `p/q = 1/(e^x - 1)`
  have h2s : (2:ℝ) ^ s = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num), hx, mul_comm]
  have hpq : (2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s)) = 1 / (Real.exp x - 1) := by
    rw [Real.rpow_neg (by norm_num), h2s]
    have : 1 < Real.exp x := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hx0
    field_simp
  have hexp : Real.exp x - 1 ≤ x + x ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_pos hx0]; exact hx1)
    linarith [le_abs_self (Real.exp x - 1 - x)]
  have hexp0 : 0 < Real.exp x - 1 := by
    have : 1 < Real.exp x := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hx0
    linarith
  -- the lower bound through `E ≤ log 2`
  have hstep1 : s * Real.log 2 * ((2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s)))
      ≤ s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s) / ((1 - (2:ℝ) ^ (-s)) * prefE s) := by
    rw [show s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s) / ((1 - (2:ℝ) ^ (-s)) * prefE s)
        = s * Real.log 2 * ((2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s))) * (Real.log 2 / prefE s) by
          field_simp]
    have : 1 ≤ Real.log 2 / prefE s := by rw [le_div_iff₀ hE]; linarith
    have hpos : 0 ≤ s * Real.log 2 * ((2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s))) := by positivity
    nlinarith
  refine le_trans ?_ hstep1
  rw [hpq, ← hx, mul_one_div, le_div_iff₀ hexp0]
  nlinarith

/-- **`eq:rate-comparison`: the derivative of `log F` beats the moment-loss rate**:
`-2 log 2 - ψ(1-s) + s (log 2)² p/(qE) > 2s log 2 · c(1-c)/(1/2 - c)` on `(0, 1)`, the
final inequality of the proof of `thm:two-contraction-distinction`. -/
theorem logPrefactorDeriv_sub_momentLoss_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    2 * s * Real.log 2 * pairRatio s * (1 - pairRatio s) / (1/2 - pairRatio s)
      < -2 * Real.log 2 - logGammaDeriv (1 - s)
        + s * Real.log 2 ^ 2 * (2:ℝ) ^ (-s) / ((1 - (2:ℝ) ^ (-s)) * prefE s) := by
  have hloss := momentLoss_lt hs0 hs1
  have hdig := neg_logGammaDeriv_one_sub_ge hs0 hs1
  have hent := entropy_term_ge hs0 hs1
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hl := Real.log_two_lt_d9
  have hπ := Real.pi_gt_d2
  have hπ2 : (3.14 : ℝ) ^ 2 < π ^ 2 := by nlinarith
  have hb : -(0.05 : ℝ) < π ^ 2 / 6 - 1 - Real.log 2 := by nlinarith
  have hsb : -(0.05 : ℝ) ≤ s * (π ^ 2 / 6 - 1 - Real.log 2) := by
    rcases le_or_gt 0 (π ^ 2 / 6 - 1 - Real.log 2) with h | h
    · nlinarith
    · nlinarith
  nlinarith

end

end BrownianImages
