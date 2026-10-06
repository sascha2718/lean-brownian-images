/-
The digamma bound in the proof of `thm:two-contraction-distinction`:
`-ψ(1-s) ≥ γ + s/(1-s) + s(π²/6 - 1)` for `0 < s < 1`.

Mathlib has the digamma function but not its series, and the bound is derived, as in the
tex, from the convexity of `log Γ` and the functional equation: `ψ(x) = ψ(x+N) - ∑_{k<N} 1/(x+k)` and
`ψ(y) ≤ log y`, after which `1/(k+1-s) ≥ 1/(k+1) + s/(k+1)²` and the limits
`H_N - log(N+1) → γ` and `∑ 1/n² = π²/6` finish.

* `logGammaDeriv`: `ψ = (log Γ)'` on the real line.
* `logGammaDeriv_add_one`, `logGammaDeriv_le_log`: the functional equation and the
  convexity bound.
* `neg_logGammaDeriv_one_sub_ge`: the digamma bound.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues

namespace BrownianImages

open Real Set Filter
open scoped Topology

/-- The digamma function `ψ = (log Γ)'` on the real line. -/
noncomputable def logGammaDeriv (x : ℝ) : ℝ := deriv (fun y => Real.log (Real.Gamma y)) x

/-- `log Γ` is differentiable on `(0, ∞)`. -/
theorem differentiableAt_logGamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun y => Real.log (Real.Gamma y)) x :=
  (Real.differentiableAt_Gamma fun m => by
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith).log (Real.Gamma_pos_of_pos hx).ne'

/-- The functional equation `ψ(x + 1) = ψ(x) + 1/x`, from `Γ(x+1) = xΓ(x)`. -/
theorem logGammaDeriv_add_one {x : ℝ} (hx : 0 < x) :
    logGammaDeriv (x + 1) = logGammaDeriv x + 1 / x := by
  have heq : (fun y => Real.log (Real.Gamma (y + 1))) =ᶠ[𝓝 x]
      fun y => Real.log y + Real.log (Real.Gamma y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Real.Gamma_add_one (ne_of_gt hy), Real.log_mul (ne_of_gt hy)
      (Real.Gamma_pos_of_pos hy).ne']
  have h1 : deriv (fun y => Real.log (Real.Gamma (y + 1))) x = logGammaDeriv (x + 1) :=
    deriv_comp_add_const (fun y => Real.log (Real.Gamma y)) 1 x
  have h2 : HasDerivAt (fun y => Real.log y + Real.log (Real.Gamma y))
      (x⁻¹ + logGammaDeriv x) x :=
    (Real.hasDerivAt_log hx.ne').add (differentiableAt_logGamma hx).hasDerivAt
  rw [← h1, heq.deriv_eq, h2.deriv, one_div, add_comm]

/-- The convexity bound `ψ(y) ≤ log y`: the derivative of the convex `log Γ` lies below
its slope `log Γ(y+1) - log Γ(y) = log y`. -/
theorem logGammaDeriv_le_log {y : ℝ} (hy : 0 < y) : logGammaDeriv y ≤ Real.log y := by
  have h := Real.convexOn_log_Gamma.deriv_le_slope (mem_Ioi.2 hy)
    (mem_Ioi.2 (show (0:ℝ) < y + 1 by linarith)) (lt_add_one y) (differentiableAt_logGamma hy)
  have hslope : slope (Real.log ∘ Real.Gamma) y (y + 1) = Real.log y := by
    rw [slope_def_field, show y + 1 - y = 1 by ring, div_one, Function.comp_apply,
      Function.comp_apply, Real.Gamma_add_one (ne_of_gt hy),
      Real.log_mul (ne_of_gt hy) (Real.Gamma_pos_of_pos hy).ne']
    ring
  rw [hslope] at h
  exact h

/-- The iterated functional equation `ψ(x) = ψ(x+N) - ∑_{k<N} 1/(x+k)`. -/
theorem logGammaDeriv_eq_sub {x : ℝ} (hx : 0 < x) (N : ℕ) :
    logGammaDeriv x = logGammaDeriv (x + N) - ∑ k ∈ Finset.range N, 1 / (x + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc,
      logGammaDeriv_add_one (show 0 < x + N by positivity), ih]
    ring

/-- **The digamma bound** `-ψ(1-s) ≥ γ + s/(1-s) + s(π²/6 - 1)` for `0 < s < 1`, used in the
proof of `thm:two-contraction-distinction`. -/
theorem neg_logGammaDeriv_one_sub_ge {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    eulerMascheroniConstant + s / (1 - s) + s * (π ^ 2 / 6 - 1)
      ≤ -logGammaDeriv (1 - s) := by
  have hx : 0 < 1 - s := by linarith
  -- `1/(m - s) ≥ 1/m + s/m²` for `m ≥ 1`
  have hterm : ∀ m : ℝ, 1 ≤ m → 1 / m + s * (1 / m ^ 2) ≤ 1 / (m - s) := by
    intro m hm
    have hm0 : 0 < m := by linarith
    have hms : 0 < m - s := by linarith
    rw [show 1 / m + s * (1 / m ^ 2) = (m + s) / m ^ 2 by field_simp,
      div_le_div_iff₀ (by positivity) hms]
    nlinarith
  -- the bound at each truncation
  have hN : ∀ N : ℕ, s / (1 - s) - s + eulerMascheroniSeq (N + 1)
      + s * ∑ k ∈ Finset.range (N + 1), 1 / ((k:ℝ) + 1) ^ 2 ≤ -logGammaDeriv (1 - s) := by
    intro N
    have h1 := logGammaDeriv_eq_sub hx (N + 1)
    have h2 := logGammaDeriv_le_log (show 0 < 1 - s + ((N + 1 : ℕ) : ℝ) by positivity)
    have h3 : Real.log (1 - s + ((N + 1 : ℕ) : ℝ)) ≤ Real.log (((N + 1 : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hsum : ∑ k ∈ Finset.range N, (1 / ((k:ℝ) + 1 + 1) + s * (1 / ((k:ℝ) + 1 + 1) ^ 2))
        ≤ ∑ k ∈ Finset.range N, 1 / (1 - s + ((k + 1 : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have := hterm ((k:ℝ) + 1 + 1) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      push_cast
      rw [show 1 - s + ((k:ℝ) + 1) = (k:ℝ) + 1 + 1 - s by ring]
      exact this
    have hfirst : 1 / (1 - s + ((0 : ℕ) : ℝ)) = s / (1 - s) - s + (1 + s) := by
      push_cast; field_simp; ring
    have hH : (harmonic (N + 1) : ℝ) = ∑ k ∈ Finset.range (N + 1), 1 / ((k:ℝ) + 1) := by
      simp [harmonic, one_div]
    have hseq : eulerMascheroniSeq (N + 1)
        = (harmonic (N + 1) : ℝ) - Real.log (((N + 1 : ℕ) : ℝ) + 1) := rfl
    rw [hseq, hH]
    rw [Finset.sum_range_succ'] at h1
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    rw [hfirst] at h1
    push_cast at h1 hsum h2 h3 ⊢
    have hsplit : ∑ k ∈ Finset.range N, 1 / ((k:ℝ) + 1 + 1) + s * ∑ k ∈ Finset.range N,
        1 / ((k:ℝ) + 1 + 1) ^ 2 ≤ ∑ k ∈ Finset.range N, 1 / (1 - s + ((k:ℝ) + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact hsum
    rw [show (1:ℝ) / (0 + 1) = 1 by norm_num, show (1:ℝ) / (0 + 1) ^ 2 = 1 by norm_num]
    nlinarith [hsplit, h1, h2, h3]
  -- pass to the limit
  have hzeta : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, 1 / ((k:ℝ) + 1) ^ 2) atTop
      (𝓝 (π ^ 2 / 6)) := by
    have h := hasSum_zeta_two
    have h' : HasSum (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
      rw [← hasSum_nat_add_iff' 1] at h
      simpa using h
    exact h'.tendsto_sum_nat
  have hlim := ((tendsto_const_nhds (x := s / (1 - s) - s)).add
    (tendsto_eulerMascheroniSeq.comp (tendsto_add_atTop_nat 1))).add
    ((hzeta.comp (tendsto_add_atTop_nat 1)).const_mul s)
  have := le_of_tendsto' hlim hN
  linarith

end BrownianImages
