/-
`sec:concentration`: the empirical profile `Y_ν` of `sec:concentration` and the
monotonicity that fills the grid in the proof of `thm:uniform-concentration`.

`r ↦ C_r(ν)` is non-decreasing, so `Y_ν` cannot move faster than the exponential
prefactor allows.  That is `eq:monotone-fill`, and it is what turns convergence along a
grid into uniform convergence on tails.

* `corr_mono`: `C_r(ν)` is non-decreasing in `r`.
* `Yprofile_le_of_le`: `Y_ν(u) ≤ e^{2s(u-t)} Y_ν(t)` for `t ≤ u`.
* `monotone_fill`: `eq:monotone-fill`, the two-sided grid bound.
-/
import BrownianImages.Defs

namespace BrownianImages

open MeasureTheory
open scoped ENNReal

variable {s : ℝ} (ν : Measure Plane)

/-- The correlation functional is non-decreasing in the radius. -/
theorem corr_mono {r r' : ℝ} (h : r ≤ r') : corr ν r ≤ corr ν r' :=
  measure_mono fun _ hp => lt_of_lt_of_le hp h

/-- The empirical profile `Y_ν` of `sec:concentration` is non-negative. -/
theorem Yprofile_nonneg (s : ℝ) (v : ℝ) : 0 ≤ Yprofile s ν v := by
  unfold Yprofile
  positivity

variable [IsProbabilityMeasure ν]

/-- The correlation functional `eq:correlation-functional` of a probability measure is
finite. -/
theorem corr_ne_top (r : ℝ) : corr ν r ≠ ⊤ := measure_ne_top _ _

/-- The empirical profile grows at most like the exponential prefactor: this is the
monotonicity of `r ↦ C_r` in the coordinate of `Y_ν`. -/
theorem Yprofile_le_of_le {v w : ℝ} (hvw : v ≤ w) :
    Yprofile s ν w ≤ Real.exp (2 * s * (w - v)) * Yprofile s ν v := by
  have hmono : corr ν (Real.exp (-w)) ≤ corr ν (Real.exp (-v)) :=
    corr_mono ν (Real.exp_le_exp.mpr (by linarith))
  have htoReal : (corr ν (Real.exp (-w))).toReal ≤ (corr ν (Real.exp (-v))).toReal :=
    ENNReal.toReal_mono (corr_ne_top ν _) hmono
  have hsplit : Real.exp (2 * s * (w - v)) * (Real.exp (2 * s * v))
      = Real.exp (2 * s * w) := by
    rw [← Real.exp_add]; ring_nf
  calc Yprofile s ν w = Real.exp (2 * s * w) * (corr ν (Real.exp (-w))).toReal := rfl
    _ ≤ Real.exp (2 * s * w) * (corr ν (Real.exp (-v))).toReal := by
        exact mul_le_mul_of_nonneg_left htoReal (Real.exp_pos _).le
    _ = Real.exp (2 * s * (w - v)) * Yprofile s ν v := by
        rw [Yprofile, ← hsplit]; ring

/-- `eq:monotone-fill`: on a grid interval of length `1/m` the empirical profile is
squeezed between `e^{-2s/m}` and `e^{2s/m}` times its values at the endpoints. -/
theorem monotone_fill (hs : 0 ≤ s) {a b v : ℝ} (hav : a ≤ v) (hvb : v ≤ b) :
    Real.exp (-(2 * s * (b - a))) * Yprofile s ν b ≤ Yprofile s ν v ∧
      Yprofile s ν v ≤ Real.exp (2 * s * (b - a)) * Yprofile s ν a := by
  constructor
  · have h := Yprofile_le_of_le (s := s) ν hvb
    have hle : Real.exp (2 * s * (b - v)) ≤ Real.exp (2 * s * (b - a)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hY : 0 ≤ Yprofile s ν v := Yprofile_nonneg ν s v
    have hchain : Yprofile s ν b ≤ Real.exp (2 * s * (b - a)) * Yprofile s ν v :=
      h.trans (mul_le_mul_of_nonneg_right hle hY)
    have hpos : (0:ℝ) < Real.exp (2 * s * (b - a)) := Real.exp_pos _
    rw [Real.exp_neg, inv_mul_le_iff₀ hpos]
    linarith
  · have h := Yprofile_le_of_le (s := s) ν hav
    have hle : Real.exp (2 * s * (v - a)) ≤ Real.exp (2 * s * (b - a)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact h.trans (mul_le_mul_of_nonneg_right hle (Yprofile_nonneg ν s a))


/-! ### The oscillation functional is Borel -/

/-- The correlation functional is a measurable function of the measure. -/
theorem measurable_corr (r : ℝ) :
    Measurable (fun ν : ProbabilityMeasure Plane => corr ν.toMeasure r) := by
  have hdiag : Measurable
      (fun ν : ProbabilityMeasure Plane => (ν, ν)) := measurable_id.prodMk measurable_id
  exact (Measure.measurable_coe (measurableSet_corrSet r)).comp
    (ProbabilityMeasure.measurable_fun_prod.comp hdiag)

/-- The empirical profile is a measurable function of the measure. -/
theorem measurable_Yprofile (s v : ℝ) :
    Measurable (fun ν : ProbabilityMeasure Plane => Yprofile s ν.toMeasure v) :=
  (ENNReal.measurable_toReal.comp (measurable_corr _)).const_mul _

end BrownianImages
