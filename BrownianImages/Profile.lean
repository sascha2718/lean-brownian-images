/-
`sec:setup`: elementary bounds on the normalised pair-distance profile `G` of
`eq:g-definition`.

`Φ ≤ 1` because it is a probability, and `eq:phi-frostman` bounds it above `0`; together
they bound `G` on the whole line by the Frostman constant.  Measurability of `Φ` comes
from monotonicity alone, so `G` is measurable with no Frostman hypothesis.

* `phi_le_one`, `G_nonneg`, `G_le_exp`: the trivial bounds.
* `measurable_Phi`, `measurable_G`: measurability without regularity hypotheses.
* `abs_G_le`: `|G| ≤ A` on the whole line.
-/
import BrownianImages.Frostman

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- `Φ ≤ 1` for a probability measure. -/
theorem phi_le_one {μ : Measure ℝ} [IsProbabilityMeasure μ] (δ : ℝ) : Phi μ δ ≤ 1 := by
  rw [Phi]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

/-- `G ≥ 0`. -/
theorem G_nonneg {s : ℝ} {μ : Measure ℝ} (w : ℝ) : 0 ≤ G s μ w :=
  mul_nonneg (Real.exp_pos _).le (phi_nonneg _)

/-- Below a threshold `c`, `G(w) ≤ e^{sc}`: the trivial bound `Φ ≤ 1`. -/
theorem G_le_exp {s : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ} [IsProbabilityMeasure μ] {w c : ℝ}
    (hw : w ≤ c) : G s μ w ≤ Real.exp (s * c) := by
  calc G s μ w ≤ Real.exp (s * w) * 1 :=
        mul_le_mul_of_nonneg_left (phi_le_one _) (Real.exp_pos _).le
    _ = Real.exp (s * w) := mul_one _
    _ ≤ Real.exp (s * c) := Real.exp_le_exp.mpr (by nlinarith)

/-- `Φ` is measurable, being monotone. -/
theorem measurable_Phi {μ : Measure ℝ} [IsProbabilityMeasure μ] : Measurable (Phi μ) := by
  have h : Monotone (Phi μ) := fun _ _ hab => phi_mono hab
  exact h.measurable

/-- `G` is measurable, with no Frostman hypothesis. -/
theorem measurable_G {s : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] : Measurable (G s μ) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    (measurable_Phi.comp (Real.measurable_exp.comp measurable_neg))

/-- `eq:phi-frostman` gives the uniform bound `|G| ≤ A`: the trivial bound below `0`,
the Frostman bound above it. -/
theorem abs_G_le {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) (w : ℝ) : |G s μ w| ≤ A := by
  rw [abs_of_nonneg (G_nonneg w)]
  rcases le_or_gt w 0 with hw | hw
  · calc G s μ w ≤ Real.exp (s * 0) := G_le_exp hs.le hw
      _ = 1 := by simp
      _ ≤ A := hμ.one_le_const
  · have hδ0 : (0:ℝ) < Real.exp (-w) := Real.exp_pos _
    have hδ1 : Real.exp (-w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hφ := phi_le hμ hδ0 hδ1
    have hrw : Real.exp (-w) ^ s = (Real.exp (s * w))⁻¹ := by
      rw [← Real.exp_mul, ← Real.exp_neg]
      congr 1
      ring
    have hpos : (0:ℝ) < Real.exp (s * w) := Real.exp_pos _
    rw [G]
    calc Real.exp (s * w) * Phi μ (Real.exp (-w))
        ≤ Real.exp (s * w) * (A * Real.exp (-w) ^ s) :=
          mul_le_mul_of_nonneg_left hφ hpos.le
      _ = A := by rw [hrw]; field_simp

end BrownianImages
