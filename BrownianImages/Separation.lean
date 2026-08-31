/-
`sec:smoothing` of `BrownianImagesComplete.tex`, `thm:non-lattice-separation`: two
non-arithmetic systems whose renewal constants of `eq:g-non-lattice-limit` differ have
mutually singular Brownian occupation laws.

The corollary is a composition of three steps.  Each normalised profile `G_i` converges
to its own renewal constant `C_i`, which is `thm:non-lattice-limit`; `eq:hb-asymptotic`
turns that into convergence of the expected profile `H_i` to `C_i ∫₀^∞ K`; and two
distinct limits force `eq:profile-separation`, which is what `thm:main` consumes.  The
middle step is `profile_asymptotics_nonLattice` and the strict positivity of `∫₀^∞ K` is
`integral_kern_pos`, so the only inputs still open are `thm:non-lattice-limit` and
`thm:main` themselves.  Both are carried as explicit hypotheses, in the text
`Challenge.lean` gives them, so that closing those endpoints discharges the hypotheses
mechanically.

* `Separation.exists_separation_of_tendsto`: the middle step, in the written-out shape
  `eq:profile-separation` is stated in.  Two functions with distinct limits stay a third
  of the gap apart at arbitrarily large times.
* `non_lattice_separation_of_main_of_limit`: `thm:non-lattice-separation`, on those two
  inputs.
-/
import BrownianImages.Asymptotics
import BrownianImages.AhlforsRegular

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Separation

/-- `eq:profile-separation` from two distinct limits.  If `f₁ → L₁` and `f₂ → L₂` with
`L₁ ≠ L₂`, then `|f₁ - f₂|` is at least `|L₁ - L₂|/3` at arbitrarily large arguments:
past a common threshold each function sits within a third of the gap of its own limit,
and the triangle inequality leaves the remaining third.  The conclusion is the
written-out form of `limsup |f₁ - f₂| > 0` that `thm:main` takes as its hypothesis. -/
theorem exists_separation_of_tendsto {f₁ f₂ : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : Tendsto f₁ atTop (𝓝 L₁)) (h₂ : Tendsto f₂ atTop (𝓝 L₂)) (hne : L₁ ≠ L₂) :
    ∃ ε > 0, ∀ V : ℝ, ∃ v ≥ V, ε ≤ |f₁ v - f₂ v| := by
  have hgap : 0 < |L₁ - L₂| := abs_pos.mpr (sub_ne_zero_of_ne hne)
  have hε : 0 < |L₁ - L₂| / 3 := by linarith
  refine ⟨|L₁ - L₂| / 3, hε, fun V => ?_⟩
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp h₁) (|L₁ - L₂| / 3) hε
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h₂) (|L₁ - L₂| / 3) hε
  set v : ℝ := max V (max N₁ N₂) with hv
  refine ⟨v, le_max_left _ _, ?_⟩
  have hd₁ : |L₁ - f₁ v| < |L₁ - L₂| / 3 := by
    have h := hN₁ v (le_trans (le_max_left N₁ N₂) (le_max_right V _))
    rw [Real.dist_eq] at h
    rwa [abs_sub_comm]
  have hd₂ : |f₂ v - L₂| < |L₁ - L₂| / 3 := by
    have h := hN₂ v (le_trans (le_max_right N₁ N₂) (le_max_right V _))
    rwa [Real.dist_eq] at h
  have key : |L₁ - L₂| ≤ |L₁ - f₁ v| + (|f₁ v - f₂ v| + |f₂ v - L₂|) := by
    calc |L₁ - L₂| ≤ |L₁ - f₁ v| + |f₁ v - L₂| := abs_sub_le _ _ _
      _ ≤ |L₁ - f₁ v| + (|f₁ v - f₂ v| + |f₂ v - L₂|) := by
          gcongr
          exact abs_sub_le _ _ _
  linarith

end Separation

set_option linter.unusedVariables false in
/-- `thm:non-lattice-separation`.  Two non-arithmetic systems whose renewal constants
`eq:g-non-lattice-limit` differ have mutually singular Brownian occupation laws.  The
hypotheses `hlim₁` and `hlim₂` are the conclusion of `audit_non_lattice_limit`, one for
each system, and `hmain` is `audit_main` at the ambient `W`, `P` and `s`, with the two
Frostman constants and its three hypotheses left quantified: the constants are produced
inside the proof by `AhlforsRegular.exists_isFrostman_of_isNatural`.  Everything else is
proved here: `eq:hb-asymptotic` moves the two limits from `G` to `H`, `integral_kern_pos`
says the common factor `∫₀^∞ K` does not collapse them, and
`Separation.exists_separation_of_tendsto` turns the two distinct limits into
`eq:profile-separation`. -/
theorem non_lattice_separation_of_main_of_limit {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (S₁ : System ι₁) (S₂ : System ι₂) {K₁ K₂ : Set ℝ} {ρ₁ ρ₂ : ℝ}
    (hsep₁ : S₁.StronglySeparated K₁ ρ₁) (hsep₂ : S₂.StronglySeparated K₂ ρ₂)
    (hdim₁ : S₁.IsDimension s) (hdim₂ : S₂.IsDimension s)
    (hna₁ : S₁.NonArithmetic) (hna₂ : S₂.NonArithmetic)
    {μ₁ μ₂ : Measure ℝ} (hμ₁ : S₁.IsNatural K₁ s μ₁) (hμ₂ : S₂.IsNatural K₂ s μ₂)
    (hne : (S₁.renewalMean s)⁻¹ * ∫ x : ℝ, S₁.renewalDefect s μ₁ x
        ≠ (S₂.renewalMean s)⁻¹ * ∫ x : ℝ, S₂.renewalDefect s μ₂ x)
    (hlim₁ : 0 < (S₁.renewalMean s)⁻¹ * ∫ x : ℝ, S₁.renewalDefect s μ₁ x ∧
      Tendsto (G s μ₁) atTop (𝓝 ((S₁.renewalMean s)⁻¹ * ∫ x : ℝ, S₁.renewalDefect s μ₁ x)))
    (hlim₂ : 0 < (S₂.renewalMean s)⁻¹ * ∫ x : ℝ, S₂.renewalDefect s μ₂ x ∧
      Tendsto (G s μ₂) atTop (𝓝 ((S₂.renewalMean s)⁻¹ * ∫ x : ℝ, S₂.renewalDefect s μ₂ x)))
    (hmain : ∀ {A₁ A₂ : ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂],
      IsFrostman s A₁ μ₁ → IsFrostman s A₂ μ₂ →
      (∃ ε > 0, ∀ V : ℝ, ∃ v ≥ V, ε ≤ |H s μ₁ v - H s μ₂ v|) →
      (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂)) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  haveI := hμ₁.isProbabilityMeasure
  haveI := hμ₂.isProbabilityMeasure
  obtain ⟨A₁, hFrost₁⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0 hsep₁ hμ₁
  obtain ⟨A₂, hFrost₂⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0 hsep₂ hμ₂
  obtain ⟨hC₁, hG₁⟩ := hlim₁
  obtain ⟨hC₂, hG₂⟩ := hlim₂
  obtain ⟨-, hH₁⟩ := profile_asymptotics_nonLattice hs0 hs1 hFrost₁ hC₁ hG₁
  obtain ⟨-, hH₂⟩ := profile_asymptotics_nonLattice hs0 hs1 hFrost₂ hC₂ hG₂
  refine hmain hFrost₁ hFrost₂ (Separation.exists_separation_of_tendsto hH₁ hH₂ ?_)
  exact fun h =>
    hne (mul_right_cancel₀ (ne_of_gt (integral_kern_pos hs0 hs1)) h)

end BrownianImages
