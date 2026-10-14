module

/-
The estimates used in §9.3 (`sec:small-dimension`).

`entropy_bounds` states `thm:entropy-factor`; `derivative_bounds` combines
`thm:main-term-derivative` with `thm:remainder-derivative` and restates
`thm:second-derivative-small-s`; `small_parameter_margin` is the comparison used
in the proof of `thm:small-dimension-monotone`. The calculations are given
in full in the paper and also worked out in `Section9Computations.nb`. Every result here is
proved from the existing Lean library; the notebook is not an assumption or an input to these proofs.

Notation: `fixedMoment s p` is J(p), `mainTerm s p` is J₀(p), `entropy p` is h(p),
and `1 - Real.log p` is the factor `1 - log p`. The dimension s is fixed when differentiating.
-/
public import BrownianImages.FixedDimension.Monotone

@[expose] public section

namespace BrownianImages.Section9Estimates

noncomputable section

/-- `thm:entropy-factor`: positivity, the explicit bound near zero, and the chord bound. -/
theorem entropy_bounds :
    (∀ p ∈ Set.Ioo (0 : ℝ) (1/2), 0 < kappa p) ∧
    (∀ p ∈ Set.Ioc (0 : ℝ) (1/50), 0.88 / (p * (1 - Real.log p)) ≤ kappa p) ∧
    (∀ p₁ ∈ Set.Ioo (0 : ℝ) (1/2), ∃ c > 0, ∀ p ∈ Set.Ico p₁ (1/2),
      c * (1/2 - p) ≤ kappa p) :=
  ⟨fun _p hp => kappa_pos hp.1 hp.2, fun _p hp => kappa_ge_of_le hp.1 hp.2,
    fun _p₁ hp₁ => kappa_ge_of_ge hp₁.1 hp₁.2⟩

/-- Combined consequence of `thm:main-term-derivative` and `thm:remainder-derivative`,
together with `thm:second-derivative-small-s`, including existence of both derivatives. -/
theorem derivative_bounds :
    (∀ s ∈ Set.Ioc (0 : ℝ) (1/2), ∀ p ∈ Set.Ioc (0 : ℝ) (1/50),
      HasDerivAt (fixedMoment s) (deriv (fixedMoment s) p) p ∧
      |deriv (fixedMoment s) p| ≤
        6 * p ^ (-s) + 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s)) ∧
    (∀ s ∈ Set.Ioc (0 : ℝ) (2 / 100000), ∀ p ∈ Set.Icc (1 / 10000 : ℝ) (1/2),
      HasDerivAt (deriv (fixedMoment s)) (deriv (deriv (fixedMoment s)) p) p ∧
      |deriv (deriv (fixedMoment s)) p| ≤
        10 ^ 11 * s * (1 - 5 / 100000) ^ s⁻¹) := by
  constructor
  · intro s hs p hp
    exact hasDerivAt_fixedMoment_small hs.1 hs.2 hp.1 hp.2
  · intro s hs p hp
    obtain ⟨D, hD, hb⟩ := (fixedMoment_second_derivative hs.1 hs.2 hp.1 hp.2).2
    exact ⟨hD.differentiableAt.hasDerivAt, by simpa only [hD.deriv, gammaQ, radQ] using hb⟩

/-- The small-parameter comparison in `thm:small-dimension-monotone`.
The library proves it on the larger dimension range `0 < s ≤ 1/4`. -/
theorem small_parameter_margin {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 0 < p) (hp : p ≤ 1 / 10000) :
    |deriv (fixedMoment s) p| < kappa p :=
  abs_deriv_fixedMoment_lt_kappa_small hs (by linarith) hp0 hp

end

end BrownianImages.Section9Estimates
