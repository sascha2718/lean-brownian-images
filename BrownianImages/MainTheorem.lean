/-
`sec:concentration` of `BrownianImagesComplete.tex`: the chain that carries the
four-point variance bound to the headline result, and `thm:main` itself.

Each step is the conditional theorem of `Concentration` fed with the endpoint below it:
`thm:variance` from `VarianceCovariance`, `eq:smoothing` from `Endpoints`, and the
measurability of the occupation law from `JointMeasurability`.

* `y_variance`: `eq:y-variance`, the variance bound in the exponential coordinate.
* `grid_convergence`: `eq:grid-convergence`, along each grid, almost surely.
* `uniform_concentration`: `thm:uniform-concentration`.
* `main`: `thm:main`.
-/
import BrownianImages.VarianceCovariance
import BrownianImages.Concentration
import BrownianImages.JointMeasurability

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

set_option linter.unusedVariables false in
/-- `eq:y-variance`: the variance bound of `thm:variance` in the exponential
coordinate. -/
theorem y_variance {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      variance (fun ω => Yprofile s (occupation W μ ω) v) P
        ≤ C * (if s < 2⁻¹ then Real.exp (-(2 * s) * v)
               else if s = 2⁻¹ then (1 + v) * Real.exp (-v)
               else Real.exp (-(2 * (1 - s)) * v)) :=
  y_variance_of_variance hW hs0 hs1 hμ (variance_four_point hW hs0 hs1 hμ)

set_option linter.unusedVariables false in
/-- `eq:grid-convergence`: along each grid `v_{j,m} = j/m` the empirical profile
converges to the expected profile almost surely, by Chebyshev and Borel--Cantelli. -/
theorem grid_convergence {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ ω ∂P, Tendsto
      (fun j : ℕ => Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m))
      atTop (𝓝 0) :=
  grid_convergence_of_y_variance hW hs0 hs1 hμ hm (hW.aemeasurable_occupationProb μ)
    (fun _ hr => smoothing hW hs0 hs1 hμ hr) (y_variance hW hs0 hs1 hμ)

set_option linter.unusedVariables false in
/-- `thm:uniform-concentration`, `eq:uniform-concentration`.  Almost surely the
empirical profile converges to the expected profile, uniformly on tails. -/
theorem uniform_concentration {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ V : ℝ, ∀ v ≥ V,
      |Yprofile s (occupation W μ ω) v - H s μ v| ≤ ε :=
  uniform_concentration_of_grid_convergence hW hs0 hs1 hμ
    (fun _ hm => grid_convergence hW hs0 hs1 hμ hm)

set_option linter.unusedVariables false in
/-- `thm:main`.  Two `s`-Frostman measures whose expected profiles do not converge to
one another have mutually singular Brownian occupation laws, as laws on `𝒫(ℝ²)`.  The
hypothesis is `eq:profile-separation`, `limsup |H₁ - H₂| > 0`, written out for a
non-negative function; `IsFrostman` carries the paper's standing assumption that the
measures live on `[0,1]`. -/
theorem main {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) :=
  main_of_uniform_concentration hW hs0 hs1 h₁ h₂ (hW.aemeasurable_occupationProb μ₁)
    (hW.aemeasurable_occupationProb μ₂) (uniform_concentration hW hs0 hs1 h₁)
    (uniform_concentration hW hs0 hs1 h₂) hsep

end BrownianImages
