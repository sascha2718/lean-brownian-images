/-
`sec:concentration` of `BrownianImagesComplete.tex`: the tail of the concentration
chain, from the variance bound of `thm:variance` to `thm:uniform-concentration` and
`thm:main`.

The variance bound of `thm:variance` is an input here, not an output: the statements
below carry the conclusion of `audit_variance` as an explicit hypothesis, in the text
`Challenge.lean` gives it, so that closing that endpoint discharges the hypothesis
mechanically.  The same holds for `audit_smoothing`, which identifies `𝔼 Y_μ(v)` with
`H_μ(t)`, and for `audit_aemeasurable_occupation`, without which the empirical profile
is not a random variable and no variance bound carries information.

* `Concentration.exp_sq_mul_varScale`: the change of variable `r = e^{-t}` in
  `eq:variance-scale`.
* `y_variance_of_variance`: `eq:y-variance`.
* `Concentration.exists_exp_bound`: the three regimes of `eq:y-variance` are dominated
  by a single exponential, so the grid sums are geometric.
* `Concentration.memLp_Yprofile`, `Concentration.integral_Yprofile`: the empirical
  profile is a bounded random variable with mean `H_μ(t)`.
* `grid_convergence_of_y_variance`: `eq:grid-convergence`, by Chebyshev and
  Borel--Cantelli.
* `Concentration.H_nonneg`, `Concentration.H_le`: the expected profile is bounded, the
  constant `M` of the proof of `thm:uniform-concentration`.
* `uniform_concentration_of_grid_convergence`: `thm:uniform-concentration`,
  `eq:uniform-concentration`, from `eq:grid-convergence`, the grid monotonicity
  `eq:monotone-fill` and `thm:profile-uniform-continuity`.
* `Concentration.tailSet`: the separating Borel set of the proof of `thm:main`, with
  its measurability and the disjointness `eq:profile-separation` forces.
* `main_of_uniform_concentration`: `thm:main`.
-/
import BrownianImages.Empirical
import BrownianImages.Occupation
import BrownianImages.UniformContinuity
import BrownianImages.WeakBorel
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Concentration

/-! ### The change of variable `r = e^{-t}` -/

/-- `exp x ^ 2 = exp (2x)`, the prefactor of `eq:y-definition` squared. -/
theorem exp_sq (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [two_mul, Real.exp_add, sq]

/-- The change of variable `r = e^{-t}` in `eq:variance-scale`: the prefactor `e^{4st}`
of `eq:y-definition` turns `V_s(e^{-t})` into the three regimes of `eq:y-variance`. -/
theorem exp_sq_mul_varScale (s v : ℝ) :
    Real.exp (2 * s * v) ^ 2 * varScale s (Real.exp (-v))
      = if s < 2⁻¹ then Real.exp (-(2 * s) * v)
        else if s = 2⁻¹ then (1 + v) * Real.exp (-v)
        else Real.exp (-(2 * (1 - s)) * v) := by
  rw [varScale, exp_sq]
  split_ifs with h1 h2
  · rw [← Real.exp_mul, ← Real.exp_add,
      show 2 * (2 * s * v) + -v * (6 * s) = -(2 * s) * v from by ring]
  · subst h2
    rw [Real.log_inv, Real.log_exp, neg_neg, ← Real.exp_mul]
    rw [show Real.exp (2 * (2 * (2:ℝ)⁻¹ * v)) * (Real.exp (-v * 3) * (1 + v))
        = (1 + v) * (Real.exp (2 * (2 * (2:ℝ)⁻¹ * v)) * Real.exp (-v * 3)) from by ring,
      ← Real.exp_add,
      show 2 * (2 * (2:ℝ)⁻¹ * v) + -v * 3 = -v from by ring]
  · rw [← Real.exp_mul, ← Real.exp_add,
      show 2 * (2 * s * v) + -v * (2 * s + 2) = -(2 * (1 - s)) * v from by ring]

/-! ### The three regimes dominated by one exponential -/

/-- The three regimes of `eq:y-variance` are dominated by a single decaying exponential
on `[0,∞)`.  This is what makes the grid sums of the proof of
`thm:uniform-concentration` geometric. -/
theorem exists_exp_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ a > 0, ∀ v : ℝ, 0 ≤ v →
      (if s < 2⁻¹ then Real.exp (-(2 * s) * v)
       else if s = 2⁻¹ then (1 + v) * Real.exp (-v)
       else Real.exp (-(2 * (1 - s)) * v)) ≤ 2 * Real.exp (-a * v) := by
  set a : ℝ := min (min (2 * s) (2 * (1 - s))) 2⁻¹ with ha
  have ha1 : a ≤ 2 * s := le_trans (min_le_left _ _) (min_le_left _ _)
  have ha2 : a ≤ 2 * (1 - s) := le_trans (min_le_left _ _) (min_le_right _ _)
  have ha3 : a ≤ 2⁻¹ := min_le_right _ _
  refine ⟨a, lt_min (lt_min (by linarith) (by linarith)) (by norm_num), fun v hv => ?_⟩
  have hpos : (0:ℝ) < Real.exp (-a * v) := Real.exp_pos _
  split_ifs with h1 h2
  · have hle : Real.exp (-(2 * s) * v) ≤ Real.exp (-a * v) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  · have hlin : 1 + v ≤ 2 * Real.exp (v / 2) := by
      have := Real.add_one_le_exp (v / 2)
      linarith
    have hmono : Real.exp (-(2⁻¹ : ℝ) * v) ≤ Real.exp (-a * v) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc (1 + v) * Real.exp (-v)
        ≤ 2 * Real.exp (v / 2) * Real.exp (-v) :=
          mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
      _ = 2 * Real.exp (-(2⁻¹ : ℝ) * v) := by
          rw [mul_assoc, ← Real.exp_add, show v / 2 + -v = -(2⁻¹ : ℝ) * v from by ring]
      _ ≤ 2 * Real.exp (-a * v) := by linarith
  · have hle : Real.exp (-(2 * (1 - s)) * v) ≤ Real.exp (-a * v) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith

/-- Along the grid `v_{j,m} = j/m` a decaying exponential is a geometric series. -/
theorem summable_exp_grid {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 0 < m) (K : ℝ) :
    Summable (fun j : ℕ => K * Real.exp (-a * ((j : ℝ) / m))) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hneg : -a / (m : ℝ) < 0 := div_neg_of_neg_of_pos (by linarith) hm0
  have hlt : Real.exp (-a / (m : ℝ)) < 1 := Real.exp_lt_one_iff.mpr hneg
  have hgeom : Summable (fun j : ℕ => Real.exp (-a / (m : ℝ)) ^ j) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hlt
  refine (hgeom.mul_left K).congr fun j => ?_
  rw [← Real.exp_nat_mul, show (j : ℝ) * (-a / (m : ℝ)) = -a * ((j : ℝ) / m) from by ring]

end Concentration


namespace Concentration

/-! ### The empirical profile as a random variable -/

/-- The empirical profile is a random variable.  `audit_aemeasurable_occupation` is
what supplies this, and without it the variance bound of `thm:variance` carries no
information. -/
theorem aemeasurable_Yprofile {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hmeas : AEMeasurable (occupationProb W μ) P) (v : ℝ) :
    AEMeasurable (fun ω => Yprofile s (occupation W μ ω) v) P := by
  refine ((measurable_Yprofile s v).comp_aemeasurable hmeas).congr ?_
  filter_upwards [hW.ae_occupationProb_toMeasure μ] with ω hω
  simp only [Function.comp_apply]
  rw [hω]

/-- The empirical profile is bounded by its own exponential prefactor, so it lies in
`L²(P)`: the correlation functional of a probability measure is at most one. -/
theorem memLp_Yprofile {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hmeas : AEMeasurable (occupationProb W μ) P) (v : ℝ) :
    MemLp (fun ω => Yprofile s (occupation W μ ω) v) 2 P := by
  refine memLp_of_bounded (a := 0) (b := Real.exp (2 * s * v)) ?_
    (aemeasurable_Yprofile hW hmeas v).aestronglyMeasurable 2
  filter_upwards [hW.ae_isProbabilityMeasure_occupation μ] with ω hω
  haveI := hω
  refine ⟨Yprofile_nonneg _ s v, ?_⟩
  have hle : (corr (occupation W μ ω) (Real.exp (-v))).toReal ≤ 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  calc Yprofile s (occupation W μ ω) v
      = Real.exp (2 * s * v) * (corr (occupation W μ ω) (Real.exp (-v))).toReal := rfl
    _ ≤ Real.exp (2 * s * v) * 1 := by
        exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (2 * s * v) := mul_one _

/-- `𝔼 Y_μ(t) = H_μ(t)`: `eq:smoothing` read in the coordinate of `eq:y-definition`.
The hypothesis is the conclusion of `audit_smoothing`. -/
theorem integral_Yprofile {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    {s : ℝ} {μ : Measure ℝ}
    (hsmooth : ∀ r : ℝ, 0 < r → expCorr W P μ r = r ^ (2 * s) * H s μ (Real.log r⁻¹))
    (v : ℝ) : ∫ ω, Yprofile s (occupation W μ ω) v ∂P = H s μ v := by
  have h1 : ∫ ω, Yprofile s (occupation W μ ω) v ∂P
      = Real.exp (2 * s * v) * expCorr W P μ (Real.exp (-v)) := by
    simp only [Yprofile, expCorr]
    exact integral_const_mul _ _
  rw [h1, hsmooth _ (Real.exp_pos _), Real.log_inv, Real.log_exp, neg_neg, ← Real.exp_mul,
    ← mul_assoc, ← Real.exp_add, show 2 * s * v + -v * (2 * s) = 0 from by ring,
    Real.exp_zero, one_mul]

end Concentration

/-! ### `eq:y-variance` -/

set_option linter.unusedVariables false in
/-- `eq:y-variance`: the variance bound of `thm:variance` in the exponential
coordinate, with the three regimes `s < 1/2`, `s = 1/2`, `s > 1/2`.  The hypothesis
`hvar` is the conclusion of `audit_variance`, and the change of variable is
`r = e^{-t}`. -/
theorem y_variance_of_variance {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hvar : ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      variance (fun ω => (corr (occupation W μ ω) r).toReal) P
        ≤ C * varScale s r) :
    ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      variance (fun ω => Yprofile s (occupation W μ ω) v) P
        ≤ C * (if s < 2⁻¹ then Real.exp (-(2 * s) * v)
               else if s = 2⁻¹ then (1 + v) * Real.exp (-v)
               else Real.exp (-(2 * (1 - s)) * v)) := by
  obtain ⟨C, hC, hbound⟩ := hvar
  refine ⟨C, hC, fun v hv => ?_⟩
  have hr0 : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
  have hr1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hvarY : variance (fun ω => Yprofile s (occupation W μ ω) v) P
      = Real.exp (2 * s * v) ^ 2
        * variance (fun ω => (corr (occupation W μ ω) (Real.exp (-v))).toReal) P := by
    simp only [Yprofile]
    exact variance_const_mul _ _ _
  rw [hvarY]
  have hpos : (0:ℝ) ≤ Real.exp (2 * s * v) ^ 2 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left (hbound _ hr0 hr1) hpos) (le_of_eq ?_)
  rw [show Real.exp (2 * s * v) ^ 2 * (C * varScale s (Real.exp (-v)))
      = C * (Real.exp (2 * s * v) ^ 2 * varScale s (Real.exp (-v))) from by ring,
    Concentration.exp_sq_mul_varScale]


/-! ### `eq:grid-convergence` -/

set_option linter.unusedVariables false in
/-- `eq:grid-convergence`: along the grid `v_{j,m} = j/m` the empirical profile
converges to the expected profile almost surely.  Chebyshev's inequality turns
`eq:y-variance` into a summable sequence of deviation probabilities, and the
Borel--Cantelli lemma turns that into almost sure convergence.  The three hypotheses
are the conclusions of `audit_aemeasurable_occupation`, `audit_smoothing` and
`audit_y_variance`. -/
theorem grid_convergence_of_y_variance {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {m : ℕ} (hm : 0 < m)
    (hmeas : AEMeasurable (occupationProb W μ) P)
    (hsmooth : ∀ r : ℝ, 0 < r → expCorr W P μ r = r ^ (2 * s) * H s μ (Real.log r⁻¹))
    (hyvar : ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      variance (fun ω => Yprofile s (occupation W μ ω) v) P
        ≤ C * (if s < 2⁻¹ then Real.exp (-(2 * s) * v)
               else if s = 2⁻¹ then (1 + v) * Real.exp (-v)
               else Real.exp (-(2 * (1 - s)) * v))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun j : ℕ => Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hyvar
  obtain ⟨a, ha, hdom⟩ := Concentration.exists_exp_bound hs0 hs1
  have hgrid : ∀ j : ℕ, (0:ℝ) ≤ (j : ℝ)/m := fun j => by positivity
  have hvbound : ∀ j : ℕ,
      variance (fun ω => Yprofile s (occupation W μ ω) ((j : ℝ)/m)) P
        ≤ 2 * C * Real.exp (-a * ((j : ℝ)/m)) := by
    intro j
    refine le_trans (hbound _ (hgrid j)) ?_
    nlinarith [hdom _ (hgrid j), Real.exp_pos (-a * ((j:ℝ)/m))]
  have hkey : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ (j : ℕ) in atTop,
      |Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m)| < 1/((k:ℝ)+1) := by
    intro k
    set ε₀ : ℝ := 1/((k:ℝ)+1) with hε₀
    have hε₀0 : (0:ℝ) < ε₀ := by positivity
    have hsummable : Summable
        (fun j : ℕ => 2 * C * Real.exp (-a * ((j : ℝ)/m)) / ε₀ ^ 2) := by
      refine (Concentration.summable_exp_grid ha hm (2 * C / ε₀ ^ 2)).congr fun j => ?_
      ring
    have hPS : ∀ j : ℕ,
        P {ω | ε₀ ≤ |Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m)|}
          ≤ ENNReal.ofReal (2 * C * Real.exp (-a * ((j : ℝ)/m)) / ε₀ ^ 2) := by
      intro j
      have hch := meas_ge_le_variance_div_sq (μ := P)
        (Concentration.memLp_Yprofile hW (s := s) hmeas ((j : ℝ)/m)) hε₀0
      rw [Concentration.integral_Yprofile hsmooth ((j : ℝ)/m)] at hch
      refine le_trans hch (ENNReal.ofReal_le_ofReal ?_)
      gcongr
      exact hvbound j
    have hne : ∑' j : ℕ,
        P {ω | ε₀ ≤ |Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m)|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hPS)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hne] with ω hω
    exact hω.mono fun j hj => by simpa using hj
  filter_upwards [ae_all_iff.mpr hkey] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hω k)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact lt_trans (hN n hn) hk


namespace Concentration

/-! ### The expected profile is bounded -/

/-- `H_μ ≥ 0`: the kernel and the normalised profile are non-negative. -/
theorem H_nonneg {s : ℝ} {μ : Measure ℝ} (v : ℝ) : 0 ≤ H s μ v :=
  setIntegral_nonneg measurableSet_Ioi fun _ hη =>
    mul_nonneg (kern_pos hη).le (G_nonneg _)

/-- `H_μ ≤ A ‖k‖₁` on the whole line: this is the supremum `M` of the proof of
`thm:uniform-concentration`, and `eq:phi-frostman` is what bounds `G`. -/
theorem H_le {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) (v : ℝ) : H s μ v ≤ A * ∫ x : ℝ, logKern s x := by
  have hkint : Integrable (logKern s) := logKern_integrable hs0 hs1
  have hb : ∀ᵐ x : ℝ, ‖logKern s x * G s μ (2 * v - x)‖ ≤ A * logKern s x := by
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logKern_pos _)]
    calc logKern s x * |G s μ (2 * v - x)|
        ≤ logKern s x * A :=
          mul_le_mul_of_nonneg_left (abs_G_le hs0 hμ _) (logKern_pos _).le
      _ = A * logKern s x := mul_comm _ _
  have hnorm := norm_integral_le_of_norm_le (hkint.const_mul A) hb
  rw [integral_const_mul] at hnorm
  rw [H_eq_Hlog, Hlog]
  exact le_trans (Real.le_norm_self _) hnorm

end Concentration

/-! ### `thm:uniform-concentration` -/

/-- `thm:uniform-concentration`, `eq:uniform-concentration`.  Almost surely the
empirical profile converges to the expected profile, uniformly on tails.  The
hypothesis `hgrid` is the conclusion of `audit_grid_convergence`, one grid for every
`m`; the grid is filled by `eq:monotone-fill`, the expected profile is moved along it
by `thm:profile-uniform-continuity`, and `eq:phi-frostman` bounds it. -/
theorem uniform_concentration_of_grid_convergence {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hgrid : ∀ m : ℕ, 0 < m → ∀ᵐ ω ∂P, Tendsto
      (fun j : ℕ => Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m))
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ V : ℝ, ∀ v ≥ V,
      |Yprofile s (occupation W μ ω) v - H s μ v| ≤ ε := by
  have hHle : ∀ v : ℝ, H s μ v ≤ A * ∫ x : ℝ, logKern s x := Concentration.H_le hs0 hs1 hμ
  have hHnn : ∀ v : ℝ, 0 ≤ H s μ v := fun v => Concentration.H_nonneg v
  set M : ℝ := A * ∫ x : ℝ, logKern s x with hMdef
  have hM0 : (0:ℝ) ≤ M := le_trans (hHnn 0) (hHle 0)
  have hM1 : (M:ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hUC := profile_uniformContinuous hs0 hs1 hμ
  rw [Metric.uniformContinuous_iff] at hUC
  have hallgrid : ∀ᵐ ω ∂P, ∀ m : ℕ, 0 < m → Tendsto
      (fun j : ℕ => Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m))
      atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : 0 < m
    · filter_upwards [hgrid m hm] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall fun _ h => absurd h hm
  filter_upwards [hallgrid, hW.ae_isProbabilityMeasure_occupation μ] with ω hωgrid hωprob
  haveI := hωprob
  intro ε hε
  obtain ⟨δ, hδ, hUCδ⟩ := hUC (ε/3) (by linarith)
  have hten : Tendsto (fun n : ℕ => Real.exp (2 * s * (1/(n:ℝ)))) atTop (𝓝 1) := by
    have hcont : Continuous fun t : ℝ => Real.exp (2 * s * t) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hzero := hcont.tendsto 0
    simp only [mul_zero, Real.exp_zero] at hzero
    exact hzero.comp tendsto_one_div_atTop_nhds_zero_nat
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hten (ε/(3*(M+1))) (div_pos hε (by linarith))
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) δ hδ
  set m : ℕ := max (max N₁ N₂) 1 with hmdef
  have hm1 : 1 ≤ m := le_max_right _ _
  have hm0 : 0 < m := hm1
  have hmR : (0:ℝ) < m := by exact_mod_cast hm0
  set c : ℝ := Real.exp (2 * s * (1/(m:ℝ))) with hcdef
  have hc1 : (1:ℝ) ≤ c :=
    Real.one_le_exp (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * s) (by positivity))
  have hcpos : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc1
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcsmall : c - 1 < ε/(3*(M+1)) := by
    have h := hN₁ m (le_trans (le_max_left _ _) (le_max_left _ _))
    rw [Real.dist_eq] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hstep : (1:ℝ)/m < δ := by
    have h := hN₂ m (le_trans (le_max_right _ _) (le_max_left _ _))
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hcM : (c - 1) * M ≤ ε/3 := by
    have h1 : (c - 1) * M ≤ (ε/(3*(M+1))) * M :=
      mul_le_mul_of_nonneg_right hcsmall.le hM0
    have h2 : (ε/(3*(M+1))) * M ≤ (ε/(3*(M+1))) * (M+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_pos hε (by linarith)).le
    have h3 : (ε/(3*(M+1))) * (M+1) = ε/3 := by field_simp
    linarith
  set η : ℝ := ε/(3*c) with hηdef
  have hηpos : (0:ℝ) < η := by rw [hηdef]; exact div_pos hε (by linarith)
  have hηle : η ≤ ε/3 := by
    rw [hηdef]
    exact div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  have hcη : c * η = ε/3 := by rw [hηdef]; field_simp
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp (hωgrid m hm0) η hηpos
  refine ⟨(J:ℝ)/m, fun v hv => ?_⟩
  -- the grid interval containing `v`
  have hV0 : (0:ℝ) ≤ (J:ℝ)/m := by positivity
  have hv0 : (0:ℝ) ≤ v := le_trans hV0 hv
  have hvm : (0:ℝ) ≤ v * m := mul_nonneg hv0 hmR.le
  set j : ℕ := ⌊v * m⌋₊ with hjdef
  have hjle : (j:ℝ) ≤ v * m := Nat.floor_le hvm
  have hjlt : v * m < (j:ℝ) + 1 := Nat.lt_floor_add_one (v * m)
  have hJj : J ≤ j := by
    refine Nat.le_floor ?_
    have : ((J:ℝ)/m) * m ≤ v * m := mul_le_mul_of_nonneg_right hv hmR.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hmR)] at this
  have hav : (j:ℝ)/m ≤ v := by
    rw [div_le_iff₀ hmR]; exact hjle
  have hvb : v ≤ ((j:ℝ)+1)/m := by
    rw [le_div_iff₀ hmR]; exact hjlt.le
  have hba : ((j:ℝ)+1)/(m:ℝ) - (j:ℝ)/(m:ℝ) = 1/(m:ℝ) := by ring
  have hfill := monotone_fill (occupation W μ ω) hs0.le hav hvb
  rw [hba, Real.exp_neg, ← hcdef] at hfill
  -- the grid values are close to the expected profile
  have hJa : |Yprofile s (occupation W μ ω) ((j:ℝ)/m) - H s μ ((j:ℝ)/m)| < η := by
    have h := hJ j hJj
    rwa [Real.dist_eq, sub_zero] at h
  have hJb : |Yprofile s (occupation W μ ω) (((j:ℝ)+1)/m)
      - H s μ (((j:ℝ)+1)/m)| < η := by
    have h := hJ (j+1) (le_trans hJj (Nat.le_succ j))
    rw [Real.dist_eq, sub_zero] at h
    push_cast at h
    exact h
  -- the expected profile barely moves along a grid interval
  have hUCa : |H s μ ((j:ℝ)/m) - H s μ v| < ε/3 := by
    have hd : dist ((j:ℝ)/m) v < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      have : v - (j:ℝ)/m ≤ 1/(m:ℝ) := by linarith [hba]
      linarith [hstep]
    have := hUCδ hd
    rwa [Real.dist_eq] at this
  have hUCb : |H s μ (((j:ℝ)+1)/m) - H s μ v| < ε/3 := by
    have hd : dist (((j:ℝ)+1)/m) v < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      have : ((j:ℝ)+1)/m - v ≤ 1/(m:ℝ) := by linarith [hba]
      linarith [hstep]
    have := hUCδ hd
    rwa [Real.dist_eq] at this
  -- the bounds on the expected profile
  have hHa0 := hHnn ((j:ℝ)/m)
  have hHaM := hHle ((j:ℝ)/m)
  have hHb0 := hHnn (((j:ℝ)+1)/m)
  have hHbM := hHle (((j:ℝ)+1)/m)
  set Ya := Yprofile s (occupation W μ ω) ((j:ℝ)/m) with hYadef
  set Yb := Yprofile s (occupation W μ ω) (((j:ℝ)+1)/m) with hYbdef
  set Yv := Yprofile s (occupation W μ ω) v with hYvdef
  set Ha := H s μ ((j:ℝ)/m) with hHadef
  set Hb := H s μ (((j:ℝ)+1)/m) with hHbdef
  set Hv := H s μ v with hHvdef
  have hmulinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hcne
  have hcinv1 : c⁻¹ ≤ 1 := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - 1) (inv_pos.mpr hcpos).le, hmulinv]
  -- the upper bound
  have e1 : c * (Ya - Ha) ≤ ε/3 := by
    have h := (abs_le.mp hJa.le).2
    have h2 := mul_le_mul_of_nonneg_left h hcpos.le
    linarith [hcη]
  have e2 : (c - 1) * Ha ≤ ε/3 := by
    have h : (c - 1) * Ha ≤ (c - 1) * M :=
      mul_le_mul_of_nonneg_left hHaM (by linarith)
    linarith
  have e3 : Ha - Hv ≤ ε/3 := (abs_le.mp hUCa.le).2
  have hup : Yv - Hv ≤ ε := by linarith [hfill.2, e1, e2, e3]
  -- the lower bound
  have f1 : c⁻¹ * (Hb - Yb) ≤ ε/3 := by
    have h : Hb - Yb ≤ η := by linarith [(abs_le.mp hJb.le).1]
    have h2 : c⁻¹ * (Hb - Yb) ≤ c⁻¹ * η :=
      mul_le_mul_of_nonneg_left h (inv_pos.mpr hcpos).le
    have h3 : c⁻¹ * η ≤ 1 * η := mul_le_mul_of_nonneg_right hcinv1 hηpos.le
    linarith
  have f2 : Hb - c⁻¹ * Hb ≤ ε/3 := by
    have h1 : 1 - c⁻¹ ≤ c - 1 := by
      rw [← sub_nonneg, show (c - 1) - (1 - c⁻¹) = (c - 1)^2 * c⁻¹ from by field_simp]
      exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hcpos.le)
    have h2 : (1 - c⁻¹) * Hb ≤ (c - 1) * Hb := mul_le_mul_of_nonneg_right h1 hHb0
    have h3 : (c - 1) * Hb ≤ (c - 1) * M := mul_le_mul_of_nonneg_left hHbM (by linarith)
    linarith [h2, h3, hcM]
  have f3 : Hv - Hb ≤ ε/3 := by linarith [(abs_le.mp hUCb.le).1]
  have hlow : Hv - Yv ≤ ε := by linarith [hfill.1, f1, f2, f3]
  exact abs_le.mpr ⟨by linarith, by linarith⟩


namespace Concentration

/-! ### The separating Borel set of `thm:main` -/

/-- The set of the proof of `thm:main`: the probability measures on the plane whose
empirical profile agrees with `H_μ` in the limit along the non-negative rationals.  The
paper writes it as `lim_n sup_{q ∈ ℚ, q ≥ n} |Y_ν(q) - H_μ(q)| = 0`; here it is written
out with a countable intersection over the tolerance, which avoids the junk value a
supremum takes on an unbounded family. -/
def tailSet (s : ℝ) (μ : Measure ℝ) : Set (ProbabilityMeasure Plane) :=
  ⋂ k : ℕ, ⋃ n : ℕ, ⋂ q : {q : ℚ // (n : ℚ) ≤ q},
    {ν | |Yprofile s ν.toMeasure ((q : ℚ) : ℝ) - H s μ ((q : ℚ) : ℝ)| ≤ 1/((k:ℝ)+1)}

/-- The set is Borel: it is built from countable unions and countable intersections of
the Borel maps `ν ↦ Y_ν(q)` of `eq:y-definition`. -/
theorem measurableSet_tailSet (s : ℝ) (μ : Measure ℝ) : MeasurableSet (tailSet s μ) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun q =>
    measurableSet_le (((measurable_Yprofile s ((q : ℚ) : ℝ)).sub measurable_const).abs)
      measurable_const

/-- Uniform convergence on tails puts a measure in the set. -/
theorem mem_tailSet {s : ℝ} {μ : Measure ℝ} {ν : ProbabilityMeasure Plane}
    (h : ∀ ε > 0, ∃ V : ℝ, ∀ v ≥ V, |Yprofile s ν.toMeasure v - H s μ v| ≤ ε) :
    ν ∈ tailSet s μ := by
  simp only [tailSet, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  intro k
  obtain ⟨V, hV⟩ := h (1/((k:ℝ)+1)) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_ge V
  refine ⟨n, fun q => hV _ (le_trans hn ?_)⟩
  exact_mod_cast q.2

/-- `eq:profile-separation` keeps the two sets apart: a measure in both would force the
two expected profiles together along the rationals, and by uniform continuity along the
line. -/
theorem tailSet_subset_compl {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|) :
    tailSet s μ₁ ⊆ (tailSet s μ₂)ᶜ := by
  intro ν hν₁ hν₂
  obtain ⟨ε, hε, hV⟩ := hsep
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε/4 by linarith)
  simp only [tailSet, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq] at hν₁ hν₂
  obtain ⟨n₁, hn₁⟩ := hν₁ k
  obtain ⟨n₂, hn₂⟩ := hν₂ k
  have hUC₁ := profile_uniformContinuous hs0 hs1 h₁
  have hUC₂ := profile_uniformContinuous hs0 hs1 h₂
  rw [Metric.uniformContinuous_iff] at hUC₁ hUC₂
  obtain ⟨δ₁, hδ₁, hd₁⟩ := hUC₁ (ε/4) (by linarith)
  obtain ⟨δ₂, hδ₂, hd₂⟩ := hUC₂ (ε/4) (by linarith)
  obtain ⟨v, hv, hvsep⟩ := hV ((max n₁ n₂ : ℕ) : ℝ)
  have hδ : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show v < v + min δ₁ δ₂ by linarith)
  have hqR : ((max n₁ n₂ : ℕ) : ℝ) ≤ ((q : ℚ) : ℝ) := le_trans hv hq1.le
  have hqn₁ : (n₁ : ℚ) ≤ q := by
    have : ((n₁ : ℕ) : ℝ) ≤ ((q : ℚ) : ℝ) :=
      le_trans (by exact_mod_cast Nat.le_max_left n₁ n₂) hqR
    exact_mod_cast this
  have hqn₂ : (n₂ : ℚ) ≤ q := by
    have : ((n₂ : ℕ) : ℝ) ≤ ((q : ℚ) : ℝ) :=
      le_trans (by exact_mod_cast Nat.le_max_right n₁ n₂) hqR
    exact_mod_cast this
  have hb₁ := hn₁ ⟨q, hqn₁⟩
  have hb₂ := hn₂ ⟨q, hqn₂⟩
  simp only at hb₁ hb₂
  have hdist : dist v ((q : ℚ) : ℝ) < min δ₁ δ₂ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  have hH₁ : |H s μ₁ v - H s μ₁ ((q : ℚ) : ℝ)| < ε/4 := by
    have h := hd₁ (lt_of_lt_of_le hdist (min_le_left _ _))
    rwa [Real.dist_eq] at h
  have hH₂ : |H s μ₂ ((q : ℚ) : ℝ) - H s μ₂ v| < ε/4 := by
    have h := hd₂ (lt_of_lt_of_le (by rwa [dist_comm] at hdist) (min_le_right _ _))
    rwa [Real.dist_eq] at h
  have t3 : |H s μ₁ ((q : ℚ) : ℝ) - H s μ₂ ((q : ℚ) : ℝ)| ≤ 2 * (1/((k:ℝ)+1)) := by
    calc |H s μ₁ ((q : ℚ) : ℝ) - H s μ₂ ((q : ℚ) : ℝ)|
        ≤ |H s μ₁ ((q : ℚ) : ℝ) - Yprofile s ν.toMeasure ((q : ℚ) : ℝ)|
            + |Yprofile s ν.toMeasure ((q : ℚ) : ℝ) - H s μ₂ ((q : ℚ) : ℝ)| :=
          abs_sub_le _ _ _
      _ ≤ 1/((k:ℝ)+1) + 1/((k:ℝ)+1) := by
          rw [abs_sub_comm (H s μ₁ ((q : ℚ) : ℝ))]
          linarith
      _ = 2 * (1/((k:ℝ)+1)) := by ring
  have t1 : |H s μ₁ v - H s μ₂ v|
      ≤ |H s μ₁ v - H s μ₁ ((q : ℚ) : ℝ)| + |H s μ₁ ((q : ℚ) : ℝ) - H s μ₂ v| :=
    abs_sub_le _ _ _
  have t2 : |H s μ₁ ((q : ℚ) : ℝ) - H s μ₂ v|
      ≤ |H s μ₁ ((q : ℚ) : ℝ) - H s μ₂ ((q : ℚ) : ℝ)|
        + |H s μ₂ ((q : ℚ) : ℝ) - H s μ₂ v| :=
    abs_sub_le _ _ _
  linarith

end Concentration

/-! ### `thm:main` -/

/-- `thm:main`.  Two `s`-Frostman measures whose expected profiles do not converge to
one another have mutually singular Brownian occupation laws.  The hypotheses `hmeas₁`
and `hmeas₂` are the conclusion of `audit_aemeasurable_occupation`, and `hconc₁`,
`hconc₂` are the conclusion of `audit_uniform_concentration`, one for each measure.
The separating Borel set is `Concentration.tailSet`, and `borel_probabilityMeasure_eq_giry`
is what says that the σ-algebra it is Borel for is the paper's. -/
theorem main_of_uniform_concentration {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
    (hmeas₁ : AEMeasurable (occupationProb W μ₁) P)
    (hmeas₂ : AEMeasurable (occupationProb W μ₂) P)
    (hconc₁ : ∀ᵐ ω ∂P, ∀ ε > 0, ∃ V : ℝ, ∀ v ≥ V,
      |Yprofile s (occupation W μ₁ ω) v - H s μ₁ v| ≤ ε)
    (hconc₂ : ∀ᵐ ω ∂P, ∀ ε > 0, ∃ V : ℝ, ∀ v ≥ V,
      |Yprofile s (occupation W μ₂ ω) v - H s μ₂ v| ≤ ε)
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  have hae₁ : ∀ᵐ ω ∂P, occupationProb W μ₁ ω ∈ Concentration.tailSet s μ₁ := by
    filter_upwards [hconc₁, hW.ae_occupationProb_toMeasure μ₁] with ω hω hωp
    refine Concentration.mem_tailSet ?_
    intro ε hε
    obtain ⟨V, hVle⟩ := hω ε hε
    exact ⟨V, fun v hv => by rw [hωp]; exact hVle v hv⟩
  have hae₂ : ∀ᵐ ω ∂P, occupationProb W μ₂ ω ∈ Concentration.tailSet s μ₂ := by
    filter_upwards [hconc₂, hW.ae_occupationProb_toMeasure μ₂] with ω hω hωp
    refine Concentration.mem_tailSet ?_
    intro ε hε
    obtain ⟨V, hVle⟩ := hω ε hε
    exact ⟨V, fun v hv => by rw [hωp]; exact hVle v hv⟩
  refine ⟨(Concentration.tailSet s μ₁)ᶜ,
    (Concentration.measurableSet_tailSet s μ₁).compl, ?_, ?_⟩
  · rw [occupationLaw, Measure.map_apply_of_aemeasurable hmeas₁
      (Concentration.measurableSet_tailSet s μ₁).compl, Set.preimage_compl]
    exact ae_iff.mp hae₁
  · rw [compl_compl, occupationLaw, Measure.map_apply_of_aemeasurable hmeas₂
      (Concentration.measurableSet_tailSet s μ₁)]
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hae₂)
    exact Concentration.tailSet_subset_compl hs0 hs1 h₁ h₂ hsep hω


end BrownianImages
