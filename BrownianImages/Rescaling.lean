/-
`sec:setup` of `BrownianImagesComplete.tex`: the exact rescaling `eq:smoothing`,
`S_μ(r) = r^{2s} H_μ(log(1/r))`.

The paper reaches `eq:smoothing` from the Stieltjes form of `eq:gaussian-reduction` by
integration by parts and the substitution `δ = r²η`.  Both steps are carried out here.
The integration by parts is the layer cake formula: the Gaussian return probability
`1 - e^{-r²/(2δ)}` is the mass the exponential density `u ↦ (r²/2)e^{-r²u/2}` puts on
`(0, 1/δ)`, so Tonelli turns the integral against `dΦ` into an integral of `Φ` itself,
with no boundary terms to discard.  The substitution is the inversion `η ↦ 1/η`
followed by the dilation `η ↦ r²η`, and both are unconditional identities.

* `Rescaling.integral_ret_pairLaw`: the analytic core, `eq:smoothing` with the
  Stieltjes form of `eq:gaussian-reduction` already substituted in.  It is
  unconditional.
* `smoothing_of_gaussian_reduction`: `eq:smoothing`, on the Stieltjes half of
  `thm:gaussian-reduction` as an explicit hypothesis.
* `non_lattice_correlation_limit_of_gaussian_reduction`: the conclusion of
  `thm:profile-asymptotics` for `μ_B`, on the same hypothesis quantified over `r`.
* `lattice_correlation_oscillation_of_smoothing`: the conclusion of
  `thm:profile-asymptotics` for `μ_A`, on `eq:smoothing` and the periodic profile
  `G̃_A` as explicit hypotheses.
-/
import BrownianImages.Profile
import BrownianImages.Kernel
import BrownianImages.Asymptotics
import BrownianImages.Smoothing
import BrownianImages.FourierMultiplier
import Mathlib.MeasureTheory.Integral.Layercake

namespace BrownianImages

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Rescaling

variable {μ : Measure ℝ}

/-! ### The exponential density behind the integration by parts -/

/-- The exponential density `u ↦ (r²/2)e^{-r²u/2}`.  Its mass on `(0, 1/δ)` is the
Gaussian return probability of `eq:gaussian-reduction`, which is what replaces the
integration by parts of `eq:smoothing`. -/
noncomputable def expDens (r u : ℝ) : ℝ := r ^ 2 / 2 * Real.exp (-(r ^ 2 * u / 2))

/-- The exponential density is continuous. -/
theorem continuous_expDens (r : ℝ) : Continuous (expDens r) := by
  unfold expDens; fun_prop

/-- The exponential density is non-negative. -/
theorem expDens_nonneg (r u : ℝ) : 0 ≤ expDens r u := by
  unfold expDens; positivity

/-- `eq:smoothing`, the integration by parts: the Gaussian return probability of
`eq:gaussian-reduction` is the mass the exponential density puts on `(0, 1/δ)`.  The
identity holds for every `δ`, the Lean convention `0⁻¹ = 0` matching `Φ(0) = 0`. -/
theorem intervalIntegral_expDens (r δ : ℝ) :
    ∫ u in (0:ℝ)..δ⁻¹, expDens r u = 1 - Real.exp (-(r ^ 2 / (2 * δ))) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) δ⁻¹,
      HasDerivAt (fun u : ℝ => -Real.exp (-(r ^ 2 * u / 2))) (expDens r x) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -(r ^ 2 * u / 2)) (-(r ^ 2 / 2)) x := by
      have hfun : (fun u : ℝ => -(r ^ 2 * u / 2)) = fun u : ℝ => -(r ^ 2 / 2) * u := by
        funext u; ring
      rw [hfun]
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (-(r ^ 2 / 2))
    have h2 := h1.exp.neg
    have hval : -(Real.exp (-(r ^ 2 * x / 2)) * -(r ^ 2 / 2)) = expDens r x := by
      unfold expDens; ring
    rwa [hval] at h2
  have hint : IntervalIntegrable (expDens r) volume 0 δ⁻¹ :=
    (continuous_expDens r).intervalIntegrable 0 δ⁻¹
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hrw : r ^ 2 * δ⁻¹ / 2 = r ^ 2 / (2 * δ) := by
    rcases eq_or_ne δ 0 with rfl | hδ
    · simp
    · field_simp
  rw [hrw]
  simp only [mul_zero, zero_div, neg_zero, Real.exp_zero]
  ring

/-! ### The pair-distance law on the half line -/

/-- The pair-distance law is a probability measure. -/
theorem isProbabilityMeasure_pairLaw [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (pairLaw μ) := by
  rw [pairLaw]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The pair-distance law charges no non-positive number: distances are non-negative,
and the atomlessness of `sec:setup` removes the value `0`. -/
theorem pairLaw_Iic_zero [IsProbabilityMeasure μ] {s A : ℝ} (hs : 0 < s)
    (hμ : IsFrostman s A μ) : pairLaw μ (Set.Iic 0) = 0 := by
  have hneg : pairLaw μ (Set.Iio (0:ℝ)) = 0 := by
    rw [pairLaw, Measure.map_apply (by fun_prop) measurableSet_Iio]
    convert measure_empty (μ := μ.prod μ)
    ext p
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact abs_nonneg _
  have hsplit : Set.Iic (0:ℝ) = Set.Iio 0 ∪ {0} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hsplit]
  exact measure_union_null hneg (pairLaw_measure_singleton hs hμ 0)

/-- `Φ` is also the mass the pair-distance law puts on `(0, δ]`: the left endpoint and
the atom at `δ` are both null. -/
theorem pairLaw_Ioo [IsProbabilityMeasure μ] {s A : ℝ} (hs : 0 < s)
    (hμ : IsFrostman s A μ) (c : ℝ) :
    pairLaw μ (Set.Ioo 0 c) = ENNReal.ofReal (Phi μ c) := by
  haveI := isProbabilityMeasure_pairLaw (μ := μ)
  have hle : pairLaw μ (Set.Iic c) ≤ pairLaw μ (Set.Ioo 0 c) := by
    have hsub : Set.Iic c ⊆ Set.Ioo 0 c ∪ (Set.Iic 0 ∪ {c}) := by
      intro x hx
      rcases le_or_gt x 0 with h | h
      · exact Or.inr (Or.inl h)
      · rcases lt_or_eq_of_le (Set.mem_Iic.mp hx) with h2 | h2
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr (Or.inr h2)
    calc pairLaw μ (Set.Iic c)
        ≤ pairLaw μ (Set.Ioo 0 c ∪ (Set.Iic 0 ∪ {c})) := measure_mono hsub
      _ ≤ pairLaw μ (Set.Ioo 0 c) + pairLaw μ (Set.Iic 0 ∪ {c}) := measure_union_le _ _
      _ = pairLaw μ (Set.Ioo 0 c) := by
          rw [measure_union_null (pairLaw_Iic_zero hs hμ)
            (pairLaw_measure_singleton hs hμ c), add_zero]
  have heq : pairLaw μ (Set.Ioo 0 c) = pairLaw μ (Set.Iic c) :=
    le_antisymm (measure_mono fun x hx => Set.mem_Iic.mpr hx.2.le) hle
  rw [heq, phi_eq_pairLaw, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The superlevel set of the inversion: for `t > 0` the points with `t < δ⁻¹` are
exactly those of `(0, 1/t)`.  This is what the layer cake formula turns into `Φ`. -/
theorem setOf_lt_inv {t : ℝ} (ht : 0 < t) : {a : ℝ | t < a⁻¹} = Set.Ioo 0 t⁻¹ := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · intro h
    have ha : 0 < a := by
      by_contra hc
      exact absurd h (not_lt.mpr (le_trans (inv_nonpos.mpr (not_lt.mp hc)) ht.le))
    exact ⟨ha, (lt_inv_comm₀ ht ha).mp h⟩
  · rintro ⟨ha, h⟩
    exact (lt_inv_comm₀ ht ha).mpr h

/-! ### The integration by parts -/

/-- `eq:smoothing`, the first half: the Stieltjes form of `eq:gaussian-reduction`
integrated by parts.  The layer cake formula does the work, and the boundary terms the
paper discards never appear. -/
theorem integral_ret_eq [IsProbabilityMeasure μ] {s A : ℝ} (hs : 0 < s)
    (hμ : IsFrostman s A μ) (r : ℝ) :
    ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ)
      = ∫ u in Set.Ioi (0:ℝ), Phi μ u⁻¹ * expDens r u := by
  haveI := isProbabilityMeasure_pairLaw (μ := μ)
  have hnonneg : ∀ᵐ δ ∂(pairLaw μ), 0 ≤ δ := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (pairLaw_Iic_zero hs hμ)
    simp only [Set.mem_setOf_eq, not_le] at hx
    exact hx.le
  have hfnn : (0 : ℝ → ℝ) ≤ᵐ[pairLaw μ] fun δ : ℝ => δ⁻¹ := by
    filter_upwards [hnonneg] with δ hδ
    simpa using inv_nonneg.mpr hδ
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul (μ := pairLaw μ)
    (f := fun δ : ℝ => δ⁻¹) (g := expDens r) hfnn (by fun_prop)
    (fun t _ => (continuous_expDens r).intervalIntegrable 0 t)
    (Eventually.of_forall fun u => expDens_nonneg r u)
  simp only [intervalIntegral_expDens] at hlc
  have hset : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
      pairLaw μ {a : ℝ | t < a⁻¹} * ENNReal.ofReal (expDens r t)
        = ENNReal.ofReal (Phi μ t⁻¹ * expDens r t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [setOf_lt_inv ht, pairLaw_Ioo hs hμ, ← ENNReal.ofReal_mul (phi_nonneg _)]
  rw [lintegral_congr_ae hset] at hlc
  have hretnn : (0 : ℝ → ℝ) ≤ᵐ[pairLaw μ] fun δ : ℝ => 1 - Real.exp (-(r ^ 2 / (2 * δ))) := by
    filter_upwards [hnonneg] with δ hδ
    have hq : 0 ≤ r ^ 2 / (2 * δ) := div_nonneg (sq_nonneg r) (by linarith)
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq)
    simpa using this
  have hLHS : ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ)
      = (∫⁻ δ, ENNReal.ofReal (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hretnn
      ((measurable_const.sub (Real.measurable_exp.comp
        ((measurable_const.div (measurable_const.mul measurable_id)).neg))).aestronglyMeasurable)
  have hRHSnn : (0 : ℝ → ℝ)
      ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] fun u : ℝ => Phi μ u⁻¹ * expDens r u :=
    Eventually.of_forall fun u => by
      simpa using mul_nonneg (phi_nonneg _) (expDens_nonneg r u)
  have hRHS : ∫ u in Set.Ioi (0:ℝ), Phi μ u⁻¹ * expDens r u
      = (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Phi μ u⁻¹ * expDens r u)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hRHSnn
      ((measurable_Phi.comp (by fun_prop)).mul
        (continuous_expDens r).measurable).aestronglyMeasurable
  rw [hLHS, hRHS, hlc]

/-! ### The substitution `δ = r²η` -/

/-- `eq:smoothing`, the second half: the substitution `δ = r²η`, which is the inversion
`η ↦ 1/η` followed by the dilation `η ↦ r²η`.  No Frostman hypothesis enters: both
changes of variable are unconditional identities. -/
theorem rpow_mul_H_eq {s : ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    r ^ (2 * s) * H s μ (Real.log r⁻¹)
      = ∫ u in Set.Ioi (0:ℝ), Phi μ u⁻¹ * expDens r u := by
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  -- the integrand of `eq:h-definition`, rescaled
  have hkey : ∀ η ∈ Set.Ioi (0:ℝ),
      r ^ (2 * s) * (kern s η * G s μ (2 * Real.log r⁻¹ - Real.log η))
        = 2⁻¹ * η ^ (-2 : ℝ) * Real.exp (-(2 * η)⁻¹) * Phi μ (r ^ 2 * η) := by
    intro η hη
    have hη0 : (0:ℝ) < η := hη
    have hexpw : Real.exp (-(2 * Real.log r⁻¹ - Real.log η)) = r ^ 2 * η := by
      have hexp : -(2 * Real.log r⁻¹ - Real.log η) = Real.log r + Real.log r + Real.log η := by
        rw [Real.log_inv]; ring
      rw [hexp, Real.exp_add, Real.exp_add, Real.exp_log hr, Real.exp_log hη0]
      ring
    have hE : r ^ (2 * s) * (η ^ (s - 2) *
        Real.exp (s * (2 * Real.log r⁻¹ - Real.log η))) = η ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hη0, Real.rpow_def_of_pos hη0,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [Real.log_inv]
      ring
    rw [kern, G, hexpw, ← hE]
    ring
  have h1 : r ^ (2 * s) * H s μ (Real.log r⁻¹)
      = ∫ η in Set.Ioi (0:ℝ),
          2⁻¹ * η ^ (-2 : ℝ) * Real.exp (-(2 * η)⁻¹) * Phi μ (r ^ 2 * η) := by
    rw [H, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hkey
  -- the inversion `η = 1/x`
  have h2 : (∫ η in Set.Ioi (0:ℝ),
        2⁻¹ * η ^ (-2 : ℝ) * Real.exp (-(2 * η)⁻¹) * Phi μ (r ^ 2 * η))
      = ∫ x in Set.Ioi (0:ℝ), 2⁻¹ * Real.exp (-(x / 2)) * Phi μ (r ^ 2 * x⁻¹) := by
    rw [← integral_comp_rpow_Ioi (fun η : ℝ =>
      2⁻¹ * η ^ (-2 : ℝ) * Real.exp (-(2 * η)⁻¹) * Phi μ (r ^ 2 * η)) (p := -1) (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    have hinv : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
    have hsq : (x⁻¹) ^ (-2 : ℝ) = (x ^ (-2 : ℝ))⁻¹ := Real.inv_rpow hx0.le _
    have hne : x ^ (-2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx0 _)
    have htwo : (2 * x⁻¹)⁻¹ = x / 2 := by
      rw [mul_inv, inv_inv]; ring
    have hexp : ((-1 : ℝ) - 1) = (-2 : ℝ) := by norm_num
    simp only [hinv, hexp, smul_eq_mul, abs_neg, abs_one, one_mul, hsq, htwo]
    field_simp
  -- the dilation `x = r²u`
  have h3 : (∫ x in Set.Ioi (0:ℝ), 2⁻¹ * Real.exp (-(x / 2)) * Phi μ (r ^ 2 * x⁻¹))
      = ∫ u in Set.Ioi (0:ℝ), Phi μ u⁻¹ * expDens r u := by
    have hdil := integral_comp_mul_left_Ioi
      (fun x : ℝ => 2⁻¹ * Real.exp (-(x / 2)) * Phi μ (r ^ 2 * x⁻¹)) 0 hr2
    rw [mul_zero, smul_eq_mul] at hdil
    have hpt : ∀ x ∈ Set.Ioi (0:ℝ),
        2⁻¹ * Real.exp (-((r ^ 2 * x) / 2)) * Phi μ (r ^ 2 * (r ^ 2 * x)⁻¹)
          = (r ^ 2)⁻¹ * (Phi μ x⁻¹ * expDens r x) := by
      intro x hx
      have hx0 : (0:ℝ) < x := hx
      have hcancel : r ^ 2 * (r ^ 2 * x)⁻¹ = x⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr2), one_mul]
      rw [hcancel]
      unfold expDens
      field_simp
    have h5 : (∫ x in Set.Ioi (0:ℝ),
          2⁻¹ * Real.exp (-((r ^ 2 * x) / 2)) * Phi μ (r ^ 2 * (r ^ 2 * x)⁻¹))
        = (r ^ 2)⁻¹ * ∫ u in Set.Ioi (0:ℝ), Phi μ u⁻¹ * expDens r u := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi hpt
    rw [h5] at hdil
    exact (mul_left_cancel₀ (inv_ne_zero (ne_of_gt hr2)) hdil).symm
  rw [h1, h2, h3]

/-! ### `eq:smoothing`, unconditionally on the Stieltjes form -/

set_option linter.unusedVariables false in
/-- `eq:smoothing`, the analytic core: the Stieltjes integral of `eq:gaussian-reduction`
is `r^{2s} H_μ(log(1/r))`.  This is the whole content of `eq:smoothing`, with the
Stieltjes form of `thm:gaussian-reduction` already substituted in. -/
theorem integral_ret_pairLaw {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ)
      = r ^ (2 * s) * H s μ (Real.log r⁻¹) := by
  rw [integral_ret_eq hs0 hμ r, rpow_mul_H_eq (μ := μ) (s := s) hr]

/-! ### Choosing a scale far out along a period -/

/-- A base point translated by enough whole periods passes any threshold. -/
theorem exists_far {v₀ p : ℝ} (hp : 0 < p) (T : ℝ) : ∃ n : ℕ, T ≤ v₀ + n * p := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - v₀) / p)
  have := (div_lt_iff₀ hp).mp hn
  exact ⟨n, by linarith⟩

end Rescaling

/-! ### `eq:smoothing` -/

variable {Ω : Type*} [MeasurableSpace Ω]

set_option linter.unusedVariables false in
/-- `eq:smoothing`.  The exact rescaling `S_μ(r) = r^{2s} H_μ(log(1/r))`, for every
`r > 0`, on the Stieltjes half of `thm:gaussian-reduction` as an explicit hypothesis.
The hypothesis is the second conjunct of `audit_gaussian_reduction`, verbatim, so
`audit_smoothing` follows from `audit_gaussian_reduction` by projection. -/
theorem smoothing_of_gaussian_reduction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ}
    (hr0 : 0 < r)
    (hgauss : expCorr W P μ r
        = ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ)) :
    expCorr W P μ r = r ^ (2 * s) * H s μ (Real.log r⁻¹) := by
  rw [hgauss]
  exact Rescaling.integral_ret_pairLaw hs0 hs1 hμ hr0

/-! ### `thm:profile-asymptotics`, the conclusions for the correlation integral -/

set_option linter.unusedVariables false in
/-- `thm:profile-asymptotics`, the conclusion for `μ_B`: the normalised expected
correlation integral has a finite positive limit.  `eq:smoothing` turns the limit at
`r → 0⁺` into the limit of `H_μ` at `+∞`, which is `eq:hb-asymptotic`.  The hypothesis
is the second conjunct of `audit_gaussian_reduction`, quantified over `r`. -/
theorem non_lattice_correlation_limit_of_gaussian_reduction {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s C A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (hCpos : 0 < C)
    (hgauss : ∀ r : ℝ, 0 < r → expCorr W P μ r
        = ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ)) :
    ∃ L > 0, Tendsto (fun r : ℝ => expCorr W P μ r / r ^ (2 * s)) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨hLpos, hLtend⟩ := profile_asymptotics_nonLattice hs0 hs1 hμ hCpos hC
  refine ⟨C * ∫ η in Set.Ioi (0:ℝ), kern s η, hLpos, ?_⟩
  have hlog : Tendsto (fun r : ℝ => Real.log r⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  refine Filter.Tendsto.congr' ?_ (hLtend.comp hlog)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  have hrpow : (0:ℝ) < r ^ (2 * s) := Real.rpow_pos_of_pos hr0 _
  rw [Function.comp_apply, hgauss r hr0, Rescaling.integral_ret_pairLaw hs0 hs1 hμ hr0]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hrpow)]

set_option linter.unusedVariables false in
/-- `thm:profile-asymptotics`, the conclusion for `μ_A`: the normalised expected
correlation integral oscillates.  `eq:ha-asymptotic` puts `H_A` within `ε` of the
`log 3 / 2`-periodic function `T G̃_A` far out, and `eq:lattice-gap` separates the
extrema of `T G̃_A`; `eq:smoothing` converts the two sequences of times into two
sequences of scales.  The hypotheses are the conclusion of `audit_smoothing`, quantified
over `r`, and the conclusion of `audit_exists_periodic_profile`. -/
theorem lattice_correlation_oscillation_of_smoothing {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {μA : Measure ℝ} [IsProbabilityMeasure μA]
    (hprofile : ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g p ∧
      (∀ w, a ≤ w → g w = G s μA w) ∧
      (∀ x, 0 < g x) ∧ ∃ x y, g x ≠ g y)
    (hsm : ∀ r : ℝ, 0 < r →
      expCorr W P μA r = r ^ (2 * s) * H s μA (Real.log r⁻¹)) :
    ∃ a b : ℝ, a < b ∧
      (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧ expCorr W P μA r ≤ a * r ^ (2 * s)) ∧
      (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧ b * r ^ (2 * s) ≤ expCorr W P μA r) := by
  obtain ⟨g, hg, hper, hagree, hgpos, hgne⟩ := hprofile
  have hhalf : (0:ℝ) < p / 2 := by linarith
  obtain ⟨C, hC0, hCbd⟩ := exists_lattice_bound hs0 hs1 (μ := μA) hg hp.ne' hper hagree
  have hne := smoothOp_nonconstant hs0 hs1 hp hg hper hgne
  obtain ⟨va, -, vb, -, hgap, hbound⟩ :=
    smoothOp_gap hs0 hs1 hp hg hper hne
  have hTper : Function.Periodic (smoothOp s g) (p / 2) :=
    smoothOp_periodic hper
  set ε : ℝ := (smoothOp s g va - smoothOp s g vb) / 4 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  -- far enough out the error term of `eq:ha-asymptotic` is below `ε`
  have hdecay : ∀ᶠ v in atTop, C * Real.exp (-2 * (1 - s) * v) ≤ ε := by
    have hneg : -2 * (1 - s) < 0 := by linarith
    have h1 : Tendsto (fun v : ℝ => -2 * (1 - s) * v) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id
    have h2 : Tendsto (fun v : ℝ => C * Real.exp (-2 * (1 - s) * v)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp h1).const_mul C
      simpa using this
    exact h2.eventually_le_const hεpos
  obtain ⟨V, hV⟩ := Filter.eventually_atTop.mp hdecay
  -- the scale attached to a base point of a period
  have hkey : ∀ v₀ : ℝ, ∀ R > 0, ∃ r : ℝ, 0 < r ∧ r < R ∧
      smoothOp s g (Real.log r⁻¹) = smoothOp s g v₀ ∧
      |H s μA (Real.log r⁻¹) - smoothOp s g (Real.log r⁻¹)| ≤ ε := by
    intro v₀ R hR
    obtain ⟨n, hn⟩ :=
      Rescaling.exists_far (v₀ := v₀) hhalf (max V (max 0 (Real.log R⁻¹ + 1)))
    set v : ℝ := v₀ + n * (p / 2) with hvdef
    have hvV : V ≤ v := le_trans (le_max_left _ _) hn
    have hv0 : 0 ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_right V _)) hn
    have hvR : Real.log R⁻¹ + 1 ≤ v :=
      le_trans (le_trans (le_max_right _ _) (le_max_right V _)) hn
    refine ⟨Real.exp (-v), Real.exp_pos _, ?_, ?_, ?_⟩
    · have hlt : -v < Real.log R := by
        have : Real.log R⁻¹ = -Real.log R := Real.log_inv R
        rw [this] at hvR; linarith
      calc Real.exp (-v) < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hlt
        _ = R := Real.exp_log hR
    · have hlr : Real.log (Real.exp (-v))⁻¹ = v := by
        rw [← Real.exp_neg, neg_neg, Real.log_exp]
      rw [hlr, hvdef]
      exact hTper.nat_mul n v₀
    · have hlr : Real.log (Real.exp (-v))⁻¹ = v := by
        rw [← Real.exp_neg, neg_neg, Real.log_exp]
      rw [hlr]
      exact le_trans (hCbd v) (hV v hvV)
  refine ⟨smoothOp s g vb + ε, smoothOp s g va - ε, by rw [hεdef]; linarith,
    ?_, ?_⟩
  · intro R hR
    obtain ⟨r, hr0, hrR, hTeq, habs⟩ := hkey vb R hR
    refine ⟨r, hr0, hrR, ?_⟩
    have hrpow : (0:ℝ) < r ^ (2 * s) := Real.rpow_pos_of_pos hr0 _
    have hle : H s μA (Real.log r⁻¹) ≤ smoothOp s g vb + ε := by
      have := (abs_le.mp habs).2
      rw [hTeq] at this
      linarith
    rw [hsm r hr0]
    calc r ^ (2 * s) * H s μA (Real.log r⁻¹)
        ≤ r ^ (2 * s) * (smoothOp s g vb + ε) :=
          mul_le_mul_of_nonneg_left hle hrpow.le
      _ = (smoothOp s g vb + ε) * r ^ (2 * s) := by ring
  · intro R hR
    obtain ⟨r, hr0, hrR, hTeq, habs⟩ := hkey va R hR
    refine ⟨r, hr0, hrR, ?_⟩
    have hrpow : (0:ℝ) < r ^ (2 * s) := Real.rpow_pos_of_pos hr0 _
    have hle : smoothOp s g va - ε ≤ H s μA (Real.log r⁻¹) := by
      have := (abs_le.mp habs).1
      rw [hTeq] at this
      linarith
    rw [hsm r hr0]
    calc (smoothOp s g va - ε) * r ^ (2 * s)
        = r ^ (2 * s) * (smoothOp s g va - ε) := by ring
      _ ≤ r ^ (2 * s) * H s μA (Real.log r⁻¹) :=
          mul_le_mul_of_nonneg_left hle hrpow.le


end BrownianImages
