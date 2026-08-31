/-
`thm:renewal-recursion` of `sec:renewal`: the self-similar recursion of the pair-distance
profile, `eq:phi-recursion` and `eq:g-recursion`.

The computation runs on the Fubini form `Φ(δ) = (∫⁻ x, μ(B̄(x,δ)) ∂μ).toReal` of
`phi_prod_eq`, never on `μ × μ` directly: Mathlib's `Measure.prod_sum` is stated for
`Measure.sum` over a countable index, not for the `Finset` sums that
`IsNatural.selfSimilar` produces.  The off-diagonal blocks are killed pointwise inside
the integrand, under `∀ᵐ x ∂μ, x ∈ K`, so no measurability of the off-diagonal section
functions is ever needed.

* `measurable_measure_closedBall`: `x ↦ μ(B̄(x,δ))` is measurable.
* `System.IsNatural.measure_eq_sum`, `.lintegral_eq_sum`: Hutchinson's identity on a set
  and on a lower integral.
* `System.StronglySeparated.measure_closedBall_map`: below the gap only the diagonal
  block survives.
* `phi_recursion`, `g_recursion`: the two recursions.
-/
import BrownianImages.SelfSimilar
import BrownianImages.Frostman

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

/-- The ball-mass function is measurable: it is the section function of the
pair-distance set. -/
theorem measurable_measure_closedBall (μ : Measure ℝ) [SFinite μ] (δ : ℝ) :
    Measurable fun x : ℝ => μ (Metric.closedBall x δ) := by
  have h : Measurable fun x : ℝ => μ (Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}) :=
    measurable_measure_prodMk_left (measurableSet_phiSet δ)
  simpa only [mk_preimage_phiSet] using h

variable {ι : Type*} [Fintype ι]

/-- Hutchinson's identity read on a measurable set. -/
theorem System.IsNatural.measure_eq_sum (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {A : Set ℝ} (hA : MeasurableSet A) :
    μ A = ∑ j, ENNReal.ofReal (S.ratio j ^ s) * μ (S.map j ⁻¹' A) := by
  conv_lhs => rw [hμ.selfSimilar]
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (S.measurable_map j) hA]

/-- Hutchinson's identity read on a lower integral. -/
theorem System.IsNatural.lintegral_eq_sum (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * ∫⁻ x, f (S.map i x) ∂μ := by
  conv_lhs => rw [hμ.selfSimilar]
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_smul_measure, lintegral_map hf (S.measurable_map i), smul_eq_mul]

/-- Below the separation gap only the diagonal block survives: a ball of radius `δ < ρ`
centred in the piece `S_i K` meets no other piece, and pulling it back through `S_i`
rescales the radius by `r_i`. -/
theorem System.StronglySeparated.measure_closedBall_map (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {δ : ℝ} (hδ : δ < ρ) (i : ι) {x : ℝ} (hx : x ∈ K) :
    μ (Metric.closedBall (S.map i x) δ)
      = ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i)) := by
  have hr := S.ratio_pos i
  rw [hμ.measure_eq_sum S measurableSet_closedBall, Finset.sum_eq_single i]
  · congr 2
    ext y
    simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, System.map]
    rw [show S.ratio i * y + S.shift i - (S.ratio i * x + S.shift i) = (y - x) * S.ratio i from
        by ring, abs_mul, abs_of_pos hr, le_div_iff₀ hr]
  · intro j _ hji
    have hsub : S.map j ⁻¹' Metric.closedBall (S.map i x) δ ⊆ Kᶜ := by
      intro y hy hyK
      have h1 : |S.map j y - S.map i x| ≤ δ := by
        simpa only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] using hy
      have h2 : ρ ≤ |S.map i x - S.map j y| := hsep.2 i j (Ne.symm hji) x hx y hyK
      rw [abs_sub_comm] at h1
      linarith
    rw [measure_mono_null hsub hμ.support, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- `thm:renewal-recursion`, `eq:phi-recursion`.  Below the separation gap the
pair-distance distribution satisfies the self-similar recursion. -/
theorem phi_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < ρ) :
    Phi μ δ = ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) := by
  haveI := hμ.isProbabilityMeasure
  have _hδ0 := hδ0  -- the positivity of `δ` is not needed below
  have hphi : ∀ δ' : ℝ, Phi μ δ' = (∫⁻ x, μ (Metric.closedBall x δ') ∂μ).toReal := by
    intro δ'; rw [Phi, phi_prod_eq]
  have hfin : ∀ δ' : ℝ, (∫⁻ x, μ (Metric.closedBall x δ') ∂μ) ≠ ⊤ := by
    intro δ'
    rw [← phi_prod_eq]
    exact measure_ne_top _ _
  have hK : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]; exact hμ.support
  have hkey : (∫⁻ x, μ (Metric.closedBall x δ) ∂μ)
      = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
          ∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ := by
    rw [hμ.lintegral_eq_sum S (measurable_measure_closedBall μ δ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hae : ∀ᵐ x ∂μ, μ (Metric.closedBall (S.map i x) δ)
        = ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i)) := by
      filter_upwards [hK] with x hx
      exact hsep.measure_closedBall_map S hμ hδ i hx
    rw [lintegral_congr_ae hae,
      lintegral_const_mul _ (measurable_measure_closedBall μ (δ / S.ratio i)), mul_assoc]
  have hne : ∀ i : ι, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
      (∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ) ≠ ⊤ :=
    fun i => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hfin _)
  rw [hphi δ, hkey, ENNReal.toReal_sum (fun i _ => hne i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hphi (δ / S.ratio i), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le]
  congr 1
  rw [← Real.rpow_add (S.ratio_pos i), two_mul]

/-- `thm:renewal-recursion`, `eq:g-recursion`.  The recursion in the normalised
profile. -/
theorem g_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {w : ℝ} (hw : Real.log ρ⁻¹ < w) :
    G s μ w = ∑ i, S.ratio i ^ s * G s μ (w - S.logRatio i) := by
  have hρ : 0 < ρ := hsep.1
  have hδ0 : 0 < Real.exp (-w) := Real.exp_pos _
  have hδ : Real.exp (-w) < ρ := by
    rw [Real.log_inv] at hw
    calc Real.exp (-w) < Real.exp (Real.log ρ) := Real.exp_lt_exp.mpr (by linarith)
      _ = ρ := Real.exp_log hρ
  rw [G, phi_recursion S hsep hμ hδ0 hδ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr := S.ratio_pos i
  have h1 : Real.exp (-(w - S.logRatio i)) = Real.exp (-w) / S.ratio i := by
    rw [show -(w - S.logRatio i) = -w + S.logRatio i from by ring, Real.exp_add,
      System.logRatio, Real.exp_log (inv_pos.mpr hr), div_eq_mul_inv]
  have h2 : Real.exp (s * (w - S.logRatio i)) = Real.exp (s * w) * S.ratio i ^ s := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_add, System.logRatio, Real.log_inv]
    congr 1
    ring
  have h3 : S.ratio i ^ (2 * s) = S.ratio i ^ s * S.ratio i ^ s := by
    rw [two_mul, Real.rpow_add hr]
  rw [G, h1, h2, h3]
  ring

end BrownianImages
