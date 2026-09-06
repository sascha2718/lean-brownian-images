/-
`sec:reconstruction`, `thm:neighbourhood-concentration` of
`BrownianImagesComplete.tex`: the abstract `L²` step in the stochastic recurrence.

This file isolates the Hilbert-space calculation from the Brownian tube estimates.
Pairwise independence gives the sharp square-sum bound for the centered weighted
pieces, while an arbitrary overlap error is handled by the `L²` triangle inequality.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace MinkowskiL2Recurrence

noncomputable section

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The real `L²` seminorm after subtracting the expectation. -/
noncomputable def centeredL2Norm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  lpNorm (fun ω ↦ X ω - ∫ x, X x ∂μ) 2 μ

/-- The centred `L²` norm is non-negative. -/
theorem centeredL2Norm_nonneg (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ centeredL2Norm X μ :=
  lpNorm_nonneg

/-- For an `L²` random variable, the square of its centered `L²` seminorm is its
variance. -/
theorem centeredL2Norm_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    centeredL2Norm X μ ^ 2 = variance X μ := by
  rw [variance_eq_integral hX.aemeasurable]
  rw [centeredL2Norm, lpNorm_eq_integral_norm_rpow_toReal]
  · norm_num only [ENNReal.toReal_ofNat, OfNat.ofNat, invOf_eq_inv]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    · apply integral_congr_ae
      filter_upwards with ω
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    · exact integral_nonneg fun ω ↦ Real.rpow_nonneg (norm_nonneg _) _
  · norm_num
  · norm_num
  · exact (hX.aestronglyMeasurable.sub aestronglyMeasurable_const)

/-- The centered `L²` seminorm is the standard deviation. -/
theorem centeredL2Norm_eq_sqrt_variance [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) :
    centeredL2Norm X μ = Real.sqrt (variance X μ) := by
  refine (sq_eq_sq₀ (centeredL2Norm_nonneg X μ) (Real.sqrt_nonneg _)).mp ?_
  rw [centeredL2Norm_sq hX, Real.sq_sqrt (variance_nonneg X μ)]

/-- Pairwise independent `L²` variables have the sharp variance identity after an
arbitrary finite real weighting. -/
theorem variance_weighted_sum [Fintype ι] [IsFiniteMeasure μ]
    (X : ι → Ω → ℝ) (p : ι → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) :
    variance (fun ω ↦ ∑ i, p i * X i ω) μ =
      ∑ i, (p i) ^ 2 * variance (X i) μ := by
  let Y : ι → Ω → ℝ := fun i ω ↦ p i * X i ω
  have hY : ∀ i, MemLp (Y i) 2 μ := fun i ↦ (hX i).const_mul (p i)
  have hYindep : Set.Pairwise (↑(Finset.univ : Finset ι))
      fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    intro i _ j _ hij
    have h := (hindep hij).comp
      (show Measurable (fun x : ℝ ↦ p i * x) by fun_prop)
      (show Measurable (fun x : ℝ ↦ p j * x) by fun_prop)
    simpa [Y, Function.comp_def] using h
  calc
    variance (fun ω ↦ ∑ i, p i * X i ω) μ = variance (∑ i, Y i) μ := by
      congr 1
      funext ω
      simp [Y]
    _ = ∑ i, variance (Y i) μ := by
      simpa using ProbabilityTheory.IndepFun.variance_sum
        (s := Finset.univ) (X := Y) (fun i _ ↦ hY i) hYindep
    _ = ∑ i, (p i) ^ 2 * variance (X i) μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact variance_const_mul (p i) (X i) μ

/-- Mutual independence implies the pairwise independence needed by the variance
calculation. -/
theorem pairwise_indepFun_of_iIndepFun {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) :
    Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j :=
  fun _ _ hij ↦ hindep.indepFun hij

/-- Sharp centered `L²` identity for a finite pairwise independent weighted family. -/
theorem centeredL2Norm_weighted_sum [Fintype ι] [IsFiniteMeasure μ]
    (X : ι → Ω → ℝ) (p : ι → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) :
    centeredL2Norm (fun ω ↦ ∑ i, p i * X i ω) μ =
      Real.sqrt (∑ i, (p i * centeredL2Norm (X i) μ) ^ 2) := by
  have hsum : MemLp (fun ω ↦ ∑ i, p i * X i ω) 2 μ :=
    memLp_finsetSum Finset.univ fun i _ ↦ (hX i).const_mul (p i)
  rw [centeredL2Norm_eq_sqrt_variance hsum,
    variance_weighted_sum X p hX hindep]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, centeredL2Norm_sq (hX i)]

/-- If the centered `L²` size of the `i`th independent input is at most `a i`,
then the centered size of their weighted sum is at most the Euclidean norm of the
weighted bounds. -/
theorem centeredL2Norm_weighted_sum_le [Fintype ι] [IsFiniteMeasure μ]
    (X : ι → Ω → ℝ) (p a : ι → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, centeredL2Norm (X i) μ ≤ a i) :
    centeredL2Norm (fun ω ↦ ∑ i, p i * X i ω) μ ≤
      Real.sqrt (∑ i, (p i * a i) ^ 2) := by
  rw [centeredL2Norm_weighted_sum X p hX hindep]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [mul_pow, mul_pow]
  apply mul_le_mul_of_nonneg_left
  · exact (sq_le_sq₀ (centeredL2Norm_nonneg (X i) μ) (ha0 i)).mpr (ha i)
  · exact sq_nonneg (p i)

/-- The square of the real `L²` seminorm is the integral of the square. -/
theorem lpNorm_two_sq {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    lpNorm X 2 μ ^ 2 = ∫ ω, X ω ^ 2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal]
  · norm_num only [ENNReal.toReal_ofNat, OfNat.ofNat, invOf_eq_inv]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    · apply integral_congr_ae
      filter_upwards with ω
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    · exact integral_nonneg fun ω ↦ Real.rpow_nonneg (norm_nonneg _) _
  · norm_num
  · norm_num
  · exact hX.aestronglyMeasurable

/-- Centering is an `L²` contraction on a probability space. -/
theorem centeredL2Norm_le_lpNorm [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) :
    centeredL2Norm X μ ≤ lpNorm X 2 μ := by
  apply (sq_le_sq₀ (centeredL2Norm_nonneg X μ) lpNorm_nonneg).mp
  rw [centeredL2Norm_sq hX, lpNorm_two_sq hX]
  exact variance_le_expectation_sq hX.aestronglyMeasurable

/-- The centered `L²` seminorm is invariant under almost-everywhere equality. -/
theorem centeredL2Norm_congr [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXY : X =ᵐ[μ] Y) :
    centeredL2Norm X μ = centeredL2Norm Y μ := by
  rw [centeredL2Norm_eq_sqrt_variance hX, centeredL2Norm_eq_sqrt_variance hY,
    variance_congr hXY]

/-- Minkowski's inequality after centering. -/
theorem centeredL2Norm_sub_le [IsFiniteMeasure μ] {X O : Ω → ℝ}
    (hX : MemLp X 2 μ) (hO : MemLp O 2 μ) :
    centeredL2Norm (fun ω ↦ X ω - O ω) μ ≤
      centeredL2Norm X μ + centeredL2Norm O μ := by
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hOi : Integrable O μ := hO.integrable one_le_two
  have hcenterX : MemLp (fun ω ↦ X ω - ∫ x, X x ∂μ) 2 μ :=
    hX.sub (memLp_const (∫ x, X x ∂μ))
  have htriangle := lpNorm_sub_le (p := (2 : ℝ≥0∞)) hcenterX
    (g := fun ω ↦ O ω - ∫ x, O x ∂μ) (by norm_num)
  unfold centeredL2Norm
  rw [integral_sub hXi hOi]
  convert htriangle using 1
  congr 1
  funext ω
  simp only [Pi.sub_apply]
  ring

/-- The recurrence step used for the tube-mass fluctuation.  The independent contribution is
estimated sharply in `L²`; centering the arbitrary overlap error costs no constant at all. -/
theorem centeredL2Norm_recurrence_le [Fintype ι] [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Xi : ι → Ω → ℝ) (O : Ω → ℝ) (p a : ι → ℝ)
    (hXi : ∀ i, MemLp (Xi i) 2 μ)
    (hindep : Pairwise fun i j ↦ Xi i ⟂ᵢ[μ] Xi j) (hO : MemLp O 2 μ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, centeredL2Norm (Xi i) μ ≤ a i)
    (hrec : X =ᵐ[μ] fun ω ↦ (∑ i, p i * Xi i ω) - O ω) :
    centeredL2Norm X μ ≤
      Real.sqrt (∑ i, (p i * a i) ^ 2) + lpNorm O 2 μ := by
  let S : Ω → ℝ := fun ω ↦ ∑ i, p i * Xi i ω
  have hS : MemLp S 2 μ :=
    memLp_finsetSum Finset.univ fun i _ ↦ (hXi i).const_mul (p i)
  have hSO : MemLp (fun ω ↦ S ω - O ω) 2 μ := hS.sub hO
  have hX : MemLp X 2 μ := by
    exact (memLp_congr_ae (by simpa [S] using hrec)).mpr hSO
  calc
    centeredL2Norm X μ = centeredL2Norm (fun ω ↦ S ω - O ω) μ :=
      centeredL2Norm_congr hX hSO (by simpa [S] using hrec)
    _ ≤ centeredL2Norm S μ + centeredL2Norm O μ :=
      centeredL2Norm_sub_le hS hO
    _ ≤ Real.sqrt (∑ i, (p i * a i) ^ 2) + lpNorm O 2 μ := by
      apply add_le_add
      · simpa [S] using centeredL2Norm_weighted_sum_le Xi p a hXi hindep ha0 ha
      · exact centeredL2Norm_le_lpNorm hO

/-- Mutual-independence form of the centered `L²` recurrence step. -/
theorem centeredL2Norm_recurrence_of_iIndepFun_le [Fintype ι]
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Xi : ι → Ω → ℝ) (O : Ω → ℝ) (p a : ι → ℝ)
    (hXi : ∀ i, MemLp (Xi i) 2 μ) (hindep : iIndepFun Xi μ) (hO : MemLp O 2 μ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, centeredL2Norm (Xi i) μ ≤ a i)
    (hrec : X =ᵐ[μ] fun ω ↦ (∑ i, p i * Xi i ω) - O ω) :
    centeredL2Norm X μ ≤
      Real.sqrt (∑ i, (p i * a i) ^ 2) + lpNorm O 2 μ :=
  centeredL2Norm_recurrence_le X Xi O p a hXi
    (pairwise_indepFun_of_iIndepFun hindep) hO ha0 ha hrec

section IdentDistrib

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}

/-- Identically distributed `L²` random variables have the same centered `L²` size. -/
theorem centeredL2Norm_eq_of_identDistrib [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hXY : IdentDistrib X Y μ ν)
    (hX : MemLp X 2 μ) :
    centeredL2Norm X μ = centeredL2Norm Y ν := by
  have hY : MemLp Y 2 ν := hXY.memLp_snd hX
  rw [centeredL2Norm_eq_sqrt_variance hX, centeredL2Norm_eq_sqrt_variance hY,
    hXY.variance_eq]

end IdentDistrib

end

end MinkowskiL2Recurrence

end BrownianImages
