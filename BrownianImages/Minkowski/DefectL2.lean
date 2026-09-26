/-
`thm:neighbourhood-concentration` of `sec:reconstruction`: the interpolation that turns
a first-moment and a third-moment bound for a non-negative random variable into an `L²`
bound, `X² ≤ T X + T⁻¹ X³` for every `T > 0`.  The concentration proof applies it to the
error `F_{r,u}`, whose expectation decays and whose third moment stays bounded.

* `memLp_two_and_lpNorm_le_of_first_third`: the interpolation.
-/
import BrownianImages.Minkowski.L2Recurrence

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-! ### Elementary first/third-moment interpolation -/

/-- The pointwise interpolation inequality used to pass from first and third
moments to a second moment. -/
theorem sq_le_scale_mul_add_inv_mul_cube {x T : ℝ} (hx : 0 ≤ x)
    (hT : 0 < T) :
    x ^ 2 ≤ T * x + T⁻¹ * x ^ 3 := by
  have hfactor : 0 ≤ T⁻¹ * x * (T - x) ^ 2 :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hT.le) hx) (sq_nonneg _)
  have hid : T * x + T⁻¹ * x ^ 3 - 2 * x ^ 2 =
      T⁻¹ * x * (T - x) ^ 2 := by
    field_simp [hT.ne']
    ring
  rw [← hid] at hfactor
  nlinarith [sq_nonneg x]

/-- Abstract interpolation lemma.  The constants `A` and `B` bound the first
and third moments, respectively. -/
theorem memLp_two_and_lpNorm_le_of_first_third
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → ℝ} {T A B : ℝ}
    (hX : Integrable X P) (hX3 : Integrable (fun omega => X omega ^ 3) P)
    (hX0 : ∀ᵐ omega ∂P, 0 ≤ X omega) (hT : 0 < T)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : (∫ omega, X omega ∂P) ≤ A)
    (hthird : (∫ omega, X omega ^ 3 ∂P) ≤ B) :
    MemLp X 2 P ∧ lpNorm X 2 P ≤ Real.sqrt (T * A + T⁻¹ * B) := by
  have hdom : Integrable
      (fun omega => T * X omega + T⁻¹ * X omega ^ 3) P :=
    (hX.const_mul T).add (hX3.const_mul T⁻¹)
  have hsq : Integrable (fun omega => X omega ^ 2) P := by
    refine Integrable.mono' hdom (hX.aestronglyMeasurable.pow 2) ?_
    filter_upwards [hX0] with omega homega
    change |X omega ^ 2| ≤ T * X omega + T⁻¹ * X omega ^ 3
    rw [abs_of_nonneg (sq_nonneg (X omega))]
    exact sq_le_scale_mul_add_inv_mul_cube homega hT
  have hmem : MemLp X 2 P :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).2 hsq
  have hintegral : (∫ omega, X omega ^ 2 ∂P) ≤ T * A + T⁻¹ * B := by
    calc
      (∫ omega, X omega ^ 2 ∂P) ≤
          ∫ omega, (T * X omega + T⁻¹ * X omega ^ 3) ∂P := by
        exact integral_mono_ae hsq hdom
          (hX0.mono fun omega homega =>
            sq_le_scale_mul_add_inv_mul_cube homega hT)
      _ = T * (∫ omega, X omega ∂P) +
          T⁻¹ * (∫ omega, X omega ^ 3 ∂P) := by
        rw [integral_add (hX.const_mul T) (hX3.const_mul T⁻¹),
          integral_const_mul, integral_const_mul]
      _ ≤ T * A + T⁻¹ * B :=
        add_le_add (mul_le_mul_of_nonneg_left hfirst hT.le)
          (mul_le_mul_of_nonneg_left hthird (inv_nonneg.mpr hT.le))
  have hright : 0 ≤ T * A + T⁻¹ * B :=
    add_nonneg (mul_nonneg hT.le hA)
      (mul_nonneg (inv_nonneg.mpr hT.le) hB)
  refine ⟨hmem, ?_⟩
  apply (sq_le_sq₀ lpNorm_nonneg (Real.sqrt_nonneg _)).mp
  rw [MinkowskiL2Recurrence.lpNorm_two_sq hmem, Real.sq_sqrt hright]
  exact hintegral

end

end BrownianImages
