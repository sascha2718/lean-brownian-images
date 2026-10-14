module

/-
The bridge from self-similar systems to the key renewal theorem used for the paper's
non-lattice profile limit.

The vendored theorem
`AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm` uses
`FellerNonlattice`, moment bounds and a strict exponential moment for the increment
law. This module proves the exponential-moment input for `ϑ = ∑ p_i δ_{α_i}`;
`KeyRenewalFourier` supplies Feller's condition under non-arithmeticity and assembles
the profile limit.

* `expTransform_renewalLaw`: the exponential transform of `ϑ` in closed form.
* `exists_expTransform_lt_one`: the strict exponential moment, using positivity of
  the finitely many log-ratios.
* `not_nonlattice_renewalLaw`: a counterexample to imposing the stronger `Nonlattice`
  condition, which excludes probability laws concentrated on any affine lattice
  `a + rℤ`. Every two-atom law is concentrated on such a lattice. The key renewal
  theorem instead uses `FellerNonlattice`, which allows non-arithmetic two-atom laws.
-/
public import BrownianImages.SelfSimilar
public import BrownianImages.Renewal

@[expose] public section

namespace BrownianImages

open MeasureTheory
open scoped ENNReal

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The exponential transform of the increment law is the weighted sum of the atom
transforms. -/
theorem expTransform_renewalLaw (s θ : ℝ) :
    AbsorptionCutoff.Renewal.expTransform θ (S.renewalLaw s)
      = ∑ i, ENNReal.ofReal (S.ratio i ^ s)
          * ENNReal.ofReal (Real.exp (-(θ * S.logRatio i))) := by
  rw [AbsorptionCutoff.Renewal.expTransform_def, renewalLaw, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (by fun_prop), smul_eq_mul]

/-- `∃ θ > 0` with `∫ e^{-θz} dϑ < 1`: the strict exponential moment the key renewal
theorem asks for.  The log-ratios are positive and finitely many, so they are bounded
below by some `m > 0`, and `∫ e^{-z} dϑ ≤ e^{-m} < 1`. -/
theorem exists_expTransform_lt_one [Nonempty ι] {s : ℝ} (hdim : S.IsDimension s) :
    ∃ θ : ℝ, 0 < θ ∧ AbsorptionCutoff.Renewal.expTransform θ (S.renewalLaw s) < 1 := by
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ S.logRatio
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hm : 0 < S.logRatio i₀ := S.logRatio_pos i₀
  refine ⟨1, one_pos, ?_⟩
  have hbound : ∀ i ∈ (Finset.univ : Finset ι),
      ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (Real.exp (-(1 * S.logRatio i)))
        ≤ ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (Real.exp (-S.logRatio i₀)) := by
    intro i _
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have := hmin i (Finset.mem_univ i)
    linarith
  calc AbsorptionCutoff.Renewal.expTransform 1 (S.renewalLaw s)
      = ∑ i, ENNReal.ofReal (S.ratio i ^ s)
          * ENNReal.ofReal (Real.exp (-(1 * S.logRatio i))) := S.expTransform_renewalLaw s 1
    _ ≤ ∑ i, ENNReal.ofReal (S.ratio i ^ s)
          * ENNReal.ofReal (Real.exp (-S.logRatio i₀)) := Finset.sum_le_sum hbound
    _ = (∑ i, ENNReal.ofReal (S.ratio i ^ s))
          * ENNReal.ofReal (Real.exp (-S.logRatio i₀)) := by rw [← Finset.sum_mul]
    _ = ENNReal.ofReal (Real.exp (-S.logRatio i₀)) := by
        rw [S.sum_ofReal_ratio_rpow hdim, one_mul]
    _ < 1 := by
        refine ENNReal.ofReal_lt_one.mpr ?_
        exact Real.exp_lt_one_iff.mpr (by linarith)


/-! ### Two-atom laws refute the stronger affine-lattice condition -/

/-- `AbsorptionCutoff.Renewal.Nonlattice` excludes probability laws concentrated on
an affine lattice `a + rℤ`. A two-atom law is concentrated on one: take `a` to be the
first atom and `r` the gap between the atoms. Thus the renewal law of a two-map system
never satisfies this stronger condition.

The key renewal theorem uses `FellerNonlattice`, whose characteristic function avoids
`1` off the origin and has modulus `1` at only countably many frequencies. The
non-arithmeticity of a self-similar system supplies these properties. For two distinct
log-ratios, the phases still align at `t = 2π/(α₁ - α₀)`, giving modulus `1`; the
counterexample therefore also explains why an everywhere strict modulus bound would
exclude systems covered by the paper's non-lattice profile limit. -/
theorem not_nonlattice_renewalLaw (S : System (Fin 2)) {s : ℝ} (hdim : S.IsDimension s) :
    ¬ AbsorptionCutoff.Renewal.Nonlattice (S.renewalLaw s) := by
  intro h
  refine h (S.logRatio 0) (S.logRatio 1 - S.logRatio 0) ?_
  set L : Set ℝ :=
    {x : ℝ | ∃ k : ℤ, x = S.logRatio 0 + k * (S.logRatio 1 - S.logRatio 0)} with hL
  have hmem : ∀ i : Fin 2, S.logRatio i ∈ L := by
    intro i
    fin_cases i
    · exact ⟨0, by simp⟩
    · exact ⟨1, by push_cast; ring⟩
  rw [renewalLaw_apply]
  have hone : ∀ i : Fin 2, (Measure.dirac (S.logRatio i)) L = 1 := by
    intro i
    rw [Measure.dirac_apply]
    exact Set.indicator_of_mem (hmem i) 1
  simp only [hone, mul_one]
  exact S.sum_ofReal_ratio_rpow hdim

end System

end BrownianImages
