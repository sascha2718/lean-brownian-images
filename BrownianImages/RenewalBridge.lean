/-
`thm:non-lattice-limit`: the bridge from this project's self-similar systems to the key
renewal theorem of `BrownianImages.Renewal`.

The vendored theorem
`AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm` takes six
hypotheses on the increment law.  This module discharges the ones that are properties of
the renewal measure `ϑ = ∑ p_i δ_{a_i}` alone; `KeyRenewalFourier` discharges the rest.

* `expTransform_renewalLaw`: the exponential transform of `ϑ` in closed form.
* `exists_expTransform_lt_one`: the strict exponential moment.  Its content is that the
  log-ratios are bounded away from zero, which is what `r_i < 1` gives.
* `not_nonlattice_renewalLaw`: the **refutation**.  The vendored theorem asks that `μ`
  charge no affine lattice `a + rℤ`, which is the strongly non-lattice condition its
  Fourier proof needs for `‖charFun μ t‖ < 1` off the origin.  A two-atom measure always
  charges one, so `ϑ` never satisfies it, and the vendored key renewal limit does not
  apply to a self-similar renewal measure.  What `thm:non-lattice-limit` needs is
  Feller's weaker condition, that the atoms lie on no lattice `dℤ` *through the origin*.

Beside `KeyRenewalFourier` and `Minkowski.TubeRenewalLimit`, which consume the key
renewal theorem, this is the only module of the library that mentions the vendored
namespace.
-/
import BrownianImages.SelfSimilar
import BrownianImages.Renewal

namespace BrownianImages

open MeasureTheory
open scoped ENNReal

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The exponential transform of the renewal measure is the weighted sum of the atom
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


/-! ### The vendored key renewal limit does not apply to `ϑ` -/

/-- **Refutation.** `AbsorptionCutoff.Renewal.Nonlattice` asks that `μ` charge no affine
lattice `a + rℤ`.  A measure carried by two atoms always charges one: take `a` to be the
first atom and `r` the gap between them.  So the renewal measure of a two-map self-similar
system never satisfies it, whatever the ratios, and the vendored key renewal theorem
cannot be applied to `ϑ`.

This is not a technicality of the formal statement.  The hypothesis is what gives
`‖charFun μ t‖ < 1` for `t ≠ 0`, and for `ϑ` that is false: at `t = 2π/(a₁ - a₀)` the two
atom phases align and the characteristic function has modulus one.  The Fourier route to
Blackwell's theorem needs a spread-out increment law; `thm:non-lattice-limit` needs
Feller's non-arithmetic condition, which forbids only lattices `dℤ` through the origin
and is satisfied by `ϑ` exactly when the log-ratios are rationally independent. -/
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
