/-
`thm:smoothing-injective` of `sec:smoothing`: the Fourier multipliers of the Gaussian
smoothing operator `T`.

`eq:fourier-multiplier` defines the `k`-th multiplier as an integral, `multInt`, and
`eq:gamma-multiplier` evaluates it in closed form, `gammaMult`.  Neither the evaluation,
which is the substitution `x = 1/(2η)`, nor the Fourier identity `T̂g(k) = M_k ĝ(k)` that
gives the multipliers their name is proved here: they are `audit_gamma_multiplier` and
`audit_fourier_multiplier`, both open.  What is proved is the sentence the paper draws
from the closed form, that neither of its two factors vanishes.  The Fourier
coefficients themselves are `fourierCoeffP` of `Defs`.

* `multInt`: the multiplier as the integral `eq:fourier-multiplier`.
* `gammaMult`: the closed form `eq:gamma-multiplier`.
* `gammaMult_ne_zero`: neither factor of the closed form vanishes, from
  `Complex.Gamma_ne_zero_of_re_pos`.
* `multInt_eq_gammaMult`: `eq:gamma-multiplier`, the evaluation of the multiplier
  integral.  The paper's substitution `x = 1/(2η)` is Mathlib's, in two steps on the
  Mellin transform: scaling by `2` contributes `2^{-w}` (`mellin_comp_mul_left`), the
  inversion reflects the exponent (`mellin_comp_inv`), and what is left is `Γ`
  (`Complex.GammaIntegral_eq_mellin`).  Every step is an unconditional identity of
  integrals, so no integrability side condition appears; `s < 1` enters only through
  `Re(1 - s + 2πik/p) = 1 - s > 0`.
* `smoothOp_periodic`: `Tg` is `p/2`-periodic, which is why its Fourier coefficients are
  taken at that period in `eq:fourier-multiplier`.
* `fourierCoeffP_eq_fourierCoeffOn`: the coefficient of `sec:smoothing` is Mathlib's
  `fourierCoeffOn`, which is what puts the `AddCircle` Fourier API, and with it the
  uniqueness theorem `thm:smoothing-injective` needs, within reach.
-/
import BrownianImages.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace BrownianImages

open Complex MeasureTheory

/-- The purely imaginary frequency `2πik/p` appearing in `eq:gamma-multiplier`. -/
noncomputable def freq (p : ℝ) (k : ℤ) : ℂ := 2 * Real.pi * Complex.I * k / p

/-- The frequency is purely imaginary. -/
@[simp] theorem freq_re (p : ℝ) (k : ℤ) : (freq p k).re = 0 := by
  simp [freq, Complex.div_re]

/-- `eq:fourier-multiplier`: the `k`-th Fourier multiplier of the smoothing operator,
`M_k = ∫₀^∞ φ(η) η^{-2πik/p} dη`. -/
noncomputable def multInt (s p : ℝ) (k : ℤ) : ℂ :=
  ∫ η in Set.Ioi (0 : ℝ), (kern s η : ℂ) * (η : ℂ) ^ (-freq p k)

/-- `eq:gamma-multiplier`: the closed form of the multiplier,
`2^{-s + 2πik/p} Γ(1 - s + 2πik/p)`. -/
noncomputable def gammaMult (s p : ℝ) (k : ℤ) : ℂ :=
  (2 : ℂ) ^ (-(s : ℂ) + freq p k) * Complex.Gamma (1 - (s : ℂ) + freq p k)

/-- Both factors of `eq:gamma-multiplier` are non-zero: the Gamma function has no zeros
in the right half plane, and the base of the power is non-zero.  This is the step of
`thm:smoothing-injective` that makes `T` injective. -/
theorem gammaMult_ne_zero {s : ℝ} (hs : s < 1) (p : ℝ) (k : ℤ) : gammaMult s p k ≠ 0 := by
  refine mul_ne_zero (mt (Complex.cpow_eq_zero_iff _ _).mp ?_) ?_
  · rintro ⟨h, -⟩; norm_num at h
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, freq_re]
    linarith


/-! ### The period of `Tg` -/

/-- `eq:periodic-smoothing`: smoothing halves the period.  The factor `2t` in the
argument of `g` is what turns a `p`-periodic `g` into a `p/2`-periodic `Tg`, and it is
why `eq:fourier-multiplier` takes the coefficient of `Tg` at period `p/2`. -/
theorem smoothOp_periodic {s p : ℝ} {g : ℝ → ℝ} (hper : Function.Periodic g p) :
    Function.Periodic (smoothOp s g) (p / 2) := by
  intro v
  have hfun : (fun η : ℝ => kern s η * g (2 * (v + p / 2) - Real.log η))
      = fun η : ℝ => kern s η * g (2 * v - Real.log η) := by
    funext η
    rw [show 2 * (v + p / 2) - Real.log η = (2 * v - Real.log η) + p by ring, hper]
  unfold smoothOp
  rw [hfun]


/-! ### The Fourier coefficient is Mathlib's -/

/-- The normalised period integral of `sec:smoothing` is Mathlib's `fourierCoeffOn` on
`[0, q]`.  Mathlib's Fourier theory for periodic functions lives on `AddCircle`, and this
is the bridge to it: `fourierBasis` is a Hilbert basis of `L²(AddCircle q)`, so a
continuous `q`-periodic function all of whose coefficients vanish is zero, which is the
Fourier uniqueness step of `thm:smoothing-injective`. -/
theorem fourierCoeffP_eq_fourierCoeffOn {q : ℝ} (hq : 0 < q) (g : ℝ → ℝ) (k : ℤ) :
    fourierCoeffP q g k = fourierCoeffOn hq (fun x => (g x : ℂ)) k := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, Complex.real_smul, Complex.ofReal_inv]
  rw [fourierCoeffP]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul]
  congr 2
  push_cast
  ring


/-! ### Fourier uniqueness -/

/-- `thm:smoothing-injective`, the uniqueness step: a continuous `q`-periodic function all
of whose Fourier coefficients vanish is zero.  The coefficients are those of
`sec:smoothing`; they are the coefficients of the lift of `g` to `AddCircle q`, and
`fourierBasis` is a Hilbert basis there, so the lift vanishes in `L²`, hence almost
everywhere, hence everywhere by continuity. -/
theorem eq_zero_of_fourierCoeffP_eq_zero {q : ℝ} (hq : 0 < q) {g : ℝ → ℝ}
    (hg : Continuous g) (hper : Function.Periodic g q)
    (h : ∀ k : ℤ, fourierCoeffP q g k = 0) (x : ℝ) : g x = 0 := by
  haveI : Fact (0 < q) := ⟨hq⟩
  have hperC : Function.Periodic (fun y : ℝ => (g y : ℂ)) q := fun y => by
    simp only []
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (hper y)
  set G : AddCircle q → ℂ := hperC.lift with hGdef
  have hGcoe : ∀ y : ℝ, G (y : AddCircle q) = (g y : ℂ) := fun y => hperC.lift_coe y
  have hGcont : Continuous G :=
    (Complex.continuous_ofReal.comp hg).quotient_liftOn' _
  have hcoeff : ∀ k : ℤ, fourierCoeff G k = 0 := by
    intro k
    rw [fourierCoeff_eq_intervalIntegral G k 0, zero_add]
    have hcongr : ∀ y ∈ Set.uIcc (0:ℝ) q,
        (fourier (-k) ((y : ℝ) : AddCircle q) : ℂ) • G (y : AddCircle q)
          = Complex.exp (-(2 * Real.pi * Complex.I * k * y / q)) * (g y : ℂ) := by
      intro y _
      rw [hGcoe y, fourier_coe_apply, smul_eq_mul]
      congr 2
      push_cast
      ring
    rw [intervalIntegral.integral_congr hcongr]
    have hk := h k
    simp only [fourierCoeffP] at hk
    rw [Complex.real_smul]
    push_cast
    rw [one_div]
    exact hk
  obtain ⟨C, hC⟩ := (isCompact_univ (X := AddCircle q)).exists_bound_of_continuousOn
    hGcont.continuousOn
  have hmem : MeasureTheory.MemLp G 2 (AddCircle.haarAddCircle (T := q)) :=
    MeasureTheory.MemLp.of_bound hGcont.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hC z (Set.mem_univ z))
  have hrepr : fourierBasis.repr (hmem.toLp G) = 0 := by
    ext k
    rw [fourierBasis_repr, fourierCoeff_congr_ae hmem.coeFn_toLp]
    simpa using hcoeff k
  have hzero : hmem.toLp G = 0 := by
    apply (fourierBasis (T := q)).repr.injective
    rw [hrepr, map_zero]
  have hae : G =ᵐ[AddCircle.haarAddCircle (T := q)] 0 := by
    have h1 := hmem.coeFn_toLp
    rw [hzero] at h1
    exact h1.symm.trans (MeasureTheory.Lp.coeFn_zero ℂ 2 _)
  have hGzero : G = 0 := (hGcont.ae_eq_iff_eq _ continuous_const).mp hae
  have : (g x : ℂ) = 0 := by rw [← hGcoe x, hGzero]; rfl
  exact_mod_cast this


/-! ### The substitution `x = 1/(2η)` -/

/-- The integrand of Euler's integral, `x ↦ e^{-x}`, complex valued. -/
noncomputable def expNeg : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)

/-- Its composition with the inversion, `x ↦ e^{-1/x}`. -/
noncomputable def expNegInv : ℝ → ℂ := fun x => (Real.exp (-x⁻¹) : ℂ)

/-- `expNegInv` is `expNeg` composed with inversion, by definition. -/
theorem expNegInv_eq : expNegInv = fun x => expNeg x⁻¹ := rfl

/-- Euler's integral as a Mellin transform: on the right half plane the Mellin transform
of `x ↦ e^{-x}` is `Γ`. -/
theorem mellin_expNeg {z : ℂ} (hz : 0 < z.re) : mellin expNeg z = Complex.Gamma z := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral_eq_mellin]
  rfl

/-- The substitution `x = 1/(2η)` of `eq:gamma-multiplier`, as an identity of Mellin
transforms. -/
theorem mellin_expNegHalfInv (w : ℂ) (hw : 0 < (-w).re) :
    mellin (fun η : ℝ => ((Real.exp (-(2 * η)⁻¹) : ℝ) : ℂ)) w
      = (2 : ℂ) ^ (-w) * Complex.Gamma (-w) := by
  have hscale : (fun η : ℝ => ((Real.exp (-(2 * η)⁻¹) : ℝ) : ℂ))
      = fun η : ℝ => expNegInv (2 * η) := rfl
  rw [hscale, mellin_comp_mul_left expNegInv w (by norm_num : (0:ℝ) < 2), expNegInv_eq,
    mellin_comp_inv expNeg w, mellin_expNeg hw]
  simp [smul_eq_mul]

/-- `eq:gamma-multiplier`: the multiplier integral evaluates in closed form. -/
theorem multInt_eq_gammaMult {s : ℝ} (hs1 : s < 1) (p : ℝ) (k : ℤ) :
    multInt s p k = gammaMult s p k := by
  have hre : 0 < (-((s : ℂ) - 1 - freq p k)).re := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, freq_re]
    linarith
  have hmellin : multInt s p k
      = 2⁻¹ * mellin (fun η : ℝ => ((Real.exp (-(2 * η)⁻¹) : ℝ) : ℂ))
          ((s : ℂ) - 1 - freq p k) := by
    rw [multInt, mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun η hη => ?_
    have hη0 : (0:ℝ) < η := hη
    have hne : (η : ℂ) ≠ 0 := by exact_mod_cast hη0.ne'
    rw [kern, smul_eq_mul,
      show ((s : ℂ) - 1 - freq p k) - 1 = ((s - 2 : ℝ) : ℂ) + (-freq p k) by push_cast; ring,
      Complex.cpow_add _ _ hne, ← Complex.ofReal_cpow hη0.le]
    push_cast
    ring
  rw [hmellin, mellin_expNegHalfInv _ hre, gammaMult,
    show -((s : ℂ) - 1 - freq p k) = 1 + (-(s : ℂ) + freq p k) by ring,
    Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one,
    show (1:ℂ) + (-(s : ℂ) + freq p k) = 1 - (s : ℂ) + freq p k by ring]
  ring

/-- `thm:smoothing-injective`, the multiplier statement: no Fourier multiplier of the
smoothing operator vanishes. -/
theorem multInt_ne_zero {s : ℝ} (hs1 : s < 1) (p : ℝ) (k : ℤ) : multInt s p k ≠ 0 := by
  rw [multInt_eq_gammaMult hs1 p k]
  exact gammaMult_ne_zero hs1 p k

end BrownianImages
