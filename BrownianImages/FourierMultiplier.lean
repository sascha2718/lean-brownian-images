/-
`eq:fourier-multiplier` of `sec:smoothing`: the Fourier identity `T̂g(k) = M_k ĝ(k)`.

The coefficient of `Tg` is taken at its own period `p/2` and that of `g` at `p`.  The
proof is the paper's: shift the argument of `g` inside the period integral, which costs
exactly the character at `log η` and leaves a bracket independent of `η`; substitute
`u = 2t`; and swap the two integrals by Fubini, with integrability from the domination
`|φ(η) g(·)| ≤ M φ(η)` on a finite measure in `t`.

* `chr`: the character of `fourierCoeffP`, with `chr_log` identifying it at `log η` with
  the power `η^{-2πik/p}` of the multiplier integral.
* `chr_shift`, `chr_double`: the two integral manipulations.
* `fourierCoeffP_smoothOp`: the identity.
-/
import BrownianImages.Kernel
import BrownianImages.Multiplier
import BrownianImages.Smoothing

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The character of `fourierCoeffP` -/

/-- The character `x ↦ e^{-2πikx/p}` of the Fourier coefficient `fourierCoeffP`. -/
noncomputable def chr (p : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * k * x / p))

theorem chr_add (p : ℝ) (k : ℤ) (x y : ℝ) :
    chr p k (x + y) = chr p k x * chr p k y := by
  rw [chr, chr, chr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chr_continuous (p : ℝ) (k : ℤ) : Continuous (chr p k) := by
  have h : Continuous fun x : ℝ =>
      -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ) / (p : ℂ)) :=
    ((continuous_const.mul Complex.continuous_ofReal).div_const _).neg
  exact Complex.continuous_exp.comp h

theorem chr_norm (p : ℝ) (k : ℤ) (x : ℝ) : ‖chr p k x‖ = 1 := by
  have h : (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ) / (p : ℂ)))
      = ((-(2 * Real.pi * k * x / p) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [chr, h, Complex.norm_exp_ofReal_mul_I]

theorem chr_period_one {p : ℝ} (hp : p ≠ 0) (k : ℤ) : chr p k p = 1 := by
  have hp' : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  have h : (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (p : ℂ) / (p : ℂ)))
      = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
    push_cast
    ring
  rw [chr, h, Complex.exp_int_mul_two_pi_mul_I]

theorem chr_periodic {p : ℝ} (hp : p ≠ 0) (k : ℤ) : Function.Periodic (chr p k) p := by
  intro x
  rw [chr_add, chr_period_one hp, mul_one]

/-- The character at `log η` is the power `η^{-2πik/p}` of the multiplier integral. -/
theorem chr_log (p : ℝ) (k : ℤ) {η : ℝ} (hη : 0 < η) :
    chr p k (Real.log η) = (η : ℂ) ^ (-freq p k) := by
  have hne : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hη.le, chr, freq]
  congr 1
  ring

/-! ### The two integral manipulations -/

/-- Shifting the argument of a `p`-periodic `g` multiplies the period integral by the
character: this is the step that makes the bracket of `eq:fourier-multiplier`
independent of `η`. -/
theorem chr_shift {p : ℝ} (hp : 0 < p) (k : ℤ) {g : ℝ → ℝ}
    (hper : Function.Periodic g p) (c : ℝ) :
    (∫ v in (0:ℝ)..(p/2), chr p k (2 * v) * ((g (2 * v - c) : ℝ) : ℂ))
      = chr p k c * ∫ v in (0:ℝ)..(p/2), chr p k (2 * v) * ((g (2 * v) : ℝ) : ℂ) := by
  set ψ : ℝ → ℂ := fun v => chr p k (2 * v) * ((g (2 * v - c) : ℝ) : ℂ) with hψdef
  have hψper : Function.Periodic ψ (p / 2) := by
    intro v
    simp only [hψdef]
    rw [show 2 * (v + p / 2) = 2 * v + p by ring, chr_periodic hp.ne' k (2 * v),
      show 2 * v + p - c = (2 * v - c) + p by ring, hper]
  calc (∫ v in (0:ℝ)..(p/2), ψ v)
      = ∫ v in (c/2)..(c/2 + p/2), ψ v := by
        have h := hψper.intervalIntegral_add_eq 0 (c / 2)
        rwa [zero_add] at h
    _ = ∫ v in (0:ℝ)..(p/2), ψ (v + c/2) := by
        rw [intervalIntegral.integral_comp_add_right ψ (c/2), zero_add,
          add_comm (p/2) (c/2)]
    _ = ∫ v in (0:ℝ)..(p/2), chr p k c * (chr p k (2 * v) * ((g (2 * v) : ℝ) : ℂ)) := by
        refine intervalIntegral.integral_congr fun v _ => ?_
        simp only [hψdef]
        rw [show 2 * (v + c/2) = 2 * v + c by ring, chr_add,
          show 2 * v + c - c = 2 * v by ring]
        ring
    _ = chr p k c * ∫ v in (0:ℝ)..(p/2), chr p k (2 * v) * ((g (2 * v) : ℝ) : ℂ) :=
        intervalIntegral.integral_const_mul _ _

/-- The substitution `u = 2t` turning the period integral of `Tg` at period `p/2` into
the period integral of `g` at period `p`. -/
theorem chr_double (p : ℝ) (k : ℤ) (g : ℝ → ℝ) :
    (∫ v in (0:ℝ)..(p/2), chr p k (2 * v) * ((g (2 * v) : ℝ) : ℂ))
      = (2:ℝ)⁻¹ • ∫ u in (0:ℝ)..p, chr p k u * ((g u : ℝ) : ℂ) := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := p/2) (c := (2:ℝ))
    (fun u => chr p k u * ((g u : ℝ) : ℂ)) two_ne_zero
  rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (p/2) = p by ring] at h
  exact h

/-! ### The integrand of the double integral -/

/-- The integrand of the Fubini step of `eq:fourier-multiplier`. -/
noncomputable def fker (s p : ℝ) (k : ℤ) (g : ℝ → ℝ) (v η : ℝ) : ℂ :=
  chr p k (2 * v) * ((kern s η : ℝ) : ℂ) * ((g (2 * v - Real.log η) : ℝ) : ℂ)

theorem measurable_kern (s : ℝ) : Measurable (kern s) := by
  unfold kern; fun_prop

theorem measurable_uncurry_fker {s p : ℝ} (k : ℤ) {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (fker s p k g)) := by
  have h1 : Measurable fun z : ℝ × ℝ => chr p k (2 * z.1) :=
    (chr_continuous p k).measurable.comp (measurable_fst.const_mul 2)
  have h2 : Measurable fun z : ℝ × ℝ => ((kern s z.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp ((measurable_kern s).comp measurable_snd)
  have h3 : Measurable fun z : ℝ × ℝ => ((g (2 * z.1 - Real.log z.2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (hg.measurable.comp
      ((measurable_fst.const_mul 2).sub (Real.measurable_log.comp measurable_snd)))
  exact (h1.mul h2).mul h3

theorem integrable_uncurry_fker {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (k : ℤ) {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    Integrable (Function.uncurry (fker s p k g))
      ((volume.restrict (Set.Ioc (0:ℝ) (p/2))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) (p/2))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp
  have hconst : Integrable (fun _ : ℝ => M) (volume.restrict (Set.Ioc (0:ℝ) (p/2))) :=
    integrable_const M
  have hkern : Integrable (kern s) (volume.restrict (Set.Ioi (0:ℝ))) :=
    kern_integrableOn hs0 hs1
  have hbig : Integrable (fun z : ℝ × ℝ => M * kern s z.2)
      ((volume.restrict (Set.Ioc (0:ℝ) (p/2))).prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
    hconst.mul_prod hkern
  refine Integrable.mono' hbig (measurable_uncurry_fker k hg).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with z hz
  have hz2 : (0:ℝ) < z.2 := hz.2
  have hk : 0 < kern s z.2 := kern_pos hz2
  have hnorm : ‖Function.uncurry (fker s p k g) z‖
      = kern s z.2 * |g (2 * z.1 - Real.log z.2)| := by
    show ‖fker s p k g z.1 z.2‖ = _
    rw [fker]
    rw [norm_mul, norm_mul, chr_norm, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hk, one_mul]
  rw [hnorm]
  calc kern s z.2 * |g (2 * z.1 - Real.log z.2)| ≤ kern s z.2 * M :=
        mul_le_mul_of_nonneg_left (hM _) hk.le
    _ = M * kern s z.2 := mul_comm _ _

/-! ### The Fourier identity -/

/-- `eq:fourier-multiplier`: the Fourier coefficients of `Tg` at period `p/2` are those
of `g` at period `p` scaled by the multiplier `M_k`. -/
theorem fourierCoeffP_smoothOp {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hbdd : ∃ M, ∀ x, |g x| ≤ M)
    (hper : Function.Periodic g p) (k : ℤ) :
    fourierCoeffP (p/2) (smoothOp s g) k = multInt s p k * fourierCoeffP p g k := by
  obtain ⟨M, hM⟩ := hbdd
  have hpne : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  set A : ℂ := ∫ u in (0:ℝ)..p, chr p k u * ((g u : ℝ) : ℂ) with hA
  have hR : fourierCoeffP p g k = (p : ℂ)⁻¹ * A := rfl
  -- The coefficient of `Tg`, with the character rewritten at period `p`.
  have hc : ((p/2 : ℝ) : ℂ) = (p : ℂ)/2 := by push_cast; ring
  have hL : fourierCoeffP (p/2) (smoothOp s g) k
      = ((p : ℂ)/2)⁻¹ * ∫ v in (0:ℝ)..(p/2), chr p k (2 * v) * ((smoothOp s g v : ℝ) : ℂ) := by
    rw [fourierCoeffP, hc]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    have hexp : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (v : ℂ) / ((p : ℂ)/2)))
        = chr p k (2 * v) := by
      rw [chr]
      congr 1
      push_cast
      field_simp
    rw [hexp]
  -- The coercion pushed inside `Tg`.
  have hsm : ∀ v : ℝ, ((smoothOp s g v : ℝ) : ℂ)
      = ∫ η in Set.Ioi (0:ℝ), ((kern s η : ℝ) : ℂ) * ((g (2 * v - Real.log η) : ℝ) : ℂ) := by
    intro v
    rw [smoothOp, ← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have hL2 : fourierCoeffP (p/2) (smoothOp s g) k
      = ((p : ℂ)/2)⁻¹ * ∫ v in (0:ℝ)..(p/2), ∫ η in Set.Ioi (0:ℝ), fker s p k g v η := by
    rw [hL]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    rw [hsm v, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun η _ => ?_
    rw [fker]
    ring
  -- Fubini.
  have hIoc : ∀ f : ℝ → ℂ, (∫ v in (0:ℝ)..(p/2), f v) = ∫ v in Set.Ioc (0:ℝ) (p/2), f v :=
    fun f => intervalIntegral.integral_of_le (by linarith)
  have hswap : (∫ v in Set.Ioc (0:ℝ) (p/2), ∫ η in Set.Ioi (0:ℝ), fker s p k g v η)
      = ∫ η in Set.Ioi (0:ℝ), ∫ v in Set.Ioc (0:ℝ) (p/2), fker s p k g v η :=
    integral_integral_swap (integrable_uncurry_fker hs0 hs1 k hg hM)
  -- The inner integral, by the shift and the substitution.
  have hstep : ∀ η ∈ Set.Ioi (0:ℝ), (∫ v in Set.Ioc (0:ℝ) (p/2), fker s p k g v η)
      = (((kern s η : ℝ) : ℂ) * (η : ℂ) ^ (-freq p k)) * ((2:ℝ)⁻¹ • A) := by
    intro η hη
    rw [← hIoc]
    have h1 : (∫ v in (0:ℝ)..(p/2), fker s p k g v η)
        = ((kern s η : ℝ) : ℂ)
          * ∫ v in (0:ℝ)..(p/2), chr p k (2 * v) * ((g (2 * v - Real.log η) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ => ?_
      rw [fker]
      ring
    rw [h1, chr_shift hp k hper (Real.log η), chr_double p k g, ← hA,
      chr_log p k hη]
    ring
  have houter : (∫ η in Set.Ioi (0:ℝ), ∫ v in Set.Ioc (0:ℝ) (p/2), fker s p k g v η)
      = multInt s p k * ((2:ℝ)⁻¹ • A) := by
    rw [multInt, ← MeasureTheory.integral_mul_const]
    exact setIntegral_congr_fun measurableSet_Ioi hstep
  rw [hL2, hIoc, hswap, houter, hR, Complex.real_smul]
  push_cast
  field_simp


/-! ### `thm:smoothing-injective`, now unconditional -/

/-- `thm:smoothing-injective`, kernel form: `Tg = 0` forces `g = 0`. -/
theorem smoothOp_eq_zero {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (h : ∀ v, smoothOp s g v = 0) : ∀ x, g x = 0 :=
  kernel_trivial_of_multiplier hs0 hs1 hp hg hper
    (fun k => fourierCoeffP_smoothOp hs0 hs1 hp hg
      (exists_bound_of_continuous_periodic hp hg hper) hper k)
    (fun k => multInt_ne_zero hs1 p k) h

/-- `thm:smoothing-injective`: `T` is injective on the continuous `p`-periodic
functions. -/
theorem smoothOp_injective {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hper₁ : Function.Periodic g₁ p) (hper₂ : Function.Periodic g₂ p)
    (h : ∀ v, smoothOp s g₁ v = smoothOp s g₂ v) : ∀ x, g₁ x = g₂ x :=
  injective_of_multiplier hs0 hs1 hp
    (fun _ hg hbdd hper k => fourierCoeffP_smoothOp hs0 hs1 hp hg hbdd hper k)
    (fun k => multInt_ne_zero hs1 p k) hg₁ hg₂ hper₁ hper₂ h

/-- `thm:smoothing-injective`, the stated consequence: smoothing preserves
non-constancy. -/
theorem smoothOp_nonconstant {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (hne : ∃ x y, g x ≠ g y) : ∃ v w, smoothOp s g v ≠ smoothOp s g w :=
  nonconstant_of_multiplier hs0 hs1 hp
    (fun _ hg hbdd hper k => fourierCoeffP_smoothOp hs0 hs1 hp hg hbdd hper k)
    (fun k => multInt_ne_zero hs1 p k) hg hper hne

end BrownianImages
