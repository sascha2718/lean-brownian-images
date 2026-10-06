/-
`eq:two-contraction-periodic` of `thm:two-contraction-formula`: in the lattice case the
expected profile of the two-contraction family is asymptotic to an explicit absolutely
convergent Fourier series.

The Fourier coefficients of the lattice limit `G̃` of `LatticeProfile` are read off the
renewal equation, as in the tex: the average of `G(w) e^{-iξw}` over `[0, T]` converges to
`m⁻¹ ẑ(ξ)` whenever every delay `a_i` is a multiple of `2π/ξ` (`eq:renewal-average`), and
it also converges to the coefficient of `G̃`.  Absolute convergence comes from
`|Γ(1 - ζ)| ≤ Γ(2 - s)/|1 - ζ|`, so the coefficients are `O(k⁻²)`.

* `hasSum_fourierCoeffP`: a continuous periodic function with summable coefficients is
  the sum of its Fourier series.
* `tendsto_avg_of_periodic`: the Cesàro mean of a continuous periodic function.
* `norm_Gamma_le`: `|Γ(z)| ≤ Γ(Re z)`.
* `System.IsNatural.tendsto_avg_G_char`: the renewal average with a character.
* `System.IsNatural.fourierCoeffP_latticeLimit`: the coefficients of the lattice limit.
* `pairSystem_integral_renewalDefect_char`: the forcing transform
  `eq:two-contraction-forcing-transform`.
* `twoContractionCoeff`, `pairSystem_periodic`: `eq:two-contraction-periodic`.
* `System.nonArithmetic_or_exists_lattice`: every system is non-lattice or has a span.
-/
import BrownianImages.TwoContraction.Formula
import BrownianImages.LatticeProfile
import BrownianImages.FourierMultiplier
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

namespace BrownianImages

open MeasureTheory Filter Set Complex
open scoped Topology ENNReal Interval

noncomputable section

/-! ### Fourier inversion -/

/-- **Fourier inversion for summable coefficients**: a continuous `q`-periodic function
whose Fourier coefficients are summable is the sum of its Fourier series at every point. -/
theorem hasSum_fourierCoeffP {q : ℝ} (hq : 0 < q) {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g q) (hsum : Summable (fourierCoeffP q g)) (x : ℝ) :
    HasSum (fun k : ℤ => fourierCoeffP q g k * Complex.exp (2 * Real.pi * I * k * x / q))
      (g x : ℂ) := by
  have : Fact (0 < q) := ⟨hq⟩
  have hperC : Function.Periodic (fun y : ℝ => (g y : ℂ)) q := fun y => by
    simp only []
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (hper y)
  set G : AddCircle q → ℂ := hperC.lift with hGdef
  have hGcoe : ∀ y : ℝ, G (y : AddCircle q) = (g y : ℂ) := fun y => hperC.lift_coe y
  have hGcont : Continuous G :=
    (Complex.continuous_ofReal.comp hg).quotient_liftOn' _
  set F : C(AddCircle q, ℂ) := ⟨G, hGcont⟩ with hF
  have hcoeff : ∀ k : ℤ, fourierCoeff F k = fourierCoeffP q g k := by
    intro k
    show fourierCoeff G k = _
    rw [fourierCoeff_eq_intervalIntegral G k 0, zero_add]
    have hcongr : ∀ y ∈ Set.uIcc (0:ℝ) q,
        (fourier (-k) ((y : ℝ) : AddCircle q) : ℂ) • G (y : AddCircle q)
          = Complex.exp (-(2 * Real.pi * Complex.I * k * y / q)) * (g y : ℂ) := by
      intro y _
      rw [hGcoe y, fourier_coe_apply, smul_eq_mul]
      congr 2
      push_cast
      ring
    rw [intervalIntegral.integral_congr hcongr, fourierCoeffP, Complex.real_smul]
    push_cast
    rw [one_div]
  have hsumF : Summable (fourierCoeff F) := by
    have : fourierCoeff F = fourierCoeffP q g := funext hcoeff
    rw [this]; exact hsum
  have h := has_pointwise_sum_fourier_series_of_summable hsumF (x : AddCircle q)
  have hval : F (x : AddCircle q) = (g x : ℂ) := hGcoe x
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  rw [hcoeff k, fourier_coe_apply, smul_eq_mul]

/-! ### The mean of a periodic function -/

/-- The Cesàro mean of a continuous `q`-periodic function is its mean over one period. -/
theorem tendsto_avg_of_periodic {q : ℝ} (hq : 0 < q) {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f q) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ u in (0:ℝ)..T, f u) atTop
      (𝓝 (q⁻¹ • ∫ u in (0:ℝ)..q, f u)) := by
  set I := ∫ u in (0:ℝ)..q, f u with hI
  set F : ℝ → ℂ := fun T => (∫ u in (0:ℝ)..T, f u) - (T / q) • I with hFdef
  have hint : ∀ a b, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have hFper : Function.Periodic F q := by
    intro T
    simp only [hFdef]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T (T + q)),
      hper.intervalIntegral_add_eq T 0, zero_add, ← hI, add_div, div_self hq.ne', add_smul,
      one_smul]
    abel
  have hFc : Continuous F :=
    (intervalIntegral.continuous_primitive (fun a b => hint a b) 0).sub
      ((continuous_id.div_const q).smul continuous_const)
  obtain ⟨B, hB⟩ : ∃ B, ∀ T, ‖F T‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hFper.compact_of_continuous hq.ne' hFc).isBounded.exists_norm_le
    exact ⟨B, fun T => hB _ (Set.mem_range_self T)⟩
  have hFlim : Tendsto (fun T : ℝ => T⁻¹ • F T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := B)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hT), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hB T) (inv_pos.2 hT).le
  have h := hFlim.add (tendsto_const_nhds (x := q⁻¹ • I))
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [hFdef, smul_sub, smul_smul]
  rw [show T⁻¹ * (T / q) = q⁻¹ by field_simp]
  abel

/-! ### A bound on `Γ` -/

/-- `|Γ(z)| ≤ Γ(Re z)` in the right half plane, from the Euler integral. -/
theorem norm_Gamma_le {z : ℂ} (hz : 0 < z.re) : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-! ### The renewal average with a character -/

namespace System

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

/-- **`eq:renewal-average` of `thm:renewal-average`.**  If every delay satisfies
`e^{iξ a_i} = 1`,
the averages of `G(w) e^{-iξw}` over `[0, T]` converge to `m⁻¹ ∫ z(w) e^{-iξw} dw`: the
character passes through the renewal equation unchanged. -/
theorem IsNatural.tendsto_avg_G_char {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {ξ : ℝ}
    (hξ : ∀ i, Complex.exp (I * ξ * S.logRatio i) = 1) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ u in (0:ℝ)..T,
        (G s μ u : ℂ) * Complex.exp (-(I * ξ * u))) atTop
      (𝓝 ((S.renewalMean s)⁻¹ • ∫ w, (S.renewalDefect s μ w : ℂ) *
        Complex.exp (-(I * ξ * w)))) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  have hsosc := hosc.strongOpenSetCondition S hμ.attractor
  have hGc := continuous_G hs0 hA
  have hchar : ∀ w : ℝ, ‖Complex.exp (-(I * ξ * w))‖ = 1 := by
    intro w
    rw [Complex.norm_exp]
    simp
  have hgc : Continuous fun w : ℝ => (G s μ w : ℂ) * Complex.exp (-(I * ξ * w)) :=
    (Complex.continuous_ofReal.comp hGc).mul (by fun_prop)
  have hgb : ∀ w, ‖(G s μ w : ℂ) * Complex.exp (-(I * ξ * w))‖ ≤ A := fun w => by
    rw [norm_mul, hchar, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_G_le hs0 hA w
  have hint : IntegrableOn (fun w : ℝ => (G s μ w : ℂ) * Complex.exp (-(I * ξ * w)))
      (Iic 0) := by
    refine (integrableOn_exp_mul_Iic hs0 0).mono' hgc.aestronglyMeasurable ?_
    filter_upwards with w
    rw [norm_mul, hchar, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (G_nonneg w)]
    exact G_le_exp hs0.le le_rfl
  have hdef : (fun w : ℝ => (G s μ w : ℂ) * Complex.exp (-(I * ξ * w))
        - ∑ i, (S.ratio i ^ s) • ((G s μ (w - S.logRatio i) : ℂ) *
          Complex.exp (-(I * ξ * ((w - S.logRatio i : ℝ) : ℂ)))))
      = fun w => (S.renewalDefect s μ w : ℂ) * Complex.exp (-(I * ξ * w)) := by
    funext w
    have hsh : ∀ i, Complex.exp (-(I * ξ * ((w - S.logRatio i : ℝ) : ℂ)))
        = Complex.exp (-(I * ξ * w)) := by
      intro i
      rw [show -(I * ξ * ((w - S.logRatio i : ℝ) : ℂ))
          = -(I * ξ * w) + I * ξ * S.logRatio i by push_cast; ring,
        Complex.exp_add, hξ i, mul_one]
    simp only [hsh, System.renewalDefect, System.renewalConv, Complex.real_smul]
    push_cast
    rw [sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have hzc : Continuous (S.renewalDefect s μ) := by
    refine hGc.sub (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul (hGc.comp (continuous_id.sub continuous_const))
  have hz : Integrable (fun w : ℝ => (S.renewalDefect s μ w : ℂ) *
      Complex.exp (-(I * ξ * w))) := by
    refine (integrable_renewalDefect S hsosc hs0 hs1 hdim hμ).norm.mono'
      ((Complex.continuous_ofReal.comp hzc).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul, hchar, mul_one, Complex.norm_real]
  have h := tendsto_avg_of_renewal (E := ℂ) hgc hgb hint (fun i => S.ratio i ^ s)
    S.logRatio (fun i => (Real.rpow_pos_of_pos (S.ratio_pos i) s).le) hdim S.logRatio_pos
    (by rw [hdef]; exact hz)
  rw [hdef] at h
  exact h

/-- **The Fourier coefficients of the lattice limit**: if `G - g → 0` for a continuous
`h`-periodic `g`, where `h` spans the lattice of the log-ratios, then
`ĝ(k) = m⁻¹ ∫ z(w) e^{-2πikw/h} dw`.  Both sides are the limit of the averages of
`G(w) e^{-2πikw/h}`. -/
theorem IsNatural.fourierCoeffP_latticeLimit {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgp : Function.Periodic g h) (hglim : Tendsto (fun w => G s μ w - g w) atTop (𝓝 0))
    (k : ℤ) :
    fourierCoeffP h g k = (S.renewalMean s)⁻¹ • ∫ w, (S.renewalDefect s μ w : ℂ) *
      Complex.exp (-(I * (2 * Real.pi * k / h : ℝ) * w)) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  have hGc := continuous_G hs0 hA
  set ξ : ℝ := 2 * Real.pi * k / h with hξdef
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  -- every delay is a multiple of `h`, so the character is trivial on the delays
  have hξ : ∀ i, Complex.exp (I * ξ * S.logRatio i) = 1 := by
    intro i
    have hmem : S.logRatio i ∈ AddSubgroup.zmultiples h := by
      rw [← hlat]; exact AddSubgroup.subset_closure (Set.mem_range_self i)
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
    rw [← hn, zsmul_eq_mul, hξdef]
    have : I * ((2 * Real.pi * k / h : ℝ) : ℂ) * ((n * h : ℝ) : ℂ)
        = ((k * n : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hchar : ∀ w : ℝ, ‖Complex.exp (-(I * ξ * w))‖ = 1 := by
    intro w
    rw [Complex.norm_exp]
    simp
  have h1 := hμ.tendsto_avg_G_char S hs0 hs1 hosc hdim hξ
  -- the periodic part
  have hfper : Function.Periodic (fun u : ℝ => (g u : ℂ) * Complex.exp (-(I * ξ * u))) h := by
    intro u
    simp only []
    rw [hgp u]
    congr 1
    rw [show -(I * ξ * ((u + h : ℝ) : ℂ)) = -(I * ξ * u) + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
      rw [hξdef]; push_cast; field_simp; ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h2 := tendsto_avg_of_periodic (f := fun u : ℝ => (g u : ℂ) * Complex.exp (-(I * ξ * u)))
    hh ((Complex.continuous_ofReal.comp hgc).mul (by fun_prop)) hfper
  -- the vanishing part
  have h3 : Tendsto (fun T : ℝ => T⁻¹ • ∫ u in (0:ℝ)..T,
      ((G s μ u - g u : ℝ) : ℂ) * Complex.exp (-(I * ξ * u))) atTop (𝓝 0) := by
    refine tendsto_avg_of_tendsto (fun T => ?_) ?_
    · exact (((Complex.continuous_ofReal.comp (hGc.sub hgc))).mul
        (by fun_prop)).intervalIntegrable 0 T
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_mul, hchar, mul_one, Complex.norm_real]
      exact (tendsto_zero_iff_norm_tendsto_zero.1 hglim)
  have hsplit : ∀ T : ℝ, T⁻¹ • ∫ u in (0:ℝ)..T, (G s μ u : ℂ) * Complex.exp (-(I * ξ * u))
      = T⁻¹ • (∫ u in (0:ℝ)..T, (g u : ℂ) * Complex.exp (-(I * ξ * u)))
        + T⁻¹ • ∫ u in (0:ℝ)..T, ((G s μ u - g u : ℝ) : ℂ) * Complex.exp (-(I * ξ * u)) := by
    intro T
    have i1 : IntervalIntegrable (fun u : ℝ => (g u : ℂ) * Complex.exp (-(I * ξ * u)))
        volume 0 T :=
      ((Complex.continuous_ofReal.comp hgc).mul (by fun_prop)).intervalIntegrable 0 T
    have i2 : IntervalIntegrable (fun u : ℝ => ((G s μ u - g u : ℝ) : ℂ) *
        Complex.exp (-(I * ξ * u))) volume 0 T :=
      ((Complex.continuous_ofReal.comp (hGc.sub hgc)).mul (by fun_prop)).intervalIntegrable 0 T
    rw [← smul_add, ← intervalIntegral.integral_add i1 i2]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast
    ring
  have h4 := h2.add h3
  rw [add_zero] at h4
  have heq := tendsto_nhds_unique h1 (h4.congr fun T => (hsplit T).symm)
  rw [heq, fourierCoeffP, Complex.real_smul]
  push_cast
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [hξdef]
  push_cast
  rw [mul_comm]
  congr 2
  ring

end System

/-! ### The forcing transform -/

/-- The moment `M_c(α) = 𝔼 Z_c^{-α}` of `sec:two-contraction-formula` at complex `α`, the
power taken through the real logarithm of `Z_c > 0`. -/
def crossMomentC (c : ℝ) (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, ((crossDist c p.1 p.2 : ℝ) : ℂ) ^ (-z) ∂(μ.prod μ)

/-- **`eq:two-contraction-forcing-transform`**:
`∫ z(w) e^{-iξw} dw = 2pq M_c(s - iξ)/(s - iξ)`, by Fubini as in the tex. -/
theorem pairSystem_integral_renewalDefect_char {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) {μ : Measure ℝ}
    (hμ : (pairSystem c hc0 hc).IsNatural K s μ) (ξ : ℝ) :
    ∫ w, ((pairSystem c hc0 hc).renewalDefect s μ w : ℂ) * Complex.exp (-(I * ξ * w))
      = ((2 * ((1/2 : ℝ) ^ s * c ^ s) : ℝ) : ℂ) *
          (crossMomentC c μ (s - I * ξ) / (s - I * ξ)) := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  set ν := μ.prod μ with hν
  set Z : ℝ × ℝ → ℝ := fun p => crossDist c p.1 p.2 with hZ
  have hZc : Continuous Z := continuous_crossDist c
  have hZpos : ∀ᵐ p ∂ν, 1/2 - c ≤ Z p ∧ Z p ≤ 1 :=
    hbox.mono fun p hp => crossDist_mem hc0.le hp.1 hp.2
  have hbpos : (0:ℝ) < 1/2 - c := by linarith
  set a : ℂ := (s : ℂ) - I * ξ with ha
  have hare : 0 < a.re := by simp [ha]; exact hs0
  set κ : ℝ := 2 * ((1/2 : ℝ) ^ s * c ^ s) with hκ
  set A : Set (ℝ × (ℝ × ℝ)) := {q | Z q.2 ≤ Real.exp (-q.1)} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le (hZc.comp continuous_snd)
      (Real.continuous_exp.comp continuous_fst.neg)).measurableSet
  set F : ℝ × (ℝ × ℝ) → ℂ := A.indicator fun q => Complex.exp (a * q.1) with hF
  have hFm : Measurable F :=
    (Continuous.measurable (by fun_prop)).indicator hAm
  -- the integrand as an inner integral
  have hinner : ∀ w : ℝ, ((pairSystem c hc0 hc).renewalDefect s μ w : ℂ) *
      Complex.exp (-(I * ξ * w)) = (κ : ℂ) * ∫ p, F (w, p) ∂ν := by
    intro w
    have hsec : (fun p => F (w, p)) = {p | Z p ≤ Real.exp (-w)}.indicator
        (fun _ => Complex.exp (a * w)) := by
      funext p
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hsec, integral_indicator_const _ ((isClosed_le hZc continuous_const).measurableSet),
      renewalDefect_eq_crossPhi _ hμ, pairSystem_crossPhi hc0 hc hμ, Complex.real_smul,
      measureReal_def]
    push_cast
    rw [show a * w = (s : ℂ) * w + -(I * ξ * w) by rw [ha]; ring, Complex.exp_add]
    simp only [hκ, hν, hZ]
    push_cast
    ring
  -- the inner integral in `w`, at a point of the unit square
  have hw : ∀ p : ℝ × ℝ, 0 < Z p →
      ∫ w, F (w, p) = ((Z p : ℝ) : ℂ) ^ (-a) / a := by
    intro p hZp
    have hsec : (fun w => F (w, p)) = (Iic (-Real.log (Z p))).indicator
        fun w => Complex.exp (a * w) := by
      funext w
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      congr 1
      exact propext (by rw [le_neg, ← Real.log_le_iff_le_exp hZp, le_neg])
    rw [hsec, integral_indicator measurableSet_Iic, integral_exp_mul_complex_Iic hare,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hZp.ne'),
      ← Complex.ofReal_log hZp.le]
    congr 2
    push_cast
    ring
  -- integrability of the joint integrand
  have hnorm : ∀ p : ℝ × ℝ, 0 < Z p → ∫ w, ‖F (w, p)‖ = Z p ^ (-s) / s := by
    intro p hZp
    have hsec : (fun w => ‖F (w, p)‖) = (Iic (-Real.log (Z p))).indicator
        fun w => Real.exp (s * w) := by
      funext w
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      by_cases hwz : Z p ≤ Real.exp (-w)
      · have hw' : w ≤ -Real.log (Z p) := by
          have := (Real.log_le_iff_le_exp hZp).2 hwz; linarith
        rw [ite_eq_left hwz, ite_eq_left hw', Complex.norm_exp]
        simp [ha]
      · have hw' : ¬ w ≤ -Real.log (Z p) := by
          intro h
          exact hwz ((Real.log_le_iff_le_exp hZp).1 (by linarith))
        rw [ite_eq_right hwz, ite_eq_right hw', norm_zero]
    rw [hsec, integral_indicator measurableSet_Iic, integral_exp_mul_Iic hs0,
      Real.rpow_def_of_pos hZp]
    congr 1
    ring_nf
  have hFint : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨hZpos.mono fun p hp => ?_, ?_⟩
    · have hZp : 0 < Z p := lt_of_lt_of_le hbpos hp.1
      have hsec : (fun w => F (w, p)) = (Iic (-Real.log (Z p))).indicator
          fun w => Complex.exp (a * w) := by
        funext w
        simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
        congr 1
        exact propext (by rw [le_neg, ← Real.log_le_iff_le_exp hZp, le_neg])
      rw [hsec, integrable_indicator_iff measurableSet_Iic]
      exact integrableOn_exp_mul_complex_Iic hare _
    · refine Integrable.of_bound ((hFm.norm.stronglyMeasurable.integral_prod_left'
        ).aestronglyMeasurable) ((1/2 - c) ^ (-s) / s) (hZpos.mono fun p hp => ?_)
      have hZp : 0 < Z p := lt_of_lt_of_le hbpos hp.1
      rw [hnorm p hZp, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.rpow_nonneg hZp.le _) hs0.le)]
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hbpos hp.1 (by linarith))
        hs0.le
  simp only [hinner]
  rw [integral_const_mul, integral_integral_swap (f := fun w p => F (w, p)) hFint]
  congr 1
  rw [crossMomentC, ← integral_div]
  refine integral_congr_ae (hZpos.mono fun p hp => ?_)
  exact hw p (lt_of_lt_of_le hbpos hp.1)

/-! ### `eq:two-contraction-periodic` -/

/-- `ζ_k = s - 2πik/h`. -/
def twoContractionZeta (s h : ℝ) (k : ℤ) : ℂ := s - 2 * Real.pi * I * k / h

/-- The `k`-th coefficient `(2pq/m) 2^{-ζ_k} Γ(1-ζ_k) M_c(ζ_k)/ζ_k` of
`eq:two-contraction-periodic`, with `p = 2^{-s}`, `q = c^s` and
`m = p log 2 + q log(1/c)`. -/
def twoContractionCoeff (c s : ℝ) (μ : Measure ℝ) (h : ℝ) (k : ℤ) : ℂ :=
  ((2 * (2:ℝ) ^ (-s) * c ^ s / ((2:ℝ) ^ (-s) * Real.log 2 + c ^ s * Real.log c⁻¹) : ℝ) : ℂ) *
    ((2:ℂ) ^ (-twoContractionZeta s h k) * Complex.Gamma (1 - twoContractionZeta s h k) /
      twoContractionZeta s h k * crossMomentC c μ (twoContractionZeta s h k))

theorem twoContractionZeta_re (s h : ℝ) (k : ℤ) : (twoContractionZeta s h k).re = s := by
  simp [twoContractionZeta, Complex.div_re]

theorem twoContractionZeta_im (s h : ℝ) (k : ℤ) :
    (twoContractionZeta s h k).im = -(2 * Real.pi * k / h) := by
  simp [twoContractionZeta, Complex.div_im]
  rcases eq_or_ne h 0 with hh | hh
  · simp [hh]
  · field_simp

/-- **The coefficients are `O(k⁻²)`**: `|2^{-ζ}| = 2^{-s}`, `|M_c(ζ)| ≤ (1/2 - c)^{-s}` and
`|Γ(1-ζ)| ≤ Γ(2-s)/|1-ζ|`, while `|ζ|` and `|1 - ζ|` are at least `2π|k|/h`. -/
theorem summable_norm_twoContractionCoeff {c s h : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hs0 : 0 < s) (hs1 : s < 1) (hh : 0 < h) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc (0:ℝ) 1)ᶜ = 0) :
    Summable (fun k : ℤ => ‖twoContractionCoeff c s μ h k‖) := by
  have hbox := ae_prod_mem_Icc hsupp
  have hbpos : (0:ℝ) < 1/2 - c := by linarith
  set K₀ := ‖(((2 * (2:ℝ) ^ (-s) * c ^ s / ((2:ℝ) ^ (-s) * Real.log 2 + c ^ s *
    Real.log c⁻¹) : ℝ) : ℂ))‖ with hK₀
  set C := K₀ * ((2:ℝ) ^ (-s) * Real.Gamma (2 - s) * (1/2 - c) ^ (-s)) *
    (h / (2 * Real.pi)) ^ 2 with hC
  have hpi : 0 < 2 * Real.pi := by positivity
  refine Summable.of_norm_bounded_eventually
    (g := fun k : ℤ => C * |(k:ℝ)| ^ (-(2:ℝ)))
    ((Real.summable_abs_int_rpow (by norm_num : (1:ℝ) < 2)).mul_left C) ?_
  filter_upwards [eventually_cofinite_ne 0] with k hk
  rw [norm_norm]
  set ζ := twoContractionZeta s h k with hζ
  have hkpos : 0 < |(k:ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  have himabs : |ζ.im| = 2 * Real.pi * |(k:ℝ)| / h := by
    rw [hζ, twoContractionZeta_im, abs_neg, abs_div, abs_mul, abs_of_pos hpi,
      abs_of_pos hh]
  have hζn : 2 * Real.pi * |(k:ℝ)| / h ≤ ‖ζ‖ := himabs ▸ Complex.abs_im_le_norm ζ
  have h1ζn : 2 * Real.pi * |(k:ℝ)| / h ≤ ‖1 - ζ‖ := by
    have : |(1 - ζ).im| = 2 * Real.pi * |(k:ℝ)| / h := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, himabs]
    exact this ▸ Complex.abs_im_le_norm (1 - ζ)
  have hlow : 0 < 2 * Real.pi * |(k:ℝ)| / h := by positivity
  have hζ0 : ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hζn; linarith
  have h1ζ0 : 1 - ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1ζn; linarith
  -- the three factors
  have h2 : ‖(2:ℂ) ^ (-ζ)‖ = (2:ℝ) ^ (-s) := by
    rw [show (2:ℂ) = ((2:ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
      Complex.neg_re, hζ, twoContractionZeta_re]
  have hΓ : ‖Complex.Gamma (1 - ζ)‖ ≤ Real.Gamma (2 - s) / ‖1 - ζ‖ := by
    have hadd := Complex.Gamma_add_one (1 - ζ) h1ζ0
    rw [show 1 - ζ + 1 = 2 - ζ by ring] at hadd
    have hre : (2 - ζ).re = 2 - s := by
      rw [Complex.sub_re, hζ, twoContractionZeta_re]; norm_num
    have hle := norm_Gamma_le (z := 2 - ζ) (by rw [hre]; linarith)
    rw [hre, hadd, norm_mul] at hle
    rw [le_div_iff₀ (norm_pos_iff.2 h1ζ0), mul_comm]
    exact hle
  have hM : ‖crossMomentC c μ ζ‖ ≤ (1/2 - c) ^ (-s) := by
    have := norm_integral_le_of_norm_le_const (μ := μ.prod μ)
      (f := fun p : ℝ × ℝ => ((crossDist c p.1 p.2 : ℝ) : ℂ) ^ (-ζ))
      (C := (1/2 - c) ^ (-s)) (hbox.mono fun p hp => by
        have hZ := crossDist_mem hc0.le hp.1 hp.2
        have hZp : 0 < crossDist c p.1 p.2 := lt_of_lt_of_le hbpos hZ.1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hZp, Complex.neg_re, hζ, twoContractionZeta_re]
        exact Real.rpow_le_rpow_of_nonpos hbpos hZ.1 (by linarith))
    rwa [probReal_univ, mul_one] at this
  -- assemble
  have hΓpos : 0 < Real.Gamma (2 - s) := Real.Gamma_pos_of_pos (by linarith)
  have hcoef : ‖twoContractionCoeff c s μ h k‖
      = K₀ * (‖(2:ℂ) ^ (-ζ)‖ * ‖Complex.Gamma (1 - ζ)‖ / ‖ζ‖ * ‖crossMomentC c μ ζ‖) := by
    rw [twoContractionCoeff, norm_mul, norm_mul, norm_div, norm_mul]
  rw [hcoef, h2]
  have hk2 : |(k:ℝ)| ^ (-(2:ℝ)) = 1 / |(k:ℝ)| ^ 2 := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, one_div]
  rw [hk2]
  have hK₀0 : 0 ≤ K₀ := norm_nonneg _
  have hden : ‖ζ‖ * ‖1 - ζ‖ ≥ (2 * Real.pi * |(k:ℝ)| / h) ^ 2 := by
    rw [sq]; exact mul_le_mul hζn h1ζn hlow.le (norm_nonneg _)
  calc K₀ * ((2:ℝ) ^ (-s) * ‖Complex.Gamma (1 - ζ)‖ / ‖ζ‖ * ‖crossMomentC c μ ζ‖)
      ≤ K₀ * ((2:ℝ) ^ (-s) * (Real.Gamma (2 - s) / ‖1 - ζ‖) / ‖ζ‖ * (1/2 - c) ^ (-s)) := by
        gcongr
    _ = K₀ * ((2:ℝ) ^ (-s) * Real.Gamma (2 - s) * (1/2 - c) ^ (-s)) / (‖ζ‖ * ‖1 - ζ‖) := by
        field_simp
    _ ≤ K₀ * ((2:ℝ) ^ (-s) * Real.Gamma (2 - s) * (1/2 - c) ^ (-s)) /
          (2 * Real.pi * |(k:ℝ)| / h) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = C * (1 / |(k:ℝ)| ^ 2) := by
        rw [hC]; field_simp

namespace System

/-- The coefficients of `T G̃` for the lattice limit `G̃` of the two-map system are the
explicit coefficients of `eq:two-contraction-periodic`. -/
theorem _root_.BrownianImages.pairSystem_fourierCoeffP_smoothOp {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1/2) {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : (pairSystem c hc0 hc).IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range (pairSystem c hc0 hc).logRatio)
      = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : (pairSystem c hc0 hc).IsNatural K s μ) {g : ℝ → ℝ}
    (hgc : Continuous g) (hgp : Function.Periodic g h)
    (hglim : Tendsto (fun w => G s μ w - g w) atTop (𝓝 0)) (k : ℤ) :
    fourierCoeffP (h / 2) (smoothOp s g) k = twoContractionCoeff c s μ h k := by
  have hosc := pairSystem_openSetCondition hc0 hc hμ.attractor
  obtain ⟨B, -, hB⟩ := exists_nonneg_bound_of_periodic hh.ne' hgc hgp
  rw [fourierCoeffP_smoothOp hs0 hs1 hh hgc ⟨B, hB⟩ hgp k, multInt_eq_gammaMult hs1 h k,
    hμ.fourierCoeffP_latticeLimit _ hs0 hs1 hosc hdim hh hlat hgc hgp hglim k,
    pairSystem_integral_renewalDefect_char hc0 hc hs0 hμ, pairSystem_renewalMean,
    gammaMult, twoContractionCoeff]
  have hhalf : (1/2 : ℝ) ^ s = (2:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
  have hz : ((s : ℂ) - I * ((2 * Real.pi * k / h : ℝ) : ℂ)) = twoContractionZeta s h k := by
    rw [twoContractionZeta]; push_cast; ring
  have he1 : -(s : ℂ) + freq h k = -twoContractionZeta s h k := by
    rw [twoContractionZeta, freq]; ring
  have he2 : 1 - (s : ℂ) + freq h k = 1 - twoContractionZeta s h k := by
    rw [twoContractionZeta, freq]; ring
  rw [hz, he1, he2, hhalf, Complex.real_smul]
  push_cast
  ring

end System

/-- **`eq:two-contraction-periodic`.**  In the lattice case, with `h` the span of the
group generated by `log 2` and `log(1/c)`, the coefficients `twoContractionCoeff` are
absolutely summable and the expected profile is asymptotic to the Fourier series
`∑_k c_k e^{4πikt/h}`. -/
theorem pairSystem_periodic {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ} {s h : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hdim : (pairSystem c hc0 hc).IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range (pairSystem c hc0 hc).logRatio)
      = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : (pairSystem c hc0 hc).IsNatural K s μ) :
    Summable (fun k : ℤ => ‖twoContractionCoeff c s μ h k‖) ∧
      Tendsto (fun t : ℝ => (H s μ t : ℂ) - ∑' k : ℤ, twoContractionCoeff c s μ h k *
        Complex.exp (4 * Real.pi * I * k * t / h)) atTop (𝓝 0) := by
  have := hμ.isProbabilityMeasure
  have hosc := pairSystem_openSetCondition hc0 hc hμ.attractor
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman _ hs0.le hμ
  obtain ⟨g, hgc, hgp, -, hglim⟩ :=
    (pairSystem c hc0 hc).lattice_G_limit hs0 hs1 hosc hdim hh hlat hμ
  obtain ⟨B, -, hB⟩ := exists_nonneg_bound_of_periodic hh.ne' hgc hgp
  have hsum := summable_norm_twoContractionCoeff hc0 hc hs0 hs1 hh (μ := μ) hμ.support_Icc
  refine ⟨hsum, ?_⟩
  have hcoeff := pairSystem_fourierCoeffP_smoothOp hc0 hc hs0 hs1 hdim hh hlat hμ hgc hgp hglim
  have hsumC : Summable (fourierCoeffP (h / 2) (smoothOp s g)) := by
    rw [funext hcoeff]; exact hsum.of_norm
  have hser : ∀ t : ℝ, ∑' k : ℤ, twoContractionCoeff c s μ h k *
      Complex.exp (4 * Real.pi * I * k * t / h) = (smoothOp s g t : ℂ) := by
    intro t
    have hs := hasSum_fourierCoeffP (by linarith : 0 < h / 2)
      (continuous_smoothOp hs0 hs1 hgc hB) (smoothOp_periodic hgp) hsumC t
    refine (HasSum.tsum_eq ?_)
    refine hs.congr_fun fun k => ?_
    rw [hcoeff k]
    congr 2
    have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast
    field_simp
    ring
  have herr := smooth_profile_error_tendsto hs0 hs1 hA hgc hh hgp hglim
  have hC := (Complex.continuous_ofReal.tendsto 0).comp herr
  rw [Complex.ofReal_zero] at hC
  refine hC.congr fun t => ?_
  simp only [Function.comp, hser]
  push_cast
  ring

/-- A system is non-lattice, or its log-ratios generate `hℤ` for some `h > 0`: a subgroup of
`ℝ` is dense or cyclic. -/
theorem System.nonArithmetic_or_exists_lattice {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : System ι) :
    S.NonArithmetic ∨ ∃ h : ℝ, 0 < h ∧
      AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h := by
  rcases AddSubgroup.dense_or_cyclic (AddSubgroup.closure (Set.range S.logRatio))
    with hd | ⟨a, ha⟩
  · exact Or.inl hd
  · right
    have hcyc : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples a := by
      rw [ha, AddSubgroup.zmultiples_eq_closure]
    have ha0 : a ≠ 0 := by
      intro h0
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hi : S.logRatio i ∈ AddSubgroup.zmultiples a := by
        rw [← hcyc]; exact AddSubgroup.subset_closure (Set.mem_range_self i)
      rw [h0, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] at hi
      exact (S.logRatio_pos i).ne' hi
    refine ⟨|a|, abs_pos.2 ha0, ?_⟩
    rw [hcyc]
    rcases lt_or_gt_of_ne ha0 with hneg | hpos
    · rw [abs_of_neg hneg]; exact AddSubgroup.zmultiples_neg.symm
    · rw [abs_of_pos hpos]

end

end BrownianImages
