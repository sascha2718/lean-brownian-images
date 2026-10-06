/-
`eq:fixed-dimension-periodic` of `thm:fixed-dimension-profiles`: in the lattice case the
expected profile of the fixed-dimension family is asymptotic to the absolutely convergent
Fourier series with coefficients `(2spq/E(p)) 2^{-ζ_k} Γ(1-ζ_k) M_p(ζ_k)/ζ_k`,
`ζ_k = s - 2πik/h`.  The proof is that of `eq:two-contraction-periodic`: the forcing
transform `eq:fixed-dimension-forcing`, the Fourier coefficients of the lattice limit read
off the renewal equation, and the `O(k⁻²)` decay from `|Γ(1-ζ)| ≤ Γ(2-s)/|1-ζ|`.

* `fixedMomentC`: `M_p(α)` at complex `α`.
* `fixedSystem_integral_renewalDefect_char`: `eq:fixed-dimension-forcing`.
* `fixedDimCoeff`, `summable_norm_fixedDimCoeff`: the coefficients and their decay.
* `fixedSystem_periodic`: `eq:fixed-dimension-periodic`.
-/
import BrownianImages.FixedDimension.Profiles
import BrownianImages.TwoContraction.Periodic

namespace BrownianImages

open MeasureTheory Filter Set Complex
open scoped Topology ENNReal Interval

noncomputable section

/-- `M_p(α) = 𝔼 Z_p^{-α}` at complex `α`, through the real logarithm of `Z_p`. -/
def fixedMomentC (s p : ℝ) (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ q : ℝ × ℝ, ((fixedCross s p q.1 q.2 : ℝ) : ℂ) ^ (-z) ∂(μ.prod μ)

/-- **`eq:fixed-dimension-forcing`**: `∫ z(w) e^{-iξw} dw = 2pq M_p(s - iξ)/(s - iξ)`. -/
theorem fixedSystem_integral_renewalDefect_char {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp0 : 0 < p) (hp1 : p < 1) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) (ξ : ℝ) :
    ∫ w, ((fixedSystem s p hs hp0 hp1).renewalDefect s μ w : ℂ) * Complex.exp (-(I * ξ * w))
      = ((2 * (p * (1 - p)) : ℝ) : ℂ) * (fixedMomentC s p μ (s - I * ξ) / (s - I * ξ)) := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  set ν := μ.prod μ with hν
  set Z : ℝ × ℝ → ℝ := fun q => fixedCross s p q.1 q.2 with hZ
  have hZc : Continuous Z := continuous_fixedCross s p
  have hbpos : 0 < crossGap s p := crossGap_pos hs hs1 hp0 hp1
  have hZpos : ∀ᵐ q ∂ν, crossGap s p ≤ Z q ∧ Z q ≤ 1 :=
    hbox.mono fun q hq => fixedCross_mem hs hp0 hp1 hq.1 hq.2
  set a : ℂ := (s : ℂ) - I * ξ with ha
  have hare : 0 < a.re := by simp [ha]; exact hs
  set κ : ℝ := 2 * (p * (1 - p)) with hκ
  set A : Set (ℝ × (ℝ × ℝ)) := {q | Z q.2 ≤ Real.exp (-q.1)} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le (hZc.comp continuous_snd)
      (Real.continuous_exp.comp continuous_fst.neg)).measurableSet
  set F : ℝ × (ℝ × ℝ) → ℂ := A.indicator fun q => Complex.exp (a * q.1) with hF
  have hFm : Measurable F :=
    (Continuous.measurable (by fun_prop)).indicator hAm
  -- the integrand as an inner integral
  have hinner : ∀ w : ℝ, ((fixedSystem s p hs hp0 hp1).renewalDefect s μ w : ℂ) *
      Complex.exp (-(I * ξ * w)) = (κ : ℂ) * ∫ q, F (w, q) ∂ν := by
    intro w
    have hsec : (fun q => F (w, q)) = {q | Z q ≤ Real.exp (-w)}.indicator
        (fun _ => Complex.exp (a * w)) := by
      funext q
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hsec, integral_indicator_const _ ((isClosed_le hZc continuous_const).measurableSet),
      renewalDefect_eq_crossPhi _ hμ, fixedSystem_crossPhi hs hs1 hp0 hp1 hμ, Complex.real_smul,
      measureReal_def]
    push_cast
    rw [show a * w = (s : ℂ) * w + -(I * ξ * w) by rw [ha]; ring, Complex.exp_add]
    simp only [hκ, hν, hZ]
    push_cast
    ring
  -- the inner integral in `w`, at a point of the unit square
  have hw : ∀ q : ℝ × ℝ, 0 < Z q →
      ∫ w, F (w, q) = ((Z q : ℝ) : ℂ) ^ (-a) / a := by
    intro q hZq
    have hsec : (fun w => F (w, q)) = (Iic (-Real.log (Z q))).indicator
        fun w => Complex.exp (a * w) := by
      funext w
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      congr 1
      exact propext (by rw [le_neg, ← Real.log_le_iff_le_exp hZq, le_neg])
    rw [hsec, integral_indicator measurableSet_Iic, integral_exp_mul_complex_Iic hare,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hZq.ne'),
      ← Complex.ofReal_log hZq.le]
    congr 2
    push_cast
    ring
  -- integrability of the joint integrand
  have hnorm : ∀ q : ℝ × ℝ, 0 < Z q → ∫ w, ‖F (w, q)‖ = Z q ^ (-s) / s := by
    intro q hZq
    have hsec : (fun w => ‖F (w, q)‖) = (Iic (-Real.log (Z q))).indicator
        fun w => Real.exp (s * w) := by
      funext w
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      by_cases hwz : Z q ≤ Real.exp (-w)
      · have hw' : w ≤ -Real.log (Z q) := by
          have := (Real.log_le_iff_le_exp hZq).2 hwz; linarith
        rw [ite_eq_left hwz, ite_eq_left hw', Complex.norm_exp]
        simp [ha]
      · have hw' : ¬ w ≤ -Real.log (Z q) := by
          intro h
          exact hwz ((Real.log_le_iff_le_exp hZq).1 (by linarith))
        rw [ite_eq_right hwz, ite_eq_right hw', norm_zero]
    rw [hsec, integral_indicator measurableSet_Iic, integral_exp_mul_Iic hs,
      Real.rpow_def_of_pos hZq]
    congr 1
    ring_nf
  have hFint : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨hZpos.mono fun q hq => ?_, ?_⟩
    · have hZq : 0 < Z q := lt_of_lt_of_le hbpos hq.1
      have hsec : (fun w => F (w, q)) = (Iic (-Real.log (Z q))).indicator
          fun w => Complex.exp (a * w) := by
        funext w
        simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
        congr 1
        exact propext (by rw [le_neg, ← Real.log_le_iff_le_exp hZq, le_neg])
      rw [hsec, integrable_indicator_iff measurableSet_Iic]
      exact integrableOn_exp_mul_complex_Iic hare _
    · refine Integrable.of_bound ((hFm.norm.stronglyMeasurable.integral_prod_left'
        ).aestronglyMeasurable) (crossGap s p ^ (-s) / s) (hZpos.mono fun q hq => ?_)
      have hZq : 0 < Z q := lt_of_lt_of_le hbpos hq.1
      rw [hnorm q hZq, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.rpow_nonneg hZq.le _) hs.le)]
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hbpos hq.1 (by linarith))
        hs.le
  simp only [hinner]
  rw [integral_const_mul, integral_integral_swap (f := fun w q => F (w, q)) hFint]
  congr 1
  rw [fixedMomentC, ← integral_div]
  refine integral_congr_ae (hZpos.mono fun q hq => ?_)
  exact hw q (lt_of_lt_of_le hbpos hq.1)

/-! ### `eq:fixed-dimension-periodic` -/

/-- The `k`-th coefficient `(2spq/E(p)) 2^{-ζ_k} Γ(1-ζ_k) M_p(ζ_k)/ζ_k` of
`eq:fixed-dimension-periodic`, with `ζ_k = s - 2πik/h`. -/
def fixedDimCoeff (s p : ℝ) (μ : Measure ℝ) (h : ℝ) (k : ℤ) : ℂ :=
  ((2 * s * p * (1 - p) / entropy p : ℝ) : ℂ) *
    ((2:ℂ) ^ (-twoContractionZeta s h k) * Complex.Gamma (1 - twoContractionZeta s h k) /
      twoContractionZeta s h k * fixedMomentC s p μ (twoContractionZeta s h k))

/-- **The coefficients are `O(k⁻²)`**: `|2^{-ζ}| = 2^{-s}`, `|M_p(ζ)| ≤ (1-a-b)^{-s}` and
`|Γ(1-ζ)| ≤ Γ(2-s)/|1-ζ|`, while `|ζ|` and `|1 - ζ|` are at least `2π|k|/h`. -/
theorem summable_norm_fixedDimCoeff {s p h : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hh : 0 < h) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc (0:ℝ) 1)ᶜ = 0) :
    Summable (fun k : ℤ => ‖fixedDimCoeff s p μ h k‖) := by
  have hbox := ae_prod_mem_Icc hsupp
  have hbpos : 0 < crossGap s p := crossGap_pos hs hs1 hp0 hp1
  set K₀ := ‖(((2 * s * p * (1 - p) / entropy p : ℝ) : ℂ))‖ with hK₀
  set C := K₀ * ((2:ℝ) ^ (-s) * Real.Gamma (2 - s) * crossGap s p ^ (-s)) *
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
  have hM : ‖fixedMomentC s p μ ζ‖ ≤ crossGap s p ^ (-s) := by
    have := norm_integral_le_of_norm_le_const (μ := μ.prod μ)
      (f := fun q : ℝ × ℝ => ((fixedCross s p q.1 q.2 : ℝ) : ℂ) ^ (-ζ))
      (C := crossGap s p ^ (-s)) (hbox.mono fun q hq => by
        have hZ := fixedCross_mem hs hp0 hp1 hq.1 hq.2
        have hZp : 0 < fixedCross s p q.1 q.2 := lt_of_lt_of_le hbpos hZ.1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hZp, Complex.neg_re, hζ, twoContractionZeta_re]
        exact Real.rpow_le_rpow_of_nonpos hbpos hZ.1 (by linarith))
    rwa [probReal_univ, mul_one] at this
  have hΓpos : 0 < Real.Gamma (2 - s) := Real.Gamma_pos_of_pos (by linarith)
  have hcoef : ‖fixedDimCoeff s p μ h k‖
      = K₀ * (‖(2:ℂ) ^ (-ζ)‖ * ‖Complex.Gamma (1 - ζ)‖ / ‖ζ‖ * ‖fixedMomentC s p μ ζ‖) := by
    rw [fixedDimCoeff, norm_mul, norm_mul, norm_div, norm_mul]
  rw [hcoef, h2]
  have hk2 : |(k:ℝ)| ^ (-(2:ℝ)) = 1 / |(k:ℝ)| ^ 2 := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, one_div]
  rw [hk2]
  have hK₀0 : 0 ≤ K₀ := norm_nonneg _
  have hden : ‖ζ‖ * ‖1 - ζ‖ ≥ (2 * Real.pi * |(k:ℝ)| / h) ^ 2 := by
    rw [sq]; exact mul_le_mul hζn h1ζn hlow.le (norm_nonneg _)
  calc K₀ * ((2:ℝ) ^ (-s) * ‖Complex.Gamma (1 - ζ)‖ / ‖ζ‖ * ‖fixedMomentC s p μ ζ‖)
      ≤ K₀ * ((2:ℝ) ^ (-s) * (Real.Gamma (2 - s) / ‖1 - ζ‖) / ‖ζ‖ * crossGap s p ^ (-s)) := by
        gcongr
    _ = K₀ * ((2:ℝ) ^ (-s) * Real.Gamma (2 - s) * crossGap s p ^ (-s)) / (‖ζ‖ * ‖1 - ζ‖) := by
        field_simp
    _ ≤ K₀ * ((2:ℝ) ^ (-s) * Real.Gamma (2 - s) * crossGap s p ^ (-s)) /
          (2 * Real.pi * |(k:ℝ)| / h) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = C * (1 / |(k:ℝ)| ^ 2) := by
        rw [hC]; field_simp

/-- The coefficients of `T G̃` for the lattice limit `G̃` of the fixed-dimension system are
the explicit coefficients of `eq:fixed-dimension-periodic`. -/
theorem fixedSystem_fourierCoeffP_smoothOp {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {K : Set ℝ} {h : ℝ} (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range (fixedSystem s p hs hp0 hp1).logRatio)
      = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) {g : ℝ → ℝ}
    (hgc : Continuous g) (hgp : Function.Periodic g h)
    (hglim : Tendsto (fun w => G s μ w - g w) atTop (𝓝 0)) (k : ℤ) :
    fourierCoeffP (h / 2) (smoothOp s g) k = fixedDimCoeff s p μ h k := by
  have hosc := fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor
  have hE := entropy_pos hp0 hp1
  obtain ⟨B, -, hB⟩ := exists_nonneg_bound_of_periodic hh.ne' hgc hgp
  rw [fourierCoeffP_smoothOp hs hs1 hh hgc ⟨B, hB⟩ hgp k, multInt_eq_gammaMult hs1 h k,
    hμ.fourierCoeffP_latticeLimit _ hs hs1 hosc (fixedSystem_isDimension hs hp0 hp1) hh hlat
      hgc hgp hglim k,
    fixedSystem_integral_renewalDefect_char hs hs1 hp0 hp1 hμ, fixedSystem_renewalMean hs hp0 hp1,
    gammaMult, fixedDimCoeff]
  have hz : ((s : ℂ) - I * ((2 * Real.pi * k / h : ℝ) : ℂ)) = twoContractionZeta s h k := by
    rw [twoContractionZeta]; push_cast; ring
  have he1 : -(s : ℂ) + freq h k = -twoContractionZeta s h k := by
    rw [twoContractionZeta, freq]; ring
  have he2 : 1 - (s : ℂ) + freq h k = 1 - twoContractionZeta s h k := by
    rw [twoContractionZeta, freq]; ring
  rw [hz, he1, he2, Complex.real_smul]
  have hEc : (entropy p : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

/-- **`eq:fixed-dimension-periodic`.**  In the lattice case, with `h` the span of the group
generated by `log(1/a)` and `log(1/b)`, the coefficients `fixedDimCoeff` are absolutely
summable and the expected profile is asymptotic to the Fourier series `∑_k c_k e^{4πikt/h}`. -/
theorem fixedSystem_periodic {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {h : ℝ} (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range (fixedSystem s p hs hp0 hp1).logRatio)
      = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    Summable (fun k : ℤ => ‖fixedDimCoeff s p μ h k‖) ∧
      Tendsto (fun t : ℝ => (H s μ t : ℂ) - ∑' k : ℤ, fixedDimCoeff s p μ h k *
        Complex.exp (4 * Real.pi * I * k * t / h)) atTop (𝓝 0) := by
  have := hμ.isProbabilityMeasure
  have hosc := fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman _ hs.le hμ
  obtain ⟨g, hgc, hgp, -, hglim⟩ :=
    (fixedSystem s p hs hp0 hp1).lattice_G_limit hs hs1 hosc (fixedSystem_isDimension hs hp0 hp1)
      hh hlat hμ
  obtain ⟨B, -, hB⟩ := exists_nonneg_bound_of_periodic hh.ne' hgc hgp
  have hsum := summable_norm_fixedDimCoeff hs hs1 hp0 hp1 hh (μ := μ) hμ.support_Icc
  refine ⟨hsum, ?_⟩
  have hcoeff := fixedSystem_fourierCoeffP_smoothOp hs hs1 hp0 hp1 hh hlat hμ hgc hgp hglim
  have hsumC : Summable (fourierCoeffP (h / 2) (smoothOp s g)) := by
    rw [funext hcoeff]; exact hsum.of_norm
  have hser : ∀ t : ℝ, ∑' k : ℤ, fixedDimCoeff s p μ h k *
      Complex.exp (4 * Real.pi * I * k * t / h) = (smoothOp s g t : ℂ) := by
    intro t
    have hs' := hasSum_fourierCoeffP (by linarith : 0 < h / 2)
      (continuous_smoothOp hs hs1 hgc hB) (smoothOp_periodic hgp) hsumC t
    refine (HasSum.tsum_eq ?_)
    refine hs'.congr_fun fun k => ?_
    rw [hcoeff k]
    congr 2
    have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast
    field_simp
    ring
  have herr := smooth_profile_error_tendsto hs hs1 hA hgc hh hgp hglim
  have hC := (Complex.continuous_ofReal.tendsto 0).comp herr
  rw [Complex.ofReal_zero] at hC
  refine hC.congr fun t => ?_
  simp only [Function.comp, hser]
  push_cast
  ring

/-! ### The lattice dichotomy -/

/-- The log-ratios of the fixed-dimension system are `log(1/a)` and `log(1/b)`. -/
theorem fixedSystem_range_logRatio {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    Set.range (fixedSystem s p hs hp0 hp1).logRatio
      = {Real.log (fixedA s p)⁻¹, Real.log (fixedB s p)⁻¹} := by
  have h0 : (fixedSystem s p hs hp0 hp1).logRatio 0 = Real.log (fixedA s p)⁻¹ := by
    simp [System.logRatio, fixedSystem]
  have h1 : (fixedSystem s p hs hp0 hp1).logRatio 1 = Real.log (fixedB s p)⁻¹ := by
    simp [System.logRatio, fixedSystem]
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, h0, h1, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

/-- `log a / log b ∉ ℚ` is exactly non-arithmeticity of the fixed-dimension system: the
additive group generated by `log(1/a)` and `log(1/b)` is dense precisely when their ratio
is irrational. -/
theorem fixedSystem_nonArithmetic_iff {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    (fixedSystem s p hs hp0 hp1).NonArithmetic
      ↔ Irrational (Real.log (fixedA s p) / Real.log (fixedB s p)) := by
  rw [System.NonArithmetic, fixedSystem_range_logRatio hs hp0 hp1,
    dense_addSubgroupClosure_pair_iff, Real.log_inv, Real.log_inv, neg_div_neg_eq]

end

end BrownianImages
