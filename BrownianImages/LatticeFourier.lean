module

/-
The Fourier analysis of the lattice limit of `G`, shared by `eq:fixed-dimension-periodic`
and the lattice branch of `thm:profile-asymptotics`.

The Fourier coefficients of the lattice limit `G̃` of `LatticeProfile` are read off the
renewal equation: the average of `G(w) e^{-iξw}` over `[0, T]` converges to `m⁻¹ ẑ(ξ)`
whenever every delay `α_i` is a multiple of `2π/ξ`, and it also converges to the
coefficient of `G̃`.  Absolute convergence of the series in `eq:fixed-dimension-periodic`
comes from `|Γ(1 - ζ)| ≤ Γ(2 - s)/|1 - ζ|`.

* `hasSum_fourierCoeffP`: a continuous periodic function with summable coefficients is
  the sum of its Fourier series.
* `tendsto_avg_of_periodic`: the Cesàro mean of a continuous periodic function.
* `norm_Gamma_le`: `|Γ(z)| ≤ Γ(Re z)`.
* `System.IsNatural.tendsto_avg_G_char`: the renewal average with a character.
* `System.IsNatural.fourierCoeffP_latticeLimit`: the coefficients of the lattice limit.
* `latticeZeta`: the frequencies `ζ_k = s - 2πik/h` of `eq:fixed-dimension-periodic`.
* `System.nonArithmetic_or_exists_lattice`: every system is non-lattice or has a span.
-/
public import BrownianImages.Cesaro
public import BrownianImages.LatticeProfile
public import BrownianImages.FourierMultiplier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

@[expose] public section

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

/-- **The renewal average with a character.**  If every delay satisfies `e^{iξ α_i} = 1`,
the averages of `G(w) e^{-iξw}` over `[0, T]` converge to `m⁻¹ ∫ z(w) e^{-iξw} dw`: the
character passes through the renewal equation unchanged.  This is the coefficient
computation behind `eq:fixed-dimension-periodic`. -/
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

/-! ### The frequencies of the lattice limit -/

/-- The frequencies `ζ_k = s - 2πik/h` of `eq:fixed-dimension-periodic`. -/
def latticeZeta (s h : ℝ) (k : ℤ) : ℂ := s - 2 * Real.pi * I * k / h

theorem latticeZeta_re (s h : ℝ) (k : ℤ) : (latticeZeta s h k).re = s := by
  simp [latticeZeta, Complex.div_re]

theorem latticeZeta_im (s h : ℝ) (k : ℤ) :
    (latticeZeta s h k).im = -(2 * Real.pi * k / h) := by
  simp [latticeZeta, Complex.div_im]
  rcases eq_or_ne h 0 with hh | hh
  · simp [hh]
  · field_simp

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
