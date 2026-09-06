/-
`sec:variance` of `BrownianImagesComplete.tex`: `eq:joint-return-bound` of
`thm:gaussian-four-point`, the joint return probability of two planar Brownian increments.

The second increment is written as `Z' = ρZ + N`, with `ρ = O/δ` the regression coefficient
of the paper's covariance matrix.  Being jointly Gaussian and uncorrelated, `Z` and `N` are
independent, and the joint return probability factors into two disc masses: the disc of
radius `r` carries at most `r²/(2v)` for a centred planar Gaussian of variance `v`, whatever
its centre, because the density is at most `(2πv)⁻¹` and the disc has area `πr²`.  With
`Var N = Δ/δ` this is `eq:joint-return-bound` in its determinant branch.

* `gaussianProd_disc_le`, `volume_disc`: the disc bound and the area behind it.
* `crossCov`, `abs_crossCov`: the signed covariance of the two increments, whose absolute
  value is the overlap `O`.
* `hasGaussianLaw_pair`, `indepFun_increment_residual`, `map_residual`: the regression
  decomposition, its independence and the law of the residual.
* `jointReturn_le_det`, `jointReturn_le_max`: the two non-trivial branches of
  `eq:joint-return-bound`.
* `det_nonneg`, `det_pos_of_ne`: `Δ ≥ 0` always, and `Δ > 0` unless the two unoriented
  intervals agree.
* `gaussian_four_point`, `gaussian_four_point_ae`, `gaussian_four_point_bundled`: the
  three forms of `eq:joint-return-bound`, behind the endpoints `audit_gaussian_four_point`,
  `audit_gaussian_four_point_ae` and `audit_thm_gaussian_four_point`.
-/
import BrownianImages.GaussianFourPoint
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace FourPointBound

/-! ### The disc bound for a centred planar Gaussian -/

/-- The product of the two coordinate densities of a centred planar Gaussian is at most its
value at the origin, `(2πv)⁻¹`. -/
theorem gaussianPDFReal_prod_le (v : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 v x * gaussianPDFReal 0 v y ≤ (2 * Real.pi * (v : ℝ))⁻¹ := by
  have hA : (0 : ℝ) ≤ 2 * Real.pi * (v : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi * (v : ℝ)) * Real.sqrt (2 * Real.pi * (v : ℝ))
      = 2 * Real.pi * (v : ℝ) := Real.mul_self_sqrt hA
  have hx : gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    rw [gaussianPDFReal]
    have h1 : Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (0 : ℝ) ≤ (x - 0) ^ 2 / (2 * (v : ℝ)) := by positivity
      rw [neg_div]
      linarith
    nlinarith [Real.sqrt_nonneg (2 * Real.pi * (v : ℝ)),
      inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (v : ℝ))),
      Real.exp_pos (-(x - 0) ^ 2 / (2 * (v : ℝ)))]
  have hy : gaussianPDFReal 0 v y ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    rw [gaussianPDFReal]
    have h1 : Real.exp (-(y - 0) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (0 : ℝ) ≤ (y - 0) ^ 2 / (2 * (v : ℝ)) := by positivity
      rw [neg_div]
      linarith
    nlinarith [Real.sqrt_nonneg (2 * Real.pi * (v : ℝ)),
      inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (v : ℝ))),
      Real.exp_pos (-(y - 0) ^ 2 / (2 * (v : ℝ)))]
  calc gaussianPDFReal 0 v x * gaussianPDFReal 0 v y
      ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
        have h0 : (0 : ℝ) ≤ gaussianPDFReal 0 v y := gaussianPDFReal_nonneg _ _ _
        have h1 : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
          inv_nonneg.mpr (Real.sqrt_nonneg _)
        exact mul_le_mul hx hy h0 h1
    _ = (2 * Real.pi * (v : ℝ))⁻¹ := by rw [← mul_inv, hsqrt]

/-- The planar Lebesgue measure of an open disc of radius `r`. -/
theorem volume_disc (x : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2}
      = ENNReal.ofReal (Real.pi * r ^ 2) := by
  have hmeas : MeasurableSet {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hset : Complex.measurableEquivRealProd ⁻¹'
      {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2}
      = Metric.ball (Complex.mk x.1 x.2) r := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball, Complex.dist_eq_re_im,
      Complex.measurableEquivRealProd_apply]
    exact (Real.sqrt_lt' hr).symm
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage hmeas.nullMeasurableSet,
    hset, Complex.volume_ball, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [NNReal.coe_real_pi]
  ring

/-- The mass of an arbitrary open disc of radius `r` under a centred planar Gaussian of
variance `v`: the density is at most `(2πv)⁻¹` and the disc has area `πr²`. -/
theorem gaussianProd_disc_le {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) (x : ℝ × ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v))
        {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2}
      ≤ ENNReal.ofReal (r ^ 2 / (2 * (v : ℝ))) := by
  have hV : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hv)
  have hS : MeasurableSet {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [gaussianReal_of_var_ne_zero 0 hv,
    prod_withDensity (measurable_gaussianPDF 0 v) (measurable_gaussianPDF 0 v),
    withDensity_apply _ hS, ← Measure.volume_eq_prod]
  calc ∫⁻ q in {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2},
        gaussianPDF 0 v q.1 * gaussianPDF 0 v q.2
      ≤ ∫⁻ _ in {q : ℝ × ℝ | (q.1 - x.1) ^ 2 + (q.2 - x.2) ^ 2 < r ^ 2},
          ENNReal.ofReal (2 * Real.pi * (v : ℝ))⁻¹ := by
        refine lintegral_mono fun q => ?_
        rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
        exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_prod_le v q.1 q.2)
    _ = ENNReal.ofReal (2 * Real.pi * (v : ℝ))⁻¹ * ENNReal.ofReal (Real.pi * r ^ 2) := by
        rw [setLIntegral_const, volume_disc x hr]
    _ = ENNReal.ofReal (r ^ 2 / (2 * (v : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-! ### The covariance of two increments -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- The covariance of the two Brownian increments over the time pairs `(t,u)` and `(t',u')`,
the rectangle increment of `min`.  Its absolute value is the overlap `O` of `sec:variance`. -/
noncomputable def crossCov (t u t' u' : ℝ) : ℝ :=
  min u u' - min u t' - min t u' + min t t'

/-- The covariance of the two increments does not depend on the order of the two pairs. -/
theorem crossCov_comm (t u t' u' : ℝ) : crossCov t' u' t u = crossCov t u t' u' := by
  rw [crossCov, crossCov, min_comm u' u, min_comm u' t, min_comm t' u, min_comm t' t]
  ring

/-- The covariance of two increments of a real Brownian motion is the rectangle increment of
`min` over the two time pairs. -/
theorem cov_increments {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a b a' b' : ℝ≥0) :
    cov[fun ω => B b ω - B a ω, fun ω => B b' ω - B a' ω; P]
      = crossCov (a : ℝ) (b : ℝ) (a' : ℝ) (b' : ℝ) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [covariance_fun_sub_fun_sub, crossCov]
  · simp_rw [hB.covariance_fun_eval]
    push_cast
    ring
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- The covariance of an increment with itself is the length of the time interval. -/
theorem crossCov_self (t u : ℝ) : crossCov t u t u = |u - t| := by
  rw [crossCov]
  rcases le_total t u with h | h
  · rw [min_self, min_eq_right h, min_eq_left h, min_self, abs_of_nonneg (by linarith)]
    ring
  · rw [min_self, min_eq_left h, min_eq_right h, min_self, abs_of_nonpos (by linarith)]
    ring

/-- The variance of an increment of a real Brownian motion is the length of the time
interval. -/
theorem var_increment {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a b : ℝ≥0) :
    cov[fun ω => B b ω - B a ω, fun ω => B b ω - B a ω; P] = |(b : ℝ) - (a : ℝ)| := by
  rw [cov_increments hB, crossCov_self]

/-- The rectangle increment of `min` over two ordered time pairs is the length of the overlap
of the two intervals. -/
theorem crossCov_eq_overlap {t u t' u' : ℝ} (htu : t ≤ u) (htu' : t' ≤ u') :
    crossCov t u t' u' = overlap t u t' u' := by
  rw [crossCov, overlap, max_eq_right htu, min_eq_left htu, max_eq_right htu',
    min_eq_left htu']
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The overlap is non-negative. -/
theorem overlap_nonneg (t u t' u' : ℝ) : 0 ≤ overlap t u t' u' := le_max_left _ _

/-- The overlap does not see the orientation of the first interval. -/
theorem overlap_swap_left (t u t' u' : ℝ) : overlap u t t' u' = overlap t u t' u' := by
  rw [overlap, overlap, max_comm u t, min_comm u t]

/-- The overlap does not see the orientation of the second interval. -/
theorem overlap_swap_right (t u t' u' : ℝ) : overlap t u u' t' = overlap t u t' u' := by
  rw [overlap, overlap, max_comm u' t', min_comm u' t']

/-- The covariance of the two increments has the overlap as its absolute value, whatever the
orientation of the two intervals. -/
theorem abs_crossCov (t u t' u' : ℝ) : |crossCov t u t' u'| = overlap t u t' u' := by
  rcases le_total t u with h | h <;> rcases le_total t' u' with h' | h'
  · rw [crossCov_eq_overlap h h', abs_of_nonneg (overlap_nonneg _ _ _ _)]
  · rw [show crossCov t u t' u' = -crossCov t u u' t' by rw [crossCov, crossCov]; ring,
      abs_neg, crossCov_eq_overlap h h', abs_of_nonneg (overlap_nonneg _ _ _ _),
      overlap_swap_right]
  · rw [show crossCov t u t' u' = -crossCov u t t' u' by rw [crossCov, crossCov]; ring,
      abs_neg, crossCov_eq_overlap h h', abs_of_nonneg (overlap_nonneg _ _ _ _),
      overlap_swap_left]
  · rw [show crossCov t u t' u' = crossCov u t u' t' by rw [crossCov, crossCov]; ring,
      crossCov_eq_overlap h h', abs_of_nonneg (overlap_nonneg _ _ _ _), overlap_swap_left,
      overlap_swap_right]

/-- The determinant `Δ = δδ' - O²` of `sec:variance`, written with the signed covariance. -/
theorem crossCov_sq (t u t' u' : ℝ) :
    crossCov t u t' u' ^ 2 = overlap t u t' u' ^ 2 := by
  rw [← abs_crossCov, sq_abs]

/-! ### The regression decomposition of the second increment -/

/-- The joint law of an increment and of the residual of the second increment after the
regression on the first, one spatial coordinate at a time. -/
theorem hasGaussianLaw_pair (hW : IsPlanarBrownian W P) {t u t' u' : ℝ≥0} (ρ : ℝ) (i : Fin 2) :
    HasGaussianLaw (fun ω => (W u ω i - W t ω i,
      (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i))) P := by
  classical
  have h4 := ((hW.coord i).toIsPreBrownianReal.isGaussianProcess).hasGaussianLaw
    ({t, u, t', u'} : Finset ℝ≥0)
  let L : ((({t, u, t', u'} : Finset ℝ≥0) : Type) → ℝ) →L[ℝ] ℝ × ℝ :=
    { toFun x := (x ⟨u, by simp⟩ - x ⟨t, by simp⟩,
        (x ⟨u', by simp⟩ - x ⟨t', by simp⟩) - ρ * (x ⟨u, by simp⟩ - x ⟨t, by simp⟩))
      map_add' := fun x y => by ext <;> simp <;> ring
      map_smul' := fun c x => by ext <;> simp <;> ring }
  exact h4.map_fun L

/-- The residual of the second increment after regression on the first is independent of the
first, since the two are jointly Gaussian and, by the choice of `ρ`, uncorrelated. -/
theorem indepFun_increment_residual [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {t u t' u' : ℝ≥0} {ρ : ℝ}
    (hρ : crossCov (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) = ρ * |(u : ℝ) - (t : ℝ)|) :
    IndepFun (fun ω => (W u ω 0 - W t ω 0, W u ω 1 - W t ω 1))
      (fun ω => ((W u' ω 0 - W t' ω 0) - ρ * (W u ω 0 - W t ω 0),
        (W u' ω 1 - W t' ω 1) - ρ * (W u ω 1 - W t ω 1))) P := by
  classical
  have hpair : ∀ i : Fin 2, HasGaussianLaw (fun ω => (W u ω i - W t ω i,
      (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i))) P :=
    fun i => hasGaussianLaw_pair hW ρ i
  have hg : Measurable
      (fun p : ℝ≥0 → ℝ => (p u - p t, (p u' - p t') - ρ * (p u - p t))) := by
    fun_prop
  have hindepPairs : iIndepFun (fun (i : Fin 2) ω => (W u ω i - W t ω i,
      (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i))) P :=
    hW.indep.comp (fun _ : Fin 2 => fun p : ℝ≥0 → ℝ =>
      (p u - p t, (p u' - p t') - ρ * (p u - p t))) fun _ => hg
  have hjoint := hindepPairs.hasGaussianLaw hpair
  let M : (Fin 2 → ℝ × ℝ) →L[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
    { toFun x := (fun i => (x i).1, fun i => (x i).2)
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun c x => by ext <;> simp }
  have hjoint2 : HasGaussianLaw (fun ω => ((fun i : Fin 2 => W u ω i - W t ω i),
      (fun i : Fin 2 => (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i)))) P :=
    hjoint.map_fun M
  -- the covariance of the two families vanishes
  have hcov : ∀ i j : Fin 2, cov[fun ω => W u ω i - W t ω i,
      fun ω => (W u' ω j - W t' ω j) - ρ * (W u ω j - W t ω j); P] = 0 := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · have hB := (hW.coord i).toIsPreBrownianReal
      have hZ : MemLp (fun ω => W u ω i - W t ω i) 2 P := (hpair i).fst.memLp_two
      have hZ' : MemLp (fun ω => W u' ω i - W t' ω i) 2 P :=
        (hB.isGaussianProcess.hasGaussianLaw_fun_sub (s := u') (t := t')).memLp_two
      have hZρ : MemLp (fun ω => ρ * (W u ω i - W t ω i)) 2 P := hZ.const_mul ρ
      rw [covariance_fun_sub_right hZ hZ' hZρ, covariance_const_mul_right,
        cov_increments hB, var_increment hB, hρ]
      ring
    · have hind : IndepFun (fun ω => W u ω i - W t ω i)
          (fun ω => (W u' ω j - W t' ω j) - ρ * (W u ω j - W t ω j)) P :=
        (hindepPairs.indepFun hij).comp measurable_fst measurable_snd
      exact hind.covariance_eq_zero (hpair i).fst.memLp_two (hpair j).snd.memLp_two
  have hindep2 := hjoint2.indepFun_of_covariance_eval hcov
  exact hindep2.comp (measurable_pi_apply 0 |>.prodMk (measurable_pi_apply 1))
    (measurable_pi_apply 0 |>.prodMk (measurable_pi_apply 1))

/-- The residual variance `δ' - 2ρO + ρ²δ` of the second increment after the regression on
the first. -/
noncomputable def residualVar (t u t' u' ρ : ℝ) : ℝ :=
  |u' - t'| - 2 * ρ * crossCov t u t' u' + ρ ^ 2 * |u - t|

/-- The law of the residual `Z' - ρZ`: its two coordinates are independent centred Gaussians
of variance `residualVar`. -/
theorem map_residual [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {t u t' u' : ℝ≥0} (ρ : ℝ) :
    P.map (fun ω => ((W u' ω 0 - W t' ω 0) - ρ * (W u ω 0 - W t ω 0),
        (W u' ω 1 - W t' ω 1) - ρ * (W u ω 1 - W t ω 1)))
      = (gaussianReal 0
            (residualVar (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ρ).toNNReal).prod
        (gaussianReal 0
            (residualVar (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ρ).toNNReal) := by
  have hpair : ∀ i : Fin 2, HasGaussianLaw (fun ω => (W u ω i - W t ω i,
      (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i))) P := fun i => hasGaussianLaw_pair hW ρ i
  have hN : ∀ i : Fin 2, HasGaussianLaw
      (fun ω => (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i)) P := fun i => (hpair i).snd
  have hlaw : ∀ i : Fin 2, P.map (fun ω => (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i))
      = gaussianReal 0 (residualVar (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ρ).toNNReal := by
    intro i
    have hB := (hW.coord i).toIsPreBrownianReal
    have hZg : HasGaussianLaw (fun ω => W u ω i - W t ω i) P :=
      hB.isGaussianProcess.hasGaussianLaw_fun_sub (s := u) (t := t)
    have hZ'g : HasGaussianLaw (fun ω => W u' ω i - W t' ω i) P :=
      hB.isGaussianProcess.hasGaussianLaw_fun_sub (s := u') (t := t')
    have hZ2 : MemLp (fun ω => W u ω i - W t ω i) 2 P := hZg.memLp_two
    have hZ'2 : MemLp (fun ω => W u' ω i - W t' ω i) 2 P := hZ'g.memLp_two
    have hρZ2 : MemLp (fun ω => ρ * (W u ω i - W t ω i)) 2 P := hZ2.const_mul ρ
    have hmean0 : ∀ a b : ℝ≥0, ∫ ω, (W b ω i - W a ω i) ∂P = 0 := by
      intro a b
      have h := (hB.hasLaw_sub b a).integral_eq
      simp only [Pi.sub_apply] at h
      rw [h, integral_id_gaussianReal]
    have hmean : ∫ ω, ((W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i)) ∂P = 0 := by
      rw [integral_sub hZ'g.integrable (hZg.integrable.const_mul ρ), integral_const_mul,
        hmean0 t u, hmean0 t' u']
      ring
    have hvar : Var[fun ω => (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i); P]
        = residualVar (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ρ := by
      rw [← covariance_self (hN i).aemeasurable,
        covariance_fun_sub_fun_sub hZ'2 hρZ2 hZ'2 hρZ2]
      simp only [covariance_const_mul_right, covariance_const_mul_left, cov_increments hB,
        crossCov_self, crossCov_comm, residualVar]
      ring
    rw [(hN i).map_eq_gaussianReal, hmean, hvar]
  have hae : ∀ i : Fin 2,
      AEMeasurable (fun ω => (W u' ω i - W t' ω i) - ρ * (W u ω i - W t ω i)) P :=
    fun i => (hN i).aemeasurable
  have hindep : IndepFun (fun ω => (W u' ω 0 - W t' ω 0) - ρ * (W u ω 0 - W t ω 0))
      (fun ω => (W u' ω 1 - W t' ω 1) - ρ * (W u ω 1 - W t ω 1)) P := by
    have hg : Measurable (fun p : ℝ≥0 → ℝ => (p u' - p t') - ρ * (p u - p t)) := by fun_prop
    exact (hW.indep.comp (fun _ : Fin 2 => fun p : ℝ≥0 → ℝ => (p u' - p t') - ρ * (p u - p t))
      fun _ => hg).indepFun (show (0 : Fin 2) ≠ 1 by decide)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hae 0) (hae 1)).mp hindep, hlaw 0, hlaw 1]

/-! ### The determinant branch of `eq:joint-return-bound` -/

/-- The mass of the disc of radius `r` centred anywhere, in the shift form the slice of the
joint event takes. -/
theorem gaussianProd_disc_le' {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v))
        {q : ℝ × ℝ | (q.1 + a) ^ 2 + (q.2 + b) ^ 2 < r ^ 2}
      ≤ ENNReal.ofReal (r ^ 2 / (2 * (v : ℝ))) := by
  have hset : {q : ℝ × ℝ | (q.1 + a) ^ 2 + (q.2 + b) ^ 2 < r ^ 2}
      = {q : ℝ × ℝ | (q.1 - (-a)) ^ 2 + (q.2 - (-b)) ^ 2 < r ^ 2} := by
    ext q
    simp [sub_neg_eq_add]
  rw [hset]
  exact gaussianProd_disc_le hv hr (-a, -b)

/-- The mass of the disc of radius `r` centred at the origin. -/
theorem gaussianProd_disc_le₀ {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)) {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2}
      ≤ ENNReal.ofReal (r ^ 2 / (2 * (v : ℝ))) := by
  have hset : {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2}
      = {q : ℝ × ℝ | (q.1 + 0) ^ 2 + (q.2 + 0) ^ 2 < r ^ 2} := by
    ext q
    simp
  rw [hset]
  exact gaussianProd_disc_le' hv hr 0 0

/-- `eq:joint-return-bound`, the determinant branch: the joint return probability is at most
`r⁴/(4Δ)`.  The second increment is written as `ρZ + N` with `N` independent of `Z`, and each
of the two factors is bounded by the mass of a disc of radius `r`. -/
theorem jointReturn_le_det [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {r : ℝ} (hr : 0 < r) {t u t' u' : ℝ≥0}
    (hΔ : 0 < |(u : ℝ) - (t : ℝ)| * |(u' : ℝ) - (t' : ℝ)|
      - overlap (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ^ 2) :
    jointReturn W P r t u t' u'
      ≤ ENNReal.ofReal (r ^ 4 / (4 * (|(u : ℝ) - (t : ℝ)| * |(u' : ℝ) - (t' : ℝ)|
          - overlap (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ^ 2))) := by
  classical
  have hcsq : crossCov (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ^ 2
      = overlap (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ^ 2 := crossCov_sq _ _ _ _
  rw [← hcsq] at hΔ ⊢
  set δ : ℝ := |(u : ℝ) - (t : ℝ)| with hδdef
  set δ' : ℝ := |(u' : ℝ) - (t' : ℝ)| with hδ'def
  set c : ℝ := crossCov (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) with hcdef
  have hδ0 : (0 : ℝ) ≤ δ := abs_nonneg _
  have hδ'0 : (0 : ℝ) ≤ δ' := abs_nonneg _
  have hc0 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
  have hδ : 0 < δ := by nlinarith
  have hδ' : 0 < δ' := by nlinarith
  set ρ : ℝ := c / δ with hρdef
  set v : ℝ := (δ * δ' - c ^ 2) / δ with hvdef
  have hv : 0 < v := div_pos hΔ hδ
  have hδv : δ * v = δ * δ' - c ^ 2 := by
    rw [hvdef]
    field_simp
  have hρc : c = ρ * δ := by
    rw [hρdef]
    field_simp
  have hresid : residualVar (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ρ = v := by
    rw [residualVar, ← hcdef, ← hδdef, ← hδ'def, hvdef, hρdef]
    field_simp
    ring
  -- the two laws
  have hZlaw := hW.map_increment t u
  have hcoe : ((nndist (u : ℝ) (t : ℝ) : ℝ≥0) : ℝ) = δ := by
    rw [coe_nndist, Real.dist_eq, hδdef]
  have hZne : nndist (u : ℝ) (t : ℝ) ≠ 0 := by
    intro h
    rw [h] at hcoe
    simp only [NNReal.coe_zero] at hcoe
    exact absurd hcoe.symm (ne_of_gt hδ)
  have hNlaw := map_residual hW (t := t) (u := u) (t' := t') (u' := u') ρ
  rw [hresid] at hNlaw
  have hvne : v.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hv).ne'
  have hvcoe : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal v hv.le
  -- the independence
  have hindep := indepFun_increment_residual hW (t := t) (u := u) (t' := t') (u' := u')
    (ρ := ρ) (by rw [← hcdef, hρc])
  have hZae : AEMeasurable (fun ω => (W u ω 0 - W t ω 0, W u ω 1 - W t ω 1)) P := by
    refine AEMeasurable.prodMk ?_ ?_ <;>
      exact (((hW.coord _).toIsPreBrownianReal.aemeasurable u).sub
        ((hW.coord _).toIsPreBrownianReal.aemeasurable t))
  have hNae : AEMeasurable (fun ω => ((W u' ω 0 - W t' ω 0) - ρ * (W u ω 0 - W t ω 0),
      (W u' ω 1 - W t' ω 1) - ρ * (W u ω 1 - W t ω 1))) P := by
    refine AEMeasurable.prodMk ?_ ?_ <;>
      exact ((((hW.coord _).toIsPreBrownianReal.aemeasurable u').sub
        ((hW.coord _).toIsPreBrownianReal.aemeasurable t')).sub
        ((((hW.coord _).toIsPreBrownianReal.aemeasurable u).sub
          ((hW.coord _).toIsPreBrownianReal.aemeasurable t)).const_mul ρ))
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hZae hNae).mp hindep
  -- the joint event, read through the pair `(Z, N)`
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1.1 ^ 2 + p.1.2 ^ 2 < r ^ 2 ∧
    (p.2.1 + ρ * p.1.1) ^ 2 + (p.2.2 + ρ * p.1.2) ^ 2 < r ^ 2} with hSdef
  have hSmeas : MeasurableSet S := by
    have h1 : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1.1 ^ 2 + p.1.2 ^ 2 < r ^ 2} :=
      measurableSet_lt (by fun_prop) measurable_const
    have h2 : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) |
        (p.2.1 + ρ * p.1.1) ^ 2 + (p.2.2 + ρ * p.1.2) ^ 2 < r ^ 2} :=
      measurableSet_lt (by fun_prop) measurable_const
    exact h1.inter h2
  have hdist : ∀ x y : Plane, dist x y < r ↔ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 < r ^ 2 := by
    intro x y
    rw [EuclideanSpace.dist_eq]
    simp only [Real.dist_eq, Fin.sum_univ_two, sq_abs]
    exact Real.sqrt_lt' hr
  have hevent : {ω | dist (W u ω) (W t ω) < r ∧ dist (W u' ω) (W t' ω) < r}
      = (fun ω => ((W u ω 0 - W t ω 0, W u ω 1 - W t ω 1),
          ((W u' ω 0 - W t' ω 0) - ρ * (W u ω 0 - W t ω 0),
            (W u' ω 1 - W t' ω 1) - ρ * (W u ω 1 - W t ω 1)))) ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdist, hSdef]
    refine and_congr Iff.rfl ?_
    have key : ((W u' ω 0 - W t' ω 0 - ρ * (W u ω 0 - W t ω 0)) + ρ * (W u ω 0 - W t ω 0)) ^ 2
        + ((W u' ω 1 - W t' ω 1 - ρ * (W u ω 1 - W t ω 1)) + ρ * (W u ω 1 - W t ω 1)) ^ 2
        = (W u' ω 0 - W t' ω 0) ^ 2 + (W u' ω 1 - W t' ω 1) ^ 2 := by ring
    rw [key]
  rw [jointReturn, hevent, ← Measure.map_apply_of_aemeasurable (hZae.prodMk hNae) hSmeas,
    hprod, hZlaw, hNlaw, Measure.prod_apply hSmeas]
  calc ∫⁻ z, ((gaussianReal 0 v.toNNReal).prod (gaussianReal 0 v.toNNReal))
          (Prod.mk z ⁻¹' S) ∂((gaussianReal 0 (nndist (u : ℝ) (t : ℝ))).prod
            (gaussianReal 0 (nndist (u : ℝ) (t : ℝ))))
      ≤ ∫⁻ z, Set.indicator {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < r ^ 2}
          (fun _ => ENNReal.ofReal (r ^ 2 / (2 * v))) z
          ∂((gaussianReal 0 (nndist (u : ℝ) (t : ℝ))).prod
            (gaussianReal 0 (nndist (u : ℝ) (t : ℝ)))) := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z.1 ^ 2 + z.2 ^ 2 < r ^ 2
        · rw [Set.indicator_of_mem (s := {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < r ^ 2}) hz]
          have hslice : Prod.mk z ⁻¹' S
              = {n : ℝ × ℝ | (n.1 + ρ * z.1) ^ 2 + (n.2 + ρ * z.2) ^ 2 < r ^ 2} := by
            ext n
            simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, hz, true_and]
          rw [hslice]
          have hb := gaussianProd_disc_le' hvne hr (ρ * z.1) (ρ * z.2)
          rwa [hvcoe] at hb
        · rw [Set.indicator_of_notMem (s := {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < r ^ 2}) hz]
          have hslice : Prod.mk z ⁻¹' S = (∅ : Set (ℝ × ℝ)) := by
            ext n
            simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, Set.mem_empty_iff_false,
              iff_false, not_and]
            exact fun h => absurd h hz
          rw [hslice, measure_empty]
    _ = ENNReal.ofReal (r ^ 2 / (2 * v))
          * ((gaussianReal 0 (nndist (u : ℝ) (t : ℝ))).prod
            (gaussianReal 0 (nndist (u : ℝ) (t : ℝ)))) {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < r ^ 2} := by
        rw [lintegral_indicator (measurableSet_lt (by fun_prop) measurable_const),
          setLIntegral_const]
    _ ≤ ENNReal.ofReal (r ^ 2 / (2 * v)) * ENNReal.ofReal (r ^ 2 / (2 * δ)) := by
        gcongr
        rw [← hcoe]
        exact gaussianProd_disc_le₀ hZne hr
    _ = ENNReal.ofReal (r ^ 4 / (4 * (δ * δ' - c ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← hδv]
        field_simp
        ring

/-! ### The marginal branch of `eq:joint-return-bound` -/

/-- The joint return event is symmetric in the two time pairs. -/
theorem jointReturn_comm (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (r : ℝ) (t u t' u' : ℝ≥0) :
    jointReturn W P r t u t' u' = jointReturn W P r t' u' t u := by
  rw [jointReturn, jointReturn]
  congr 1
  ext ω
  exact and_comm

/-- `eq:joint-return-bound`, the marginal branch for the first pair: the joint return
probability is at most the return probability `1 - e^{-r²/(2δ)} ≤ r²/(2δ)` of the first
increment. -/
theorem jointReturn_le_marginal [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {r : ℝ} (hr : 0 < r) {t u t' u' : ℝ≥0} (htu : t ≠ u) :
    jointReturn W P r t u t' u' ≤ ENNReal.ofReal (r ^ 2 / (2 * |(u : ℝ) - (t : ℝ)|)) := by
  have hsub : {ω | dist (W u ω) (W t ω) < r ∧ dist (W u' ω) (W t' ω) < r}
      ⊆ {ω | dist (W u ω) (W t ω) < r} := fun ω h => h.1
  calc jointReturn W P r t u t' u' ≤ P {ω | dist (W u ω) (W t ω) < r} := measure_mono hsub
    _ = ENNReal.ofReal (1 - Real.exp (-(r ^ 2 / (2 * |(u : ℝ) - (t : ℝ)|)))) :=
        hW.return_prob hr htu
    _ ≤ ENNReal.ofReal (r ^ 2 / (2 * |(u : ℝ) - (t : ℝ)|)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h := Real.add_one_le_exp (-(r ^ 2 / (2 * |(u : ℝ) - (t : ℝ)|)))
        linarith

/-- `eq:joint-return-bound`, the marginal branch: the longer of the two increments gives the
bound `r²/(2 max(δ,δ'))`. -/
theorem jointReturn_le_max [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {r : ℝ} (hr : 0 < r) {t u t' u' : ℝ≥0} (htu : t ≠ u) (htu' : t' ≠ u') :
    jointReturn W P r t u t' u'
      ≤ ENNReal.ofReal (r ^ 2 / (2 * max |(u : ℝ) - (t : ℝ)| |(u' : ℝ) - (t' : ℝ)|)) := by
  rcases max_cases |(u : ℝ) - (t : ℝ)| |(u' : ℝ) - (t' : ℝ)| with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact jointReturn_le_marginal hW hr htu
  · rw [h, jointReturn_comm]
    exact jointReturn_le_marginal hW hr htu'

/-- The two time pairs are non-degenerate as soon as the determinant is positive. -/
theorem ne_of_det_pos {t u t' u' : ℝ≥0}
    (hΔ : 0 < |(u : ℝ) - (t : ℝ)| * |(u' : ℝ) - (t' : ℝ)|
      - overlap (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ^ 2) :
    0 < |(u : ℝ) - (t : ℝ)| ∧ 0 < |(u' : ℝ) - (t' : ℝ)| := by
  have hδ0 : (0 : ℝ) ≤ |(u : ℝ) - (t : ℝ)| := abs_nonneg _
  have hδ'0 : (0 : ℝ) ≤ |(u' : ℝ) - (t' : ℝ)| := abs_nonneg _
  have hc0 : (0 : ℝ) ≤ overlap (t : ℝ) (u : ℝ) (t' : ℝ) (u' : ℝ) ^ 2 := sq_nonneg _
  constructor <;> nlinarith

/-- Distinct times, from a non-degenerate interval. -/
theorem ne_of_abs_pos {t u : ℝ≥0} (h : 0 < |(u : ℝ) - (t : ℝ)|) : t ≠ u := by
  intro htu
  rw [htu] at h
  simp at h

/-! ### The degenerate case of `eq:joint-return-bound` -/

/-- The overlap never exceeds the length of the first interval. -/
theorem overlap_le_left (x₁ x₂ x₃ x₄ : ℝ) : overlap x₁ x₂ x₃ x₄ ≤ |x₂ - x₁| := by
  have habs : |x₂ - x₁| = max x₁ x₂ - min x₁ x₂ := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
  rw [overlap, habs]
  refine max_le (sub_nonneg.mpr min_le_max) ?_
  have h1 : min (max x₁ x₂) (max x₃ x₄) ≤ max x₁ x₂ := min_le_left _ _
  have h2 : min x₁ x₂ ≤ max (min x₁ x₂) (min x₃ x₄) := le_max_left _ _
  linarith

/-- The overlap never exceeds the length of the second interval. -/
theorem overlap_le_right (x₁ x₂ x₃ x₄ : ℝ) : overlap x₁ x₂ x₃ x₄ ≤ |x₄ - x₃| := by
  have habs : |x₄ - x₃| = max x₃ x₄ - min x₃ x₄ := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
  rw [overlap, habs]
  refine max_le (sub_nonneg.mpr min_le_max) ?_
  have h1 : min (max x₁ x₂) (max x₃ x₄) ≤ max x₃ x₄ := min_le_right _ _
  have h2 : min x₃ x₄ ≤ max (min x₁ x₂) (min x₃ x₄) := le_max_right _ _
  linarith

/-- The determinant `Δ = δδ' - O²` is never negative. -/
theorem det_nonneg (x₁ x₂ x₃ x₄ : ℝ) :
    0 ≤ |x₂ - x₁| * |x₄ - x₃| - overlap x₁ x₂ x₃ x₄ ^ 2 := by
  have h0 := overlap_nonneg x₁ x₂ x₃ x₄
  have h1 := overlap_le_left x₁ x₂ x₃ x₄
  have h2 := overlap_le_right x₁ x₂ x₃ x₄
  nlinarith

/-- The degenerate case `Δ = 0` with a positive overlap forces the two unoriented intervals
to agree, so that the third endpoint is one of the first two.  Hence `Δ > 0` as soon as the
third endpoint avoids the first two. -/
theorem det_pos_of_ne {x₁ x₂ x₃ x₄ : ℝ} (h₁ : x₃ ≠ x₁) (h₂ : x₃ ≠ x₂)
    (hO : 0 < overlap x₁ x₂ x₃ x₄) :
    0 < |x₂ - x₁| * |x₄ - x₃| - overlap x₁ x₂ x₃ x₄ ^ 2 := by
  rcases (det_nonneg x₁ x₂ x₃ x₄).lt_or_eq with h | h
  · exact h
  exfalso
  have h1 := overlap_le_left x₁ x₂ x₃ x₄
  have h2 := overlap_le_right x₁ x₂ x₃ x₄
  have hd1 : |x₂ - x₁| = overlap x₁ x₂ x₃ x₄ := by nlinarith
  have hd2 : |x₄ - x₃| = overlap x₁ x₂ x₃ x₄ := by nlinarith
  have hX : 0 < min (max x₁ x₂) (max x₃ x₄) - max (min x₁ x₂) (min x₃ x₄) := by
    by_contra hcon
    rw [overlap, max_eq_left (not_lt.mp hcon)] at hO
    exact absurd hO (lt_irrefl 0)
  have hOval : overlap x₁ x₂ x₃ x₄
      = min (max x₁ x₂) (max x₃ x₄) - max (min x₁ x₂) (min x₃ x₄) := by
    rw [overlap, max_eq_right hX.le]
  have e1 : max x₁ x₂ - min x₁ x₂
      = min (max x₁ x₂) (max x₃ x₄) - max (min x₁ x₂) (min x₃ x₄) := by
    rw [← hOval, ← hd1, max_sub_min_eq_abs, abs_sub_comm]
  have e2 : max x₃ x₄ - min x₃ x₄
      = min (max x₁ x₂) (max x₃ x₄) - max (min x₁ x₂) (min x₃ x₄) := by
    rw [← hOval, ← hd2, max_sub_min_eq_abs, abs_sub_comm]
  have m1 : min (max x₁ x₂) (max x₃ x₄) ≤ max x₁ x₂ := min_le_left _ _
  have m2 : min (max x₁ x₂) (max x₃ x₄) ≤ max x₃ x₄ := min_le_right _ _
  have m3 : min x₁ x₂ ≤ max (min x₁ x₂) (min x₃ x₄) := le_max_left _ _
  have m4 : min x₃ x₄ ≤ max (min x₁ x₂) (min x₃ x₄) := le_max_right _ _
  have hmax : max x₁ x₂ = max x₃ x₄ := by linarith
  have hmin : min x₁ x₂ = min x₃ x₄ := by linarith
  have hx3 : x₃ = min x₁ x₂ ∨ x₃ = max x₁ x₂ := by
    rcases le_total x₃ x₄ with h | h
    · exact Or.inl (by rw [hmin]; exact (min_eq_left h).symm)
    · exact Or.inr (by rw [hmax]; exact (max_eq_left h).symm)
  rcases hx3 with h | h
  · rcases min_choice x₁ x₂ with hm | hm <;> rw [hm] at h
    · exact h₁ h
    · exact h₂ h
  · rcases max_choice x₁ x₂ with hm | hm <;> rw [hm] at h
    · exact h₁ h
    · exact h₂ h

/-! ### The null set of `thm:gaussian-four-point` -/

/-- A fixed value is `μ`-null in the third coordinate of the quadruple. -/
theorem prod_slice_null {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) (x : ℝ) : (μ.prod μ) {z : ℝ × ℝ | z.1 = x} = 0 := by
  have hset : {z : ℝ × ℝ | z.1 = x} = ({x} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext z
    simp
  rw [hset, Measure.prod_prod, hμ.measure_singleton hs, zero_mul]

/-- The third endpoint differs from the first, `μ⁴`-almost everywhere. -/
theorem ae_third_ne_first {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), q.2.2.1 ≠ q.1 := by
  have hmeas : MeasurableSet {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 = q.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hnull : (μ.prod (μ.prod (μ.prod μ))) {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 = q.1} = 0 := by
    have hs2 : ∀ x : ℝ, (μ.prod (μ.prod μ)) {p : ℝ × ℝ × ℝ | p.2.1 = x} = 0 := by
      intro x
      have hmeas2 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.1 = x} :=
        measurableSet_eq_fun (by fun_prop) measurable_const
      rw [Measure.prod_apply hmeas2]
      calc ∫⁻ y, (μ.prod μ) (Prod.mk y ⁻¹' {p : ℝ × ℝ × ℝ | p.2.1 = x}) ∂μ
          = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun y => prod_slice_null hs hμ x
        _ = 0 := lintegral_zero
    rw [Measure.prod_apply hmeas]
    calc ∫⁻ x, (μ.prod (μ.prod μ))
            (Prod.mk x ⁻¹' {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 = q.1}) ∂μ
        = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun x => hs2 x
      _ = 0 := lintegral_zero
  rw [ae_iff]
  exact measure_mono_null (fun q hq => not_not.mp hq) hnull

/-- The third endpoint differs from the second, `μ⁴`-almost everywhere. -/
theorem ae_third_ne_second {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), q.2.2.1 ≠ q.2.1 := by
  have hmeas : MeasurableSet {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 = q.2.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hnull : (μ.prod (μ.prod (μ.prod μ))) {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 = q.2.1} = 0 := by
    have hmeas2 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.1 = p.1} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hs2 : (μ.prod (μ.prod μ)) {p : ℝ × ℝ × ℝ | p.2.1 = p.1} = 0 := by
      rw [Measure.prod_apply hmeas2]
      calc ∫⁻ y, (μ.prod μ) (Prod.mk y ⁻¹' {p : ℝ × ℝ × ℝ | p.2.1 = p.1}) ∂μ
          = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun y => prod_slice_null hs hμ y
        _ = 0 := lintegral_zero
    rw [Measure.prod_apply hmeas]
    calc ∫⁻ x, (μ.prod (μ.prod μ))
            (Prod.mk x ⁻¹' {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 = q.2.1}) ∂μ
        = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun x => hs2
      _ = 0 := lintegral_zero
  rw [ae_iff]
  exact measure_mono_null (fun q hq => not_not.mp hq) hnull

/-- The determinant is positive as soon as neither interval is degenerate and the two
unoriented intervals do not agree.  There is no overlap hypothesis: where the intervals
are disjoint the overlap vanishes and the determinant is the product of the two lengths.
This is the unconditional `Δ > 0` of `thm:gaussian-four-point`. -/
theorem det_pos_of_ne_of_nondegenerate {x₁ x₂ x₃ x₄ : ℝ} (h₁ : x₃ ≠ x₁) (h₂ : x₃ ≠ x₂)
    (h₁₂ : x₂ ≠ x₁) (h₃₄ : x₄ ≠ x₃) :
    0 < |x₂ - x₁| * |x₄ - x₃| - overlap x₁ x₂ x₃ x₄ ^ 2 := by
  rcases (overlap_nonneg x₁ x₂ x₃ x₄).lt_or_eq with hO | hO
  · exact det_pos_of_ne h₁ h₂ hO
  · have hd1 : 0 < |x₂ - x₁| := abs_pos.mpr (sub_ne_zero.mpr h₁₂)
    have hd2 : 0 < |x₄ - x₃| := abs_pos.mpr (sub_ne_zero.mpr h₃₄)
    rw [← hO]
    simpa using mul_pos hd1 hd2

/-- The diagonal of `μ × μ` is null, which is atomlessness again. -/
theorem prod_diag_null {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) : (μ.prod μ) {z : ℝ × ℝ | z.2 = z.1} = 0 := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | z.2 = z.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  rw [Measure.prod_apply hmeas]
  calc ∫⁻ a, μ (Prod.mk a ⁻¹' {z : ℝ × ℝ | z.2 = z.1}) ∂μ
      = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun a => by
          have hpre : (Prod.mk a ⁻¹' {z : ℝ × ℝ | z.2 = z.1}) = ({a} : Set ℝ) := by
            ext b; simp
          rw [hpre, hμ.measure_singleton hs]
    _ = 0 := lintegral_zero

/-- Fixing the first of three coordinates is null. -/
theorem triple_slice_null {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) (x : ℝ) :
    (μ.prod (μ.prod μ)) {p : ℝ × ℝ × ℝ | p.1 = x} = 0 := by
  have hset : {p : ℝ × ℝ × ℝ | p.1 = x} = ({x} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext p; simp
  rw [hset, Measure.prod_prod, hμ.measure_singleton hs, zero_mul]

/-- The second endpoint differs from the first, `μ⁴`-almost everywhere: the first
interval is non-degenerate. -/
theorem ae_second_ne_first {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), q.2.1 ≠ q.1 := by
  have hmeas : MeasurableSet {q : ℝ × ℝ × ℝ × ℝ | q.2.1 = q.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hnull : (μ.prod (μ.prod (μ.prod μ))) {q : ℝ × ℝ × ℝ × ℝ | q.2.1 = q.1} = 0 := by
    rw [Measure.prod_apply hmeas]
    calc ∫⁻ x, (μ.prod (μ.prod μ))
            (Prod.mk x ⁻¹' {q : ℝ × ℝ × ℝ × ℝ | q.2.1 = q.1}) ∂μ
        = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun x => triple_slice_null hs hμ x
      _ = 0 := lintegral_zero
  rw [ae_iff]
  exact measure_mono_null (fun q hq => not_not.mp hq) hnull

/-- The fourth endpoint differs from the third, `μ⁴`-almost everywhere: the second
interval is non-degenerate. -/
theorem ae_fourth_ne_third {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), q.2.2.2 ≠ q.2.2.1 := by
  have hmeas : MeasurableSet {q : ℝ × ℝ × ℝ × ℝ | q.2.2.2 = q.2.2.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hnull : (μ.prod (μ.prod (μ.prod μ))) {q : ℝ × ℝ × ℝ × ℝ | q.2.2.2 = q.2.2.1} = 0 := by
    have hs2 : (μ.prod (μ.prod μ)) {p : ℝ × ℝ × ℝ | p.2.2 = p.2.1} = 0 := by
      have hmeas2 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.2 = p.2.1} :=
        measurableSet_eq_fun (by fun_prop) (by fun_prop)
      rw [Measure.prod_apply hmeas2]
      calc ∫⁻ y, (μ.prod μ) (Prod.mk y ⁻¹' {p : ℝ × ℝ × ℝ | p.2.2 = p.2.1}) ∂μ
          = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun y => prod_diag_null hs hμ
        _ = 0 := lintegral_zero
    rw [Measure.prod_apply hmeas]
    calc ∫⁻ x, (μ.prod (μ.prod μ))
            (Prod.mk x ⁻¹' {q : ℝ × ℝ × ℝ × ℝ | q.2.2.2 = q.2.2.1}) ∂μ
        = ∫⁻ _ : ℝ, 0 ∂μ := lintegral_congr fun x => hs2
      _ = 0 := lintegral_zero
  rw [ae_iff]
  exact measure_mono_null (fun q hq => not_not.mp hq) hnull

/-- The four endpoints are non-negative, `μ⁴`-almost everywhere: `μ` sits on `[0,1]`. -/
theorem ae_nonneg {s A : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))),
      0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2.1 ∧ 0 ≤ q.2.2.2 := by
  have hcompl : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → 0 ≤ x := fun x hx => hx.1
  have h1 : ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), 0 ≤ q.1 := by
    rw [ae_iff]
    have hsub : {q : ℝ × ℝ × ℝ × ℝ | ¬ 0 ≤ q.1}
        ⊆ (Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set (ℝ × ℝ × ℝ)) :=
      fun q hq => Set.mem_prod.mpr ⟨fun hmem => hq (hcompl _ hmem), Set.mem_univ _⟩
    refine measure_mono_null hsub ?_
    rw [Measure.prod_prod, hμ.support, zero_mul]
  have h2 : ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), 0 ≤ q.2.1 := by
    rw [ae_iff]
    have hsub : {q : ℝ × ℝ × ℝ × ℝ | ¬ 0 ≤ q.2.1}
        ⊆ (Set.univ : Set ℝ) ×ˢ ((Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set (ℝ × ℝ))) :=
      fun q hq => Set.mem_prod.mpr ⟨Set.mem_univ _,
        Set.mem_prod.mpr ⟨fun hmem => hq (hcompl _ hmem), Set.mem_univ _⟩⟩
    refine measure_mono_null hsub ?_
    rw [Measure.prod_prod, Measure.prod_prod, hμ.support, zero_mul, mul_zero]
  have h3 : ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), 0 ≤ q.2.2.1 := by
    rw [ae_iff]
    have hsub : {q : ℝ × ℝ × ℝ × ℝ | ¬ 0 ≤ q.2.2.1}
        ⊆ (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ
          ((Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ))) :=
      fun q hq => Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_prod.mpr ⟨Set.mem_univ _,
        Set.mem_prod.mpr ⟨fun hmem => hq (hcompl _ hmem), Set.mem_univ _⟩⟩⟩
    refine measure_mono_null hsub ?_
    rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hμ.support, zero_mul,
      mul_zero, mul_zero]
  have h4 : ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))), 0 ≤ q.2.2.2 := by
    rw [ae_iff]
    have hsub : {q : ℝ × ℝ × ℝ × ℝ | ¬ 0 ≤ q.2.2.2}
        ⊆ (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ
          ((Set.univ : Set ℝ) ×ˢ (Set.Icc (0:ℝ) 1)ᶜ)) :=
      fun q hq => Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_prod.mpr ⟨Set.mem_univ _,
        Set.mem_prod.mpr ⟨Set.mem_univ _, fun hmem => hq (hcompl _ hmem)⟩⟩⟩
    refine measure_mono_null hsub ?_
    rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hμ.support, mul_zero,
      mul_zero, mul_zero]
  filter_upwards [h1, h2, h3, h4] with q hq1 hq2 hq3 hq4
  exact ⟨hq1, hq2, hq3, hq4⟩

end FourPointBound

/-! ### `thm:gaussian-four-point`, `eq:joint-return-bound` -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `thm:gaussian-four-point`, `eq:joint-return-bound`.  The joint return probability of
two overlapping Brownian increments.  The times are non-negative by type. -/
theorem gaussian_four_point {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {r : ℝ} {t u t' u' : ℝ≥0}
    (hr : 0 < r)
    (hΔ : 0 < |(u:ℝ) - t| * |(u':ℝ) - t'| - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2) :
    (jointReturn W P r t u t' u').toReal
      ≤ min 1 (min (r ^ 2 / (2 * max |(u:ℝ) - t| |(u':ℝ) - t'|))
          (r ^ 4 / (4 * (|(u:ℝ) - t| * |(u':ℝ) - t'|
            - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2)))) := by
  obtain ⟨hδ, hδ'⟩ := FourPointBound.ne_of_det_pos hΔ
  have htu : t ≠ u := FourPointBound.ne_of_abs_pos hδ
  have htu' : t' ≠ u' := FourPointBound.ne_of_abs_pos hδ'
  refine le_min ?_ (le_min ?_ ?_)
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (FourPointBound.jointReturn_le_max hW hr htu htu')
  · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (FourPointBound.jointReturn_le_det hW hr hΔ)

/-- `thm:gaussian-four-point`, `eq:joint-return-bound` as the paper states it: outside a
`μ⁴`-null set the determinant is positive and the bound holds.  The degenerate case
`Δ = 0` forces the two unoriented intervals to agree, which is null for a Frostman
measure. -/
theorem gaussian_four_point_ae {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (_hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))),
      0 < |q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
          - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2 ∧
        (0 < overlap q.1 q.2.1 q.2.2.1 q.2.2.2 →
          (jointReturn W P r q.1.toNNReal q.2.1.toNNReal q.2.2.1.toNNReal
              q.2.2.2.toNNReal).toReal
            ≤ min 1 (min (r ^ 2 / (2 * max |q.2.1 - q.1| |q.2.2.2 - q.2.2.1|))
                (r ^ 4 / (4 * (|q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
                  - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2))))) := by
  filter_upwards [FourPointBound.ae_nonneg hμ, FourPointBound.ae_third_ne_first hs0 hμ,
    FourPointBound.ae_third_ne_second hs0 hμ, FourPointBound.ae_second_ne_first hs0 hμ,
    FourPointBound.ae_fourth_ne_third hs0 hμ] with q hq hne1 hne2 hne12 hne34
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hΔ : 0 < |q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
      - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2 :=
    FourPointBound.det_pos_of_ne_of_nondegenerate hne1 hne2 hne12 hne34
  refine ⟨hΔ, fun _ => ?_⟩
  have c1 : ((q.1.toNNReal : ℝ≥0) : ℝ) = q.1 := Real.coe_toNNReal _ h1
  have c2 : ((q.2.1.toNNReal : ℝ≥0) : ℝ) = q.2.1 := Real.coe_toNNReal _ h2
  have c3 : ((q.2.2.1.toNNReal : ℝ≥0) : ℝ) = q.2.2.1 := Real.coe_toNNReal _ h3
  have c4 : ((q.2.2.2.toNNReal : ℝ≥0) : ℝ) = q.2.2.2 := Real.coe_toNNReal _ h4
  have key := gaussian_four_point hW (r := r) (t := q.1.toNNReal) (u := q.2.1.toNNReal)
    (t' := q.2.2.1.toNNReal) (u' := q.2.2.2.toNNReal) hr (by rw [c1, c2, c3, c4]; exact hΔ)
  rwa [c1, c2, c3, c4] at key

/-- `thm:gaussian-four-point` as one statement: independence off the overlap, and the
almost everywhere return bound on it. -/
theorem gaussian_four_point_bundled {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    (∀ t u t' u' : ℝ≥0, (max t u ≤ min t' u' ∨ max t' u' ≤ min t u) →
        IndepFun (fun ω => W u ω - W t ω) (fun ω => W u' ω - W t' ω) P) ∧
      ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))),
        0 < |q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
            - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2 ∧
          (0 < overlap q.1 q.2.1 q.2.2.1 q.2.2.2 →
            (jointReturn W P r q.1.toNNReal q.2.1.toNNReal q.2.2.1.toNNReal
                q.2.2.2.toNNReal).toReal
              ≤ min 1 (min (r ^ 2 / (2 * max |q.2.1 - q.1| |q.2.2.2 - q.2.2.1|))
                  (r ^ 4 / (4 * (|q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
                    - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2))))) := by
  refine ⟨fun t u t' u' hdisj => disjoint_increments_indep hW hdisj, ?_⟩
  exact gaussian_four_point_ae hW hs0 hs1 hμ hr

end BrownianImages


