/-
`thm:neighbourhood-concentration` of `sec:reconstruction`: the `L²` input that
`thm:neighbourhood-moments` provides.  The `q = 2` moment bound gives a bound for the
`L²` norm of the normalised profile `X(t)`, uniform in `t ≥ 0`; the concentration proof
uses it for the variance of every summand of `Y_{r,u}` and at the small scales the
stopping argument does not cover.

* `MinkowskiL2Recurrence.centeredL2Norm_const_mul`: homogeneity of the centred norm.
* `IsNatural.exists_brownianTubeProfile_lpNorm_bound_of_tubeMomentsUpper`: the uniform
  `L²` bound.
-/
import BrownianImages.Minkowski.L2Recurrence
import BrownianImages.Minkowski.Profile

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace MinkowskiL2Recurrence

/-- Centered `L²` size is homogeneous under multiplication by a nonnegative
real scalar. -/
theorem centeredL2Norm_const_mul
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsFiniteMeasure P] {X : Omega → ℝ} (hX : MemLp X 2 P)
    {c : ℝ} (hc : 0 ≤ c) :
    centeredL2Norm (fun omega => c * X omega) P =
      c * centeredL2Norm X P := by
  have hXi : Integrable X P := hX.integrable one_le_two
  unfold centeredL2Norm
  rw [integral_const_mul]
  have heq : (fun omega => c * X omega - c * ∫ x, X x ∂P) =
      c • (fun omega => X omega - ∫ x, X x ∂P) := by
    funext omega
    dsimp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, lpNorm_const_smul, coe_nnnorm,
    Real.norm_of_nonneg hc]

end MinkowskiL2Recurrence

namespace System

universe u v

variable {Omega : Type u} {iota : Type v} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]

/-! ### Uniform profile `L²` input -/

omit [Nonempty iota] in
/-- The `q = 2` tube-moment estimate gives a uniform `L²` bound for the
normalized tube profile on the nonnegative half-line. -/
theorem IsNatural.exists_brownianTubeProfile_lpNorm_bound_of_tubeMomentsUpper
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu)
    (hmom : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        Integrable (fun omega =>
          (tubeArea rho
            (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        Integrable (fun omega =>
          (tubeMass rho
            (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        (∫ omega,
            (tubeArea rho
              (brownianImage W hmu.compactAttractor omega)) ^ q ∂P) +
          (∫ omega,
            (tubeMass rho
              (brownianImage W hmu.compactAttractor omega)) ^ q ∂P) ≤
            Cq * rho ^ (q * tubeExponent s)) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : ℝ, 0 ≤ v →
      MemLp (brownianTubeProfile W hmu.compactAttractor s v) 2 P ∧
      lpNorm (brownianTubeProfile W hmu.compactAttractor s v) 2 P ≤ B := by
  obtain ⟨C, hC, hmoment⟩ := hmom 2 (by norm_num)
  let B : ℝ := Real.sqrt C
  have hB : 0 < B := Real.sqrt_pos.2 hC
  refine ⟨B, hB, ?_⟩
  intro v hv
  have hrho : 0 < tubeRadiusReal v := tubeRadiusReal_pos v
  have hrho1 : tubeRadiusReal v ≤ 1 := by
    unfold tubeRadiusReal
    exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr hv)
  obtain ⟨_harea2, hmass2Real, hsum⟩ :=
    hmoment (tubeRadiusReal v) hrho hrho1
  have hareaMean0 : 0 ≤
      ∫ omega,
        (tubeArea (tubeRadiusReal v)
          (brownianImage W hmu.compactAttractor omega)) ^ (2 : ℝ) ∂P :=
    integral_nonneg fun omega =>
      Real.rpow_nonneg (tubeArea_nonneg _ _) 2
  have hmassMeanReal :
      (∫ omega,
        (tubeMass (tubeRadiusReal v)
          (brownianImage W hmu.compactAttractor omega)) ^ (2 : ℝ) ∂P) ≤
        C * tubeRadiusReal v ^ (2 * tubeExponent s) := by
    calc
      (∫ omega,
        (tubeMass (tubeRadiusReal v)
          (brownianImage W hmu.compactAttractor omega)) ^ (2 : ℝ) ∂P) ≤
          (∫ omega,
            (tubeArea (tubeRadiusReal v)
              (brownianImage W hmu.compactAttractor omega)) ^ (2 : ℝ) ∂P) +
          (∫ omega,
            (tubeMass (tubeRadiusReal v)
              (brownianImage W hmu.compactAttractor omega)) ^ (2 : ℝ) ∂P) :=
        le_add_of_nonneg_left hareaMean0
      _ ≤ C * tubeRadiusReal v ^ ((2 : ℝ) * tubeExponent s) := hsum
  have hpow : (fun omega =>
      (tubeMass (tubeRadiusReal v)
        (brownianImage W hmu.compactAttractor omega)) ^ (2 : ℝ)) =
      (fun omega =>
        tubeMass (tubeRadiusReal v)
          (brownianImage W hmu.compactAttractor omega) ^ (2 : ℕ)) := by
    funext omega
    exact Real.rpow_natCast _ 2
  have hmass2 : Integrable (fun omega =>
      tubeMass (tubeRadiusReal v)
        (brownianImage W hmu.compactAttractor omega) ^ (2 : ℕ)) P := by
    rw [← hpow]
    exact hmass2Real
  have hmassMean :
      (∫ omega,
        tubeMass (tubeRadiusReal v)
          (brownianImage W hmu.compactAttractor omega) ^ (2 : ℕ) ∂P) ≤
        C * tubeRadiusReal v ^ (2 * tubeExponent s) := by
    rw [← hpow]
    exact hmassMeanReal
  have hprofileSq : Integrable (fun omega =>
      brownianTubeProfile W hmu.compactAttractor s v omega ^ 2) P := by
    have hscaled := hmass2.const_mul
      (Real.exp (2 * tubeExponent s * v))
    convert hscaled using 1
    funext omega
    unfold brownianTubeProfile normalizedTubeMass
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hprofile : MemLp
      (brownianTubeProfile W hmu.compactAttractor s v) 2 P :=
    (memLp_two_iff_integrable_sq
      (hW.aemeasurable_brownianTubeProfile hmu.compactAttractor s v
        |>.aestronglyMeasurable)).2 hprofileSq
  have hprofileMean :
      (∫ omega,
        brownianTubeProfile W hmu.compactAttractor s v omega ^ 2 ∂P) ≤ C := by
    calc
      (∫ omega,
        brownianTubeProfile W hmu.compactAttractor s v omega ^ 2 ∂P) =
          Real.exp (2 * tubeExponent s * v) *
            ∫ omega,
              tubeMass (tubeRadiusReal v)
                (brownianImage W hmu.compactAttractor omega) ^ 2 ∂P := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with omega
        unfold brownianTubeProfile normalizedTubeMass
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ Real.exp (2 * tubeExponent s * v) *
          (C * tubeRadiusReal v ^ (2 * tubeExponent s)) :=
        mul_le_mul_of_nonneg_left hmassMean (Real.exp_pos _).le
      _ = C := by
        unfold tubeRadiusReal
        rw [← Real.exp_mul]
        calc
          Real.exp (2 * tubeExponent s * v) *
              (C * Real.exp (-v * (2 * tubeExponent s))) =
              C * (Real.exp (2 * tubeExponent s * v) *
                Real.exp (-v * (2 * tubeExponent s))) := by ring
          _ = C := by
            rw [← Real.exp_add]
            convert mul_one C using 1
            rw [← Real.exp_zero]
            congr 1
            ring_nf
  refine ⟨hprofile, ?_⟩
  apply (sq_le_sq₀ lpNorm_nonneg (Real.sqrt_nonneg C)).mp
  rw [MinkowskiL2Recurrence.lpNorm_two_sq hprofile,
    Real.sq_sqrt hC.le]
  exact hprofileMean

end System

end

end BrownianImages
