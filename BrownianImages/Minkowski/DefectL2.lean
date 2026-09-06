/-
`L²` estimates for the multiple-counting error in the Brownian tube
recurrence.

The analytic input is deliberately separated into a first-moment estimate and
a third-moment estimate.  Interpolation at the scale `T = rho ^ (alpha / 2)`
gives the sharp consequence of those two hypotheses:

`E X² = O(rho ^ (5 alpha / 2))`, hence
`||X||₂ = O(rho ^ (5 alpha / 4))`.

After the tube normalization by `rho ^ (-alpha)`, this leaves an exponentially
decaying error of rate `alpha / 4`, which is enough for the delayed
contraction argument.
-/
import BrownianImages.Minkowski.OverlapSystem
import BrownianImages.Minkowski.TubeUpper
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

/-! ### Scaling simplification -/

/-- First moment `rho^(2 alpha)` and third moment `rho^(3 alpha)` imply the
optimal interpolated `L²` rate `rho^(5 alpha / 4)`. -/
theorem memLp_two_and_lpNorm_le_rpow_five_fourths
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → ℝ} {rho alpha C1 C3 : ℝ}
    (hX : Integrable X P) (hX3 : Integrable (fun omega => X omega ^ 3) P)
    (hX0 : ∀ᵐ omega ∂P, 0 ≤ X omega) (hrho : 0 < rho)
    (hC1 : 0 ≤ C1) (hC3 : 0 ≤ C3)
    (hfirst : (∫ omega, X omega ∂P) ≤ C1 * rho ^ (2 * alpha))
    (hthird : (∫ omega, X omega ^ 3 ∂P) ≤
      C3 * rho ^ (3 * alpha)) :
    MemLp X 2 P ∧
      lpNorm X 2 P ≤ Real.sqrt (C1 + C3) * rho ^ (5 * alpha / 4) := by
  let T : ℝ := rho ^ (alpha / 2)
  have hT : 0 < T := Real.rpow_pos_of_pos hrho _
  obtain ⟨hmem, hnorm⟩ := memLp_two_and_lpNorm_le_of_first_third
    hX hX3 hX0 hT
      (mul_nonneg hC1 (Real.rpow_nonneg hrho.le _))
      (mul_nonneg hC3 (Real.rpow_nonneg hrho.le _)) hfirst hthird
  refine ⟨hmem, hnorm.trans_eq ?_⟩
  have hsum : 0 ≤ C1 + C3 := add_nonneg hC1 hC3
  have hrpow : 0 ≤ rho ^ (5 * alpha / 2) :=
    Real.rpow_nonneg hrho.le _
  have hinside :
      T * (C1 * rho ^ (2 * alpha)) +
          T⁻¹ * (C3 * rho ^ (3 * alpha)) =
        (C1 + C3) * rho ^ (5 * alpha / 2) := by
    dsimp only [T]
    rw [← Real.rpow_neg hrho.le]
    have hpow1 : rho ^ (alpha / 2) * rho ^ (2 * alpha) =
        rho ^ (5 * alpha / 2) := by
      rw [← Real.rpow_add hrho]
      congr 1
      ring
    have hpow3 : rho ^ (-(alpha / 2)) * rho ^ (3 * alpha) =
        rho ^ (5 * alpha / 2) := by
      rw [← Real.rpow_add hrho]
      congr 1
      ring
    calc
      rho ^ (alpha / 2) * (C1 * rho ^ (2 * alpha)) +
          rho ^ (-(alpha / 2)) * (C3 * rho ^ (3 * alpha)) =
          C1 * (rho ^ (alpha / 2) * rho ^ (2 * alpha)) +
            C3 * (rho ^ (-(alpha / 2)) * rho ^ (3 * alpha)) := by ring
      _ = C1 * rho ^ (5 * alpha / 2) +
          C3 * rho ^ (5 * alpha / 2) := by rw [hpow1, hpow3]
      _ = (C1 + C3) * rho ^ (5 * alpha / 2) := by ring
  rw [hinside, Real.sqrt_mul hsum]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrho.le]
  congr 1
  ring

/-! ### Finite-family defect domination -/

/-- If every compact set in a finite family is contained in `G`, then its
smoothed multiple-counting defect is at most `card iota` times the raw tube
area of `G`. -/
theorem tubeDefect_le_card_mul_tubeArea_of_subset
    {iota : Type*} [Fintype iota] [Nonempty iota]
    {r : ℝ} (hr : 0 < r) (F : iota → CompactPlane) (G : CompactPlane)
    (hFG : ∀ i, (F i : Set Plane) ⊆ (G : Set Plane)) :
    tubeDefect r F ≤ (Fintype.card iota : ℝ) * tubeArea r G := by
  calc
    tubeDefect r F ≤ ∑ i, tubeMass r (F i) := by
      unfold tubeDefect
      exact sub_le_self _ (tubeMass_nonneg r (compactUnion F))
    _ ≤ ∑ _i : iota, tubeArea r G := by
      apply Finset.sum_le_sum
      intro i _
      exact (tubeMass_le_tubeArea hr (F i)).trans (tubeArea_mono (hFG i))
    _ = (Fintype.card iota : ℝ) * tubeArea r G := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Random finite-family assembly -/

/-- A first-moment bound for a random finite-family defect and a third-moment
bound for one ambient raw tube imply the interpolated `L²` defect estimate. -/
theorem memLp_tubeDefect_two_and_lpNorm_le
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota] [Nonempty iota] {P : Measure Omega}
    {F : iota → Omega → CompactPlane} {G : Omega → CompactPlane}
    {rho alpha C1 C3 : ℝ} (hrho : 0 < rho)
    (hF : ∀ i, AEMeasurable (F i) P)
    (hsubset : ∀ᵐ omega ∂P, ∀ i, (F i omega : Set Plane) ⊆ (G omega : Set Plane))
    (hdefect : Integrable
      (fun omega => tubeDefect rho (fun i => F i omega)) P)
    (harea3 : Integrable (fun omega => tubeArea rho (G omega) ^ 3) P)
    (hC1 : 0 ≤ C1) (hC3 : 0 ≤ C3)
    (hfirst : (∫ omega, tubeDefect rho (fun i => F i omega) ∂P) ≤
      C1 * rho ^ (2 * alpha))
    (hthird : (∫ omega, tubeArea rho (G omega) ^ 3 ∂P) ≤
      C3 * rho ^ (3 * alpha)) :
    MemLp (fun omega => tubeDefect rho (fun i => F i omega)) 2 P ∧
      lpNorm (fun omega => tubeDefect rho (fun i => F i omega)) 2 P ≤
        Real.sqrt (C1 + (Fintype.card iota : ℝ) ^ 3 * C3) *
          rho ^ (5 * alpha / 4) := by
  let N : ℝ := Fintype.card iota
  let D : Omega → ℝ := fun omega => tubeDefect rho (fun i => F i omega)
  let A : Omega → ℝ := fun omega => tubeArea rho (G omega)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hD0 : ∀ᵐ omega ∂P, 0 ≤ D omega :=
    Filter.Eventually.of_forall fun omega =>
      tubeDefect_nonneg hrho (fun i => F i omega)
  have hA0 : ∀ omega, 0 ≤ A omega := fun omega => tubeArea_nonneg rho _
  have hDA : ∀ᵐ omega ∂P, D omega ≤ N * A omega := by
    filter_upwards [hsubset] with omega homega
    exact tubeDefect_le_card_mul_tubeArea_of_subset hrho
      (fun i => F i omega) (G omega) homega
  have hdom3 : Integrable (fun omega => (N * A omega) ^ 3) P := by
    simpa only [A, N, mul_pow] using
      harea3.const_mul ((Fintype.card iota : ℝ) ^ 3)
  have hD3 : Integrable (fun omega => D omega ^ 3) P := by
    refine Integrable.mono' hdom3
      ((aemeasurable_tubeDefect_of_forall hrho hF).aestronglyMeasurable.pow 3) ?_
    filter_upwards [hD0, hDA] with omega hDomega hle
    change |D omega ^ 3| ≤ (N * A omega) ^ 3
    rw [abs_of_nonneg (pow_nonneg hDomega 3)]
    exact pow_le_pow_left₀ hDomega hle 3
  have hDthird : (∫ omega, D omega ^ 3 ∂P) ≤
      (N ^ 3 * C3) * rho ^ (3 * alpha) := by
    calc
      (∫ omega, D omega ^ 3 ∂P) ≤
          ∫ omega, (N * A omega) ^ 3 ∂P := by
        exact integral_mono_ae hD3 hdom3
          ((hD0.and hDA).mono fun omega h =>
            pow_le_pow_left₀ h.1 h.2 3)
      _ = N ^ 3 * (∫ omega, A omega ^ 3 ∂P) := by
        simp only [mul_pow, integral_const_mul]
      _ ≤ N ^ 3 * (C3 * rho ^ (3 * alpha)) :=
        mul_le_mul_of_nonneg_left (by simpa only [A] using hthird)
          (pow_nonneg hN0 3)
      _ = (N ^ 3 * C3) * rho ^ (3 * alpha) := by ring
  have hinterp := memLp_two_and_lpNorm_le_rpow_five_fourths
    (X := D) hdefect hD3 hD0 hrho hC1
      (mul_nonneg (pow_nonneg hN0 3) hC3)
      (by simpa only [D] using hfirst) hDthird
  simpa only [D, N] using hinterp

/-! ### Brownian first-level defect -/

namespace System

universe u v

variable {Omega : Type u} {iota : Type v} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]

/-- The first- and third-moment consequences of the tube-moment theorem give
an `L²` bound for the first-level Brownian multiple-counting defect. -/
theorem IsNatural.exists_tubeDefect_lpNorm_bound_of_tubeMomentsUpper
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
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
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      MemLp (fun omega => tubeDefect rho
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P ∧
      lpNorm (fun omega => tubeDefect rho
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P ≤
          C2 * rho ^ (5 * tubeExponent s / 4) := by
  obtain ⟨C1, hC1, hoverlap⟩ :=
    hmu.tubeOverlap_of_tubeMomentsUpper hW S hs0 hs1 hsep hdim hmom
  obtain ⟨C3, hC3, hmoment3⟩ := hmom 3 (by norm_num)
  let C2 : ℝ :=
    Real.sqrt (C1 + (Fintype.card iota : ℝ) ^ 3 * C3)
  have hinside : 0 < C1 + (Fintype.card iota : ℝ) ^ 3 * C3 := by
    have hcard : 0 ≤ (Fintype.card iota : ℝ) := Nat.cast_nonneg _
    exact add_pos_of_pos_of_nonneg hC1
      (mul_nonneg (pow_nonneg hcard 3) hC3.le)
  have hC2 : 0 < C2 := Real.sqrt_pos.2 hinside
  refine ⟨C2, hC2, ?_⟩
  intro rho hrho hrho1
  obtain ⟨_hpair, hdefect, hdefectMean⟩ := hoverlap rho hrho hrho1
  obtain ⟨harea3, _hmass3, hmomentSum⟩ := hmoment3 rho hrho hrho1
  have hmass3Mean0 : 0 ≤
      ∫ omega,
        (tubeMass rho
          (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ) ∂P :=
    integral_nonneg fun omega =>
      Real.rpow_nonneg (tubeMass_nonneg rho _) 3
  have harea3MeanReal :
      (∫ omega,
        (tubeArea rho
          (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ) ∂P) ≤
          C3 * rho ^ (3 * tubeExponent s) := by
    calc
      (∫ omega,
        (tubeArea rho
          (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ) ∂P) ≤
          (∫ omega,
            (tubeArea rho
              (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ) ∂P) +
          (∫ omega,
            (tubeMass rho
              (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ) ∂P) :=
        le_add_of_nonneg_right hmass3Mean0
      _ ≤ C3 * rho ^ ((3 : ℝ) * tubeExponent s) := hmomentSum
  have harea3Nat : Integrable (fun omega =>
      tubeArea rho (brownianImage W hmu.compactAttractor omega) ^ (3 : ℕ)) P := by
    have hpow : (fun omega =>
        (tubeArea rho
          (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ)) =
        (fun omega =>
          tubeArea rho
            (brownianImage W hmu.compactAttractor omega) ^ (3 : ℕ)) := by
      funext omega
      exact Real.rpow_natCast _ 3
    rw [← hpow]
    exact harea3
  have harea3Mean :
      (∫ omega,
        tubeArea rho (brownianImage W hmu.compactAttractor omega) ^ (3 : ℕ) ∂P) ≤
          C3 * rho ^ (3 * tubeExponent s) := by
    have hpow : (fun omega =>
        (tubeArea rho
          (brownianImage W hmu.compactAttractor omega)) ^ (3 : ℝ)) =
        (fun omega =>
          tubeArea rho
            (brownianImage W hmu.compactAttractor omega) ^ (3 : ℕ)) := by
      funext omega
      exact Real.rpow_natCast _ 3
    rw [← hpow]
    exact harea3MeanReal
  have hsubset : ∀ᵐ omega ∂P, ∀ i,
      (hmu.brownianFirstLevelPiece S W omega i : Set Plane) ⊆
        brownianImage W hmu.compactAttractor omega := by
    filter_upwards [hW.ae_continuous] with omega homega
    intro i
    exact hmu.brownianImage_compactPiece_subset S homega i
  have hresult := memLp_tubeDefect_two_and_lpNorm_le
    (P := P)
    (F := fun i omega => hmu.brownianFirstLevelPiece S W omega i)
    (G := fun omega => brownianImage W hmu.compactAttractor omega)
    hrho
    (fun i => hW.aemeasurable_brownianImage (hmu.compactPiece S i))
    hsubset hdefect harea3Nat hC1.le hC3.le hdefectMean harea3Mean
  simpa only [C2] using hresult

/-- Logarithmic-scale form of the preceding estimate.  The tube
normalization consumes one power `rho ^ tubeExponent s`, leaving exponential
decay at rate `tubeExponent s / 4`. -/
theorem IsNatural.exists_normalizedTubeDefect_lpNorm_decay_of_tubeMomentsUpper
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
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
    ∃ E : ℝ, 0 < E ∧ ∀ v : ℝ, 0 ≤ v →
      MemLp (fun omega => normalizedTubeDefect s v
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P ∧
      lpNorm (fun omega => normalizedTubeDefect s v
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P ≤
          E * Real.exp (-(tubeExponent s / 4) * v) := by
  obtain ⟨E, hE, hraw⟩ :=
    hmu.exists_tubeDefect_lpNorm_bound_of_tubeMomentsUpper
      hW S hs0 hs1 hsep hdim hmom
  refine ⟨E, hE, ?_⟩
  intro v hv
  let D : Omega → ℝ := fun omega =>
    tubeDefect (tubeRadiusReal v)
      (fun i => hmu.brownianFirstLevelPiece S W omega i)
  have hrho : 0 < tubeRadiusReal v := tubeRadiusReal_pos v
  have hrho1 : tubeRadiusReal v ≤ 1 := by
    unfold tubeRadiusReal
    exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr hv)
  obtain ⟨hD, hDraw⟩ := hraw (tubeRadiusReal v) hrho hrho1
  have hnormeq :
      lpNorm (fun omega => normalizedTubeDefect s v
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P =
        Real.exp (tubeExponent s * v) * lpNorm D 2 P := by
    change lpNorm (fun omega =>
      Real.exp (tubeExponent s * v) * D omega) 2 P = _
    rw [show (fun omega => Real.exp (tubeExponent s * v) * D omega) =
      Real.exp (tubeExponent s * v) • D by rfl,
      lpNorm_const_smul]
    rw [coe_nnnorm, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ⟨?_, ?_⟩
  · change MemLp (fun omega =>
      Real.exp (tubeExponent s * v) * D omega) 2 P
    exact hD.const_mul _
  · rw [hnormeq]
    calc
      Real.exp (tubeExponent s * v) * lpNorm D 2 P ≤
          Real.exp (tubeExponent s * v) *
            (E * tubeRadiusReal v ^ (5 * tubeExponent s / 4)) :=
        mul_le_mul_of_nonneg_left (by simpa only [D] using hDraw)
          (Real.exp_pos _).le
      _ = E * Real.exp (-(tubeExponent s / 4) * v) := by
        unfold tubeRadiusReal
        rw [← Real.exp_mul]
        calc
          Real.exp (tubeExponent s * v) *
              (E * Real.exp (-v * (5 * tubeExponent s / 4))) =
              E * (Real.exp (tubeExponent s * v) *
                Real.exp (-v * (5 * tubeExponent s / 4))) := by ring
          _ = E * Real.exp
              (tubeExponent s * v + -v * (5 * tubeExponent s / 4)) := by
            rw [Real.exp_add]
          _ = E * Real.exp (-(tubeExponent s / 4) * v) := by
            congr 2
            ring

end System

end

end BrownianImages
