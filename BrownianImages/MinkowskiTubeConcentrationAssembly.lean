/-
System-level assembly of the Brownian tube `L²` recurrence.

This file combines independence of the centered first-level Brownian pieces,
the normalized defect estimate from `MinkowskiDefectL2`, the abstract centered
variance recurrence, and the deterministic delayed contraction lemma.
-/
import BrownianImages.MinkowskiDefectL2
import BrownianImages.MinkowskiContraction
import BrownianImages.MinkowskiAlmostSure
import BrownianImages.MinkowskiStoppingTubeUpper

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

/-! ### Independence of first-level tube masses -/

/-- In an interval-separated system, the normalized tube masses of the
first-level Brownian cylinders are mutually independent. -/
theorem IsNatural.iIndepFun_normalizedTubeMass_brownianFirstLevelPiece
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hsep : S.IntervalSeparated) (v : ℝ) :
    iIndepFun (fun i omega => normalizedTubeMass s v
      (hmu.brownianFirstLevelPiece S W omega i)) P := by
  let a : iota → NNReal := fun i => (S.shift i).toNNReal
  let r : iota → NNReal := fun i => (S.ratio i).toNNReal
  let L : iota → NonemptyCompacts ℝ := fun _ => hmu.compactAttractor
  have ha (i : iota) : (a i : ℝ) = S.shift i := by
    exact Real.coe_toNNReal _ (S.shift_nonneg_of_mapsTo i)
  have hrcoe (i : iota) : (r i : ℝ) = S.ratio i := by
    exact Real.coe_toNNReal _ (S.ratio_pos i).le
  have hr : ∀ i, r i ≠ 0 := by
    intro i
    exact NNReal.coe_ne_zero.mp (by rw [hrcoe i]; exact (S.ratio_pos i).ne')
  have hL : ∀ i, (L i : Set ℝ) ⊆ Set.Icc 0 1 :=
    fun _ => hmu.attractor.2.2.1
  obtain ⟨gap, hgap, horder⟩ := hsep.exists_gap_and_pair_order S
  have hdisjoint : ∀ ⦃i j : iota⦄, i ≠ j →
      a i + r i ≤ a j ∨ a j + r j ≤ a i := by
    intro i j hij
    obtain hij' | hji' := horder i j hij
    · left
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_add, ha, hrcoe]
      linarith
    · right
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_add, ha, hrcoe]
      linarith
  have hindCentered :=
    hW.iIndepFun_centeredBrownianCompactPieces a r L hr hL hdisjoint
  have hindMass : iIndepFun (fun i omega =>
      normalizedTubeMass s v
        (centeredBrownianCompactPiece W (a i) (r i) (L i) omega)) P := by
    simpa only [Function.comp_def] using
      hindCentered.comp
        (fun _ F => normalizedTubeMass s v F)
        (fun _ => (continuous_normalizedTubeMass s v).measurable)
  apply hindMass.congr
  intro i
  filter_upwards [hW.ae_continuous] with omega homega
  have haffine :
      translateCompact (W (a i) omega)
          (centeredBrownianCompactPiece W (a i) (r i) (L i) omega) =
        hmu.brownianFirstLevelPiece S W omega i := by
    have htranslate :=
      translate_dilate_rescaledBrownianCompactPiece_of_continuous
        (a := a i) (r := r i) (K := L i) (hr i) (hL i) homega
    simpa only [centeredBrownianCompactPiece, L,
      smulCompact_eq_dilateCompact,
      IsNatural.brownianFirstLevelPiece,
      hmu.compactPiece_eq_affineTimeCompact S i,
      affineBrownianCompactPiece, a, r] using htranslate
  unfold normalizedTubeMass
  rw [← haffine, tubeMass_translate]

/-! ### Uniform profile `L²` input -/

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
            ring
  refine ⟨hprofile, ?_⟩
  apply (sq_le_sq₀ lpNorm_nonneg (Real.sqrt_nonneg C)).mp
  rw [MinkowskiL2Recurrence.lpNorm_two_sq hprofile,
    Real.sq_sqrt hC.le]
  exact hprofileMean

/-! ### The centered one-step recurrence -/

/-- At one logarithmic scale, independence of the first-level cylinders gives
the sharp square-sum recurrence for the centered profile. -/
theorem IsNatural.centeredL2Norm_brownianTubeProfile_recurrence_le
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hsep : S.IntervalSeparated) (v : ℝ)
    (hdelayed : ∀ i,
      MemLp (brownianTubeProfile W hmu.compactAttractor s
        (v - S.halfLogRatio i)) 2 P)
    (hdefect : MemLp (fun omega => normalizedTubeDefect s v
      (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P) :
    MinkowskiL2Recurrence.centeredL2Norm
        (brownianTubeProfile W hmu.compactAttractor s v) P ≤
      Real.sqrt (∑ i,
        (S.tubeWeight s i *
          MinkowskiL2Recurrence.centeredL2Norm
            (brownianTubeProfile W hmu.compactAttractor s
              (v - S.halfLogRatio i)) P) ^ 2) +
      lpNorm (fun omega => normalizedTubeDefect s v
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P := by
  let X : Omega → ℝ :=
    brownianTubeProfile W hmu.compactAttractor s v
  let Z : iota → Omega → ℝ := fun i omega =>
    normalizedTubeMass s v (hmu.brownianFirstLevelPiece S W omega i)
  let Y : iota → Omega → ℝ := fun i omega =>
    S.tubeWeight s i *
      brownianTubeProfile W hmu.compactAttractor s
        (v - S.halfLogRatio i) omega
  let O : Omega → ℝ := fun omega => normalizedTubeDefect s v
    (fun i => hmu.brownianFirstLevelPiece S W omega i)
  let a : iota → ℝ := fun i =>
    S.tubeWeight s i *
      MinkowskiL2Recurrence.centeredL2Norm
        (brownianTubeProfile W hmu.compactAttractor s
          (v - S.halfLogRatio i)) P
  have hcopy : ∀ i, IdentDistrib (Z i) (Y i) P P := by
    intro i
    simpa only [Z, Y] using
      hW.identDistrib_normalizedTubeMass_brownianFirstLevelPiece S hmu v i
  have hY : ∀ i, MemLp (Y i) 2 P := by
    intro i
    exact (hdelayed i).const_mul (S.tubeWeight s i)
  have hZ : ∀ i, MemLp (Z i) 2 P := fun i =>
    (hcopy i).memLp_iff.mpr (hY i)
  have hindep : iIndepFun Z P := by
    simpa only [Z] using
      hmu.iIndepFun_normalizedTubeMass_brownianFirstLevelPiece hW S hsep v
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    exact mul_nonneg (S.tubeWeight_pos s i).le
      (MinkowskiL2Recurrence.centeredL2Norm_nonneg _ _)
  have ha : ∀ i,
      MinkowskiL2Recurrence.centeredL2Norm (Z i) P ≤ a i := by
    intro i
    have heq := MinkowskiL2Recurrence.centeredL2Norm_eq_of_identDistrib
      (hcopy i) (hZ i)
    rw [heq]
    exact le_of_eq
      (MinkowskiL2Recurrence.centeredL2Norm_const_mul
        (hdelayed i) (S.tubeWeight_pos s i).le)
  have hrec : X =ᵐ[P] fun omega =>
      (∑ i, (1 : ℝ) * Z i omega) - O omega := by
    filter_upwards [hW.ae_compactUnion_brownianFirstLevelPiece_eq S hmu]
      with omega hunion
    dsimp only [X, Z, O]
    unfold brownianTubeProfile
    rw [← hunion]
    simpa only [one_mul] using
      normalizedTubeMass_compactUnion_eq_sum_sub_defect s v
        (fun i => hmu.brownianFirstLevelPiece S W omega i)
  have hstep :=
    MinkowskiL2Recurrence.centeredL2Norm_recurrence_of_iIndepFun_le
      X Z O (fun _ => (1 : ℝ)) a hZ hindep hdefect ha0 ha hrec
  simpa only [X, O, a, one_mul] using hstep

/-! ### Delayed contraction -/

/-- The complete real-`L²` concentration estimate, conditional on the tube
moments. -/
theorem IsNatural.exists_centeredBrownianTubeProfile_lpNorm_decay_of_tubeMomentsUpper
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
    ∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        lpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          C * Real.exp (-gamma * v) := by
  obtain ⟨B, hB, hprofile⟩ :=
    hmu.exists_brownianTubeProfile_lpNorm_bound_of_tubeMomentsUpper hW S hmom
  obtain ⟨E, hE, hdefect⟩ :=
    hmu.exists_normalizedTubeDefect_lpNorm_decay_of_tubeMomentsUpper
      hW S hs0 hs1 hsep hdim hmom
  let a : ℝ → ℝ := fun v =>
    MinkowskiL2Recurrence.centeredL2Norm
      (brownianTubeProfile W hmu.compactAttractor s v) P
  let delta : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty S.halfLogRatio
  let b : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty S.halfLogRatio
  let eta : ℝ := tubeExponent s / 4
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact (Finset.lt_inf'_iff _).2 fun i _ => S.halfLogRatio_pos i
  have hbetaLower : ∀ i, delta ≤ S.halfLogRatio i := by
    intro i
    exact Finset.inf'_le S.halfLogRatio (Finset.mem_univ i)
  have hbetaUpper : ∀ i, S.halfLogRatio i ≤ b := by
    intro i
    exact Finset.le_sup' S.halfLogRatio (Finset.mem_univ i)
  obtain ⟨i0⟩ := (‹Nonempty iota›)
  have hbpos : 0 < b := (S.halfLogRatio_pos i0).trans_le (hbetaUpper i0)
  have heta : 0 < eta := div_pos (tubeExponent_pos hs1) (by norm_num)
  have ha0 : ∀ v, 0 ≤ a v := fun v =>
    MinkowskiL2Recurrence.centeredL2Norm_nonneg _ _
  have hbase : ∀ v, 0 ≤ v → v ≤ b → a v ≤ B := by
    intro v hv _hvb
    exact (MinkowskiL2Recurrence.centeredL2Norm_le_lpNorm
      (hprofile v hv).1).trans (hprofile v hv).2
  have hrec : ∀ v, b ≤ v →
      a v ≤ Real.sqrt (∑ i,
        (S.tubeWeight s i * a (v - S.halfLogRatio i)) ^ 2) +
        E * Real.exp (-eta * v) := by
    intro v hvb
    have hv0 : 0 ≤ v := le_trans hbpos.le hvb
    have hprev0 : ∀ i, 0 ≤ v - S.halfLogRatio i := by
      intro i
      linarith [hbetaUpper i]
    have hstep :=
      hmu.centeredL2Norm_brownianTubeProfile_recurrence_le
        hW S hsep v (fun i => (hprofile _ (hprev0 i)).1)
          (hdefect v hv0).1
    have hstep' : a v ≤ Real.sqrt (∑ i,
        (S.tubeWeight s i * a (v - S.halfLogRatio i)) ^ 2) +
        lpNorm (fun omega => normalizedTubeDefect s v
          (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P := by
      simpa only [a] using hstep
    have herr : lpNorm (fun omega => normalizedTubeDefect s v
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) 2 P ≤
        E * Real.exp (-eta * v) := by
      simpa only [eta] using (hdefect v hv0).2
    exact hstep'.trans (add_le_add le_rfl herr)
  obtain ⟨gamma, hgamma, _hgammaEta, C0, hC0, hdecay⟩ :=
    MinkowskiContraction.exists_exponential_decay_of_delayed_sqrt_recurrence
      (fun i => S.tubeWeight s i) S.halfLogRatio a
      (fun i => S.tubeWeight_pos s i) hdelta hbetaLower hbetaUpper
      hB.le hE.le heta (S.sum_sq_tubeWeight_lt_one hs0 hdim)
      ha0 hbase hrec
  let C : ℝ := C0 + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, gamma, hgamma, ?_⟩
  intro v hv
  have hprof := (hprofile v hv).1
  have hcenter : MemLp
      (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P := by
    unfold centeredBrownianTubeProfile meanBrownianTubeProfile
    exact hprof.sub (memLp_const _)
  refine ⟨hcenter, ?_⟩
  have hnormeq :
      lpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P =
        a v := rfl
  rw [hnormeq]
  exact (hdecay v hv).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
      (Real.exp_pos _).le)

/-- Endpoint-shaped tube concentration theorem, including the fixed-phase
almost-sure conclusion, conditional on the tube moments. -/
theorem IsNatural.tubeConcentration_of_tubeMomentsUpper
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
    (∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v))) ∧
    ∀ t : ℝ, ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => centeredBrownianTubeProfile W P hmu.compactAttractor s
        ((n : ℝ) + t) omega) atTop (nhds 0) := by
  obtain ⟨C, hC, gamma, hgamma, hreal⟩ :=
    hmu.exists_centeredBrownianTubeProfile_lpNorm_decay_of_tubeMomentsUpper
      hW S hs0 hs1 hsep hdim hmom
  have hbound : ∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v)) := by
    refine ⟨C, hC, gamma, hgamma, ?_⟩
    intro v hv
    obtain ⟨hmem, hlp⟩ := hreal v hv
    refine ⟨hmem, ?_⟩
    rw [← ofReal_lpNorm hmem]
    exact ENNReal.ofReal_le_ofReal hlp
  exact ⟨hbound,
    MinkowskiAlmostSure.tubeGridConcentration_of_exponential_eLpNorm hbound⟩

/-- Tube concentration reduced all the way to moments of the unit-interval
Brownian radius. -/
theorem IsNatural.tubeConcentration_of_standardRadiusMoments
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hunit : ∀ p : ℝ, 1 ≤ p →
      Integrable (fun omega =>
        (1 + standardBrownianRadius W omega) ^ p) P) :
    (∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v))) ∧
    ∀ t : ℝ, ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => centeredBrownianTubeProfile W P hmu.compactAttractor s
        ((n : ℝ) + t) omega) atTop (nhds 0) := by
  have hupper :=
    hmu.tubeMomentUpper_of_standardRadiusMoments S hdim hs0 hW hunit
  have hmom : ∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
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
            Cq * rho ^ (q * tubeExponent s) := by
    intro q hq
    obtain ⟨Cq, hCq, hqbound⟩ := hupper q hq
    refine ⟨Cq, hCq, ?_⟩
    intro rho hrho hrho1
    simpa only [brownianTubeArea] using hqbound rho hrho hrho1
  exact hmu.tubeConcentration_of_tubeMomentsUpper
    hW S hs0 hs1 hsep hdim hmom

end System

end

end BrownianImages
