/-
The separated first-level-cylinder specialization of the Brownian overlap
estimate.

The probabilistic estimate is proved for two affine compact time sets around
an oriented temporal gap.  Here interval separation supplies that orientation
and a single positive lower bound for every gap.  Each cylinder is contained
in the full attractor image, so the `q = 1` raw-neighbourhood estimate for the full
image supplies both moment inputs.  The finite-family assembly then gives the
multiple-counting defect estimate as well.
-/
import BrownianImages.MinkowskiBrownianOverlapGeometry
import BrownianImages.MinkowskiIntervalGap
import BrownianImages.MinkowskiOverlapAssembly
import BrownianImages.MinkowskiTubeRenewal

namespace BrownianImages

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal

noncomputable section

namespace System

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]

set_option linter.unusedSectionVars false in
/-- Every first-level compact piece is contained in the attractor. -/
theorem IsNatural.compactPiece_subset_compactAttractor
    (S : System iota) {K : Set Real} {s : Real} {mu : Measure Real}
    (hmu : S.IsNatural K s mu) (i : iota) :
    (hmu.compactPiece S i : Set Real) ⊆ hmu.compactAttractor := by
  rw [IsNatural.coe_compactPiece]
  intro t ht
  change t ∈ K
  rw [hmu.attractor.2.2.2]
  exact Set.mem_iUnion.mpr ⟨i, ht⟩

set_option linter.unusedSectionVars false in
/-- On a continuous path, a first-level Brownian image is contained in the
Brownian image of the full attractor. -/
theorem IsNatural.brownianImage_compactPiece_subset
    (S : System iota) {K : Set Real} {s : Real} {mu : Measure Real}
    (hmu : S.IsNatural K s mu)
    {W : NNReal → Omega → Plane} {omega : Omega}
    (homega : Continuous (fun t => W t omega)) (i : iota) :
    (brownianImage W (hmu.compactPiece S i) omega : Set Plane) ⊆
      brownianImage W hmu.compactAttractor omega := by
  rw [coe_brownianImage_of_continuous _ homega,
    coe_brownianImage_of_continuous _ homega]
  exact Set.image_mono (hmu.compactPiece_subset_compactAttractor S i)

/-- Integrability and a first-moment upper bound descend from the full
Brownian image to each first-level cylinder. -/
theorem IsNatural.integrable_and_integral_tubeArea_compactPiece_le
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (S : System iota)
    {K : Set Real} {s : Real} {mu : Measure Real}
    (hmu : S.IsNatural K s mu) (i : iota)
    {rho alpha C : Real}
    (hfull : Integrable (fun omega =>
      tubeArea rho (brownianImage W hmu.compactAttractor omega)) P)
    (hmean : (∫ omega,
      tubeArea rho (brownianImage W hmu.compactAttractor omega) ∂P) ≤
        C * rho ^ alpha) :
    Integrable (fun omega =>
      tubeArea rho (brownianImage W (hmu.compactPiece S i) omega)) P ∧
    (∫ omega,
      tubeArea rho (brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
        C * rho ^ alpha := by
  have hle : ∀ᵐ omega ∂P,
      tubeArea rho (brownianImage W (hmu.compactPiece S i) omega) ≤
        tubeArea rho (brownianImage W hmu.compactAttractor omega) := by
    filter_upwards [hW.ae_continuous] with omega homega
    exact tubeArea_mono (hmu.brownianImage_compactPiece_subset S homega i)
  have hpieceMeas : AEStronglyMeasurable (fun omega =>
      tubeArea rho (brownianImage W (hmu.compactPiece S i) omega)) P :=
    (measurable_tubeArea rho).comp_aemeasurable
      (hW.aemeasurable_brownianImage (hmu.compactPiece S i))
      |>.aestronglyMeasurable
  have hpiece : Integrable (fun omega =>
      tubeArea rho (brownianImage W (hmu.compactPiece S i) omega)) P :=
    hfull.mono_nonneg hpieceMeas
      (Filter.Eventually.of_forall fun omega => tubeArea_nonneg rho _)
      hle
  refine ⟨hpiece, ?_⟩
  exact (integral_mono_ae hpiece hfull hle).trans hmean

/-- A positive common lower bound for all temporal gaps gives a uniform
distinct-cylinder overlap estimate from the raw first-moment bound of the
full Brownian image. -/
theorem IsNatural.exists_pairwise_tubeOverlap_of_tubeArea_mean_upper
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hsep : S.IntervalSeparated)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hupper : ∃ A : Real, 0 < A ∧ ∀ rho : Real, 0 < rho → rho ≤ 1 →
      Integrable (fun omega =>
        tubeArea rho (brownianImage W hmu.compactAttractor omega)) P ∧
      (∫ omega,
        tubeArea rho (brownianImage W hmu.compactAttractor omega) ∂P) ≤
          A * rho ^ tubeExponent s) :
    ∃ C0 : Real, 0 < C0 ∧ ∀ rho : Real, 0 < rho → rho ≤ 1 →
      ∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
            C0 * rho ^ (2 * tubeExponent s) := by
  obtain ⟨gap, hgap, horder⟩ := hsep.exists_gap_and_pair_order S
  obtain ⟨A, hA, hupper⟩ := hupper
  let C0 : Real := (2 * Real.pi * gap)⁻¹ * (A * A)
  refine ⟨C0, ?_, ?_⟩
  · dsimp [C0]
    positivity
  intro rho hrho hrho1 i j hij
  obtain hleft | hright := horder i j hij
  · let a : NNReal := (S.shift i).toNNReal
    let r : NNReal := (S.ratio i).toNNReal
    let b : NNReal := (S.shift j).toNNReal
    let q : NNReal := b - (a + r)
    let t : NNReal := (S.ratio j).toNNReal
    have ha : (a : Real) = S.shift i := by
      exact Real.coe_toNNReal _ (S.shift_nonneg_of_mapsTo i)
    have hr : (r : Real) = S.ratio i := by
      exact Real.coe_toNNReal _ (S.ratio_pos i).le
    have hb : (b : Real) = S.shift j := by
      exact Real.coe_toNNReal _ (S.shift_nonneg_of_mapsTo j)
    have ht : (t : Real) = S.ratio j := by
      exact Real.coe_toNNReal _ (S.ratio_pos j).le
    have harb : a + r ≤ b := by
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_add, ha, hr, hb]
      linarith
    have haqb : a + r + q = b := by
      exact add_tsub_cancel_of_le harb
    have hpieceIeq : hmu.compactPiece S i =
        affineTimeCompact a r hmu.compactAttractor := by
      simpa [a, r] using hmu.compactPiece_eq_affineTimeCompact S i
    have hpieceJeq : hmu.compactPiece S j =
        affineTimeCompact (a + r + q) t hmu.compactAttractor := by
      rw [haqb]
      simpa [b, t] using hmu.compactPiece_eq_affineTimeCompact S j
    have hqgap : gap ≤ (q : Real) := by
      rw [NNReal.coe_sub harb, NNReal.coe_add, ha, hr, hb]
      linarith
    have hrne : r ≠ 0 := by
      apply NNReal.coe_ne_zero.mp
      rw [hr]
      exact ne_of_gt (S.ratio_pos i)
    have htne : t ≠ 0 := by
      apply NNReal.coe_ne_zero.mp
      rw [ht]
      exact ne_of_gt (S.ratio_pos j)
    have hqne : q ≠ 0 := by
      exact ne_of_gt (NNReal.coe_pos.mp (hgap.trans_le hqgap))
    obtain ⟨hfull, hfullMean⟩ := hupper rho hrho hrho1
    obtain ⟨hpieceI, hpieceIMean⟩ :=
      hmu.integrable_and_integral_tubeArea_compactPiece_le
        hW S i hfull hfullMean
    obtain ⟨hpieceJ, hpieceJMean⟩ :=
      hmu.integrable_and_integral_tubeArea_compactPiece_le
        hW S j hfull hfullMean
    have hpair := hW.integrable_and_integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
      a hrne hqne htne hmu.compactAttractor hmu.compactAttractor
        hmu.attractor.2.2.1 hmu.attractor.2.2.1 hrho
        (by simpa [affineBrownianCompactPiece, ← hpieceIeq] using hpieceI)
        (by simpa [affineBrownianCompactPiece, ← hpieceJeq] using hpieceJ)
        (by simpa [affineBrownianCompactPiece, ← hpieceIeq] using hpieceIMean)
        (by simpa [affineBrownianCompactPiece, ← hpieceJeq] using hpieceJMean)
    constructor
    · simpa [affineBrownianCompactPiece, ← hpieceIeq, ← hpieceJeq] using hpair.1
    · have hcoef : (2 * Real.pi * (q : Real))⁻¹ * (A * A) ≤ C0 := by
        dsimp [C0]
        have hden : 2 * Real.pi * gap ≤ 2 * Real.pi * (q : Real) := by
          nlinarith [Real.pi_pos]
        have hinv : (2 * Real.pi * (q : Real))⁻¹ ≤
            (2 * Real.pi * gap)⁻¹ := by
          exact inv_anti₀ (by positivity) hden
        exact mul_le_mul_of_nonneg_right hinv (mul_nonneg hA.le hA.le)
      calc
        (∫ omega, tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
            (2 * Real.pi * (q : Real))⁻¹ * (A * A) *
              rho ^ (2 * tubeExponent s) := by
                simpa [affineBrownianCompactPiece, ← hpieceIeq, ← hpieceJeq]
                  using hpair.2
        _ ≤ C0 * rho ^ (2 * tubeExponent s) :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hrho.le _)
  · let a : NNReal := (S.shift j).toNNReal
    let r : NNReal := (S.ratio j).toNNReal
    let b : NNReal := (S.shift i).toNNReal
    let q : NNReal := b - (a + r)
    let t : NNReal := (S.ratio i).toNNReal
    have ha : (a : Real) = S.shift j := by
      exact Real.coe_toNNReal _ (S.shift_nonneg_of_mapsTo j)
    have hr : (r : Real) = S.ratio j := by
      exact Real.coe_toNNReal _ (S.ratio_pos j).le
    have hb : (b : Real) = S.shift i := by
      exact Real.coe_toNNReal _ (S.shift_nonneg_of_mapsTo i)
    have ht : (t : Real) = S.ratio i := by
      exact Real.coe_toNNReal _ (S.ratio_pos i).le
    have harb : a + r ≤ b := by
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_add, ha, hr, hb]
      linarith
    have haqb : a + r + q = b := add_tsub_cancel_of_le harb
    have hpieceJeq : hmu.compactPiece S j =
        affineTimeCompact a r hmu.compactAttractor := by
      simpa [a, r] using hmu.compactPiece_eq_affineTimeCompact S j
    have hpieceIeq : hmu.compactPiece S i =
        affineTimeCompact (a + r + q) t hmu.compactAttractor := by
      rw [haqb]
      simpa [b, t] using hmu.compactPiece_eq_affineTimeCompact S i
    have hqgap : gap ≤ (q : Real) := by
      rw [NNReal.coe_sub harb, NNReal.coe_add, ha, hr, hb]
      linarith
    have hrne : r ≠ 0 := by
      apply NNReal.coe_ne_zero.mp
      rw [hr]
      exact ne_of_gt (S.ratio_pos j)
    have htne : t ≠ 0 := by
      apply NNReal.coe_ne_zero.mp
      rw [ht]
      exact ne_of_gt (S.ratio_pos i)
    have hqne : q ≠ 0 := by
      exact ne_of_gt (NNReal.coe_pos.mp (hgap.trans_le hqgap))
    obtain ⟨hfull, hfullMean⟩ := hupper rho hrho hrho1
    obtain ⟨hpieceJ, hpieceJMean⟩ :=
      hmu.integrable_and_integral_tubeArea_compactPiece_le
        hW S j hfull hfullMean
    obtain ⟨hpieceI, hpieceIMean⟩ :=
      hmu.integrable_and_integral_tubeArea_compactPiece_le
        hW S i hfull hfullMean
    have hpair := hW.integrable_and_integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
      a hrne hqne htne hmu.compactAttractor hmu.compactAttractor
        hmu.attractor.2.2.1 hmu.attractor.2.2.1 hrho
        (by simpa [affineBrownianCompactPiece, ← hpieceJeq] using hpieceJ)
        (by simpa [affineBrownianCompactPiece, ← hpieceIeq] using hpieceI)
        (by simpa [affineBrownianCompactPiece, ← hpieceJeq] using hpieceJMean)
        (by simpa [affineBrownianCompactPiece, ← hpieceIeq] using hpieceIMean)
    constructor
    · have hpairInt := hpair.1
      simpa [tubeOverlapArea_comm, affineBrownianCompactPiece,
        ← hpieceJeq, ← hpieceIeq] using hpairInt
    · have hcoef : (2 * Real.pi * (q : Real))⁻¹ * (A * A) ≤ C0 := by
        dsimp [C0]
        have hden : 2 * Real.pi * gap ≤ 2 * Real.pi * (q : Real) := by
          nlinarith [Real.pi_pos]
        have hinv : (2 * Real.pi * (q : Real))⁻¹ ≤
            (2 * Real.pi * gap)⁻¹ := inv_anti₀ (by positivity) hden
        exact mul_le_mul_of_nonneg_right hinv (mul_nonneg hA.le hA.le)
      calc
        (∫ omega, tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega) ∂P) =
            ∫ omega, tubeOverlapArea rho
              (brownianImage W (hmu.compactPiece S j) omega)
              (brownianImage W (hmu.compactPiece S i) omega) ∂P := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun omega =>
                  tubeOverlapArea_comm rho _ _
        _ ≤ (2 * Real.pi * (q : Real))⁻¹ * (A * A) *
              rho ^ (2 * tubeExponent s) := by
                simpa [affineBrownianCompactPiece, ← hpieceJeq, ← hpieceIeq]
                  using hpair.2
        _ ≤ C0 * rho ^ (2 * tubeExponent s) :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hrho.le _)

/-- The complete system-level overlap and defect conclusion, conditional only
on the raw `q = 1` tube-area estimate for the full image. -/
theorem IsNatural.tubeOverlap_of_tubeArea_mean_upper
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hupper : ∃ A : Real, 0 < A ∧ ∀ rho : Real, 0 < rho → rho ≤ 1 →
      Integrable (fun omega =>
        tubeArea rho (brownianImage W hmu.compactAttractor omega)) P ∧
      (∫ omega,
        tubeArea rho (brownianImage W hmu.compactAttractor omega) ∂P) ≤
          A * rho ^ tubeExponent s) :
    ∃ C : Real, 0 < C ∧ ∀ rho : Real, 0 < rho → rho ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
            C * rho ^ (2 * tubeExponent s)) ∧
      Integrable (fun omega => tubeDefect rho
        (fun i => brownianImage W (hmu.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect rho
        (fun i => brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
          C * rho ^ (2 * tubeExponent s) := by
  apply hmu.tubeOverlap_of_pairwise hW S hs0 hs1 hsep hdim
  exact hmu.exists_pairwise_tubeOverlap_of_tubeArea_mean_upper hW S hsep hupper

/-- The overlap theorem follows directly from the upper half of the tube-moment
theorem by taking its exponent equal to one. -/
theorem IsNatural.tubeOverlap_of_tubeMomentsUpper
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hmom : ∀ q : Real, 1 ≤ q → ∃ Cq : Real, 0 < Cq ∧
      ∀ rho : Real, 0 < rho → rho ≤ 1 →
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
    ∃ C : Real, 0 < C ∧ ∀ rho : Real, 0 < rho → rho ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea rho
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
            C * rho ^ (2 * tubeExponent s)) ∧
      Integrable (fun omega => tubeDefect rho
        (fun i => brownianImage W (hmu.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect rho
        (fun i => brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
          C * rho ^ (2 * tubeExponent s) := by
  apply hmu.tubeOverlap_of_tubeArea_mean_upper hW S hs0 hs1 hsep hdim
  obtain ⟨C1, hC1, hmoment⟩ := hmom 1 le_rfl
  refine ⟨C1, hC1, ?_⟩
  intro rho hrho hrho1
  obtain ⟨hareaPow, _hmassPow, hsum⟩ := hmoment rho hrho hrho1
  have harea : Integrable (fun omega =>
      tubeArea rho (brownianImage W hmu.compactAttractor omega)) P := by
    simpa using hareaPow
  refine ⟨harea, ?_⟩
  calc
    (∫ omega,
      tubeArea rho (brownianImage W hmu.compactAttractor omega) ∂P) ≤
        (∫ omega,
          tubeArea rho (brownianImage W hmu.compactAttractor omega) ∂P) +
        ∫ omega,
          tubeMass rho (brownianImage W hmu.compactAttractor omega) ∂P := by
            exact le_add_of_nonneg_right
              (integral_nonneg fun omega => tubeMass_nonneg rho _)
    _ ≤ C1 * rho ^ ((1 : Real) * tubeExponent s) := by
      simpa using hsum
    _ = C1 * rho ^ tubeExponent s := by rw [one_mul]

end System

end

end BrownianImages
