/-
Pathwise geometry relating actual affine Brownian cylinders to the centered
configuration used in the Gaussian gap estimate.

The probabilistic independence argument is most naturally expressed after
centering the left cylinder at its right endpoint and the right cylinder at
its left endpoint.  Common translation invariance then identifies that
configuration exactly with the overlap of the original Brownian images.
-/
import BrownianImages.Minkowski.OverlapProbability

namespace BrownianImages

open MeasureTheory Set TopologicalSpace
open scoped NNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The two names used for scalar dilation of a rescaled compact Brownian
piece agree. -/
theorem centeredBrownianCompactPiece_eq_dilateCompact
    (W : NNReal → Omega → Plane) (a r : NNReal)
    (K : NonemptyCompacts Real) (omega : Omega) :
    centeredBrownianCompactPiece W a r K omega =
      dilateCompact (Real.sqrt (r : Real))
        (rescaledBrownianCompactPiece W a r K omega) := by
  apply NonemptyCompacts.ext
  rfl

/-- Translating a left-centered compact piece back by its initial Brownian
position recovers the actual affine Brownian image. -/
theorem translate_centeredBrownianCompactPiece_of_continuous
    {W : NNReal → Omega → Plane} {a r : NNReal} (hr : r ≠ 0)
    {K : NonemptyCompacts Real} (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    {omega : Omega} (homega : Continuous (fun t => W t omega)) :
    translateCompact (W a omega)
        (centeredBrownianCompactPiece W a r K omega) =
      affineBrownianCompactPiece W a r K omega := by
  rw [centeredBrownianCompactPiece_eq_dilateCompact]
  exact translate_dilate_rescaledBrownianCompactPiece_of_continuous
    hr hK homega

/-- Right-centering does not change raw tube area. -/
theorem tubeArea_rightCenteredBrownianCompactPiece
    {W : NNReal → Omega → Plane} (a r : NNReal)
    (K : NonemptyCompacts Real) (omega : Omega)
    {rho : Real} (hrho : 0 < rho) :
    tubeArea rho (rightCenteredBrownianCompactPiece W a r K omega) =
      tubeArea rho (centeredBrownianCompactPiece W a r K omega) := by
  unfold rightCenteredBrownianCompactPiece
  exact tubeArea_translate hrho _ _

/-- Almost surely, centering an affine Brownian cylinder does not change its
raw tube area. -/
theorem IsPlanarBrownian.ae_tubeArea_centeredBrownianCompactPiece_eq_affine
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) {a r : NNReal} (hr : r ≠ 0)
    {K : NonemptyCompacts Real} (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    {rho : Real} (hrho : 0 < rho) :
    (fun omega => tubeArea rho
      (centeredBrownianCompactPiece W a r K omega)) =ᵐ[P]
      fun omega => tubeArea rho (affineBrownianCompactPiece W a r K omega) := by
  filter_upwards [hW.ae_continuous] with omega homega
  rw [← translate_centeredBrownianCompactPiece_of_continuous hr hK homega,
    tubeArea_translate hrho]

/-- The same equality for right-centering. -/
theorem IsPlanarBrownian.ae_tubeArea_rightCenteredBrownianCompactPiece_eq_affine
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) {a r : NNReal} (hr : r ≠ 0)
    {K : NonemptyCompacts Real} (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    {rho : Real} (hrho : 0 < rho) :
    (fun omega => tubeArea rho
      (rightCenteredBrownianCompactPiece W a r K omega)) =ᵐ[P]
      fun omega => tubeArea rho (affineBrownianCompactPiece W a r K omega) := by
  filter_upwards
    [hW.ae_tubeArea_centeredBrownianCompactPiece_eq_affine hr hK hrho]
      with omega homega
  rw [tubeArea_rightCenteredBrownianCompactPiece a r K omega hrho, homega]

/-- The actual affine-cylinder overlap is integrable under the same two area
integrability hypotheses as the centered Gaussian-gap configuration. -/
theorem IsPlanarBrownian.integrable_tubeOverlapArea_affineCompactPieces_gap
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r q s : NNReal}
    (hr : r ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (K L : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    (hL : (L : Set Real) ⊆ Set.Icc 0 1)
    {rho : Real} (hrho : 0 < rho)
    (hareaA : Integrable (fun omega =>
      tubeArea rho (rightCenteredBrownianCompactPiece W a r K omega)) P)
    (hareaB : Integrable (fun omega =>
      tubeArea rho
        (centeredBrownianCompactPiece W (a + r + q) s L omega)) P) :
    Integrable (fun omega => tubeOverlapArea rho
      (affineBrownianCompactPiece W a r K omega)
      (affineBrownianCompactPiece W (a + r + q) s L omega)) P := by
  have hcenter := hW.integrable_tubeOverlapArea_compactPieces_gap
    a hr hq hs K L hK hL hrho hareaA hareaB
  apply hcenter.congr
  filter_upwards
    [hW.ae_tubeOverlapArea_affineCompactPieces_eq_gap
      (q := q) a hr hs K L hK hL hrho] with omega homega
  exact homega.symm

/-- Paper-scaled overlap estimate for the two actual affine Brownian
cylinders. -/
theorem IsPlanarBrownian.integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r q s : NNReal}
    (hr : r ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (K L : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    (hL : (L : Set Real) ⊆ Set.Icc 0 1)
    {rho alpha CA CB : Real} (hrho : 0 < rho)
    (hareaA : Integrable (fun omega =>
      tubeArea rho (rightCenteredBrownianCompactPiece W a r K omega)) P)
    (hareaB : Integrable (fun omega =>
      tubeArea rho
        (centeredBrownianCompactPiece W (a + r + q) s L omega)) P)
    (hmeanA : (∫ omega, tubeArea rho
      (rightCenteredBrownianCompactPiece W a r K omega) ∂P) ≤
        CA * rho ^ alpha)
    (hmeanB : (∫ omega, tubeArea rho
      (centeredBrownianCompactPiece W (a + r + q) s L omega) ∂P) ≤
        CB * rho ^ alpha) :
    (∫ omega, tubeOverlapArea rho
      (affineBrownianCompactPiece W a r K omega)
      (affineBrownianCompactPiece W (a + r + q) s L omega) ∂P) ≤
      (2 * Real.pi * (q : Real))⁻¹ * (CA * CB) *
        rho ^ (2 * alpha) := by
  rw [integral_congr_ae
    (hW.ae_tubeOverlapArea_affineCompactPieces_eq_gap
      (q := q) a hr hs K L hK hL hrho)]
  exact hW.integral_tubeOverlapArea_compactPieces_gap_le_rpow
    a hr hq hs K L hK hL hrho hareaA hareaB hmeanA hmeanB

/-- The affine-cylinder overlap estimate with its moment hypotheses stated for
the two actual affine Brownian images.  This is the form used when the pieces
are compared with the Brownian image of the full attractor. -/
theorem IsPlanarBrownian.integrable_and_integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r q s : NNReal}
    (hr : r ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (K L : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    (hL : (L : Set Real) ⊆ Set.Icc 0 1)
    {rho alpha CA CB : Real} (hrho : 0 < rho)
    (hareaA : Integrable (fun omega =>
      tubeArea rho (affineBrownianCompactPiece W a r K omega)) P)
    (hareaB : Integrable (fun omega =>
      tubeArea rho
        (affineBrownianCompactPiece W (a + r + q) s L omega)) P)
    (hmeanA : (∫ omega, tubeArea rho
      (affineBrownianCompactPiece W a r K omega) ∂P) ≤
        CA * rho ^ alpha)
    (hmeanB : (∫ omega, tubeArea rho
      (affineBrownianCompactPiece W (a + r + q) s L omega) ∂P) ≤
        CB * rho ^ alpha) :
    Integrable (fun omega => tubeOverlapArea rho
      (affineBrownianCompactPiece W a r K omega)
      (affineBrownianCompactPiece W (a + r + q) s L omega)) P ∧
    (∫ omega, tubeOverlapArea rho
      (affineBrownianCompactPiece W a r K omega)
      (affineBrownianCompactPiece W (a + r + q) s L omega) ∂P) ≤
      (2 * Real.pi * (q : Real))⁻¹ * (CA * CB) *
        rho ^ (2 * alpha) := by
  have hAeq := hW.ae_tubeArea_rightCenteredBrownianCompactPiece_eq_affine
    (a := a) (r := r) hr hK hrho
  have hBeq := hW.ae_tubeArea_centeredBrownianCompactPiece_eq_affine
    (a := a + r + q) (r := s) hs hL hrho
  have hareaAcenter : Integrable (fun omega =>
      tubeArea rho (rightCenteredBrownianCompactPiece W a r K omega)) P := by
    apply hareaA.congr
    filter_upwards [hAeq] with omega homega
    exact homega.symm
  have hareaBcenter : Integrable (fun omega =>
      tubeArea rho
        (centeredBrownianCompactPiece W (a + r + q) s L omega)) P := by
    apply hareaB.congr
    filter_upwards [hBeq] with omega homega
    exact homega.symm
  have hmeanAcenter : (∫ omega, tubeArea rho
      (rightCenteredBrownianCompactPiece W a r K omega) ∂P) ≤
        CA * rho ^ alpha := by
    rw [integral_congr_ae hAeq]
    exact hmeanA
  have hmeanBcenter : (∫ omega, tubeArea rho
      (centeredBrownianCompactPiece W (a + r + q) s L omega) ∂P) ≤
        CB * rho ^ alpha := by
    rw [integral_congr_ae hBeq]
    exact hmeanB
  exact ⟨hW.integrable_tubeOverlapArea_affineCompactPieces_gap
      a hr hq hs K L hK hL hrho hareaAcenter hareaBcenter,
    hW.integral_tubeOverlapArea_affineCompactPieces_gap_le_rpow
      a hr hq hs K L hK hL hrho hareaAcenter hareaBcenter
        hmeanAcenter hmeanBcenter⟩

end

end BrownianImages
