/-
`sec:reconstruction`: Brownian cylinders indexed by arbitrary nonempty compact subsets of the
unit time interval.

This file extends the interval-piece results from `Minkowski.BrownianPieces` from the full unit
interval to a prescribed nonempty compact time set.  It records Brownian scaling, the exact
pathwise affine image identity, independence on ordered disjoint host intervals, and the induced
scaling law for smoothed tube mass.
-/
import BrownianImages.Minkowski.BrownianPieces
import BrownianImages.Minkowski.TubeAlgebra

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Pointwise Topology

/-! ### Compact affine time copies -/

/-- The affine time copy `a + r K` of a nonempty compact real set. -/
noncomputable def affineTimeCompact (a r : NNReal) (K : NonemptyCompacts Real) :
    NonemptyCompacts Real :=
  K.map (fun t => (a : Real) + (r : Real) * t) (by fun_prop)

/-- The underlying set of an affinely rescaled compact time set is its image under `t ↦
a + rt`. -/
@[simp]
theorem coe_affineTimeCompact (a r : NNReal) (K : NonemptyCompacts Real) :
    (affineTimeCompact a r K : Set Real) =
      (fun t => (a : Real) + (r : Real) * t) '' K :=
  rfl

/-- The corresponding unnormalized affine Brownian cylinder. -/
noncomputable def affineBrownianCompactPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal -> Omega -> Plane)
    (a r : NNReal) (K : NonemptyCompacts Real) (omega : Omega) : CompactPlane :=
  brownianImage W (affineTimeCompact a r K) omega

/-- Brownian scaling gives the rescaled compact `K`-image the same law as the standard
compact `K`-image. -/
theorem IsPlanarBrownian.map_rescaledBrownianCompactPiece_eq
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P) (a : NNReal)
    {r : NNReal} (hr : r ≠ 0) (K : NonemptyCompacts Real) :
    P.map (rescaledBrownianCompactPiece W a r K) = P.map (brownianImage W K) := by
  exact (hW.intervalRescale a hr).map_brownianImage_eq hW K

/-- On a continuous path, translating and dilating the rescaled compact image recovers exactly
the Brownian image over the affine time copy `a + r K`. -/
theorem translate_dilate_rescaledBrownianCompactPiece_of_continuous
    {Omega : Type*} [MeasurableSpace Omega] {W : NNReal -> Omega -> Plane}
    {a r : NNReal} (hr : r ≠ 0) {K : NonemptyCompacts Real}
    (hK : (K : Set Real) ⊆ Set.Icc 0 1) {omega : Omega}
    (homega : Continuous (fun t => W t omega)) :
    translateCompact (W a omega)
        (dilateCompact (Real.sqrt (r : Real))
          (rescaledBrownianCompactPiece W a r K omega)) =
      affineBrownianCompactPiece W a r K omega := by
  apply NonemptyCompacts.ext
  rw [coe_translateCompact, coe_dilateCompact, ← Set.image_smul, Set.image_image,
    rescaledBrownianCompactPiece, coe_brownianImage_of_continuous K,
    affineBrownianCompactPiece, coe_brownianImage_of_continuous
      (affineTimeCompact a r K), coe_affineTimeCompact, Set.image_image]
  · rw [Set.image_image]
    apply Set.image_congr
    intro t ht
    have ht0 : 0 ≤ t := (hK ht).1
    have hrpos : 0 < (r : Real) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    have hsqrt : Real.sqrt (r : Real) ≠ 0 := Real.sqrt_ne_zero'.mpr hrpos
    simp only [intervalRescale, smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
    rw [Real.toNNReal_add (NNReal.coe_nonneg a) (mul_nonneg (NNReal.coe_nonneg r) ht0),
      Real.toNNReal_mul (NNReal.coe_nonneg r), Real.toNNReal_of_nonneg ht0]
    simp
  · exact homega
  · change Continuous (fun t : NNReal =>
      (Real.sqrt (r : Real))⁻¹ • (W (a + r * t) omega - W a omega))
    fun_prop

/-! ### Independence on ordered host intervals -/

/-! ### Tube-mass scaling for affine Brownian cylinders -/

/-- The pathwise compact-image identity holds almost surely for Brownian motion. -/
theorem IsPlanarBrownian.ae_translate_dilate_rescaledBrownianCompactPiece
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    {a r : NNReal} (hr : r ≠ 0) {K : NonemptyCompacts Real}
    (hK : (K : Set Real) ⊆ Set.Icc 0 1) :
    ∀ᵐ omega ∂P,
      translateCompact (W a omega)
          (dilateCompact (Real.sqrt (r : Real))
            (rescaledBrownianCompactPiece W a r K omega)) =
        affineBrownianCompactPiece W a r K omega := by
  filter_upwards [hW.ae_continuous] with omega homega
  exact translate_dilate_rescaledBrownianCompactPiece_of_continuous hr hK homega

/-- On a continuous path, planar quadratic scaling turns the tube mass of an affine Brownian
cylinder into `r` times the tube mass of its Brownian-rescaled compact image. -/
theorem tubeMass_affineBrownianCompactPiece_of_continuous
    {Omega : Type*} [MeasurableSpace Omega] {W : NNReal -> Omega -> Plane}
    {rho : Real} (hrho : 0 < rho) {a r : NNReal} (hr : r ≠ 0)
    {K : NonemptyCompacts Real} (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    {omega : Omega} (homega : Continuous (fun t => W t omega)) :
    tubeMass rho (affineBrownianCompactPiece W a r K omega) =
      (r : Real) * tubeMass (rho / Real.sqrt (r : Real))
        (rescaledBrownianCompactPiece W a r K omega) := by
  have hrpos : 0 < (r : Real) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have hsqrtpos : 0 < Real.sqrt (r : Real) := Real.sqrt_pos.2 hrpos
  rw [← translate_dilate_rescaledBrownianCompactPiece_of_continuous hr hK homega,
    tubeMass_translate_dilate hrho hsqrtpos, Real.sq_sqrt (NNReal.coe_nonneg r)]

/-- Exact equality in law for the tube mass of the affine Brownian cylinder over `a + r K`.
The planar spatial dilation is by `sqrt r`, hence its quadratic Jacobian is exactly `r`. -/
theorem IsPlanarBrownian.map_tubeMass_affineBrownianCompactPiece_eq
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    {rho : Real} (hrho : 0 < rho) (a : NNReal) {r : NNReal} (hr : r ≠ 0)
    (K : NonemptyCompacts Real) (hK : (K : Set Real) ⊆ Set.Icc 0 1) :
    P.map (fun omega => tubeMass rho (affineBrownianCompactPiece W a r K omega)) =
      P.map (fun omega => (r : Real) *
        tubeMass (rho / Real.sqrt (r : Real)) (brownianImage W K omega)) := by
  have hrpos : 0 < (r : Real) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have hsqrtpos : 0 < Real.sqrt (r : Real) := Real.sqrt_pos.2 hrpos
  have hrhoScaled : 0 < rho / Real.sqrt (r : Real) := div_pos hrho hsqrtpos
  let g : CompactPlane -> Real := fun F =>
    (r : Real) * tubeMass (rho / Real.sqrt (r : Real)) F
  have hg : Measurable g :=
    (continuous_const.mul (continuous_tubeMass hrhoScaled)).measurable
  have hrescaled : AEMeasurable (rescaledBrownianCompactPiece W a r K) P :=
    (hW.intervalRescale a hr).aemeasurable_brownianImage K
  have hstandard : AEMeasurable (brownianImage W K) P :=
    hW.aemeasurable_brownianImage K
  have hpath : (fun omega =>
      tubeMass rho (affineBrownianCompactPiece W a r K omega)) =ᵐ[P]
      g ∘ rescaledBrownianCompactPiece W a r K := by
    filter_upwards [hW.ae_continuous] with omega homega
    exact tubeMass_affineBrownianCompactPiece_of_continuous hrho hr hK homega
  calc
    P.map (fun omega => tubeMass rho (affineBrownianCompactPiece W a r K omega)) =
        P.map (g ∘ rescaledBrownianCompactPiece W a r K) := Measure.map_congr hpath
    _ = (P.map (rescaledBrownianCompactPiece W a r K)).map g :=
      (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hrescaled).symm
    _ = (P.map (brownianImage W K)).map g := by
      rw [hW.map_rescaledBrownianCompactPiece_eq a hr K]
    _ = P.map (g ∘ brownianImage W K) :=
      AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hstandard
    _ = P.map (fun omega => (r : Real) *
        tubeMass (rho / Real.sqrt (r : Real)) (brownianImage W K omega)) := rfl

end BrownianImages
