/-
`sec:reconstruction`: Brownian cylinders indexed by arbitrary nonempty compact subsets of the
unit time interval.

This file extends the interval-piece results from `Minkowski.BrownianPieces` from the full unit
interval to a prescribed nonempty compact time set.  It records Brownian scaling, the exact
pathwise affine image identity, independence on ordered disjoint host intervals, and the induced
scaling law for smoothed tube mass.  The oriented copies `orientCompact ε K`, which are `K`
for `ε = 1` and the reflection `1 - K` for `ε = -1`, carry the time reversal of the
increments that `sec:reconstruction` uses when a similarity reverses orientation:
`brownianImage_reflectCompact_of_continuous` is the pathwise identity, and
`IsPlanarBrownian.map_tubeMass_affineBrownianCompactPiece_orientCompact_eq` the resulting
scaling law.
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

/-! ### Oriented time copies -/

/-- The reflection `1 - K` of a compact time set. -/
noncomputable def reflectCompact (K : NonemptyCompacts Real) : NonemptyCompacts Real :=
  K.map (fun t => 1 - t) (by fun_prop)

/-- The underlying set of the reflection is the image under `t ↦ 1 - t`. -/
@[simp]
theorem coe_reflectCompact (K : NonemptyCompacts Real) :
    (reflectCompact K : Set Real) = (fun t => 1 - t) '' K :=
  rfl

/-- The reflection of a compact subset of `[0,1]` lies in `[0,1]`. -/
theorem reflectCompact_subset_Icc {K : NonemptyCompacts Real}
    (hK : (K : Set Real) ⊆ Set.Icc 0 1) : (reflectCompact K : Set Real) ⊆ Set.Icc 0 1 := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨h0, h1⟩ := hK ht
  exact ⟨by linarith, by linarith⟩

/-- The oriented copy of a compact time set: `K` itself for `ε = 1` and its reflection
`1 - K` for `ε = -1`, through the one formula `t ↦ (1 - ε)/2 + ε t`.  A similarity of
`[0,1]` with orientation `ε`, ratio `r` and left endpoint `a` sends `K` to
`a + r · orientCompact ε K`. -/
noncomputable def orientCompact (ε : Real) (K : NonemptyCompacts Real) :
    NonemptyCompacts Real :=
  K.map (fun t => (1 - ε) / 2 + ε * t) (by fun_prop)

/-- The underlying set of an oriented copy. -/
@[simp]
theorem coe_orientCompact (ε : Real) (K : NonemptyCompacts Real) :
    (orientCompact ε K : Set Real) = (fun t => (1 - ε) / 2 + ε * t) '' K :=
  rfl

/-- The orientation-preserving copy is the set itself. -/
theorem orientCompact_one (K : NonemptyCompacts Real) : orientCompact 1 K = K := by
  apply NonemptyCompacts.ext
  rw [coe_orientCompact]
  simp

/-- The orientation-reversing copy is the reflection. -/
theorem orientCompact_neg_one (K : NonemptyCompacts Real) :
    orientCompact (-1) K = reflectCompact K := by
  apply NonemptyCompacts.ext
  rw [coe_orientCompact, coe_reflectCompact]
  apply Set.image_congr
  intro t _
  ring

/-- An oriented copy of a compact subset of `[0,1]` lies in `[0,1]`. -/
theorem orientCompact_subset_Icc {ε : Real} (hε : ε = 1 ∨ ε = -1) {K : NonemptyCompacts Real}
    (hK : (K : Set Real) ⊆ Set.Icc 0 1) : (orientCompact ε K : Set Real) ⊆ Set.Icc 0 1 := by
  rcases hε with rfl | rfl
  · rw [orientCompact_one]
    exact hK
  · rw [orientCompact_neg_one]
    exact reflectCompact_subset_Icc hK

/-- **Time reversal on a continuous path.**  The Brownian image of the reflected time set
`1 - K` is the translate by `W(1)` of the image of `K` under the reversed motion
`t ↦ W(1 - t) - W(1)`. -/
theorem brownianImage_reflectCompact_of_continuous
    {Omega : Type*} [MeasurableSpace Omega] {W : NNReal -> Omega -> Plane}
    {K : NonemptyCompacts Real} (hK : (K : Set Real) ⊆ Set.Icc 0 1) {omega : Omega}
    (homega : Continuous (fun t => W t omega)) :
    brownianImage W (reflectCompact K) omega =
      translateCompact (W 1 omega) (brownianImage (timeReversal W 1) K omega) := by
  have hrev : Continuous (fun t => timeReversal W 1 t omega) :=
    continuous_timeReversal 1 homega
  apply NonemptyCompacts.ext
  rw [coe_translateCompact, coe_brownianImage_of_continuous _ homega,
    coe_brownianImage_of_continuous _ hrev, coe_reflectCompact, Set.image_image,
    Set.image_image]
  apply Set.image_congr
  intro t ht
  obtain ⟨ht0, ht1⟩ := hK ht
  have hle : t.toNNReal ≤ 1 := Real.toNNReal_le_one.mpr ht1
  have hrt : revTime 1 t.toNNReal = (1 - t).toNNReal := by
    simp only [revTime, NNReal.coe_one, Real.coe_toNNReal t ht0]
  simp only [timeReversal, min_eq_left hle, hrt]
  abel

/-- The tube mass of the Brownian image of the reflected time set has the law of the tube
mass of the Brownian image of the set itself: the reversed motion is a planar Brownian
motion, and the tube mass is translation invariant. -/
theorem IsPlanarBrownian.map_tubeMass_brownianImage_reflectCompact_eq
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P) {rho : Real} (hrho : 0 < rho)
    (K : NonemptyCompacts Real) (hK : (K : Set Real) ⊆ Set.Icc 0 1) :
    P.map (fun omega => tubeMass rho (brownianImage W (reflectCompact K) omega)) =
      P.map (fun omega => tubeMass rho (brownianImage W K omega)) := by
  have hrev : IsPlanarBrownian (BrownianImages.timeReversal W 1) P := hW.timeReversal 1
  let g : CompactPlane -> Real := tubeMass rho
  have hg : Measurable g := (continuous_tubeMass hrho).measurable
  have hpath : (fun omega => tubeMass rho (brownianImage W (reflectCompact K) omega)) =ᵐ[P]
      g ∘ brownianImage (BrownianImages.timeReversal W 1) K := by
    filter_upwards [hW.ae_continuous] with omega homega
    simp only [Function.comp, g]
    rw [brownianImage_reflectCompact_of_continuous hK homega, tubeMass_translate]
  calc
    P.map (fun omega => tubeMass rho (brownianImage W (reflectCompact K) omega)) =
        P.map (g ∘ brownianImage (BrownianImages.timeReversal W 1) K) := Measure.map_congr hpath
    _ = (P.map (brownianImage (BrownianImages.timeReversal W 1) K)).map g :=
      (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable
        (hrev.aemeasurable_brownianImage K)).symm
    _ = (P.map (brownianImage W K)).map g := by
      rw [hrev.map_brownianImage_eq hW K]
    _ = P.map (g ∘ brownianImage W K) :=
      AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (hW.aemeasurable_brownianImage K)
    _ = P.map (fun omega => tubeMass rho (brownianImage W K omega)) := rfl

/-- The tube mass of the Brownian image of an oriented copy of `K` has the law of the
tube mass of the Brownian image of `K`. -/
theorem IsPlanarBrownian.map_tubeMass_brownianImage_orientCompact_eq
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P) {rho : Real} (hrho : 0 < rho)
    {ε : Real} (hε : ε = 1 ∨ ε = -1) (K : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1) :
    P.map (fun omega => tubeMass rho (brownianImage W (orientCompact ε K) omega)) =
      P.map (fun omega => tubeMass rho (brownianImage W K omega)) := by
  rcases hε with rfl | rfl
  · rw [orientCompact_one]
  · rw [orientCompact_neg_one]
    exact hW.map_tubeMass_brownianImage_reflectCompact_eq hrho K hK

/-- **Brownian scaling for an oriented affine time copy**, `eq:neighbourhood-union-scaling`
with time reversal of the increments when the similarity reverses orientation: the tube
mass of the Brownian image of `a + r · orientCompact ε K` has the law of `r` times the
tube mass of the Brownian image of `K` at radius `rho / √r`. -/
theorem IsPlanarBrownian.map_tubeMass_affineBrownianCompactPiece_orientCompact_eq
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    {rho : Real} (hrho : 0 < rho) (a : NNReal) {r : NNReal} (hr : r ≠ 0)
    {ε : Real} (hε : ε = 1 ∨ ε = -1) (K : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1) :
    P.map (fun omega =>
        tubeMass rho (affineBrownianCompactPiece W a r (orientCompact ε K) omega)) =
      P.map (fun omega => (r : Real) *
        tubeMass (rho / Real.sqrt (r : Real)) (brownianImage W K omega)) := by
  rw [hW.map_tubeMass_affineBrownianCompactPiece_eq hrho a hr (orientCompact ε K)
    (orientCompact_subset_Icc hε hK)]
  have hrpos : 0 < (r : Real) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have hrho' : 0 < rho / Real.sqrt (r : Real) := div_pos hrho (Real.sqrt_pos.2 hrpos)
  have h := hW.map_tubeMass_brownianImage_orientCompact_eq hrho' hε K hK
  let g : Real -> Real := fun x => (r : Real) * x
  have hg : Measurable g := by fun_prop
  have h1 : AEMeasurable (fun omega => tubeMass (rho / Real.sqrt (r : Real))
      (brownianImage W (orientCompact ε K) omega)) P :=
    (continuous_tubeMass hrho').measurable.comp_aemeasurable (hW.aemeasurable_brownianImage _)
  have h2 : AEMeasurable (fun omega => tubeMass (rho / Real.sqrt (r : Real))
      (brownianImage W K omega)) P :=
    (continuous_tubeMass hrho').measurable.comp_aemeasurable (hW.aemeasurable_brownianImage _)
  calc
    P.map (fun omega => (r : Real) * tubeMass (rho / Real.sqrt (r : Real))
        (brownianImage W (orientCompact ε K) omega)) =
        (P.map (fun omega => tubeMass (rho / Real.sqrt (r : Real))
          (brownianImage W (orientCompact ε K) omega))).map g :=
      (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h1).symm
    _ = (P.map (fun omega => tubeMass (rho / Real.sqrt (r : Real))
          (brownianImage W K omega))).map g := by rw [h]
    _ = P.map (fun omega => (r : Real) * tubeMass (rho / Real.sqrt (r : Real))
          (brownianImage W K omega)) :=
      AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h2

end BrownianImages
