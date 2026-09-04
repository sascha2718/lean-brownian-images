/-
Brownian scaling reduction for the maximal-oscillation input in
`thm:neighbourhood-moments`.

Mathlib does not currently provide a continuous-time Brownian maximal-moment
theorem.  This file proves everything around that missing theorem.  A
continuous functional `compactRadius` measures how far a compact planar set is
from the origin.  The normalized Brownian image on any affine interval has the
same radius law as the image on `[0,1]`.  Consequently, the local estimate in
the stopping-cover proof follows from one unit-interval moment, with the exact
Brownian square-root scaling and no independence assumption.
-/
import BrownianImages.MinkowskiBrownianPieces
import BrownianImages.MinkowskiBrownianCompactPieces
import BrownianImages.MinkowskiTubeUpper

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### A continuous radius functional on compact sets -/

/-- A continuous radius dominating the distance of every point of `F` from
the origin.  It is the Hausdorff distance from `F` to the singleton `{0}`. -/
def compactRadius (F : CompactPlane) : ℝ :=
  dist F ({0} : CompactPlane)

theorem compactRadius_nonneg (F : CompactPlane) : 0 ≤ compactRadius F :=
  dist_nonneg

theorem continuous_compactRadius : Continuous compactRadius := by
  exact continuous_id.dist continuous_const

theorem measurable_compactRadius : Measurable compactRadius :=
  continuous_compactRadius.measurable

/-- Every point of a compact set lies in the closed disc centered at zero with
radius `compactRadius F`. -/
theorem subset_closedBall_zero_compactRadius (F : CompactPlane) :
    (F : Set Plane) ⊆ Metric.closedBall 0 (compactRadius F) := by
  intro x hx
  rw [Metric.mem_closedBall, compactRadius]
  change dist x 0 ≤ Metric.hausdorffDist (F : Set Plane) ({0} : Set Plane)
  have hfin : Metric.hausdorffEDist (F : Set Plane) ({0} : Set Plane) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      F.nonempty (Set.singleton_nonempty 0) F.isCompact.isBounded
        Bornology.isBounded_singleton
  have h := Metric.infDist_le_hausdorffDist_of_mem
    (s := (F : Set Plane)) (t := ({0} : Set Plane)) hx hfin
  simpa only [Metric.infDist_singleton] using h

/-! ### The normalized affine interval radius has the unit law -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Radius of the normalized compact Brownian image over an affine interval. -/
def rescaledBrownianRadius (W : NNReal → Omega → Plane) (a r : NNReal)
    (omega : Omega) : ℝ :=
  compactRadius (rescaledBrownianPiece W a r omega)

/-- Radius of the reference Brownian image over `[0,1]`. -/
def standardBrownianRadius (W : NNReal → Omega → Plane) (omega : Omega) : ℝ :=
  compactRadius (standardBrownianPiece W omega)

theorem IsPlanarBrownian.aemeasurable_rescaledBrownianRadius
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r : NNReal} (hr : r ≠ 0) :
    AEMeasurable (rescaledBrownianRadius W a r) P :=
  measurable_compactRadius.comp_aemeasurable
    ((hW.intervalRescale a hr).aemeasurable_brownianImage unitIntervalCompact)

theorem IsPlanarBrownian.aemeasurable_standardBrownianRadius
    {P : Measure Omega} {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) :
    AEMeasurable (standardBrownianRadius W) P :=
  measurable_compactRadius.comp_aemeasurable
    (hW.aemeasurable_brownianImage unitIntervalCompact)

/-- Brownian scaling identifies the entire law of the normalized affine
interval radius with the unit-interval radius law. -/
theorem IsPlanarBrownian.map_rescaledBrownianRadius_eq
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r : NNReal} (hr : r ≠ 0) :
    P.map (rescaledBrownianRadius W a r) =
      P.map (standardBrownianRadius W) := by
  have hrescaled : AEMeasurable (rescaledBrownianPiece W a r) P :=
    (hW.intervalRescale a hr).aemeasurable_brownianImage unitIntervalCompact
  have hstandard : AEMeasurable (standardBrownianPiece W) P :=
    hW.aemeasurable_brownianImage unitIntervalCompact
  calc
    P.map (rescaledBrownianRadius W a r) =
        (P.map (rescaledBrownianPiece W a r)).map compactRadius := by
      rw [AEMeasurable.map_map_of_aemeasurable
        measurable_compactRadius.aemeasurable hrescaled]
      rfl
    _ = (P.map (standardBrownianPiece W)).map compactRadius := by
      rw [hW.map_rescaledBrownianPiece_eq a hr]
    _ = P.map (standardBrownianRadius W) := by
      rw [AEMeasurable.map_map_of_aemeasurable
        measurable_compactRadius.aemeasurable hstandard]
      rfl

/-- Any measurable real functional of the normalized radius has the same
integral on an affine interval and on the unit interval. -/
theorem IsPlanarBrownian.integral_rescaledBrownianRadius_eq
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r : NNReal} (hr : r ≠ 0)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ omega, g (rescaledBrownianRadius W a r omega) ∂P) =
      ∫ omega, g (standardBrownianRadius W omega) ∂P := by
  rw [← integral_map (hW.aemeasurable_rescaledBrownianRadius a hr)
      hg.aestronglyMeasurable,
    hW.map_rescaledBrownianRadius_eq a hr,
    integral_map (hW.aemeasurable_standardBrownianRadius)
      hg.aestronglyMeasurable]

/-- Integrability of a measurable unit-radius functional transfers to every
normalized affine interval. -/
theorem IsPlanarBrownian.integrable_rescaledBrownianRadius_of_standard
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r : NNReal} (hr : r ≠ 0)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hint : Integrable (fun omega => g (standardBrownianRadius W omega)) P) :
    Integrable (fun omega => g (rescaledBrownianRadius W a r omega)) P := by
  have hstdmap : Integrable g (P.map (standardBrownianRadius W)) := by
    rw [integrable_map_measure hg.aestronglyMeasurable
      (hW.aemeasurable_standardBrownianRadius)]
    exact hint
  have hresmap : Integrable g (P.map (rescaledBrownianRadius W a r)) := by
    rw [hW.map_rescaledBrownianRadius_eq a hr]
    exact hstdmap
  rw [integrable_map_measure hg.aestronglyMeasurable
    (hW.aemeasurable_rescaledBrownianRadius a hr)] at hresmap
  exact hresmap

/-! ### The exact local oscillation reduction -/

/-- The radius used for the Brownian image over `[a,a+length]`. -/
def brownianIntervalOscillationRadius
    (W : NNReal → Omega → Plane) (a length : NNReal) (omega : Omega) : ℝ :=
  Real.sqrt (length : ℝ) * rescaledBrownianRadius W a length omega

theorem brownianIntervalOscillationRadius_nonneg
    (W : NNReal → Omega → Plane) (a length : NNReal) (omega : Omega) :
    0 ≤ brownianIntervalOscillationRadius W a length omega :=
  mul_nonneg (Real.sqrt_nonneg _) (compactRadius_nonneg _)

/-- A compact time subset of `[0,1]`, placed in the affine host interval
`[a,a+length]`, has Brownian image inside the disc given by the normalized
full-interval radius. -/
theorem affineBrownianCompactPiece_subset_intervalOscillation_disc
    {W : NNReal → Omega → Plane} {a length : NNReal} (hlength : length ≠ 0)
    {K : NonemptyCompacts ℝ} (hK : (K : Set ℝ) ⊆ Set.Icc 0 1)
    {omega : Omega} (homega : Continuous (fun t => W t omega)) :
    (affineBrownianCompactPiece W a length K omega : Set Plane) ⊆
      Metric.closedBall (W a omega)
        (brownianIntervalOscillationRadius W a length omega) := by
  have hsubset :
      (rescaledBrownianCompactPiece W a length K omega : Set Plane) ⊆
        (rescaledBrownianPiece W a length omega : Set Plane) := by
    rw [rescaledBrownianCompactPiece, rescaledBrownianPiece,
      coe_brownianImage_of_continuous K,
      coe_brownianImage_of_continuous unitIntervalCompact]
    · exact Set.image_mono hK
    · change Continuous (fun t : NNReal =>
        (Real.sqrt (length : Real))⁻¹ • (W (a + length * t) omega - W a omega))
      fun_prop
    · change Continuous (fun t : NNReal =>
        (Real.sqrt (length : Real))⁻¹ • (W (a + length * t) omega - W a omega))
      fun_prop
  intro x hx
  have heq := translate_dilate_rescaledBrownianCompactPiece_of_continuous
    (W := W) (a := a) (r := length) hlength (K := K) hK
      (omega := omega) homega
  rw [← heq, coe_translateCompact, coe_dilateCompact] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, rfl⟩ := hy
  have hzrad := subset_closedBall_zero_compactRadius
    (rescaledBrownianPiece W a length omega) (hsubset hz)
  rw [Metric.mem_closedBall] at hzrad ⊢
  have hsqrt : 0 ≤ Real.sqrt (length : ℝ) := Real.sqrt_nonneg _
  calc
    dist (W a omega + Real.sqrt (length : ℝ) • z) (W a omega) =
        Real.sqrt (length : ℝ) * dist z 0 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hsqrt, dist_zero_right]
    _ ≤ Real.sqrt (length : ℝ) * compactRadius
        (rescaledBrownianPiece W a length omega) :=
      mul_le_mul_of_nonneg_left hzrad hsqrt
    _ = brownianIntervalOscillationRadius W a length omega := rfl

/-- The paper's local maximal-moment estimate reduced to one unit-interval
moment.  If `length ≤ rho²`, then for every real `p ≥ 1`,
`E (rho + oscillation)^p ≤ rho^p E (1 + unitRadius)^p`.

The unit moment in the hypothesis is exactly the continuous-time Brownian
maximal estimate missing from Mathlib; all scaling, integrability, and
expectation algebra is discharged here. -/
theorem IsPlanarBrownian.intervalOscillation_moment_le_of_standard
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {length : NNReal} (hlength : length ≠ 0)
    {rho p : ℝ} (hrho : 0 < rho) (hp : 1 ≤ p)
    (hlen : (length : ℝ) ≤ rho ^ 2)
    (hunit : Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ p) P) :
    Integrable (fun omega =>
      (rho + brownianIntervalOscillationRadius W a length omega) ^ p) P ∧
      (∫ omega,
          (rho + brownianIntervalOscillationRadius W a length omega) ^ p ∂P) ≤
        rho ^ p *
          ∫ omega, (1 + standardBrownianRadius W omega) ^ p ∂P := by
  let g : ℝ → ℝ := fun x => (1 + x) ^ p
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hg : Measurable g :=
    ((Real.continuous_rpow_const hp0).comp (continuous_const.add continuous_id)).measurable
  have hresint : Integrable
      (fun omega => g (rescaledBrownianRadius W a length omega)) P :=
    hW.integrable_rescaledBrownianRadius_of_standard a hlength g hg hunit
  have hscaledint : Integrable (fun omega =>
      rho ^ p * g (rescaledBrownianRadius W a length omega)) P :=
    hresint.const_mul _
  have hsqrt_le : Real.sqrt (length : ℝ) ≤ rho := by
    rw [Real.sqrt_le_iff]
    exact ⟨hrho.le, by simpa [sq] using hlen⟩
  have htarget_meas : AEStronglyMeasurable (fun omega =>
      (rho + brownianIntervalOscillationRadius W a length omega) ^ p) P := by
    have hradiusMeas := hW.aemeasurable_rescaledBrownianRadius a hlength
    have hoscMeas : AEMeasurable
        (brownianIntervalOscillationRadius W a length) P :=
      aemeasurable_const.mul hradiusMeas
    exact (Real.continuous_rpow_const hp0).measurable.comp_aemeasurable
      (aemeasurable_const.add hoscMeas) |>.aestronglyMeasurable
  have hpoint : ∀ omega,
      (rho + brownianIntervalOscillationRadius W a length omega) ^ p ≤
        rho ^ p * g (rescaledBrownianRadius W a length omega) := by
    intro omega
    have hR := compactRadius_nonneg (rescaledBrownianPiece W a length omega)
    have hbase :
        rho + brownianIntervalOscillationRadius W a length omega ≤
          rho * (1 + rescaledBrownianRadius W a length omega) := by
      dsimp [brownianIntervalOscillationRadius, rescaledBrownianRadius]
      nlinarith [mul_le_mul_of_nonneg_right hsqrt_le hR]
    calc
      (rho + brownianIntervalOscillationRadius W a length omega) ^ p ≤
          (rho * (1 + rescaledBrownianRadius W a length omega)) ^ p :=
        Real.rpow_le_rpow
          (add_nonneg hrho.le (brownianIntervalOscillationRadius_nonneg W a length omega))
          hbase hp0
      _ = rho ^ p * g (rescaledBrownianRadius W a length omega) := by
        rw [Real.mul_rpow hrho.le (by
          exact add_nonneg zero_le_one
            (compactRadius_nonneg (rescaledBrownianPiece W a length omega)))]
  have htarget_nonneg : ∀ omega,
      0 ≤ (rho + brownianIntervalOscillationRadius W a length omega) ^ p :=
    fun omega => Real.rpow_nonneg
      (add_nonneg hrho.le (brownianIntervalOscillationRadius_nonneg W a length omega)) p
  have htargetint : Integrable (fun omega =>
      (rho + brownianIntervalOscillationRadius W a length omega) ^ p) P :=
    hscaledint.mono_nonneg htarget_meas
      (Filter.Eventually.of_forall htarget_nonneg)
      (Filter.Eventually.of_forall hpoint)
  refine ⟨htargetint, ?_⟩
  calc
    (∫ omega,
        (rho + brownianIntervalOscillationRadius W a length omega) ^ p ∂P) ≤
        ∫ omega, rho ^ p * g (rescaledBrownianRadius W a length omega) ∂P :=
      integral_mono htargetint hscaledint hpoint
    _ = rho ^ p *
        ∫ omega, g (rescaledBrownianRadius W a length omega) ∂P := by
      rw [integral_const_mul]
    _ = rho ^ p *
        ∫ omega, g (standardBrownianRadius W omega) ∂P := by
      rw [hW.integral_rescaledBrownianRadius_eq a hlength g hg]
    _ = rho ^ p *
        ∫ omega, (1 + standardBrownianRadius W omega) ^ p ∂P := rfl

end

end BrownianImages
