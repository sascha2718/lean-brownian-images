/-
The deterministic translation identity behind the tube-overlap estimate.

For two compact planar sets, the overlap of the first tube with a translate of
the second is the convolution of the first tube indicator with the reflected
second tube indicator.  Tonelli/Fubini therefore turns its integral over the
translation parameter into the product of the two tube areas.  The final
bounded-density estimate is the form used after conditioning on all random
variables except the relative translation.
-/
import BrownianImages.MinkowskiProfile
import Mathlib.Analysis.Convolution

namespace BrownianImages

open MeasureTheory Set TopologicalSpace
open scoped Convolution ENNReal NNReal Topology

/-- The real-valued indicator of the open `r`-tube around `F`. -/
noncomputable def tubeIndicator (r : ℝ) (F : CompactPlane) : Plane → ℝ :=
  (Metric.thickening r (F : Set Plane)).indicator fun _ => 1

/-- The reflected tube indicator.  Reflection makes translated overlap a
standard additive convolution. -/
noncomputable def reflectedTubeIndicator (r : ℝ) (F : CompactPlane) : Plane → ℝ :=
  fun x => tubeIndicator r F (-x)

theorem measurable_tubeIndicator (r : ℝ) (F : CompactPlane) :
    Measurable (tubeIndicator r F) := by
  exact measurable_const.indicator Metric.isOpen_thickening.measurableSet

theorem integrable_tubeIndicator (r : ℝ) (F : CompactPlane) :
    Integrable (tubeIndicator r F) := by
  simpa only [tubeIndicator, inter_self] using
    (integrable_tubeOverlapIndicator (r := r) F F)

theorem integral_tubeIndicator (r : ℝ) (F : CompactPlane) :
    ∫ x : Plane, tubeIndicator r F x = tubeArea r F := by
  let A := Metric.thickening r (F : Set Plane)
  have hindicator : A.indicator (fun _ : Plane => (1 : ℝ)) = A.indicator 1 := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [tubeIndicator, show Metric.thickening r (F : Set Plane) = A from rfl,
    hindicator, integral_indicator_one Metric.isOpen_thickening.measurableSet]
  rfl

/-- Raw tube area is monotone under inclusion of the underlying compact sets. -/
theorem tubeArea_mono {r : ℝ} {F G : CompactPlane}
    (hFG : (F : Set Plane) ⊆ (G : Set Plane)) :
    tubeArea r F ≤ tubeArea r G := by
  rw [← integral_tubeIndicator, ← integral_tubeIndicator]
  apply integral_mono (integrable_tubeIndicator r F)
    (integrable_tubeIndicator r G)
  intro x
  unfold tubeIndicator
  by_cases hx : x ∈ Metric.thickening r (F : Set Plane)
  · have hxG : x ∈ Metric.thickening r (G : Set Plane) :=
      Metric.thickening_subset_of_subset r hFG hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxG]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxG : x ∈ Metric.thickening r (G : Set Plane)
    · rw [Set.indicator_of_mem hxG]
      norm_num
    · rw [Set.indicator_of_notMem hxG]

theorem measurable_reflectedTubeIndicator (r : ℝ) (F : CompactPlane) :
    Measurable (reflectedTubeIndicator r F) :=
  (measurable_tubeIndicator r F).comp measurable_neg

theorem integrable_reflectedTubeIndicator (r : ℝ) (F : CompactPlane) :
    Integrable (reflectedTubeIndicator r F) :=
  (integrable_tubeIndicator r F).comp_neg

theorem integral_reflectedTubeIndicator (r : ℝ) (F : CompactPlane) :
    ∫ x : Plane, reflectedTubeIndicator r F x = tubeArea r F := by
  change (∫ x : Plane, tubeIndicator r F (-x)) = tubeArea r F
  rw [integral_neg_eq_self, integral_tubeIndicator]

/-- Membership in a translated tube, expressed in the original coordinates. -/
theorem mem_thickening_translateCompact_iff {r : ℝ} (hr : 0 < r)
    (a : Plane) (F : CompactPlane) (x : Plane) :
    x ∈ Metric.thickening r (translateCompact a F : Set Plane) ↔
      x - a ∈ Metric.thickening r (F : Set Plane) := by
  rw [Metric.mem_thickening_iff_infDist_lt (translateCompact a F).nonempty,
    Metric.mem_thickening_iff_infDist_lt F.nonempty,
    ← tubeCutoff_pos_iff hr, ← tubeCutoff_pos_iff hr]
  have hax : a + (x - a) = x := by abel
  have hcut := congrArg (fun z : ℝ => 0 < z)
    (tubeCutoff_translate r a F (x - a))
  rw [hax] at hcut
  constructor
  · exact fun h => Eq.mp hcut h
  · exact fun h => Eq.mpr hcut h

/-- Translating both compact sets by the same vector does not change their
tube-overlap area. -/
theorem tubeOverlapArea_translate_both {r : ℝ} (hr : 0 < r)
    (a : Plane) (F G : CompactPlane) :
    tubeOverlapArea r (translateCompact a F) (translateCompact a G) =
      tubeOverlapArea r F G := by
  unfold tubeOverlapArea
  rw [← integral_add_left_eq_self
    ((Metric.thickening r (translateCompact a F : Set Plane) ∩
      Metric.thickening r (translateCompact a G : Set Plane)).indicator
        fun _ => (1 : ℝ)) a]
  apply integral_congr_ae
  filter_upwards with x
  have hF :
      a + x ∈ Metric.thickening r (translateCompact a F : Set Plane) ↔
        x ∈ Metric.thickening r (F : Set Plane) := by
    simpa using mem_thickening_translateCompact_iff hr a F (a + x)
  have hG :
      a + x ∈ Metric.thickening r (translateCompact a G : Set Plane) ↔
        x ∈ Metric.thickening r (G : Set Plane) := by
    simpa using mem_thickening_translateCompact_iff hr a G (a + x)
  by_cases hxF : x ∈ Metric.thickening r (F : Set Plane)
  · by_cases hxG : x ∈ Metric.thickening r (G : Set Plane)
    · have hleft : a + x ∈
          Metric.thickening r (translateCompact a F : Set Plane) ∩
            Metric.thickening r (translateCompact a G : Set Plane) :=
        ⟨hF.2 hxF, hG.2 hxG⟩
      have hright : x ∈ Metric.thickening r (F : Set Plane) ∩
          Metric.thickening r (G : Set Plane) := ⟨hxF, hxG⟩
      rw [Set.indicator_of_mem hleft, Set.indicator_of_mem hright]
    · have hleft : a + x ∉
          Metric.thickening r (translateCompact a F : Set Plane) ∩
            Metric.thickening r (translateCompact a G : Set Plane) :=
        fun h => hxG (hG.1 h.2)
      have hright : x ∉ Metric.thickening r (F : Set Plane) ∩
          Metric.thickening r (G : Set Plane) := fun h => hxG h.2
      rw [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hright]
  · have hleft : a + x ∉
        Metric.thickening r (translateCompact a F : Set Plane) ∩
          Metric.thickening r (translateCompact a G : Set Plane) :=
      fun h => hxF (hF.1 h.1)
    have hright : x ∉ Metric.thickening r (F : Set Plane) ∩
        Metric.thickening r (G : Set Plane) := fun h => hxF h.1
    rw [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hright]

/-- Self-overlap is the raw tube area. -/
theorem tubeOverlapArea_self (r : ℝ) (F : CompactPlane) :
    tubeOverlapArea r F F = tubeArea r F := by
  rw [tubeOverlapArea, Set.inter_self, ← integral_tubeIndicator]
  rfl

/-- Raw tube area is translation-invariant. -/
theorem tubeArea_translate {r : ℝ} (hr : 0 < r)
    (a : Plane) (F : CompactPlane) :
    tubeArea r (translateCompact a F) = tubeArea r F := by
  rw [← tubeOverlapArea_self, tubeOverlapArea_translate_both hr,
    tubeOverlapArea_self]

/-- The raw tube indicator respects positive scalar dilation. -/
theorem tubeIndicator_dilate {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (F : CompactPlane) (x : Plane) :
    tubeIndicator r (dilateCompact q F) (q • x) =
      tubeIndicator (r / q) F x := by
  have hmem :
      q • x ∈ Metric.thickening r (dilateCompact q F : Set Plane) ↔
        x ∈ Metric.thickening (r / q) (F : Set Plane) := by
    rw [Metric.mem_thickening_iff_infDist_lt (dilateCompact q F).nonempty,
      Metric.mem_thickening_iff_infDist_lt F.nonempty,
      ← tubeCutoff_pos_iff hr,
      ← tubeCutoff_pos_iff (div_pos hr hq), tubeCutoff_dilate hr hq]
  unfold tubeIndicator
  by_cases hx : x ∈ Metric.thickening (r / q) (F : Set Plane)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx (hmem.1 h))]

/-- Raw tube area scales quadratically under positive planar dilation. -/
theorem tubeArea_dilate {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (F : CompactPlane) :
    tubeArea r (dilateCompact q F) = q ^ 2 * tubeArea (r / q) F := by
  have hpoint : ∀ y : Plane,
      tubeIndicator r (dilateCompact q F) y =
        tubeIndicator (r / q) F (q⁻¹ • y) := by
    intro y
    rw [← tubeIndicator_dilate hr hq F (q⁻¹ • y),
      smul_inv_smul₀ hq.ne' y]
  rw [← integral_tubeIndicator, ← integral_tubeIndicator]
  conv_lhs =>
    enter [2, y]
    rw [hpoint y]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (tubeIndicator (r / q) F) hq.le]
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  simp only [hdim, smul_eq_mul]

/-- Affine covariance of raw tube area. -/
theorem tubeArea_translate_dilate {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (a : Plane) (F : CompactPlane) :
    tubeArea r (translateCompact a (dilateCompact q F)) =
      q ^ 2 * tubeArea (r / q) F := by
  rw [tubeArea_translate hr, tubeArea_dilate hr hq]

/-- Translated tube overlap is a convolution of tube indicators. -/
theorem tubeOverlapArea_translate_eq_convolution {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) (a : Plane) :
    tubeOverlapArea r F (translateCompact a G) =
      (tubeIndicator r F ⋆[ContinuousLinearMap.mul ℝ ℝ]
        reflectedTubeIndicator r G) a := by
  rw [tubeOverlapArea, convolution_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxF : x ∈ Metric.thickening r (F : Set Plane)
  · by_cases hxG : x - a ∈ Metric.thickening r (G : Set Plane)
    · have hxGa : x ∈ Metric.thickening r (translateCompact a G : Set Plane) :=
        (mem_thickening_translateCompact_iff hr a G x).2 hxG
      have hxInter : x ∈ Metric.thickening r (F : Set Plane) ∩
          Metric.thickening r (translateCompact a G : Set Plane) := ⟨hxF, hxGa⟩
      change
        (Metric.thickening r (F : Set Plane) ∩
          Metric.thickening r (translateCompact a G : Set Plane)).indicator
            (fun _ => (1 : ℝ)) x =
          (Metric.thickening r (F : Set Plane)).indicator (fun _ => (1 : ℝ)) x *
            (Metric.thickening r (G : Set Plane)).indicator (fun _ => (1 : ℝ)) (-(a - x))
      rw [neg_sub]
      rw [Set.indicator_of_mem hxInter, Set.indicator_of_mem hxF,
        Set.indicator_of_mem hxG, mul_one]
    · have hxGa : x ∉ Metric.thickening r (translateCompact a G : Set Plane) :=
        fun h => hxG ((mem_thickening_translateCompact_iff hr a G x).1 h)
      have hxInter : x ∉ Metric.thickening r (F : Set Plane) ∩
          Metric.thickening r (translateCompact a G : Set Plane) :=
        fun h => hxGa h.2
      change
        (Metric.thickening r (F : Set Plane) ∩
          Metric.thickening r (translateCompact a G : Set Plane)).indicator
            (fun _ => (1 : ℝ)) x =
          (Metric.thickening r (F : Set Plane)).indicator (fun _ => (1 : ℝ)) x *
            (Metric.thickening r (G : Set Plane)).indicator (fun _ => (1 : ℝ)) (-(a - x))
      rw [neg_sub]
      rw [Set.indicator_of_notMem hxInter, Set.indicator_of_mem hxF,
        Set.indicator_of_notMem hxG, mul_zero]
  · have hxInter : x ∉ Metric.thickening r (F : Set Plane) ∩
        Metric.thickening r (translateCompact a G : Set Plane) :=
      fun h => hxF h.1
    change
      (Metric.thickening r (F : Set Plane) ∩
        Metric.thickening r (translateCompact a G : Set Plane)).indicator
          (fun _ => (1 : ℝ)) x =
        (Metric.thickening r (F : Set Plane)).indicator (fun _ => (1 : ℝ)) x *
          (Metric.thickening r (G : Set Plane)).indicator (fun _ => (1 : ℝ)) (-(a - x))
    rw [Set.indicator_of_notMem hxInter, Set.indicator_of_notMem hxF, zero_mul]

/-- The translated-overlap function is Borel measurable. -/
theorem measurable_tubeOverlapArea_translate {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) :
    Measurable fun a : Plane => tubeOverlapArea r F (translateCompact a G) := by
  let f := tubeIndicator r F
  let g := reflectedTubeIndicator r G
  have hf : Measurable f := measurable_tubeIndicator r F
  have hg : Measurable g := measurable_reflectedTubeIndicator r G
  have hjoint : StronglyMeasurable
      (fun p : Plane × Plane => f p.2 * g (p.1 - p.2)) :=
    ((hf.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  have hconv : Measurable fun a : Plane =>
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) a := by
    simpa only [convolution_mul] using hjoint.integral_prod_right.measurable
  have heq : (fun a : Plane => tubeOverlapArea r F (translateCompact a G)) =
      fun a : Plane => (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) a := by
    funext a
    exact tubeOverlapArea_translate_eq_convolution hr F G a
  rw [heq]
  exact hconv

/-- The translated-overlap function is integrable over the translation plane. -/
theorem integrable_tubeOverlapArea_translate {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) :
    Integrable fun a : Plane => tubeOverlapArea r F (translateCompact a G) := by
  have hconv := (integrable_tubeIndicator r F).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_reflectedTubeIndicator r G)
  apply hconv.congr
  filter_upwards with a
  exact (tubeOverlapArea_translate_eq_convolution hr F G a).symm

/-- Integrating tube overlap over every translation gives exactly the product
of the two tube areas. -/
theorem integral_tubeOverlapArea_translate {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) :
    (∫ a : Plane, tubeOverlapArea r F (translateCompact a G)) =
      tubeArea r F * tubeArea r G := by
  calc
    (∫ a : Plane, tubeOverlapArea r F (translateCompact a G)) =
        ∫ a : Plane, (tubeIndicator r F ⋆[ContinuousLinearMap.mul ℝ ℝ]
          reflectedTubeIndicator r G) a := by
            apply integral_congr_ae
            filter_upwards with a
            exact tubeOverlapArea_translate_eq_convolution hr F G a
    _ = (∫ x : Plane, tubeIndicator r F x) *
        ∫ x : Plane, reflectedTubeIndicator r G x := by
          simpa using integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
            (integrable_tubeIndicator r F) (integrable_reflectedTubeIndicator r G)
    _ = tubeArea r F * tubeArea r G := by
      rw [integral_tubeIndicator, integral_reflectedTubeIndicator]

theorem tubeOverlapArea_nonneg (r : ℝ) (F G : CompactPlane) :
    0 ≤ tubeOverlapArea r F G := by
  rw [tubeOverlapArea_eq_measureReal]
  exact ENNReal.toReal_nonneg

/-- A bounded nonnegative density can increase the translation-averaged
overlap by at most its pointwise upper bound. -/
theorem integrable_density_mul_tubeOverlapArea_translate {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) {density : Plane → ℝ} {C : ℝ}
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C) :
    Integrable fun a : Plane =>
      density a * tubeOverlapArea r F (translateCompact a G) := by
  apply (integrable_tubeOverlapArea_translate hr F G).bdd_mul
    hdensity.aestronglyMeasurable
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (hdensity_nonneg a)]
  exact hdensity_le a

/-- Deterministic bounded-density inequality, ready to apply to a conditional
density for the relative translation of two random pieces. -/
theorem integral_density_mul_tubeOverlapArea_translate_le {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) {density : Plane → ℝ} {C : ℝ}
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C) :
    (∫ a : Plane, density a * tubeOverlapArea r F (translateCompact a G)) ≤
      C * (tubeArea r F * tubeArea r G) := by
  have hoverlap := integrable_tubeOverlapArea_translate hr F G
  have hweighted := integrable_density_mul_tubeOverlapArea_translate hr F G
    hdensity hdensity_nonneg hdensity_le
  calc
    (∫ a : Plane, density a * tubeOverlapArea r F (translateCompact a G)) ≤
        ∫ a : Plane, C * tubeOverlapArea r F (translateCompact a G) := by
          apply integral_mono hweighted (hoverlap.const_mul C)
          intro a
          exact mul_le_mul_of_nonneg_right (hdensity_le a)
            (tubeOverlapArea_nonneg r F (translateCompact a G))
    _ = C * (tubeArea r F * tubeArea r G) := by
      rw [integral_const_mul, integral_tubeOverlapArea_translate hr]

end BrownianImages
