/-
`sec:reconstruction`: deterministic algebra for smoothed planar neighbourhoods.

This file proves the finite-union, translation, and positive-dilation identities used in
`eq:neighbourhood-union-scaling`.  It also defines the multiple-counting defect for a finite nonempty
family of compact sets and proves the smoothed- and raw-overlap forms of
`eq:neighbourhood-defect-elementary`.  An unordered-pair sum is represented as half of the symmetric
ordered distinct-pair sum, avoiding an arbitrary order on the index type.
-/
import BrownianImages.Minkowski.Tube
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace BrownianImages

open MeasureTheory Set TopologicalSpace
open scoped BigOperators BoundedContinuousFunction ENNReal NNReal Pointwise Topology

/-! ### Finite unions -/

/-- The union of a finite nonempty family of nonempty compact subsets of the plane. -/
noncomputable def compactUnion {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ι → CompactPlane) : CompactPlane :=
  Finset.univ.sup' Finset.univ_nonempty F

/-- Finite union is continuous for the product Hausdorff topology on a finite
family of nonempty compact sets. -/
theorem continuous_compactUnion {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (compactUnion : (ι → CompactPlane) → CompactPlane) := by
  unfold compactUnion
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  fun_prop

/-- The distance to the union of two compact sets is the minimum of the two distances. -/
theorem infDist_sup (F G : CompactPlane) (x : Plane) :
    Metric.infDist x (F ⊔ G) = min (Metric.infDist x F) (Metric.infDist x G) := by
  change Metric.infDist x ((F : Set Plane) ∪ (G : Set Plane)) = _
  rw [Metric.infDist, Metric.infEDist_union,
    ENNReal.toReal_min (Metric.infEDist_ne_top F.nonempty)
      (Metric.infEDist_ne_top G.nonempty)]
  rfl

/-- The cut-off of a binary union is the pointwise maximum of the two cut-offs. -/
theorem tubeCutoff_sup {r : ℝ} (hr : 0 < r) (F G : CompactPlane) (x : Plane) :
    tubeCutoff r (F ⊔ G) x = max (tubeCutoff r F x) (tubeCutoff r G x) := by
  change max (1 - Metric.infDist x ((F : Set Plane) ∪ (G : Set Plane)) / r) 0 =
    max (max (1 - Metric.infDist x F / r) 0) (max (1 - Metric.infDist x G / r) 0)
  rw [show Metric.infDist x ((F : Set Plane) ∪ (G : Set Plane)) =
    min (Metric.infDist x F) (Metric.infDist x G) from infDist_sup F G x]
  by_cases h : Metric.infDist x F ≤ Metric.infDist x G
  · rw [min_eq_left h]
    have hcut : max (1 - Metric.infDist x G / r) 0 ≤
        max (1 - Metric.infDist x F / r) 0 :=
      max_le_max (sub_le_sub_left (div_le_div_of_nonneg_right h hr.le) 1) le_rfl
    exact (max_eq_left hcut).symm
  · have h' : Metric.infDist x G ≤ Metric.infDist x F := le_of_not_ge h
    rw [min_eq_right h']
    have hcut : max (1 - Metric.infDist x F / r) 0 ≤
        max (1 - Metric.infDist x G / r) 0 :=
      max_le_max (sub_le_sub_left (div_le_div_of_nonneg_right h' hr.le) 1) le_rfl
    exact (max_eq_right hcut).symm

/-- The cut-off of a finite nonempty union is the pointwise maximum of the cut-offs. -/
theorem tubeCutoff_compactUnion {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℝ}
    (hr : 0 < r) (F : ι → CompactPlane) (x : Plane) :
    tubeCutoff r (compactUnion F) x =
      Finset.univ.sup' Finset.univ_nonempty fun i => tubeCutoff r (F i) x := by
  unfold compactUnion
  simpa only [Function.comp_apply] using
    (Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty
      (fun K : CompactPlane => tubeCutoff r K x) (fun A B => tubeCutoff_sup hr A B x))

/-! ### Translation and dilation -/

/-- Translation of a nonempty compact set in the plane. -/
noncomputable def translateCompact (a : Plane) (F : CompactPlane) : CompactPlane :=
  F.map (fun x => a + x) (continuous_const.add continuous_id)

/-- The underlying set of a translated compact set is its translate. -/
@[simp]
theorem coe_translateCompact (a : Plane) (F : CompactPlane) :
    (translateCompact a F : Set Plane) = (fun x => a + x) '' F :=
  rfl

/-- Translation preserves the tube cut-off after translating the evaluation point. -/
theorem tubeCutoff_translate (r : ℝ) (a : Plane) (F : CompactPlane) (x : Plane) :
    tubeCutoff r (translateCompact a F) (a + x) = tubeCutoff r F x := by
  have hdist : Metric.infDist (a + x) ((fun y => a + y) '' (F : Set Plane)) =
      Metric.infDist x F := by
    simpa using
      (Metric.infDist_image (x := x) (t := (F : Set Plane))
        (IsometryEquiv.addLeft a).isometry)
  rw [tubeCutoff, tubeCutoff, coe_translateCompact, hdist]

/-- Smoothed tube mass is translation-invariant. -/
theorem tubeMass_translate (r : ℝ) (a : Plane) (F : CompactPlane) :
    tubeMass r (translateCompact a F) = tubeMass r F := by
  rw [tubeMass, tubeMass,
    ← integral_add_left_eq_self (tubeCutoff r (translateCompact a F)) a]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => tubeCutoff_translate r a F x)

/-- Positive scalar dilation of a nonempty compact set in the plane. -/
noncomputable def dilateCompact (q : ℝ) (F : CompactPlane) : CompactPlane :=
  F.map (fun x => q • x) (continuous_const_smul q)

/-- The underlying set of a dilated compact set is its dilate. -/
@[simp]
theorem coe_dilateCompact (q : ℝ) (F : CompactPlane) :
    (dilateCompact q F : Set Plane) = q • (F : Set Plane) := by
  rw [dilateCompact, NonemptyCompacts.coe_map, Set.image_smul]

/-- The distance cut-off respects positive scalar dilation. -/
theorem tubeCutoff_dilate {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (F : CompactPlane)
    (x : Plane) :
    tubeCutoff r (dilateCompact q F) (q • x) = tubeCutoff (r / q) F x := by
  rw [tubeCutoff, tubeCutoff, coe_dilateCompact,
    infDist_smul₀ hq.ne' (F : Set Plane) x, Real.norm_eq_abs, abs_of_pos hq]
  congr 2
  field_simp

/-- Smoothed tube mass scales quadratically under positive planar dilation. -/
theorem tubeMass_dilate {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (F : CompactPlane) :
    tubeMass r (dilateCompact q F) = q ^ 2 * tubeMass (r / q) F := by
  have hpoint : ∀ y : Plane,
      tubeCutoff r (dilateCompact q F) y = tubeCutoff (r / q) F (q⁻¹ • y) := by
    intro y
    rw [← tubeCutoff_dilate hr hq F (q⁻¹ • y), smul_inv_smul₀ hq.ne' y]
  rw [tubeMass, tubeMass]
  conv_lhs =>
    enter [2, y]
    rw [hpoint y]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (tubeCutoff (r / q) F) hq.le]
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  simp only [hdim, smul_eq_mul]

/-- The affine form of the tube scaling identity from `eq:neighbourhood-union-scaling`. -/
theorem tubeMass_translate_dilate {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (a : Plane) (F : CompactPlane) :
    tubeMass r (translateCompact a (dilateCompact q F)) =
      q ^ 2 * tubeMass (r / q) F := by
  rw [tubeMass_translate, tubeMass_dilate hr hq]

/-! ### The multiple-counting defect -/

/-- The sum of pairwise minima over ordered distinct pairs from a finite index set. -/
noncomputable def orderedPairMinSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s.erase i, min (f i) (f j)

/-- For a nonnegative finite family, the sum minus its maximum is nonnegative. -/
theorem sum_sub_sup'_nonneg {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ (∑ i ∈ s, f i) - s.sup' hs f := by
  obtain ⟨j, hj, hmax⟩ := s.exists_mem_eq_sup' hs f
  rw [hmax]
  exact sub_nonneg.mpr (Finset.single_le_sum hf hj)

/-- Counting both orientations of every distinct pair shows that the ordered-pair sum is at
least twice the excess over the maximum. -/
theorem two_mul_sum_sub_sup'_le_orderedPairMinSum {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    2 * ((∑ i ∈ s, f i) - s.sup' hs f) ≤ orderedPairMinSum s f := by
  obtain ⟨j, hj, hmax⟩ := s.exists_mem_eq_sup' hs f
  have hle : ∀ i ∈ s, f i ≤ f j := by
    intro i hi
    rw [← hmax]
    exact Finset.le_sup' f hi
  have hdefect : (∑ i ∈ s, f i) - s.sup' hs f = ∑ i ∈ s.erase j, f i := by
    rw [hmax, ← Finset.sum_erase_add _ _ hj]
    ring
  have hfirst : (∑ i ∈ s.erase j, f i) ≤
      ∑ i ∈ s.erase j, ∑ k ∈ s.erase i, min (f i) (f k) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
    calc
      f i = min (f i) (f j) := (min_eq_left (hle i his)).symm
      _ ≤ ∑ k ∈ s.erase i, min (f i) (f k) := by
        apply Finset.single_le_sum (s := s.erase i) (f := fun k => min (f i) (f k))
        · intro k hk
          exact le_min (hf i his) (hf k (Finset.mem_of_mem_erase hk))
        · exact Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hjterm : (∑ k ∈ s.erase j, min (f j) (f k)) = ∑ k ∈ s.erase j, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact min_eq_right (hle k (Finset.mem_of_mem_erase hk))
  rw [hdefect]
  unfold orderedPairMinSum
  calc
    2 * (∑ i ∈ s.erase j, f i) =
        (∑ i ∈ s.erase j, f i) + ∑ i ∈ s.erase j, f i := by ring
    _ = (∑ i ∈ s.erase j, f i) + ∑ k ∈ s.erase j, min (f j) (f k) := by
      rw [hjterm]
    _ ≤ (∑ i ∈ s.erase j, ∑ k ∈ s.erase i, min (f i) (f k)) +
        ∑ k ∈ s.erase j, min (f j) (f k) := add_le_add hfirst le_rfl
    _ = ∑ i ∈ s, ∑ k ∈ s.erase i, min (f i) (f k) := by
      rw [Finset.sum_erase_add _ _ hj]

/-- The sum of minima over unordered pairs, represented without choosing an order on the index
type as half of the ordered distinct-pair sum. -/
noncomputable def pairMinSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) : ℝ :=
  orderedPairMinSum s f / 2

/-- The excess of a nonnegative finite sum over its maximum is bounded by the sum of minima over
unordered pairs. -/
theorem sum_sub_sup'_le_pairMinSum {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) - s.sup' hs f ≤ pairMinSum s f := by
  unfold pairMinSum
  have h := two_mul_sum_sub_sup'_le_orderedPairMinSum hs f hf
  linarith

/-- The pointwise excess obtained by summing the cut-offs of the members of a finite family
instead of taking the cut-off of their union. -/
noncomputable def tubeDefectIntegrand {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℝ) (F : ι → CompactPlane) (x : Plane) : ℝ :=
  (∑ i, tubeCutoff r (F i) x) - tubeCutoff r (compactUnion F) x

/-- The ordered-pair overlap integrand associated to a finite family of tube cut-offs. -/
noncomputable def orderedTubeOverlapIntegrand {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℝ) (F : ι → CompactPlane) (x : Plane) : ℝ := by
  classical
  exact orderedPairMinSum Finset.univ fun i => tubeCutoff r (F i) x

/-- The pointwise multiple-counting defect is nonnegative. -/
theorem tubeDefectIntegrand_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) (x : Plane) :
    0 ≤ tubeDefectIntegrand r F x := by
  classical
  rw [tubeDefectIntegrand, tubeCutoff_compactUnion hr]
  exact sum_sub_sup'_nonneg Finset.univ_nonempty _ fun i _ =>
    tubeCutoff_nonneg r (F i) x

/-- The sum of pointwise cut-off overlaps over unordered pairs, represented as half of the
symmetric ordered-pair sum. -/
noncomputable def pairwiseTubeOverlapIntegrand {ι : Type*}
    [Fintype ι] [Nonempty ι] (r : ℝ) (F : ι → CompactPlane) (x : Plane) : ℝ :=
  orderedTubeOverlapIntegrand r F x / 2

/-- The factor-one pointwise pairwise-overlap estimate. -/
theorem tubeDefectIntegrand_le_pairwiseTubeOverlapIntegrand {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane)
    (x : Plane) :
    tubeDefectIntegrand r F x ≤ pairwiseTubeOverlapIntegrand r F x := by
  classical
  rw [tubeDefectIntegrand, pairwiseTubeOverlapIntegrand,
    orderedTubeOverlapIntegrand, tubeCutoff_compactUnion hr]
  exact sum_sub_sup'_le_pairMinSum Finset.univ_nonempty _ fun i _ =>
    tubeCutoff_nonneg r (F i) x

/-- The smoothed overlap of the radius-`r` cut-offs of two compact sets. -/
noncomputable def smoothedTubeOverlap (r : ℝ) (F G : CompactPlane) : ℝ :=
  ∫ x : Plane, min (tubeCutoff r F x) (tubeCutoff r G x)

/-- The overlap of two positive-radius cut-offs is integrable. -/
theorem integrable_smoothedTubeOverlap {r : ℝ} (hr : 0 < r) (F G : CompactPlane) :
    Integrable (fun x : Plane => min (tubeCutoff r F x) (tubeCutoff r G x)) := by
  apply (integrable_tubeCutoff hr F).mono
    ((continuous_tubeCutoff_right r F).min
      (continuous_tubeCutoff_right r G)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (le_min (tubeCutoff_nonneg r F x) (tubeCutoff_nonneg r G x)),
      Real.norm_eq_abs, abs_of_nonneg (tubeCutoff_nonneg r F x)]
    exact min_le_left _ _

/-- The Lebesgue area of the intersection of the two open radius-`r` thickenings.  Writing the
area as a real integral avoids an unnecessary extended-real coercion in subsequent estimates. -/
noncomputable def tubeOverlapArea (r : ℝ) (F G : CompactPlane) : ℝ :=
  ∫ x : Plane, (Metric.thickening r (F : Set Plane) ∩
    Metric.thickening r (G : Set Plane)).indicator (fun _ => (1 : ℝ)) x

/-- The indicator of an intersection of two thickenings is integrable. -/
theorem integrable_tubeOverlapIndicator {r : ℝ} (F G : CompactPlane) :
    Integrable ((Metric.thickening r (F : Set Plane) ∩
      Metric.thickening r (G : Set Plane)).indicator fun _ => (1 : ℝ)) := by
  let A := Metric.thickening r (F : Set Plane) ∩ Metric.thickening r (G : Set Plane)
  let K := Metric.cthickening r (F : Set Plane)
  have hK : IsCompact K := F.isCompact.cthickening
  have hAK : A ⊆ K := fun x hx =>
    Metric.thickening_subset_cthickening r (F : Set Plane) hx.1
  have hA : IntegrableOn (fun _ : Plane => (1 : ℝ)) A :=
    (continuousOn_const.integrableOn_compact hK).mono_set hAK
  have hAmeas : MeasurableSet A :=
    (Metric.isOpen_thickening.inter Metric.isOpen_thickening).measurableSet
  simpa only [A] using hA.integrable_indicator hAmeas

/-- `tubeOverlapArea` is precisely planar Lebesgue measure, converted to a real number. -/
theorem tubeOverlapArea_eq_measureReal (r : ℝ) (F G : CompactPlane) :
    tubeOverlapArea r F G = volume.real
      (Metric.thickening r (F : Set Plane) ∩ Metric.thickening r (G : Set Plane)) := by
  unfold tubeOverlapArea
  let A := Metric.thickening r (F : Set Plane) ∩ Metric.thickening r (G : Set Plane)
  have hindicator : A.indicator (fun _ : Plane => (1 : ℝ)) = A.indicator 1 := by
    funext x
    by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [show (fun x : Plane => A.indicator (fun _ => (1 : ℝ)) x) =
    A.indicator 1 from hindicator]
  exact integral_indicator_one
    (Metric.isOpen_thickening.inter Metric.isOpen_thickening).measurableSet

/-- A smoothed overlap is bounded by the area of the intersection of the corresponding open
thickenings. -/
theorem smoothedTubeOverlap_le_tubeOverlapArea {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) :
    smoothedTubeOverlap r F G ≤ tubeOverlapArea r F G := by
  unfold smoothedTubeOverlap tubeOverlapArea
  apply integral_mono (integrable_smoothedTubeOverlap hr F G)
    (integrable_tubeOverlapIndicator F G)
  intro x
  let A := Metric.thickening r (F : Set Plane) ∩ Metric.thickening r (G : Set Plane)
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    exact (min_le_left _ _).trans (tubeCutoff_le_one hr F x)
  · rw [Set.indicator_of_notMem hx]
    change min (tubeCutoff r F x) (tubeCutoff r G x) ≤ 0
    simp only [A, Set.mem_inter_iff, not_and_or] at hx
    rcases hx with hxF | hxG
    · have hz : tubeCutoff r F x = 0 := (tubeCutoff_eq_zero_iff hr F x).2 <|
        le_of_not_gt ((Metric.mem_thickening_iff_infDist_lt F.nonempty).not.mp hxF)
      rw [hz, min_eq_left (tubeCutoff_nonneg r G x)]
    · have hz : tubeCutoff r G x = 0 := (tubeCutoff_eq_zero_iff hr G x).2 <|
        le_of_not_gt ((Metric.mem_thickening_iff_infDist_lt G.nonempty).not.mp hxG)
      rw [hz, min_eq_right (tubeCutoff_nonneg r F x)]

/-- The tube overlap area is symmetric in the two sets. -/
theorem tubeOverlapArea_comm (r : ℝ) (F G : CompactPlane) :
    tubeOverlapArea r F G = tubeOverlapArea r G F := by
  unfold tubeOverlapArea
  rw [inter_comm]

/-- The sum of smoothed overlaps over all ordered distinct pairs in a finite family. -/
noncomputable def orderedSmoothedTubeOverlapSum {ι : Type*}
    [Fintype ι] [Nonempty ι] (r : ℝ) (F : ι → CompactPlane) : ℝ := by
  classical
  exact ∑ i, ∑ j ∈ Finset.univ.erase i, smoothedTubeOverlap r (F i) (F j)

/-- The sum of smoothed tube overlaps over unordered distinct pairs, represented as half of the
symmetric ordered-pair sum. -/
noncomputable def pairwiseSmoothedTubeOverlapSum {ι : Type*}
    [Fintype ι] [Nonempty ι] (r : ℝ) (F : ι → CompactPlane) : ℝ :=
  orderedSmoothedTubeOverlapSum r F / 2

/-- The ordered sum of raw areas of intersections of radius-`r` thickenings. -/
noncomputable def orderedTubeOverlapAreaSum {ι : Type*}
    [Fintype ι] [Nonempty ι] (r : ℝ) (F : ι → CompactPlane) : ℝ := by
  classical
  exact ∑ i, ∑ j ∈ Finset.univ.erase i, tubeOverlapArea r (F i) (F j)

/-- The sum of raw overlap areas over unordered pairs, again represented as half of the
symmetric ordered-pair sum. -/
noncomputable def pairwiseTubeOverlapAreaSum {ι : Type*}
    [Fintype ι] [Nonempty ι] (r : ℝ) (F : ι → CompactPlane) : ℝ :=
  orderedTubeOverlapAreaSum r F / 2

/-- The unordered smoothed-overlap sum is bounded by the corresponding sum of raw thickening
intersection areas. -/
theorem pairwiseSmoothedTubeOverlapSum_le_pairwiseTubeOverlapAreaSum {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    pairwiseSmoothedTubeOverlapSum r F ≤ pairwiseTubeOverlapAreaSum r F := by
  classical
  unfold pairwiseSmoothedTubeOverlapSum pairwiseTubeOverlapAreaSum
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold orderedSmoothedTubeOverlapSum orderedTubeOverlapAreaSum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact smoothedTubeOverlap_le_tubeOverlapArea hr (F i) (F j)

/-- The ordered-pair overlap integrand is integrable. -/
theorem integrable_orderedTubeOverlapIntegrand {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    Integrable (orderedTubeOverlapIntegrand r F) := by
  classical
  unfold orderedTubeOverlapIntegrand orderedPairMinSum
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact integrable_smoothedTubeOverlap hr (F i) (F j)

/-- Integrating the ordered overlap integrand gives the ordered sum of smoothed overlaps. -/
theorem integral_orderedTubeOverlapIntegrand {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    (∫ x : Plane, orderedTubeOverlapIntegrand r F x) =
      orderedSmoothedTubeOverlapSum r F := by
  classical
  unfold orderedTubeOverlapIntegrand orderedPairMinSum orderedSmoothedTubeOverlapSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · rfl
    · intro j _
      exact integrable_smoothedTubeOverlap hr (F i) (F j)
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact integrable_smoothedTubeOverlap hr (F i) (F j)

/-- The unordered-pair overlap integrand is integrable. -/
theorem integrable_pairwiseTubeOverlapIntegrand {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    Integrable (pairwiseTubeOverlapIntegrand r F) := by
  unfold pairwiseTubeOverlapIntegrand
  simpa only [div_eq_mul_inv] using
    (integrable_orderedTubeOverlapIntegrand hr F).mul_const (2 : ℝ)⁻¹

/-- Integrating the unordered-pair overlap integrand gives the unordered sum of smoothed
overlaps. -/
theorem integral_pairwiseTubeOverlapIntegrand {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    (∫ x : Plane, pairwiseTubeOverlapIntegrand r F x) =
      pairwiseSmoothedTubeOverlapSum r F := by
  unfold pairwiseTubeOverlapIntegrand pairwiseSmoothedTubeOverlapSum
  rw [integral_div, integral_orderedTubeOverlapIntegrand hr]

/-- The multiple-counting defect in smoothed tube mass. -/
noncomputable def tubeDefect {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℝ) (F : ι → CompactPlane) : ℝ :=
  (∑ i, tubeMass r (F i)) - tubeMass r (compactUnion F)

/-- At positive radius the multiple-counting defect is continuous in the finite
family of compact sets. -/
theorem continuous_tubeDefect {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) :
    Continuous (tubeDefect r : (ι → CompactPlane) → ℝ) := by
  unfold tubeDefect
  apply Continuous.sub
  · exact continuous_finsetSum Finset.univ fun i _ =>
      (continuous_tubeMass hr).comp (continuous_apply i)
  · exact (continuous_tubeMass hr).comp continuous_compactUnion

/-- At positive radius the multiple-counting defect is Borel measurable. -/
theorem measurable_tubeDefect {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) :
    Measurable (tubeDefect r : (ι → CompactPlane) → ℝ) :=
  (continuous_tubeDefect hr).measurable

/-- A finite family of almost-everywhere measurable random compact sets has an
almost-everywhere measurable tube defect. -/
theorem aemeasurable_tubeDefect_of_forall
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    {P : Measure Omega} {F : ι → Omega → CompactPlane} {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, AEMeasurable (F i) P) :
    AEMeasurable (fun omega => tubeDefect r (fun i => F i omega)) P := by
  apply (measurable_tubeDefect hr).comp_aemeasurable
  exact aemeasurable_pi_lambda _ hF

/-- The pointwise defect integrand is integrable at every positive radius. -/
theorem integrable_tubeDefectIntegrand {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    Integrable (tubeDefectIntegrand r F) := by
  unfold tubeDefectIntegrand
  apply Integrable.sub
  · apply integrable_finsetSum
    intro i _
    exact integrable_tubeCutoff hr (F i)
  · exact integrable_tubeCutoff hr (compactUnion F)

/-- The mass defect is the integral of its pointwise counterpart. -/
theorem tubeDefect_eq_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    tubeDefect r F = ∫ x : Plane, tubeDefectIntegrand r F x := by
  unfold tubeDefect tubeMass tubeDefectIntegrand
  have hsum : Integrable (fun x : Plane => ∑ i, tubeCutoff r (F i) x) := by
    apply integrable_finsetSum
    intro i _
    exact integrable_tubeCutoff hr (F i)
  rw [integral_sub hsum (integrable_tubeCutoff hr (compactUnion F)),
    integral_finsetSum]
  intro i _
  exact integrable_tubeCutoff hr (F i)

/-- The smoothed tube-mass defect is nonnegative. -/
theorem tubeDefect_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    0 ≤ tubeDefect r F := by
  rw [tubeDefect_eq_integral hr]
  exact integral_nonneg fun x => tubeDefectIntegrand_nonneg hr F x

/-- The factor-one elementary multiple-counting estimate for smoothed tubes: the mass defect is
bounded by the sum of smoothed overlaps over unordered pairs. -/
theorem tubeDefect_le_pairwiseSmoothedTubeOverlapSum {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    tubeDefect r F ≤ pairwiseSmoothedTubeOverlapSum r F := by
  rw [tubeDefect_eq_integral hr, ← integral_pairwiseTubeOverlapIntegrand hr]
  exact integral_mono (integrable_tubeDefectIntegrand hr F)
    (integrable_pairwiseTubeOverlapIntegrand hr F)
    (tubeDefectIntegrand_le_pairwiseTubeOverlapIntegrand hr F)

/-- The raw-area form of `eq:neighbourhood-defect-elementary`: the smoothed mass defect is at most the sum
of Lebesgue areas of pairwise intersections of the open radius-`r` thickenings. -/
theorem tubeDefect_le_pairwiseTubeOverlapAreaSum {ι : Type*}
    [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    tubeDefect r F ≤ pairwiseTubeOverlapAreaSum r F :=
  (tubeDefect_le_pairwiseSmoothedTubeOverlapSum hr F).trans
    (pairwiseSmoothedTubeOverlapSum_le_pairwiseTubeOverlapAreaSum hr F)

/-! ### Affine covariance of the normalized tube probability -/

/-- Integration against the normalized tube probability is integration against its cut-off
density divided by the tube mass. -/
theorem integral_tubeProbability {r : ℝ} (hr : 0 < r) (F : CompactPlane)
    (f : Plane → ℝ) :
    (∫ x, f x ∂(tubeProbability r hr F : Measure Plane)) =
      (tubeMass r F)⁻¹ * ∫ x, tubeCutoff r F x * f x := by
  rw [tubeProbability_toMeasure hr F, integral_smul_nnreal_measure]
  change ((tubeFiniteMeasure r hr F).mass : ℝ)⁻¹ *
      (∫ x, f x ∂(tubeFiniteMeasure r hr F : Measure Plane)) = _
  rw [integral_tubeFiniteMeasure hr]
  congr 1
  apply inv_inj.mpr
  have hmass := congrArg ENNReal.toReal (tubeFiniteMeasure_ennreal_mass hr F)
  simpa only [ENNReal.toReal_ofReal (tubeMass_nonneg r F), ENNReal.coe_toReal] using hmass

end BrownianImages
