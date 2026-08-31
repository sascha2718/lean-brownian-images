/-
The probabilistic form of the deterministic translation-overlap identity.

The main theorem packages the three independent inputs as two compact sets and
their relative translation.  If the latter has a bounded Lebesgue density,
the expected overlap is bounded by the density bound times the product of the
two expected tube areas.
-/
import BrownianImages.MinkowskiOverlapTranslation
import BrownianImages.MinkowskiBrownianPieces
import BrownianImages.MinkowskiBrownianCompactPieces
import BrownianImages.MinkowskiGaussianIncrement
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Independence.Basic

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

/-- Joint continuity of translation on the Hausdorff hyperspace of nonempty
compact planar sets. -/
theorem continuous_translateCompact_pair :
    Continuous fun p : Plane × CompactPlane => translateCompact p.1 p.2 := by
  change Continuous fun p : Plane × CompactPlane =>
    p.2.map (fun x => p.1 + x) (by fun_prop)
  exact continuous_snd.nonemptyCompacts_map' (by fun_prop)

/-- Joint measurability of translation on compact planar sets. -/
theorem measurable_translateCompact_pair :
    Measurable fun p : Plane × CompactPlane => translateCompact p.1 p.2 :=
  continuous_translateCompact_pair.measurable

/-- Successive translations of a compact set add their translation vectors. -/
theorem translateCompact_translate (a b : Plane) (F : CompactPlane) :
    translateCompact a (translateCompact b F) = translateCompact (a + b) F := by
  apply SetLike.coe_injective
  rw [coe_translateCompact, coe_translateCompact, coe_translateCompact,
    Set.image_image]
  apply Set.image_congr
  intro x _hx
  abel

/-- The scalar-map construction used for centered Brownian pieces is the
same compact dilation used by the deterministic tube algebra. -/
theorem smulCompact_eq_dilateCompact (q : Real) (F : CompactPlane) :
    smulCompact q F = dilateCompact q F := rfl

/-- Tube overlap as a function of two compact sets and their relative
translation. -/
noncomputable def translatedTubeOverlap (r : ℝ)
    (p : (CompactPlane × CompactPlane) × Plane) : ℝ :=
  tubeOverlapArea r p.1.1 (translateCompact p.2 p.1.2)

set_option maxHeartbeats 800000 in
/-- The translated tube-overlap kernel is jointly Borel measurable in both
compact sets and the translation. -/
theorem measurable_translatedTubeOverlap {r : ℝ} (hr : 0 < r) :
    Measurable (translatedTubeOverlap r) := by
  let d : CompactPlane × Plane → ℝ := fun p => Metric.infDist p.2 (p.1 : Set Plane)
  let eF : (((CompactPlane × CompactPlane) × Plane) × Plane) → CompactPlane × Plane :=
    fun p => (p.1.1.1, p.2)
  let eG : (((CompactPlane × CompactPlane) × Plane) × Plane) → CompactPlane × Plane :=
    fun p => (p.1.1.2, p.2 - p.1.2)
  let S : Set (((CompactPlane × CompactPlane) × Plane) × Plane) :=
    {p | d (eF p) < r ∧ d (eG p) < r}
  let g : (((CompactPlane × CompactPlane) × Plane) × Plane) → ℝ :=
    S.indicator fun _ => 1
  have hd : Measurable d := continuous_infDist_compactPlane.measurable
  have heF : Measurable eF := by fun_prop
  have heG : Measurable eG := by fun_prop
  have hS : MeasurableSet S := by
    exact (measurableSet_lt (hd.comp heF) measurable_const).inter
      (measurableSet_lt (hd.comp heG) measurable_const)
  have hg : StronglyMeasurable g :=
    (measurable_const.indicator hS).stronglyMeasurable
  have hout : Measurable fun p : (CompactPlane × CompactPlane) × Plane =>
      ∫ x : Plane, g (p, x) := hg.integral_prod_right'.measurable
  have heq : translatedTubeOverlap r = fun p : (CompactPlane × CompactPlane) × Plane =>
      ∫ x : Plane, g (p, x) := by
    funext p
    rw [translatedTubeOverlap, tubeOverlapArea]
    apply integral_congr_ae
    filter_upwards with x
    change
      (Metric.thickening r (p.1.1 : Set Plane) ∩
        Metric.thickening r (translateCompact p.2 p.1.2 : Set Plane)).indicator
          (fun _ => (1 : ℝ)) x = S.indicator (fun _ => (1 : ℝ)) (p, x)
    by_cases hxF : x ∈ Metric.thickening r (p.1.1 : Set Plane)
    · by_cases hxG : x - p.2 ∈ Metric.thickening r (p.1.2 : Set Plane)
      · have hxGa : x ∈ Metric.thickening r
            (translateCompact p.2 p.1.2 : Set Plane) :=
          (mem_thickening_translateCompact_iff hr p.2 p.1.2 x).2 hxG
        have hxFdist : Metric.infDist x (p.1.1 : Set Plane) < r :=
          (Metric.mem_thickening_iff_infDist_lt p.1.1.nonempty).1 hxF
        have hxGdist : Metric.infDist (x - p.2) (p.1.2 : Set Plane) < r :=
          (Metric.mem_thickening_iff_infDist_lt p.1.2.nonempty).1 hxG
        have hxInter : x ∈ Metric.thickening r (p.1.1 : Set Plane) ∩
            Metric.thickening r (translateCompact p.2 p.1.2 : Set Plane) := ⟨hxF, hxGa⟩
        have hxS : (p, x) ∈ S := by
          change Metric.infDist x (p.1.1 : Set Plane) < r ∧
            Metric.infDist (x - p.2) (p.1.2 : Set Plane) < r
          exact ⟨hxFdist, hxGdist⟩
        rw [Set.indicator_of_mem hxInter, Set.indicator_of_mem hxS]
      · have hxGa : x ∉ Metric.thickening r
            (translateCompact p.2 p.1.2 : Set Plane) :=
          fun h => hxG ((mem_thickening_translateCompact_iff hr p.2 p.1.2 x).1 h)
        have hxGdist : ¬ Metric.infDist (x - p.2) (p.1.2 : Set Plane) < r :=
          fun h => hxG ((Metric.mem_thickening_iff_infDist_lt p.1.2.nonempty).2 h)
        have hxInter : x ∉ Metric.thickening r (p.1.1 : Set Plane) ∩
            Metric.thickening r (translateCompact p.2 p.1.2 : Set Plane) :=
          fun h => hxGa h.2
        have hxS : (p, x) ∉ S := by
          intro h
          exact hxGdist h.2
        rw [Set.indicator_of_notMem hxInter, Set.indicator_of_notMem hxS]
    · have hxFdist : ¬ Metric.infDist x (p.1.1 : Set Plane) < r :=
        fun h => hxF ((Metric.mem_thickening_iff_infDist_lt p.1.1.nonempty).2 h)
      have hxInter : x ∉ Metric.thickening r (p.1.1 : Set Plane) ∩
          Metric.thickening r (translateCompact p.2 p.1.2 : Set Plane) :=
        fun h => hxF h.1
      have hxS : (p, x) ∉ S := by
        intro h
        exact hxFdist h.1
      rw [Set.indicator_of_notMem hxInter, Set.indicator_of_notMem hxS]
  rw [heq]
  exact hout

theorem translatedTubeOverlap_nonneg (r : ℝ)
    (p : (CompactPlane × CompactPlane) × Plane) :
    0 ≤ translatedTubeOverlap r p :=
  tubeOverlapArea_nonneg r p.1.1 (translateCompact p.2 p.1.2)

/-- Integrability of the translation kernel under a bounded density. -/
theorem integrable_translatedTubeOverlap_withDensity {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) {density : Plane → ℝ} {C : ℝ}
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C) :
    Integrable (fun z : Plane => translatedTubeOverlap r ((F, G), z))
      (volume.withDensity fun z => ENNReal.ofReal (density z)) := by
  have hden : Measurable fun z : Plane => ENNReal.ofReal (density z) :=
    hdensity.ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hden (by simp)]
  simpa only [translatedTubeOverlap, ENNReal.toReal_ofReal (hdensity_nonneg _),
    smul_eq_mul] using
    integrable_density_mul_tubeOverlapArea_translate hr F G hdensity
      hdensity_nonneg hdensity_le

/-- The deterministic bounded-density estimate written directly as an
integral against the measure having that density. -/
theorem integral_translatedTubeOverlap_withDensity_le {r : ℝ} (hr : 0 < r)
    (F G : CompactPlane) {density : Plane → ℝ} {C : ℝ}
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C) :
    (∫ z : Plane, translatedTubeOverlap r ((F, G), z)
      ∂volume.withDensity fun z => ENNReal.ofReal (density z)) ≤
      C * (tubeArea r F * tubeArea r G) := by
  have hden : Measurable fun z : Plane => ENNReal.ofReal (density z) :=
    hdensity.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hden (by simp)]
  simpa only [translatedTubeOverlap, ENNReal.toReal_ofReal (hdensity_nonneg _),
    smul_eq_mul] using
    integral_density_mul_tubeOverlapArea_translate_le hr F G hdensity
      hdensity_nonneg hdensity_le

/-- Product-measure form of the probabilistic overlap estimate.  This is the
analytic core after mutual independence has replaced the joint law by the
product of the three marginal laws. -/
theorem integrable_translatedTubeOverlap_prod_withDensity {r : ℝ} (hr : 0 < r)
    (muA muB : Measure CompactPlane) [IsProbabilityMeasure muA]
    [IsProbabilityMeasure muB] {density : Plane → ℝ} {C : ℝ}
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C)
    (hareaA : Integrable (tubeArea r) muA)
    (hareaB : Integrable (tubeArea r) muB) :
    Integrable (translatedTubeOverlap r)
      ((muA.prod muB).prod
        (volume.withDensity fun z => ENNReal.ofReal (density z))) := by
  let nu : Measure Plane := volume.withDensity fun z => ENNReal.ofReal (density z)
  have hareaProd : Integrable
      (fun p : CompactPlane × CompactPlane => tubeArea r p.1 * tubeArea r p.2)
      (muA.prod muB) := by
    have hind := indepFun_prod₀ hareaA.aemeasurable hareaB.aemeasurable
    have hmul := hind.integrable_mul (hareaA.comp_fst muB) (hareaB.comp_snd muA)
    change Integrable
      (fun p : CompactPlane × CompactPlane => tubeArea r p.1 * tubeArea r p.2)
      (muA.prod muB) at hmul
    exact hmul
  have hC : 0 ≤ C := (hdensity_nonneg 0).trans (hdensity_le 0)
  have hmeas : AEStronglyMeasurable (translatedTubeOverlap r)
      ((muA.prod muB).prod nu) :=
    (measurable_translatedTubeOverlap hr).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Filter.Eventually.of_forall fun p =>
      integrable_translatedTubeOverlap_withDensity hr p.1 p.2 hdensity
        hdensity_nonneg hdensity_le
  · let q : CompactPlane × CompactPlane → ℝ := fun p =>
      ∫ z : Plane, ‖translatedTubeOverlap r (p, z)‖ ∂nu
    have hq : StronglyMeasurable q :=
      (measurable_translatedTubeOverlap hr).norm.stronglyMeasurable.integral_prod_right'
    apply (hareaProd.const_mul C).mono' hq.aestronglyMeasurable
    filter_upwards with p
    have hnorm : (fun z : Plane => ‖translatedTubeOverlap r (p, z)‖) =
        fun z : Plane => translatedTubeOverlap r (p, z) := by
      funext z
      rw [Real.norm_eq_abs, abs_of_nonneg (translatedTubeOverlap_nonneg r (p, z))]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnorm]
    exact integral_translatedTubeOverlap_withDensity_le hr p.1 p.2 hdensity
      hdensity_nonneg hdensity_le

/-- The product-law expectation of translated overlap is bounded by the
product of the marginal mean tube areas. -/
theorem integral_translatedTubeOverlap_prod_withDensity_le {r : ℝ} (hr : 0 < r)
    (muA muB : Measure CompactPlane) [IsProbabilityMeasure muA]
    [IsProbabilityMeasure muB] {density : Plane → ℝ} {C : ℝ}
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C)
    (hareaA : Integrable (tubeArea r) muA)
    (hareaB : Integrable (tubeArea r) muB) :
    (∫ p, translatedTubeOverlap r p
      ∂(muA.prod muB).prod
        (volume.withDensity fun z => ENNReal.ofReal (density z))) ≤
      C * ((∫ F, tubeArea r F ∂muA) * ∫ G, tubeArea r G ∂muB) := by
  let nu : Measure Plane := volume.withDensity fun z => ENNReal.ofReal (density z)
  have hglobal := integrable_translatedTubeOverlap_prod_withDensity hr muA muB
    hdensity hdensity_nonneg hdensity_le hareaA hareaB
  have hareaProd : Integrable
      (fun p : CompactPlane × CompactPlane => tubeArea r p.1 * tubeArea r p.2)
      (muA.prod muB) := by
    have hind := indepFun_prod₀ hareaA.aemeasurable hareaB.aemeasurable
    have hmul := hind.integrable_mul (hareaA.comp_fst muB) (hareaB.comp_snd muA)
    change Integrable
      (fun p : CompactPlane × CompactPlane => tubeArea r p.1 * tubeArea r p.2)
      (muA.prod muB) at hmul
    exact hmul
  calc
    (∫ p, translatedTubeOverlap r p ∂(muA.prod muB).prod nu) =
        ∫ p : CompactPlane × CompactPlane,
          ∫ z : Plane, translatedTubeOverlap r (p, z) ∂nu ∂muA.prod muB :=
      integral_prod _ hglobal
    _ ≤ ∫ p : CompactPlane × CompactPlane,
        C * (tubeArea r p.1 * tubeArea r p.2) ∂muA.prod muB := by
      apply integral_mono hglobal.integral_prod_left (hareaProd.const_mul C)
      intro p
      exact integral_translatedTubeOverlap_withDensity_le hr p.1 p.2 hdensity
        hdensity_nonneg hdensity_le
    _ = C * ((∫ F, tubeArea r F ∂muA) * ∫ G, tubeArea r G ∂muB) := by
      rw [integral_const_mul, integral_prod_mul]

/-! ### Independent random inputs -/

/-- Two-stage independence gives the product law of two compact random sets
and a planar translation.  The hypotheses say precisely that `A`, `B`, and
`Z` are mutually independent, in a form convenient for heterogeneous
codomains. -/
theorem map_compactPair_translation_eq_prod_of_indep
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {A B : Omega → CompactPlane} {Z : Omega → Plane}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hZ : AEMeasurable Z P) (hAB : IndepFun A B P)
    (hABZ : IndepFun (fun omega => (A omega, B omega)) Z P) :
    P.map (fun omega => ((A omega, B omega), Z omega)) =
      ((P.map A).prod (P.map B)).prod (P.map Z) := by
  rw [hABZ.map_prod_eq_prod_map_map (hA.prodMk hB) hZ,
    hAB.map_prod_eq_prod_map_map hA hB]

/-- Integrability of random translated overlap under mutual independence and
a bounded-density law for the translation. -/
theorem integrable_tubeOverlapArea_translate_of_indep_boundedDensity
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {A B : Omega → CompactPlane} {Z : Omega → Plane}
    {r : ℝ} (hr : 0 < r) {density : Plane → ℝ} {C : ℝ}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hZ : AEMeasurable Z P) (hAB : IndepFun A B P)
    (hABZ : IndepFun (fun omega => (A omega, B omega)) Z P)
    (hZlaw : P.map Z = volume.withDensity fun z => ENNReal.ofReal (density z))
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C)
    (hareaA : Integrable (fun omega => tubeArea r (A omega)) P)
    (hareaB : Integrable (fun omega => tubeArea r (B omega)) P) :
    Integrable (fun omega =>
      tubeOverlapArea r (A omega) (translateCompact (Z omega) (B omega))) P := by
  letI : IsProbabilityMeasure (P.map A) := Measure.isProbabilityMeasure_map hA
  letI : IsProbabilityMeasure (P.map B) := Measure.isProbabilityMeasure_map hB
  have hareaAmap : Integrable (tubeArea r) (P.map A) := by
    rw [integrable_map_measure (measurable_tubeArea r).aestronglyMeasurable hA]
    simpa only [Function.comp_def] using hareaA
  have hareaBmap : Integrable (tubeArea r) (P.map B) := by
    rw [integrable_map_measure (measurable_tubeArea r).aestronglyMeasurable hB]
    simpa only [Function.comp_def] using hareaB
  have hprod := integrable_translatedTubeOverlap_prod_withDensity hr
    (P.map A) (P.map B) hdensity hdensity_nonneg hdensity_le hareaAmap hareaBmap
  have hmap := map_compactPair_translation_eq_prod_of_indep hA hB hZ hAB hABZ
  rw [hZlaw] at hmap
  have hprod' : Integrable (translatedTubeOverlap r)
      (P.map fun omega => ((A omega, B omega), Z omega)) := by
    rw [hmap]
    exact hprod
  have htriple : AEMeasurable (fun omega => ((A omega, B omega), Z omega)) P :=
    (hA.prodMk hB).prodMk hZ
  have hpull := (integrable_map_measure
    (measurable_translatedTubeOverlap hr).aestronglyMeasurable htriple).1 hprod'
  simpa only [Function.comp_def, translatedTubeOverlap] using hpull

/-- Expected-overlap bound for mutually independent random compact sets and a
translation whose law has a bounded Lebesgue density. -/
theorem integral_tubeOverlapArea_translate_le_of_indep_boundedDensity
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {A B : Omega → CompactPlane} {Z : Omega → Plane}
    {r : ℝ} (hr : 0 < r) {density : Plane → ℝ} {C : ℝ}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hZ : AEMeasurable Z P) (hAB : IndepFun A B P)
    (hABZ : IndepFun (fun omega => (A omega, B omega)) Z P)
    (hZlaw : P.map Z = volume.withDensity fun z => ENNReal.ofReal (density z))
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ x, 0 ≤ density x)
    (hdensity_le : ∀ x, density x ≤ C)
    (hareaA : Integrable (fun omega => tubeArea r (A omega)) P)
    (hareaB : Integrable (fun omega => tubeArea r (B omega)) P) :
    (∫ omega, tubeOverlapArea r (A omega)
      (translateCompact (Z omega) (B omega)) ∂P) ≤
      C * ((∫ omega, tubeArea r (A omega) ∂P) *
        ∫ omega, tubeArea r (B omega) ∂P) := by
  letI : IsProbabilityMeasure (P.map A) := Measure.isProbabilityMeasure_map hA
  letI : IsProbabilityMeasure (P.map B) := Measure.isProbabilityMeasure_map hB
  have hareaAmap : Integrable (tubeArea r) (P.map A) := by
    rw [integrable_map_measure (measurable_tubeArea r).aestronglyMeasurable hA]
    simpa only [Function.comp_def] using hareaA
  have hareaBmap : Integrable (tubeArea r) (P.map B) := by
    rw [integrable_map_measure (measurable_tubeArea r).aestronglyMeasurable hB]
    simpa only [Function.comp_def] using hareaB
  have hmap := map_compactPair_translation_eq_prod_of_indep hA hB hZ hAB hABZ
  rw [hZlaw] at hmap
  have htriple : AEMeasurable (fun omega => ((A omega, B omega), Z omega)) P :=
    (hA.prodMk hB).prodMk hZ
  calc
    (∫ omega, tubeOverlapArea r (A omega)
        (translateCompact (Z omega) (B omega)) ∂P) =
        ∫ p, translatedTubeOverlap r p
          ∂P.map (fun omega => ((A omega, B omega), Z omega)) := by
      rw [integral_map htriple (measurable_translatedTubeOverlap hr).aestronglyMeasurable]
      rfl
    _ = ∫ p, translatedTubeOverlap r p
        ∂((P.map A).prod (P.map B)).prod
          (volume.withDensity fun z => ENNReal.ofReal (density z)) := by rw [hmap]
    _ ≤ C * ((∫ F, tubeArea r F ∂P.map A) *
        ∫ G, tubeArea r G ∂P.map B) :=
      integral_translatedTubeOverlap_prod_withDensity_le hr (P.map A) (P.map B)
        hdensity hdensity_nonneg hdensity_le hareaAmap hareaBmap
    _ = C * ((∫ omega, tubeArea r (A omega) ∂P) *
        ∫ omega, tubeArea r (B omega) ∂P) := by
      rw [integral_map hA (measurable_tubeArea r).aestronglyMeasurable,
        integral_map hB (measurable_tubeArea r).aestronglyMeasurable]

/-! ### Three Brownian pieces separated by a temporal gap -/

/-- The compact Brownian image over the affine copy `a + r K`, translated so
that the right endpoint of its host interval is at the origin. -/
noncomputable def rightCenteredBrownianCompactPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal → Omega → Plane)
    (a r : NNReal) (K : NonemptyCompacts Real) (omega : Omega) : CompactPlane :=
  translateCompact (W a omega - W (a + r) omega)
    (centeredBrownianCompactPiece W a r K omega)

/-- The full-host-interval specialization of
`rightCenteredBrownianCompactPiece`. -/
noncomputable def rightCenteredBrownianPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal → Omega → Plane)
    (a r : NNReal) (omega : Omega) : CompactPlane :=
  rightCenteredBrownianCompactPiece W a r unitIntervalCompact omega

theorem rightCenteredBrownianPiece_eq_compactPiece
    {Omega : Type*} [MeasurableSpace Omega] (W : NNReal → Omega → Plane)
    (a r : NNReal) :
    rightCenteredBrownianPiece W a r =
      rightCenteredBrownianCompactPiece W a r unitIntervalCompact := rfl

/-- A right-endpoint-centered compact Brownian piece is almost everywhere
measurable. -/
theorem IsPlanarBrownian.aemeasurable_rightCenteredBrownianCompactPiece
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r : NNReal} (hr : r ≠ 0)
    (K : NonemptyCompacts Real) :
    AEMeasurable (rightCenteredBrownianCompactPiece W a r K) P := by
  have hshift : AEMeasurable (fun omega => W a omega - W (a + r) omega) P :=
    (JointMeasurability.aemeasurable_eval hW a).sub
      (JointMeasurability.aemeasurable_eval hW (a + r))
  have hpiece : AEMeasurable (centeredBrownianCompactPiece W a r K) P :=
    (measurable_smulCompact (Real.sqrt (r : Real))).comp_aemeasurable
      ((hW.intervalRescale a hr).aemeasurable_brownianImage K)
  exact measurable_translateCompact_pair.comp_aemeasurable
    (hshift.prodMk hpiece)

/-- A right-endpoint-centered Brownian compact piece is almost everywhere
measurable. -/
theorem IsPlanarBrownian.aemeasurable_rightCenteredBrownianPiece
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r : NNReal} (hr : r ≠ 0) :
    AEMeasurable (rightCenteredBrownianPiece W a r) P := by
  exact hW.aemeasurable_rightCenteredBrownianCompactPiece a hr unitIntervalCompact

/-- On a continuous path, the right-centered compact is exactly the path
image translated by its terminal value. -/
theorem coe_rightCenteredBrownianPiece_of_continuous
    {Omega : Type*} [MeasurableSpace Omega] {W : NNReal → Omega → Plane}
    {a r : NNReal} (hr : r ≠ 0) {omega : Omega}
    (homega : Continuous fun t => W t omega) :
    (rightCenteredBrownianPiece W a r omega : Set Plane) =
      (fun t : Real => W (a + r * t.toNNReal) omega - W (a + r) omega) ''
        Set.Icc 0 1 := by
  change (translateCompact (W a omega - W (a + r) omega)
      (centeredBrownianPiece W a r omega) : Set Plane) = _
  rw [coe_translateCompact,
    coe_centeredBrownianPiece_of_continuous hr homega, Set.image_image]
  apply Set.image_congr
  intro t _ht
  abel

set_option maxHeartbeats 800000 in
/-- The right-centered compact path piece on the left of a gap and the
left-centered compact path piece on its right, taken together, are independent
of the Brownian displacement across the gap.  This is the three-input
independence statement needed by the overlap estimate. -/
theorem IsPlanarBrownian.indepFun_rightCenteredPiece_centeredPiece_gapIncrement
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r q s : NNReal}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    IndepFun
      (fun omega =>
        (rightCenteredBrownianPiece W a r omega,
          centeredBrownianPiece W (a + r + q) s omega))
      (fun omega => W (a + r + q) omega - W (a + r) omega) P := by
  let starts : Fin 3 → NNReal := ![a, a + r, a + r + q]
  let lengths : Fin 3 → NNReal := ![r, q, s]
  let K : Fin 3 → NonemptyCompacts Real := fun _ => unitIntervalCompact
  let proc : Fin 3 → Omega → (unitIntervalCompact → Plane) := fun i omega t =>
    W (starts i + lengths i * t.1.toNNReal) omega - W (starts i) omega
  have hK : ∀ i, (K i : Set Real) ⊆ Set.Icc 0 1 := by
    intro i x hx
    simpa only [K, coe_unitIntervalCompact] using hx
  have hdisjoint : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      starts i + lengths i ≤ starts j ∨ starts j + lengths j ≤ starts i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [starts, lengths, add_assoc]
  have hproc : iIndepFun proc P := by
    have h := hW.iIndepFun_centered_compact_piece_processes starts lengths K hK hdisjoint
    change iIndepFun proc P at h
    exact h
  let FX : Nat → Omega → CompactPlane := fun n omega =>
    translateCompact (W a omega - W (a + r) omega)
      (smulCompact (Real.sqrt (r : Real))
        (finiteImage (finiteCompactApprox (T := unitIntervalCompact) n)
          (finite_finiteCompactApprox (T := unitIntervalCompact) n)
          (fun t : unitIntervalCompact =>
            BrownianImages.intervalRescale W a r t.1.toNNReal omega)))
  let FY : Nat → Omega → CompactPlane := fun n omega =>
    smulCompact (Real.sqrt (s : Real))
      (finiteImage (finiteCompactApprox (T := unitIntervalCompact) n)
        (finite_finiteCompactApprox (T := unitIntervalCompact) n)
        (fun t : unitIntervalCompact =>
          BrownianImages.intervalRescale W (a + r + q) s t.1.toNNReal omega))
  let Z : Omega → Plane := fun omega => W (a + r + q) omega - W (a + r) omega
  let hWa := hW.intervalRescale a hr
  let hWc := hW.intervalRescale (a + r + q) hs
  have hFX : ∀ n, AEMeasurable (FX n) P := by
    intro n
    have hshift : AEMeasurable (fun omega => W a omega - W (a + r) omega) P :=
      (JointMeasurability.aemeasurable_eval hW a).sub
        (JointMeasurability.aemeasurable_eval hW (a + r))
    have himage : AEMeasurable (fun omega =>
        finiteImage (finiteCompactApprox (T := unitIntervalCompact) n)
          (finite_finiteCompactApprox (T := unitIntervalCompact) n)
          (fun t : unitIntervalCompact =>
            BrownianImages.intervalRescale W a r t.1.toNNReal omega)) P :=
      aemeasurable_finiteImage_process P _ _ _
        (fun t => JointMeasurability.aemeasurable_eval hWa t.1.toNNReal)
    have hscaled : AEMeasurable (fun omega =>
        smulCompact (Real.sqrt (r : Real))
          (finiteImage (finiteCompactApprox (T := unitIntervalCompact) n)
            (finite_finiteCompactApprox (T := unitIntervalCompact) n)
            (fun t : unitIntervalCompact =>
              BrownianImages.intervalRescale W a r t.1.toNNReal omega))) P :=
      (measurable_smulCompact (Real.sqrt (r : Real))).comp_aemeasurable himage
    exact measurable_translateCompact_pair.comp_aemeasurable
      (hshift.prodMk hscaled)
  have hFY : ∀ n, AEMeasurable (FY n) P := by
    intro n
    exact (measurable_smulCompact (Real.sqrt (s : Real))).comp_aemeasurable
      (aemeasurable_finiteImage_process P _ _ _
        (fun t => JointMeasurability.aemeasurable_eval hWc t.1.toNNReal))
  have hA : AEMeasurable (rightCenteredBrownianPiece W a r) P :=
    hW.aemeasurable_rightCenteredBrownianPiece a hr
  have hB : AEMeasurable (centeredBrownianPiece W (a + r + q) s) P :=
    (measurable_smulCompact (Real.sqrt (s : Real))).comp_aemeasurable
      (hWc.aemeasurable_brownianImage unitIntervalCompact)
  have hZ : AEMeasurable Z P :=
    (JointMeasurability.aemeasurable_eval hW (a + r + q)).sub
      (JointMeasurability.aemeasurable_eval hW (a + r))
  have hsmul (c : Real) : Continuous (smulCompact c) :=
    (show Continuous (fun x : Plane => c • x) by fun_prop).nonemptyCompacts_map
  have hFXlim : ∀ᵐ omega ∂P,
      Tendsto (fun n => FX n omega) atTop
        (nhds (rightCenteredBrownianPiece W a r omega)) := by
    filter_upwards [hWa.ae_continuous] with omega homega
    have hscaled := (hsmul (Real.sqrt (r : Real))).tendsto
      (rescaledBrownianPiece W a r omega) |>.comp
        (tendsto_finiteImage_compactImageOfFunction (0 : Plane)
          (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val)))
    exact (continuous_translateCompact_pair.tendsto
      (W a omega - W (a + r) omega, centeredBrownianPiece W a r omega)).comp
        (tendsto_const_nhds.prodMk_nhds hscaled)
  have hFYlim : ∀ᵐ omega ∂P,
      Tendsto (fun n => FY n omega) atTop
        (nhds (centeredBrownianPiece W (a + r + q) s omega)) := by
    filter_upwards [hWc.ae_continuous] with omega homega
    exact (hsmul (Real.sqrt (s : Real))).tendsto
      (rescaledBrownianPiece W (a + r + q) s omega) |>.comp
        (tendsto_finiteImage_compactImageOfFunction (0 : Plane)
          (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val)))
  have hfinite : ∀ n, IndepFun (fun omega => (FX n omega, FY n omega)) Z P := by
    intro n
    let L := finiteCompactApprox (T := unitIntervalCompact) n
    let hL : (L : Set unitIntervalCompact).Finite :=
      finite_finiteCompactApprox (T := unitIntervalCompact) n
    letI : Fintype L := hL.fintype
    let oneK : unitIntervalCompact := ⟨1, by constructor <;> norm_num⟩
    let sample : (unitIntervalCompact → Plane) → (L → Plane) × Plane := fun z =>
      (fun t : L => z t.1, z oneK)
    have msample : Measurable sample := by
      apply Measurable.prodMk
      · apply measurable_pi_lambda
        intro t
        exact measurable_pi_apply t.1
      · exact measurable_pi_apply oneK
    have hsampled := hproc.comp (fun _ => sample) (fun _ => msample)
    have hsampleMeas : ∀ i, AEMeasurable (sample ∘ proc i) P := by
      intro i
      apply AEMeasurable.prodMk
      · apply aemeasurable_pi_lambda
        intro t
        exact (JointMeasurability.aemeasurable_eval hW
          (starts i + lengths i * t.1.1.toNNReal)).sub
            (JointMeasurability.aemeasurable_eval hW (starts i))
      · exact (JointMeasurability.aemeasurable_eval hW
          (starts i + lengths i * oneK.1.toNNReal)).sub
            (JointMeasurability.aemeasurable_eval hW (starts i))
    let gX : ((L → Plane) × Plane) → CompactPlane := fun z =>
      translateCompact (-z.2)
        (smulCompact (Real.sqrt (r : Real))
          (finiteRange fun t : L => (Real.sqrt (r : Real))⁻¹ • z.1 t))
    let gY : ((L → Plane) × Plane) → CompactPlane := fun z =>
      smulCompact (Real.sqrt (s : Real))
        (finiteRange fun t : L => (Real.sqrt (s : Real))⁻¹ • z.1 t)
    have mgX : Measurable gX := by
      have hsamples : Measurable (fun z : (L → Plane) × Plane => fun t : L =>
          (Real.sqrt (r : Real))⁻¹ • z.1 t) := by
        apply measurable_pi_lambda
        intro t
        fun_prop
      have hrange := (measurable_finiteRange (I := L) (E := Plane)).comp hsamples
      exact measurable_translateCompact_pair.comp
        ((measurable_neg.comp measurable_snd).prodMk
          ((measurable_smulCompact (Real.sqrt (r : Real))).comp hrange))
    have mgY : Measurable gY := by
      have hsamples : Measurable (fun z : (L → Plane) × Plane => fun t : L =>
          (Real.sqrt (s : Real))⁻¹ • z.1 t) := by
        apply measurable_pi_lambda
        intro t
        fun_prop
      have hrange := (measurable_finiteRange (I := L) (E := Plane)).comp hsamples
      exact (measurable_smulCompact (Real.sqrt (s : Real))).comp hrange
    have hbase := hsampled.indepFun_prodMk₀ hsampleMeas (0 : Fin 3) 2 1
      (by decide) (by decide)
    have hcomp := hbase.comp
      (mgX.comp measurable_fst |>.prodMk (mgY.comp measurable_snd))
      measurable_snd
    change IndepFun
      (fun omega => (gX (sample (proc 0 omega)), gY (sample (proc 2 omega))))
      (fun omega => (sample (proc 1 omega)).2) P at hcomp
    simpa [FX, FY, Z, gX, gY, sample, proc, starts, lengths,
      BrownianImages.intervalRescale, oneK, finiteImage_eq_finiteRange] using hcomp
  have hpairlim : ∀ᵐ omega ∂P,
      Tendsto (fun n => (FX n omega, FY n omega)) atTop
        (nhds (rightCenteredBrownianPiece W a r omega,
          centeredBrownianPiece W (a + r + q) s omega)) := by
    filter_upwards [hFXlim, hFYlim] with omega hx hy
    exact hx.prodMk_nhds hy
  exact indepFun_of_ae_tendsto
    (fun n => (hFX n).prodMk (hFY n)) (fun _ => hZ)
    (hA.prodMk hB) hZ hpairlim
    (Filter.Eventually.of_forall fun _ => tendsto_const_nhds) hfinite

set_option maxHeartbeats 1200000 in
/-- For compact parameter sets `K,L ⊆ [0,1]`, the right-centered Brownian
image over `a + r K`, the separating gap increment, and the left-centered
Brownian image over `a+r+q+sL` are mutually independent.  The conclusion is
packaged in the two heterogeneous independence statements consumed by the
bounded-density overlap theorem. -/
theorem IsPlanarBrownian.indepFun_compactPieces_gapIncrement
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r q s : NNReal}
    (hr : r ≠ 0) (hs : s ≠ 0) (K L : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    (hL : (L : Set Real) ⊆ Set.Icc 0 1) :
    IndepFun
        (rightCenteredBrownianCompactPiece W a r K)
        (centeredBrownianCompactPiece W (a + r + q) s L) P ∧
      IndepFun
        (fun omega =>
          (rightCenteredBrownianCompactPiece W a r K omega,
            centeredBrownianCompactPiece W (a + r + q) s L omega))
        (fun omega => W (a + r + q) omega - W (a + r) omega) P := by
  let starts : Fin 3 → NNReal := ![a, a + r, a + r + q]
  let lengths : Fin 3 → NNReal := ![r, q, s]
  let hosts : Fin 3 → NonemptyCompacts Real := fun _ => unitIntervalCompact
  let proc : Fin 3 → Omega → (unitIntervalCompact → Plane) := fun i omega t =>
    W (starts i + lengths i * t.1.toNNReal) omega - W (starts i) omega
  have hhosts : ∀ i, (hosts i : Set Real) ⊆ Set.Icc 0 1 := by
    intro i x hx
    simpa only [hosts, coe_unitIntervalCompact] using hx
  have hdisjoint : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      starts i + lengths i ≤ starts j ∨ starts j + lengths j ≤ starts i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [starts, lengths, add_assoc]
  have hproc : iIndepFun proc P := by
    have h := hW.iIndepFun_centered_compact_piece_processes
      starts lengths hosts hhosts hdisjoint
    change iIndepFun proc P at h
    exact h
  let A : Omega → CompactPlane := rightCenteredBrownianCompactPiece W a r K
  let B : Omega → CompactPlane := centeredBrownianCompactPiece W (a + r + q) s L
  let Z : Omega → Plane := fun omega => W (a + r + q) omega - W (a + r) omega
  let FX : Nat → Omega → CompactPlane := fun n omega =>
    translateCompact (W a omega - W (a + r) omega)
      (smulCompact (Real.sqrt (r : Real))
        (finiteImage (finiteCompactApprox (T := K) n)
          (finite_finiteCompactApprox (T := K) n)
          (fun t : K =>
            BrownianImages.intervalRescale W a r t.1.toNNReal omega)))
  let FY : Nat → Omega → CompactPlane := fun n omega =>
    smulCompact (Real.sqrt (s : Real))
      (finiteImage (finiteCompactApprox (T := L) n)
        (finite_finiteCompactApprox (T := L) n)
        (fun t : L => BrownianImages.intervalRescale W
          (a + r + q) s t.1.toNNReal omega))
  let hWa := hW.intervalRescale a hr
  let hWc := hW.intervalRescale (a + r + q) hs
  have hFX : ∀ n, AEMeasurable (FX n) P := by
    intro n
    have hshift : AEMeasurable (fun omega => W a omega - W (a + r) omega) P :=
      (JointMeasurability.aemeasurable_eval hW a).sub
        (JointMeasurability.aemeasurable_eval hW (a + r))
    have himage : AEMeasurable (fun omega =>
        finiteImage (finiteCompactApprox (T := K) n)
          (finite_finiteCompactApprox (T := K) n)
          (fun t : K => BrownianImages.intervalRescale W a r
            t.1.toNNReal omega)) P :=
      aemeasurable_finiteImage_process P _ _ _
        (fun t => JointMeasurability.aemeasurable_eval hWa t.1.toNNReal)
    exact measurable_translateCompact_pair.comp_aemeasurable
      (hshift.prodMk
        ((measurable_smulCompact (Real.sqrt (r : Real))).comp_aemeasurable himage))
  have hFY : ∀ n, AEMeasurable (FY n) P := by
    intro n
    exact (measurable_smulCompact (Real.sqrt (s : Real))).comp_aemeasurable
      (aemeasurable_finiteImage_process P _ _ _
        (fun t => JointMeasurability.aemeasurable_eval hWc t.1.toNNReal))
  have hA : AEMeasurable A P :=
    hW.aemeasurable_rightCenteredBrownianCompactPiece a hr K
  have hB : AEMeasurable B P :=
    (measurable_smulCompact (Real.sqrt (s : Real))).comp_aemeasurable
      (hWc.aemeasurable_brownianImage L)
  have hZ : AEMeasurable Z P :=
    (JointMeasurability.aemeasurable_eval hW (a + r + q)).sub
      (JointMeasurability.aemeasurable_eval hW (a + r))
  have hsmul (c : Real) : Continuous (smulCompact c) :=
    (show Continuous (fun x : Plane => c • x) by fun_prop).nonemptyCompacts_map
  have hFXlim : ∀ᵐ omega ∂P, Tendsto (fun n => FX n omega) atTop (nhds (A omega)) := by
    filter_upwards [hWa.ae_continuous] with omega homega
    have hscaled := (hsmul (Real.sqrt (r : Real))).tendsto
      (rescaledBrownianCompactPiece W a r K omega) |>.comp
        (tendsto_finiteImage_compactImageOfFunction (0 : Plane)
          (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val)))
    exact (continuous_translateCompact_pair.tendsto
      (W a omega - W (a + r) omega,
        centeredBrownianCompactPiece W a r K omega)).comp
      (tendsto_const_nhds.prodMk_nhds hscaled)
  have hFYlim : ∀ᵐ omega ∂P, Tendsto (fun n => FY n omega) atTop (nhds (B omega)) := by
    filter_upwards [hWc.ae_continuous] with omega homega
    exact (hsmul (Real.sqrt (s : Real))).tendsto
      (rescaledBrownianCompactPiece W (a + r + q) s L omega) |>.comp
        (tendsto_finiteImage_compactImageOfFunction (0 : Plane)
          (homega.comp (continuous_real_toNNReal.comp continuous_subtype_val)))
  let zeroCompact : CompactPlane := {0}
  let oneU : unitIntervalCompact := ⟨1, by constructor <;> norm_num⟩
  let inK : K → unitIntervalCompact := fun t => ⟨t.1, hK t.2⟩
  let inL : L → unitIntervalCompact := fun t => ⟨t.1, hL t.2⟩
  let g0 (n : Nat) : (unitIntervalCompact → Plane) → CompactPlane × Plane := fun z =>
    (translateCompact (-z oneU)
      (smulCompact (Real.sqrt (r : Real))
        (finiteImage (finiteCompactApprox (T := K) n)
          (finite_finiteCompactApprox (T := K) n)
          (fun t : K => (Real.sqrt (r : Real))⁻¹ • z (inK t)))), 0)
  let g1 : (unitIntervalCompact → Plane) → CompactPlane × Plane := fun z =>
    (zeroCompact, z oneU)
  let g2 (n : Nat) : (unitIntervalCompact → Plane) → CompactPlane × Plane := fun z =>
    (smulCompact (Real.sqrt (s : Real))
      (finiteImage (finiteCompactApprox (T := L) n)
        (finite_finiteCompactApprox (T := L) n)
        (fun t : L => (Real.sqrt (s : Real))⁻¹ • z (inL t))), 0)
  have mg0 : ∀ n, Measurable (g0 n) := by
    intro n
    let LK := finiteCompactApprox (T := K) n
    let hLK : (LK : Set K).Finite := finite_finiteCompactApprox (T := K) n
    letI : Fintype LK := hLK.fintype
    have hsamples : Measurable (fun z : unitIntervalCompact → Plane => fun t : LK =>
        (Real.sqrt (r : Real))⁻¹ • z (inK t.1)) := by
      apply measurable_pi_lambda
      intro t
      fun_prop
    have hrange : Measurable (fun z : unitIntervalCompact → Plane =>
        (finiteRange fun t : LK =>
          (Real.sqrt (r : Real))⁻¹ • z (inK t.1) : CompactPlane)) :=
      (@measurable_finiteRange Plane LK inferInstance inferInstance inferInstance
        inferInstance inferInstance instMeasurableSpaceCompactPlane
        instBorelSpaceCompactPlane).comp hsamples
    have hcompact : Measurable (fun z : unitIntervalCompact → Plane =>
        smulCompact (Real.sqrt (r : Real))
          (finiteImage LK hLK
            (fun t : K => (Real.sqrt (r : Real))⁻¹ • z (inK t)))) := by
      have hsmulMeas := measurable_smulCompact (Real.sqrt (r : Real))
      change @Measurable CompactPlane CompactPlane instMeasurableSpaceCompactPlane
        instMeasurableSpaceCompactPlane (smulCompact (Real.sqrt (r : Real))) at hsmulMeas
      simpa only [finiteImage_eq_finiteRange, Function.comp_def] using
        hsmulMeas.comp hrange
    exact (measurable_translateCompact_pair.comp
      ((measurable_neg.comp (measurable_pi_apply oneU)).prodMk hcompact)).prodMk
        measurable_const
  have mg1 : Measurable g1 := by
    exact measurable_const.prodMk (measurable_pi_apply oneU)
  have mg2 : ∀ n, Measurable (g2 n) := by
    intro n
    let LL := finiteCompactApprox (T := L) n
    let hLL : (LL : Set L).Finite := finite_finiteCompactApprox (T := L) n
    letI : Fintype LL := hLL.fintype
    have hsamples : Measurable (fun z : unitIntervalCompact → Plane => fun t : LL =>
        (Real.sqrt (s : Real))⁻¹ • z (inL t.1)) := by
      apply measurable_pi_lambda
      intro t
      fun_prop
    have hrange : Measurable (fun z : unitIntervalCompact → Plane =>
        (finiteRange fun t : LL =>
          (Real.sqrt (s : Real))⁻¹ • z (inL t.1) : CompactPlane)) :=
      (@measurable_finiteRange Plane LL inferInstance inferInstance inferInstance
        inferInstance inferInstance instMeasurableSpaceCompactPlane
        instBorelSpaceCompactPlane).comp hsamples
    have hcompact : Measurable (fun z : unitIntervalCompact → Plane =>
        smulCompact (Real.sqrt (s : Real))
          (finiteImage LL hLL
            (fun t : L => (Real.sqrt (s : Real))⁻¹ • z (inL t)))) := by
      have hsmulMeas := measurable_smulCompact (Real.sqrt (s : Real))
      change @Measurable CompactPlane CompactPlane instMeasurableSpaceCompactPlane
        instMeasurableSpaceCompactPlane (smulCompact (Real.sqrt (s : Real))) at hsmulMeas
      simpa only [finiteImage_eq_finiteRange, Function.comp_def] using
        hsmulMeas.comp hrange
    exact hcompact.prodMk measurable_const
  let g (n : Nat) : Fin 3 →
      (unitIntervalCompact → Plane) → CompactPlane × Plane :=
    ![g0 n, g1, g2 n]
  have hg : ∀ n i, Measurable (g n i) := by
    intro n i
    fin_cases i
    · simpa [g] using mg0 n
    · simpa [g] using mg1
    · simpa [g] using mg2 n
  let X : Nat → Fin 3 → Omega → CompactPlane × Plane := fun n i omega =>
    g n i (proc i omega)
  let x : Fin 3 → Omega → CompactPlane × Plane :=
    ![fun omega => (A omega, 0), fun omega => (zeroCompact, Z omega),
      fun omega => (B omega, 0)]
  have hX0 : ∀ n, X n 0 = fun omega => (FX n omega, 0) := by
    intro n
    funext omega
    simp [X, g, g0, proc, starts, lengths, FX, inK, oneU,
      BrownianImages.intervalRescale]
  have hX1 : ∀ n, X n 1 = fun omega => (zeroCompact, Z omega) := by
    intro n
    funext omega
    simp [X, g, g1, proc, starts, lengths, Z, oneU]
  have hX2 : ∀ n, X n 2 = fun omega => (FY n omega, 0) := by
    intro n
    funext omega
    simp [X, g, g2, proc, starts, lengths, FY, inL,
      BrownianImages.intervalRescale]
  have hX : ∀ n i, AEMeasurable (X n i) P := by
    intro n i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hX0 n]
      exact (hFX n).prodMk aemeasurable_const
    · refine Fin.cases ?_ (fun i => ?_) i
      · change AEMeasurable (X n (1 : Fin 3)) P
        rw [hX1 n]
        exact aemeasurable_const.prodMk hZ
      · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        change AEMeasurable (X n (2 : Fin 3)) P
        rw [hX2 n]
        exact (hFY n).prodMk aemeasurable_const
  have hx : ∀ i, AEMeasurable (x i) P := by
    intro i
    fin_cases i
    · simpa [x] using hA.prodMk aemeasurable_const
    · simpa [x] using aemeasurable_const.prodMk hZ
    · simpa [x] using hB.prodMk aemeasurable_const
  have hlim : ∀ i, ∀ᵐ omega ∂P,
      Tendsto (fun n => X n i omega) atTop (nhds (x i omega)) := by
    intro i
    fin_cases i
    · filter_upwards [hFXlim] with omega homega
      simpa [hX0, x] using homega.prodMk_nhds tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun omega => by
        simp [hX1, x]
    · filter_upwards [hFYlim] with omega homega
      simpa [hX2, x] using homega.prodMk_nhds tendsto_const_nhds
  have hfinite : ∀ n, iIndepFun (X n) P := by
    intro n
    exact hproc.comp (g n) (hg n)
  have hall : iIndepFun x P := iIndepFun_of_ae_tendsto hX hx hlim hfinite
  constructor
  · have h02 := hall.indepFun (show (0 : Fin 3) ≠ 2 by decide)
    have hcomp := h02.comp measurable_fst measurable_fst
    change IndepFun A B P at hcomp
    simpa only [A, B] using hcomp
  · have hpair := hall.indepFun_prodMk₀ hx (0 : Fin 3) 2 1
      (by decide) (by decide)
    have hcomp := hpair.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
      measurable_snd
    change IndepFun (fun omega => (A omega, B omega)) Z P at hcomp
    simpa only [A, B, Z] using hcomp

/-- Almost surely, overlap of the two actual affine Brownian compact images is
exactly the right/left-centered overlap translated by the increment across the
intervening gap.  This removes the common spatial translation by the right
endpoint of the first host interval. -/
theorem IsPlanarBrownian.ae_tubeOverlapArea_affineCompactPieces_eq_gap
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (a : NNReal) {r q s : NNReal} (hr : r ≠ 0) (hs : s ≠ 0)
    (K L : NonemptyCompacts Real)
    (hK : (K : Set Real) ⊆ Set.Icc 0 1)
    (hL : (L : Set Real) ⊆ Set.Icc 0 1)
    {rho : Real} (hrho : 0 < rho) :
    ∀ᵐ omega ∂P,
      tubeOverlapArea rho (affineBrownianCompactPiece W a r K omega)
          (affineBrownianCompactPiece W (a + r + q) s L omega) =
        tubeOverlapArea rho
          (rightCenteredBrownianCompactPiece W a r K omega)
          (translateCompact (W (a + r + q) omega - W (a + r) omega)
            (centeredBrownianCompactPiece W (a + r + q) s L omega)) := by
  have hfirst := hW.ae_translate_dilate_rescaledBrownianCompactPiece
    (a := a) (r := r) (K := K) hr hK
  have hsecond := hW.ae_translate_dilate_rescaledBrownianCompactPiece
    (a := a + r + q) (r := s) (K := L) hs hL
  filter_upwards [hfirst, hsecond] with omega hfirstOmega hsecondOmega
  let A := rightCenteredBrownianCompactPiece W a r K omega
  let B := centeredBrownianCompactPiece W (a + r + q) s L omega
  have hactualA : affineBrownianCompactPiece W a r K omega =
      translateCompact (W (a + r) omega) A := by
    symm
    dsimp only [A]
    rw [rightCenteredBrownianCompactPiece, translateCompact_translate]
    have hshift : W (a + r) omega + (W a omega - W (a + r) omega) =
        W a omega := by abel
    rw [hshift]
    simpa only [centeredBrownianCompactPiece, smulCompact_eq_dilateCompact] using
      hfirstOmega
  have hactualB : affineBrownianCompactPiece W (a + r + q) s L omega =
      translateCompact (W (a + r + q) omega) B := by
    symm
    simpa only [B, centeredBrownianCompactPiece,
      smulCompact_eq_dilateCompact] using hsecondOmega
  have htranslateB : translateCompact (W (a + r + q) omega) B =
      translateCompact (W (a + r) omega)
        (translateCompact (W (a + r + q) omega - W (a + r) omega) B) := by
    rw [translateCompact_translate]
    congr 1
    abel
  rw [hactualA, hactualB, htranslateB,
    tubeOverlapArea_translate_both hrho]

/-! ### The Brownian bounded-density overlap estimate -/

/-- The overlap of compact Brownian pieces on opposite sides of a
nondegenerate temporal gap is integrable, provided their two tube areas are
integrable.  The first piece is centered at the right endpoint of its host
interval and the second at the left endpoint of its host interval, so the
only relative translation is the independent gap increment. -/
theorem IsPlanarBrownian.integrable_tubeOverlapArea_compactPieces_gap
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r q s : NNReal}
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
    Integrable (fun omega =>
      tubeOverlapArea rho
        (rightCenteredBrownianCompactPiece W a r K omega)
        (translateCompact (W (a + r + q) omega - W (a + r) omega)
          (centeredBrownianCompactPiece W (a + r + q) s L omega))) P := by
  let A : Omega → CompactPlane := rightCenteredBrownianCompactPiece W a r K
  let B : Omega → CompactPlane := centeredBrownianCompactPiece W (a + r + q) s L
  let Z : Omega → Plane := fun omega => W (a + r + q) omega - W (a + r) omega
  have hA : AEMeasurable A P :=
    hW.aemeasurable_rightCenteredBrownianCompactPiece a hr K
  have hB : AEMeasurable B P :=
    (measurable_smulCompact (Real.sqrt (s : Real))).comp_aemeasurable
      ((hW.intervalRescale (a + r + q) hs).aemeasurable_brownianImage L)
  have hZ : AEMeasurable Z P :=
    (JointMeasurability.aemeasurable_eval hW (a + r + q)).sub
      (JointMeasurability.aemeasurable_eval hW (a + r))
  have hind := hW.indepFun_compactPieces_gapIncrement (q := q) a hr hs K L hK hL
  have hgap : a + r < a + r + q :=
    lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hq)
  have hZlaw : P.map Z = volume.withDensity fun z =>
      ENNReal.ofReal (planarGaussianDensity q z) := by
    simpa only [Z, add_tsub_cancel_left] using
      hW.map_increment_eq_withDensity hgap
  exact integrable_tubeOverlapArea_translate_of_indep_boundedDensity hrho
    hA hB hZ hind.1 hind.2 hZlaw (measurable_planarGaussianDensity q)
    (planarGaussianDensity_nonneg q) (planarGaussianDensity_le q)
    (by simpa only [A] using hareaA) (by simpa only [B] using hareaB)

/-- Expected translated-overlap bound for two compact Brownian pieces around
a gap of duration `q`.  The exact density constant is `1 / (2πq)`. -/
theorem IsPlanarBrownian.integral_tubeOverlapArea_compactPieces_gap_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r q s : NNReal}
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
    (∫ omega, tubeOverlapArea rho
      (rightCenteredBrownianCompactPiece W a r K omega)
      (translateCompact (W (a + r + q) omega - W (a + r) omega)
        (centeredBrownianCompactPiece W (a + r + q) s L omega)) ∂P) ≤
      (2 * Real.pi * (q : Real))⁻¹ *
        ((∫ omega, tubeArea rho
            (rightCenteredBrownianCompactPiece W a r K omega) ∂P) *
          ∫ omega, tubeArea rho
            (centeredBrownianCompactPiece W (a + r + q) s L omega) ∂P) := by
  let A : Omega → CompactPlane := rightCenteredBrownianCompactPiece W a r K
  let B : Omega → CompactPlane := centeredBrownianCompactPiece W (a + r + q) s L
  let Z : Omega → Plane := fun omega => W (a + r + q) omega - W (a + r) omega
  have hA : AEMeasurable A P :=
    hW.aemeasurable_rightCenteredBrownianCompactPiece a hr K
  have hB : AEMeasurable B P :=
    (measurable_smulCompact (Real.sqrt (s : Real))).comp_aemeasurable
      ((hW.intervalRescale (a + r + q) hs).aemeasurable_brownianImage L)
  have hZ : AEMeasurable Z P :=
    (JointMeasurability.aemeasurable_eval hW (a + r + q)).sub
      (JointMeasurability.aemeasurable_eval hW (a + r))
  have hind := hW.indepFun_compactPieces_gapIncrement (q := q) a hr hs K L hK hL
  have hgap : a + r < a + r + q :=
    lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hq)
  have hZlaw : P.map Z = volume.withDensity fun z =>
      ENNReal.ofReal (planarGaussianDensity q z) := by
    simpa only [Z, add_tsub_cancel_left] using
      hW.map_increment_eq_withDensity hgap
  exact integral_tubeOverlapArea_translate_le_of_indep_boundedDensity hrho
    hA hB hZ hind.1 hind.2 hZlaw (measurable_planarGaussianDensity q)
    (planarGaussianDensity_nonneg q) (planarGaussianDensity_le q)
    (by simpa only [A] using hareaA) (by simpa only [B] using hareaB)

/-- Paper-scaled form of the compact-piece overlap estimate.  Its last four
hypotheses are exactly the first-moment (`q = 1` in the tube-moment theorem)
inputs for the two pieces: integrability and an `O(rho ^ alpha)` expectation
bound. -/
theorem IsPlanarBrownian.integral_tubeOverlapArea_compactPieces_gap_le_rpow
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {W : NNReal → Omega → Plane}
    (hW : IsPlanarBrownian W P) (a : NNReal) {r q s : NNReal}
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
      (rightCenteredBrownianCompactPiece W a r K omega)
      (translateCompact (W (a + r + q) omega - W (a + r) omega)
        (centeredBrownianCompactPiece W (a + r + q) s L omega)) ∂P) ≤
      (2 * Real.pi * (q : Real))⁻¹ * (CA * CB) * rho ^ (2 * alpha) := by
  have hbase := hW.integral_tubeOverlapArea_compactPieces_gap_le a hr hq hs K L
    hK hL hrho hareaA hareaB
  have hEA : 0 ≤ ∫ omega, tubeArea rho
      (rightCenteredBrownianCompactPiece W a r K omega) ∂P :=
    integral_nonneg fun omega => tubeArea_nonneg rho _
  have hEB : 0 ≤ ∫ omega, tubeArea rho
      (centeredBrownianCompactPiece W (a + r + q) s L omega) ∂P :=
    integral_nonneg fun omega => tubeArea_nonneg rho _
  have hupperA : 0 ≤ CA * rho ^ alpha := hEA.trans hmeanA
  have hprod :
      (∫ omega, tubeArea rho
        (rightCenteredBrownianCompactPiece W a r K omega) ∂P) *
          (∫ omega, tubeArea rho
            (centeredBrownianCompactPiece W (a + r + q) s L omega) ∂P) ≤
        (CA * rho ^ alpha) * (CB * rho ^ alpha) :=
    mul_le_mul hmeanA hmeanB hEB hupperA
  have hqpos : 0 < (q : Real) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hq)
  have hden : 0 ≤ (2 * Real.pi * (q : Real))⁻¹ := by positivity
  have hpow : rho ^ alpha * rho ^ alpha = rho ^ (2 * alpha) := by
    rw [← Real.rpow_add hrho]
    ring_nf
  calc
    (∫ omega, tubeOverlapArea rho
        (rightCenteredBrownianCompactPiece W a r K omega)
        (translateCompact (W (a + r + q) omega - W (a + r) omega)
          (centeredBrownianCompactPiece W (a + r + q) s L omega)) ∂P) ≤
        (2 * Real.pi * (q : Real))⁻¹ *
          ((∫ omega, tubeArea rho
              (rightCenteredBrownianCompactPiece W a r K omega) ∂P) *
            ∫ omega, tubeArea rho
              (centeredBrownianCompactPiece W (a + r + q) s L omega) ∂P) := hbase
    _ ≤ (2 * Real.pi * (q : Real))⁻¹ *
        ((CA * rho ^ alpha) * (CB * rho ^ alpha)) :=
      mul_le_mul_of_nonneg_left hprod hden
    _ = (2 * Real.pi * (q : Real))⁻¹ * (CA * CB) *
        (rho ^ alpha * rho ^ alpha) := by ring
    _ = (2 * Real.pi * (q : Real))⁻¹ * (CA * CB) * rho ^ (2 * alpha) := by
      rw [hpow]

end BrownianImages
