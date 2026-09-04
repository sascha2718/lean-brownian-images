/-
`sec:reconstruction`: the deterministic smoothed-neighbourhood construction used to recover an
occupation measure from a nonempty compact image.

The compact hyperspace is `NonemptyCompacts Plane`, with its Hausdorff metric.  For a positive
radius `r`, `tubeCutoff r F x` is `(1 - dist(x, F) / r)₊`, `tubeMass r F` is its integral against
planar Lebesgue measure, and `tubeProbability r F` is the corresponding normalized finite
measure.  The results in this file establish that the cut-off is jointly continuous, integrable,
and has strictly positive finite mass.  They also record the exact density formula for the
normalized probability measure.
-/
import BrownianImages.WeakBorel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Thickening

namespace BrownianImages

open MeasureTheory Filter Set TopologicalSpace
open scoped BoundedContinuousFunction ENNReal NNReal Topology

/-- The Hausdorff space of nonempty compact subsets of the plane. -/
abbrev CompactPlane := NonemptyCompacts Plane

instance : MeasurableSpace CompactPlane := borel CompactPlane

instance : BorelSpace CompactPlane := ⟨rfl⟩

/-- The triangular distance cut-off `(1 - dist(x, F) / r)₊`. -/
noncomputable def tubeCutoff (r : ℝ) (F : CompactPlane) (x : Plane) : ℝ :=
  max (1 - Metric.infDist x F / r) 0

set_option maxHeartbeats 800000 in
/-- Distance to a nonempty compact set, with the point and compact set in the order used by
`tubeCutoff`, is jointly continuous. -/
theorem continuous_infDist_compactPlane :
    Continuous fun p : CompactPlane × Plane => Metric.infDist p.2 p.1 := by
  exact (Metric.lipschitz_infDist (α := Plane)).continuous.comp continuous_swap

set_option maxHeartbeats 800000 in
/-- The tube cut-off is jointly continuous in the compact set and the spatial point. -/
theorem continuous_tubeCutoff (r : ℝ) :
    Continuous fun p : CompactPlane × Plane => tubeCutoff r p.1 p.2 := by
  exact (continuous_const.sub
    (continuous_infDist_compactPlane.div_const r)).max continuous_const

/-- For a fixed compact set, the tube cut-off is continuous in the spatial point. -/
theorem continuous_tubeCutoff_right (r : ℝ) (F : CompactPlane) :
    Continuous (tubeCutoff r F) := by
  change Continuous fun x : Plane => max (1 - Metric.infDist x F / r) 0
  exact (continuous_const.sub
    ((Metric.lipschitz_infDist_pt (F : Set Plane)).continuous.div_const r)).max continuous_const

/-- For a fixed point, the tube cut-off is continuous in the compact set. -/
theorem continuous_tubeCutoff_left (r : ℝ) (x : Plane) :
    Continuous fun F : CompactPlane => tubeCutoff r F x := by
  change Continuous fun F : CompactPlane => max (1 - Metric.infDist x F / r) 0
  exact (continuous_const.sub
    ((Metric.lipschitz_infDist_set x).continuous.div_const r)).max continuous_const

theorem tubeCutoff_nonneg (r : ℝ) (F : CompactPlane) (x : Plane) :
    0 ≤ tubeCutoff r F x := by
  simp [tubeCutoff]

theorem tubeCutoff_le_one {r : ℝ} (hr : 0 < r) (F : CompactPlane) (x : Plane) :
    tubeCutoff r F x ≤ 1 := by
  rw [tubeCutoff, max_le_iff]
  exact ⟨sub_le_self _ (div_nonneg Metric.infDist_nonneg hr.le), zero_le_one⟩

@[simp]
theorem tubeCutoff_of_mem {r : ℝ} {F : CompactPlane} {x : Plane}
    (hx : x ∈ F) : tubeCutoff r F x = 1 := by
  simp [tubeCutoff, Metric.infDist_zero_of_mem hx]

theorem tubeCutoff_pos_iff {r : ℝ} (hr : 0 < r) (F : CompactPlane) (x : Plane) :
    0 < tubeCutoff r F x ↔ Metric.infDist x F < r := by
  simp only [tubeCutoff, lt_max_iff, lt_sub_iff_add_lt, zero_add, div_lt_one hr]
  exact or_iff_left (lt_irrefl 0)

theorem tubeCutoff_eq_zero_iff {r : ℝ} (hr : 0 < r) (F : CompactPlane) (x : Plane) :
    tubeCutoff r F x = 0 ↔ r ≤ Metric.infDist x F := by
  constructor
  · intro hz
    by_contra h
    exact (ne_of_gt ((tubeCutoff_pos_iff hr F x).2 (lt_of_not_ge h))) hz
  · intro h
    apply le_antisymm
    · exact le_of_not_gt fun hpos => h.not_gt ((tubeCutoff_pos_iff hr F x).1 hpos)
    · exact tubeCutoff_nonneg r F x

/-- The support of the cut-off is contained in the closed `r`-neighbourhood of `F`. -/
theorem support_tubeCutoff_subset_cthickening {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    Function.support (tubeCutoff r F) ⊆ Metric.cthickening r (F : Set Plane) := by
  intro x hx
  have hpos : 0 < tubeCutoff r F x :=
    lt_of_le_of_ne (tubeCutoff_nonneg r F x) (Ne.symm hx)
  have hdist : Metric.infDist x F ≤ r := ((tubeCutoff_pos_iff hr F x).1 hpos).le
  change Metric.infEDist x (F : Set Plane) ≤ ENNReal.ofReal r
  rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top F.nonempty)]
  exact ENNReal.ofReal_le_ofReal hdist

/-- Membership in a closed thickening of a nonempty compact set can be read using the real-valued
point-to-set distance. -/
theorem mem_cthickening_compactPlane_iff {r : ℝ} (hr : 0 ≤ r) (F : CompactPlane)
    (x : Plane) :
    x ∈ Metric.cthickening r (F : Set Plane) ↔ Metric.infDist x F ≤ r := by
  change Metric.infEDist x (F : Set Plane) ≤ ENNReal.ofReal r ↔ _
  rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top F.nonempty),
    ENNReal.ofReal_le_ofReal_iff hr]
  rfl

/-- If `G` is Hausdorff-close to `F`, then the `r`-cutoff around `G` is supported in a fixed
slightly larger thickening of `F`. -/
theorem tubeCutoff_eq_zero_of_notMem_cthickening {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {F G : CompactPlane} (hFG : dist G F < δ) {x : Plane}
    (hx : x ∉ Metric.cthickening (r + δ) (F : Set Plane)) :
    tubeCutoff r G x = 0 := by
  have hx' : r + δ < Metric.infDist x F := by
    rw [mem_cthickening_compactPlane_iff (add_nonneg hr.le hδ.le)] at hx
    exact lt_of_not_ge hx
  have hfin : Metric.hausdorffEDist (G : Set Plane) F ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded G.nonempty F.nonempty
      G.isCompact.isBounded F.isCompact.isBounded
  have hdist : Metric.infDist x F ≤ Metric.infDist x G + dist G F := by
    simpa only [Metric.NonemptyCompacts.dist_eq] using
      (Metric.infDist_le_infDist_add_hausdorffDist (x := x) (s := (G : Set Plane))
        (t := (F : Set Plane)) hfin)
  apply (tubeCutoff_eq_zero_iff hr G x).2
  linarith

/-- For positive radius, the tube cut-off has compact support. -/
theorem hasCompactSupport_tubeCutoff {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    HasCompactSupport (tubeCutoff r F) := by
  have hsub : tsupport (tubeCutoff r F) ⊆ Metric.cthickening r (F : Set Plane) :=
    closure_minimal (support_tubeCutoff_subset_cthickening hr F) Metric.isClosed_cthickening
  exact F.isCompact.cthickening.of_isClosed_subset (isClosed_tsupport _) hsub

/-- The tube cut-off is Lebesgue integrable for every positive radius. -/
theorem integrable_tubeCutoff {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    Integrable (tubeCutoff r F) :=
  (continuous_tubeCutoff_right r F).integrable_of_hasCompactSupport
    (hasCompactSupport_tubeCutoff hr F)

/-- The smoothed tube mass `M_r(F)`. -/
noncomputable def tubeMass (r : ℝ) (F : CompactPlane) : ℝ :=
  ∫ x : Plane, tubeCutoff r F x

theorem tubeMass_nonneg (r : ℝ) (F : CompactPlane) : 0 ≤ tubeMass r F := by
  exact integral_nonneg fun x => tubeCutoff_nonneg r F x

/-- A nonempty compact set has strictly positive smoothed tube mass at every positive radius. -/
theorem tubeMass_pos {r : ℝ} (hr : 0 < r) (F : CompactPlane) : 0 < tubeMass r F := by
  obtain ⟨x, hx⟩ := F.nonempty
  apply (continuous_tubeCutoff_right r F).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_tubeCutoff hr F) (tubeCutoff_nonneg r F)
  rw [tubeCutoff_of_mem hx]
  exact one_ne_zero

/-- For a fixed positive radius, smoothed tube mass is continuous in the Hausdorff metric. -/
theorem continuous_tubeMass {r : ℝ} (hr : 0 < r) : Continuous (tubeMass r) := by
  rw [continuous_iff_continuousAt]
  intro F
  let K : Set Plane := Metric.cthickening (r + 1) (F : Set Plane)
  let bound : Plane → ℝ := K.indicator fun _ => 1
  have hK : IsCompact K := F.isCompact.cthickening
  have hbound_integrable : Integrable bound := by
    exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun G =>
      (continuous_tubeCutoff_right r G).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds F zero_lt_one] with G hG
    rw [Metric.mem_ball] at hG
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [bound, Set.indicator_of_mem hx, abs_of_nonneg
          (tubeCutoff_nonneg r G x), Real.norm_eq_abs]
        exact tubeCutoff_le_one hr G x
      · have hzero : tubeCutoff r G x = 0 := by
          exact tubeCutoff_eq_zero_of_notMem_cthickening hr zero_lt_one hG hx
        simp [bound, Set.indicator_of_notMem hx, hzero]
  · exact hbound_integrable
  · exact Filter.Eventually.of_forall fun x => (continuous_tubeCutoff_left r x).continuousAt

theorem measurable_tubeMass {r : ℝ} (hr : 0 < r) : Measurable (tubeMass r) :=
  (continuous_tubeMass hr).measurable

/-- The unnormalised tube measure, with density `tubeCutoff r F` against planar Lebesgue
measure. -/
noncomputable def tubeMeasure (r : ℝ) (F : CompactPlane) : Measure Plane :=
  volume.withDensity fun x => ENNReal.ofReal (tubeCutoff r F x)

/-- The total mass of `tubeMeasure` is the real integral `tubeMass`. -/
theorem tubeMeasure_apply_univ {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    tubeMeasure r F Set.univ = ENNReal.ofReal (tubeMass r F) := by
  rw [tubeMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_tubeCutoff hr F)
      (Filter.Eventually.of_forall fun x => tubeCutoff_nonneg r F x)]
  rfl

/-- The tube measure bundled as a finite measure. -/
noncomputable def tubeFiniteMeasure (r : ℝ) (hr : 0 < r) (F : CompactPlane) :
    FiniteMeasure Plane :=
  ⟨tubeMeasure r F,
    isFiniteMeasure_withDensity_ofReal (integrable_tubeCutoff hr F).hasFiniteIntegral⟩

/-- The bundled finite measure has exactly the real tube mass as its total mass. -/
theorem tubeFiniteMeasure_ennreal_mass {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    ((tubeFiniteMeasure r hr F).mass : ℝ≥0∞) = ENNReal.ofReal (tubeMass r F) := by
  rw [FiniteMeasure.ennreal_mass]
  exact tubeMeasure_apply_univ hr F

/-- Integrating against the unnormalised tube measure is the same as multiplying the integrand
by the tube cut-off and integrating against planar Lebesgue measure. -/
theorem integral_tubeFiniteMeasure {r : ℝ} (hr : 0 < r) (F : CompactPlane)
    (f : Plane → ℝ) :
    ∫ x, f x ∂(tubeFiniteMeasure r hr F : Measure Plane) =
      ∫ x, tubeCutoff r F x * f x := by
  change ∫ x, f x ∂tubeMeasure r F = _
  rw [tubeMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((continuous_tubeCutoff_right r F).measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => by simp) f]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [ENNReal.toReal_ofReal (tubeCutoff_nonneg r F x), smul_eq_mul]

/-- Integrals of a bounded continuous test function against the unnormalised tube measures vary
continuously with the compact set. -/
theorem continuous_integral_tubeFiniteMeasure {r : ℝ} (hr : 0 < r)
    (f : Plane →ᵇ ℝ) :
    Continuous fun F : CompactPlane =>
      ∫ x, f x ∂(tubeFiniteMeasure r hr F : Measure Plane) := by
  simp_rw [integral_tubeFiniteMeasure hr]
  rw [continuous_iff_continuousAt]
  intro F
  let K : Set Plane := Metric.cthickening (r + 1) (F : Set Plane)
  let bound : Plane → ℝ := K.indicator fun _ => ‖f‖
  have hK : IsCompact K := F.isCompact.cthickening
  have hbound_integrable : Integrable bound := by
    exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun G =>
      ((continuous_tubeCutoff_right r G).mul f.continuous).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds F zero_lt_one] with G hG
    rw [Metric.mem_ball] at hG
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [bound, Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (tubeCutoff_nonneg r G x)]
        calc
          tubeCutoff r G x * ‖f x‖ ≤ 1 * ‖f x‖ :=
            mul_le_mul_of_nonneg_right (tubeCutoff_le_one hr G x) (norm_nonneg _)
          _ ≤ ‖f‖ := by simpa using f.norm_coe_le_norm x
      · have hzero : tubeCutoff r G x = 0 := by
          exact tubeCutoff_eq_zero_of_notMem_cthickening hr zero_lt_one hG hx
        simp [bound, Set.indicator_of_notMem hx, hzero]
  · exact hbound_integrable
  · exact Filter.Eventually.of_forall fun x =>
      (continuous_tubeCutoff_left r x).continuousAt.mul_const (f x)

/-- The unnormalised tube finite measure depends continuously on the compact set in the weak
topology. -/
theorem continuous_tubeFiniteMeasure {r : ℝ} (hr : 0 < r) :
    Continuous (tubeFiniteMeasure r hr) := by
  exact FiniteMeasure.continuous_iff_forall_continuous_integral.mpr
    (continuous_integral_tubeFiniteMeasure hr)

theorem tubeFiniteMeasure_ne_zero {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    tubeFiniteMeasure r hr F ≠ 0 := by
  intro hzero
  have hmeasure : tubeMeasure r F = 0 := congrArg FiniteMeasure.toMeasure hzero
  have huniv := congrArg (fun μ : Measure Plane => μ Set.univ) hmeasure
  rw [tubeMeasure_apply_univ hr F] at huniv
  have : ENNReal.ofReal (tubeMass r F) = 0 := by simpa using huniv
  exact (not_le_of_gt (tubeMass_pos hr F)) (ENNReal.ofReal_eq_zero.mp this)

/-- The probability measure obtained by normalising the tube density. -/
noncomputable def tubeProbability (r : ℝ) (hr : 0 < r) (F : CompactPlane) :
    ProbabilityMeasure Plane :=
  (tubeFiniteMeasure r hr F).normalize

/-- At fixed positive radius, the normalized tube probability measure is a continuous, hence
Borel measurable, function of the compact set in the Hausdorff metric. -/
theorem continuous_tubeProbability {r : ℝ} (hr : 0 < r) :
    Continuous (tubeProbability r hr) := by
  rw [continuous_iff_continuousAt]
  intro F
  exact FiniteMeasure.tendsto_normalize_of_tendsto
    (continuous_tubeFiniteMeasure hr).continuousAt (tubeFiniteMeasure_ne_zero hr F)

theorem measurable_tubeProbability {r : ℝ} (hr : 0 < r) :
    Measurable (tubeProbability r hr) := by
  have h : @Measurable CompactPlane (ProbabilityMeasure Plane) (borel CompactPlane)
      (borel (ProbabilityMeasure Plane)) (tubeProbability r hr) := by
    letI : MeasurableSpace (ProbabilityMeasure Plane) := borel (ProbabilityMeasure Plane)
    haveI : BorelSpace (ProbabilityMeasure Plane) := ⟨rfl⟩
    exact (continuous_tubeProbability hr).measurable
  exact @Eq.ndrec (MeasurableSpace (ProbabilityMeasure Plane))
    (borel (ProbabilityMeasure Plane))
    (fun m => @Measurable CompactPlane (ProbabilityMeasure Plane) (borel CompactPlane) m
      (tubeProbability r hr)) h
    (inferInstance : MeasurableSpace (ProbabilityMeasure Plane))
    borel_probabilityMeasure_eq_giry

/-- The normalized tube probability is the tube measure divided by its finite positive mass. -/
theorem tubeProbability_toMeasure {r : ℝ} (hr : 0 < r) (F : CompactPlane) :
    (tubeProbability r hr F : Measure Plane) =
      (tubeFiniteMeasure r hr F).mass⁻¹ • tubeMeasure r F := by
  exact (tubeFiniteMeasure r hr F).toMeasure_normalize_eq_of_nonzero
    (tubeFiniteMeasure_ne_zero hr F)

/-- The explicit density formula from `eq:neighbourhood-measure-definition`. -/
theorem tubeProbability_apply {r : ℝ} (hr : 0 < r) (F : CompactPlane) {s : Set Plane}
    (hs : MeasurableSet s) :
    (tubeProbability r hr F : Measure Plane) s =
      (ENNReal.ofReal (tubeMass r F))⁻¹ *
        ∫⁻ x in s, ENNReal.ofReal (tubeCutoff r F x) := by
  rw [tubeProbability_toMeasure hr F, Measure.coe_nnreal_smul_apply, tubeMeasure,
    withDensity_apply _ hs, ENNReal.coe_inv
      ((tubeFiniteMeasure r hr F).mass_nonzero_iff.mpr (tubeFiniteMeasure_ne_zero hr F)),
    tubeFiniteMeasure_ennreal_mass hr F]

/-! ### The deterministic sequence used in Minkowski reconstruction -/

/-- The radius `e⁻ⁿ` used by the reconstruction sequence. -/
noncomputable def tubeRadius (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ))

theorem tubeRadius_pos (n : ℕ) : 0 < tubeRadius n :=
  Real.exp_pos _

/-- The reconstruction radii decrease to zero. -/
theorem tendsto_tubeRadius : Tendsto tubeRadius atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ Real.exp (-(n : ℝ))) atTop (nhds 0)
  simpa [Function.comp_def] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- The `n`th normalised smoothed-neighbourhood approximation associated with a compact set. -/
noncomputable def tubeProbabilitySeq (n : ℕ) (F : CompactPlane) : ProbabilityMeasure Plane :=
  tubeProbability (tubeRadius n) (tubeRadius_pos n) F

theorem continuous_tubeProbabilitySeq (n : ℕ) : Continuous (tubeProbabilitySeq n) :=
  continuous_tubeProbability (tubeRadius_pos n)

theorem measurable_tubeProbabilitySeq (n : ℕ) : Measurable (tubeProbabilitySeq n) :=
  measurable_tubeProbability (tubeRadius_pos n)

end BrownianImages
