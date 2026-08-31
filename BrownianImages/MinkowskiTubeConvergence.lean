/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: compactness and Borel
detectability of convergence of the deterministic tube-probability sequence.

For a fixed nonempty compact set `F`, every member of the tube sequence is
supported by the compact set `Metric.cthickening 1 F`.  Prokhorov's theorem
therefore places the whole sequence in a compact subset of the weak space of
probability measures.  Consequently the sequence converges weakly exactly when
its image in the compatible Levy--Prokhorov metric is Cauchy.  The latter is a
Borel property of `F`, by the usual countable Cauchy criterion.
-/
import BrownianImages.CompactImage
import BrownianImages.MinkowskiTube
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace BrownianImages

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace MinkowskiTubeConvergence

/-- The tube sequence, viewed in the Levy--Prokhorov metric which metrizes weak
convergence on the plane. -/
noncomputable def levyTubeProbabilitySeq (n : ℕ) (F : CompactPlane) :
    LevyProkhorov (ProbabilityMeasure Plane) :=
  LevyProkhorov.ofMeasure (tubeProbabilitySeq n F)

theorem continuous_levyTubeProbabilitySeq (n : ℕ) :
    Continuous (levyTubeProbabilitySeq n) :=
  LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
    (continuous_tubeProbabilitySeq n)

/-- The compact sets whose tube sequence is Cauchy in the Levy--Prokhorov
metric. -/
def tubeCauchySet : Set CompactPlane :=
  {F | CauchySeq (fun n ↦ levyTubeProbabilitySeq n F)}

/-- Cauchyness of the tube sequence is a Borel property of the compact set. -/
theorem measurableSet_tubeCauchySet : MeasurableSet tubeCauchySet := by
  let A : Set CompactPlane := ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n},
    {F | dist (levyTubeProbabilitySeq n.1 F) (levyTubeProbabilitySeq N F) <
      1 / ((k : ℝ) + 1)}
  have hA : MeasurableSet A := by
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iUnion
    intro N
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_lt
      ((continuous_levyTubeProbabilitySeq n.1).dist
        (continuous_levyTubeProbabilitySeq N)).measurable measurable_const
  suffices tubeCauchySet = A by simpa [this] using hA
  ext F
  simp only [tubeCauchySet, A, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro h k
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 h) _ hpos
    exact ⟨N, fun n ↦ hN n.1 n.2⟩
  · intro h
    apply Metric.cauchySeq_iff'.2
    intro epsilon hepsilon
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hepsilon
    obtain ⟨N, hN⟩ := h k
    exact ⟨N, fun n hn ↦ (hN ⟨n, hn⟩).trans hk⟩

theorem tubeRadius_le_one (n : ℕ) : tubeRadius n ≤ 1 := by
  rw [tubeRadius, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))

/-- Every member of the tube sequence gives zero mass to the complement of the
fixed compact one-thickening of `F`. -/
theorem tubeProbabilitySeq_compl_cthickening_one (n : ℕ) (F : CompactPlane) :
    (tubeProbabilitySeq n F : Measure Plane)
      (Metric.cthickening 1 (F : Set Plane))ᶜ = 0 := by
  rw [tubeProbabilitySeq, tubeProbability_apply (tubeRadius_pos n) F
    Metric.isClosed_cthickening.measurableSet.compl]
  suffices ∫⁻ x in (Metric.cthickening 1 (F : Set Plane))ᶜ,
      ENNReal.ofReal (tubeCutoff (tubeRadius n) F x) = 0 by simp [this]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem
    Metric.isClosed_cthickening.measurableSet.compl] with x hx
  simp only [Set.mem_compl_iff, mem_cthickening_compactPlane_iff zero_le_one] at hx
  change ENNReal.ofReal (tubeCutoff (tubeRadius n) F x) = (0 : ℝ≥0∞)
  have hzero : tubeCutoff (tubeRadius n) F x = 0 :=
    (tubeCutoff_eq_zero_iff (tubeRadius_pos n) F x).2
      ((tubeRadius_le_one n).trans (le_of_not_ge hx))
  simp [hzero]

/-- Prokhorov compactness for all probability measures supported by the fixed
one-thickening of `F`. -/
theorem isCompact_tubeSupportSet (F : CompactPlane) :
    IsCompact {nu : ProbabilityMeasure Plane |
      (nu : Measure Plane) (Metric.cthickening 1 (F : Set Plane))ᶜ ≤ 0} := by
  simpa using
    (isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := fun _ ↦ 0) (K := fun _ ↦ Metric.cthickening 1 (F : Set Plane))
      tendsto_const_nhds (fun _ ↦ F.isCompact.cthickening) (Or.inr monotone_const))

/-- At a fixed compact set, Cauchyness in the Levy--Prokhorov metric is
equivalent to existence of a weak limit.  Compact support supplies the missing
completeness for this particular sequence. -/
theorem mem_tubeCauchySet_iff_exists_tendsto (F : CompactPlane) :
    F ∈ tubeCauchySet ↔ ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop (nhds nu) := by
  constructor
  · intro hCauchy
    let S : Set (ProbabilityMeasure Plane) :=
      {nu | (nu : Measure Plane) (Metric.cthickening 1 (F : Set Plane))ᶜ ≤ 0}
    have hcompact : IsCompact S := isCompact_tubeSupportSet F
    have hmem : ∀ n, tubeProbabilitySeq n F ∈ S := by
      intro n
      exact (tubeProbabilitySeq_compl_cthickening_one n F).le
    have hcompactLevy : IsCompact (LevyProkhorov.ofMeasure '' S) :=
      hcompact.image LevyProkhorov.continuous_ofMeasure_probabilityMeasure
    obtain ⟨eta, heta, hlim⟩ := hcompactLevy.isSeqCompact.exists_tendsto
      (fun n ↦ ⟨tubeProbabilitySeq n F, hmem n, rfl⟩) hCauchy
    refine ⟨LevyProkhorov.toMeasure eta, ?_⟩
    exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto eta).comp hlim
  · rintro ⟨nu, hlim⟩
    exact ((LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto nu).comp
      hlim).cauchySeq

/-- Almost-sure pathwise convergence of the tube sequence pushes through a
compact-image law.  The Borel Cauchy event and compact support are what make the
reverse direction of the map argument available. -/
theorem ae_tube_hasLimit_brownianImageLaw_of_ae_tendsto
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K : NonemptyCompacts ℝ} {limit : Omega → ProbabilityMeasure Plane}
    (hlim : ∀ᵐ omega ∂P, Tendsto
      (fun n ↦ tubeProbabilitySeq n (brownianImage W K omega)) atTop
      (nhds (limit omega))) :
    ∀ᵐ F ∂brownianImageLaw W P K, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop (nhds nu) := by
  have hsource : ∀ᵐ omega ∂P, brownianImage W K omega ∈ tubeCauchySet := by
    filter_upwards [hlim] with omega homega
    exact (mem_tubeCauchySet_iff_exists_tendsto _).2 ⟨limit omega, homega⟩
  have himage : ∀ᵐ F ∂brownianImageLaw W P K, F ∈ tubeCauchySet := by
    rw [brownianImageLaw]
    exact (ae_map_iff (hW.aemeasurable_brownianImage K)
      measurableSet_tubeCauchySet).2 hsource
  filter_upwards [himage] with F hF
  exact (mem_tubeCauchySet_iff_exists_tendsto F).1 hF

end MinkowskiTubeConvergence

end BrownianImages
