/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: the formal bridge from the
analytic smoothed-neighbourhood limit to singularity of compact Brownian image laws.

The weak probability-measure space does not expose a complete-metrizable instance in
the measurable-limit API.  For the tube sequence this causes no gap.
`Minkowski.TubeConvergence` proves that every term is supported in the fixed compact
one-thickening of the underlying compact set.  Prokhorov compactness then says that
this particular sequence converges exactly when it is Cauchy in the compatible
Levy--Prokhorov metric.  Its Cauchy event is Borel by a countable distance formula.
Thus pathwise convergence can be pushed through `brownianImageLaw`, and the full
Borel reconstruction map follows from the pathwise assertion alone.

`TubeReconstructionHypothesis` packages both analytic fields as a convenient interface;
its `imageLaw` field is a formal consequence of `pathwise`.  Independently,
`Minkowski.LimitClassifier` pulls back any Borel property of the limit without first
constructing the whole measurable limit map.

* `TubeReconstructsOccupation`: the exact pathwise assertion of
  `thm:minkowski-reconstruction`, with
  `tubeReconstructsOccupation_of_ae_cylinder_approximation` its almost-sure derivation
  from the finite-cylinder approximation.
* `TubeLimitExistsUnderImageLaw`: convergence existence under the compact-image law.
* `TubeReconstructsOccupation.imageLaw`: derive that image-law convergence from the
  pathwise assertion by Borel Cauchy detection and Prokhorov compactness.
* `exists_common_borel_tube_reconstruction`: a single Borel limit map for two image
  laws.
* `exists_common_borel_reconstruction_of_pathwise`: full occupation reconstruction
  from the two pathwise assertions alone.
* `exists_borel_reconstruction_of_pathwise`: the one-system reconstruction statement,
  the endpoint `audit_borel_reconstruction_of_pathwise`.
* `brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction`: descent of
  occupation-law singularity to compact-image-law singularity from pathwise convergence
  alone, the endpoint `audit_brownianImageLaw_mutuallySingular_of_pathwise`.
* `homogeneous_brownianImage_application_pair_of_pathwise`: the paired application,
  conditional on the two pathwise assertions.
-/
import BrownianImages.CompactImage
import BrownianImages.Minkowski.Tube
import BrownianImages.Minkowski.Limit
import BrownianImages.Minkowski.LimitClassifier
import BrownianImages.Minkowski.System
import BrownianImages.Minkowski.TubeConvergence
import BrownianImages.Minkowski.CylinderConvergence
import BrownianImages.NonLattice

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BoundedContinuousFunction NNReal Topology

namespace MinkowskiReconstruction

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The normalised tube probabilities of the compact Brownian image converge weakly
almost surely to the Brownian occupation measure.  Convergence in
`ProbabilityMeasure Plane` is weak convergence. -/
def TubeReconstructsOccupation (W : ℝ≥0 → Omega → Plane) (P : Measure Omega)
    (K : NonemptyCompacts ℝ) (mu : Measure ℝ) : Prop :=
  ∀ᵐ omega ∂P, Tendsto
    (fun n ↦ tubeProbabilitySeq n (brownianImage W K omega)) atTop
    (nhds (occupationProb W mu omega))

/-- Almost-sure cylinder ratios, shrinking weighted image diameters, and convergence
of the weighted anchor quadratures imply pathwise Minkowski reconstruction.  This is
the probability-space wrapper around the deterministic two-scale theorem
`tendsto_tubeProbability_of_cylinder_approximation`. -/
theorem tubeReconstructsOccupation_of_ae_cylinder_approximation
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane}
    {K : NonemptyCompacts ℝ} {mu : Measure ℝ}
    (I : Nat → Type*) [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    (F : Omega → (k : Nat) → I k → CompactPlane)
    (x0 : Omega → (k : Nat) → I k → Plane)
    (p : (k : Nat) → I k → Real)
    (hp : ∀ k i, 0 ≤ p k i) (hpsum : ∀ k, ∑ i, p k i = 1)
    (hunion : ∀ᵐ omega ∂P, ∀ k, compactUnion (F omega k) = brownianImage W K omega)
    (hanchor : ∀ᵐ omega ∂P, ∀ k i, x0 omega k i ∈ F omega k i)
    (hratio : ∀ᵐ omega ∂P, ∀ k i,
      Tendsto (fun n => tubeMassRatio (tubeRadius n) (F omega k) i) atTop
        (nhds (p k i)))
    (hdiam : ∀ᵐ omega ∂P, Tendsto
      (fun k => ∑ i, p k i * Metric.diam (F omega k i : Set Plane)) atTop
        (nhds 0))
    (hatomic : ∀ᵐ omega ∂P,
      ∀ (f : Plane →ᵇ Real) {L : NNReal}, LipschitzWith L f →
        Tendsto (fun k => ∑ i, p k i * f (x0 omega k i)) atTop
          (nhds (∫ x, f x ∂(occupationProb W mu omega : Measure Plane)))) :
    TubeReconstructsOccupation W P K mu := by
  filter_upwards [hunion, hanchor, hratio, hdiam, hatomic] with
    omega hunionOmega hanchorOmega hratioOmega hdiamOmega hatomicOmega
  change Tendsto
    (fun n => tubeProbability (tubeRadius n) (tubeRadius_pos n)
      (brownianImage W K omega)) atTop
    (nhds (occupationProb W mu omega))
  exact tendsto_tubeProbability_of_cylinder_approximation
    tubeRadius tubeRadius_pos tendsto_tubeRadius I (brownianImage W K omega)
    (F omega) (x0 omega) p hunionOmega hanchorOmega hp hpsum
    hratioOmega hdiamOmega (occupationProb W mu omega) hatomicOmega

/-- Almost every compact set under its Brownian image law has a weak tube limit.  This
is stated separately from `TubeReconstructsOccupation` as the image-law input to the
abstract measurable-limit theorem.  For the tube sequence it follows formally from
pathwise convergence via `TubeReconstructsOccupation.imageLaw`. -/
def TubeLimitExistsUnderImageLaw (W : ℝ≥0 → Omega → Plane) (P : Measure Omega)
    (K : NonemptyCompacts ℝ) : Prop :=
  ∀ᵐ F ∂brownianImageLaw W P K, ∃ nu : ProbabilityMeasure Plane,
    Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop (nhds nu)

/-- Prokhorov compactness and Borel detection of the Cauchy event push pathwise
tube convergence through the Brownian compact-image law. -/
theorem TubeReconstructsOccupation.imageLaw
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K : NonemptyCompacts ℝ} {mu : Measure ℝ}
    (hpath : TubeReconstructsOccupation W P K mu) :
    TubeLimitExistsUnderImageLaw W P K := by
  exact MinkowskiTubeConvergence.ae_tube_hasLimit_brownianImageLaw_of_ae_tendsto
    hW hpath

/-- The two explicit analytic inputs used by the formal reconstruction bridge. -/
structure TubeReconstructionHypothesis (W : ℝ≥0 → Omega → Plane)
    (P : Measure Omega) (K : NonemptyCompacts ℝ) (mu : Measure ℝ) : Prop where
  /-- Pathwise convergence to the occupation measure. -/
  pathwise : TubeReconstructsOccupation W P K mu
  /-- Almost-everywhere existence of the limit under the compact-image law. -/
  imageLaw : TubeLimitExistsUnderImageLaw W P K

/-- Two compact-image laws under which the tube sequence converges almost everywhere
have one common Borel reconstruction map.  The use of the sum of the two laws is
encapsulated by `Minkowski.Limit`. -/
theorem exists_common_borel_tube_reconstruction
    {Q1 Q2 : Measure CompactPlane}
    (hlim1 : ∀ᵐ F ∂Q1, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop (nhds nu))
    (hlim2 : ∀ᵐ F ∂Q2, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop (nhds nu)) :
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (∀ᵐ F ∂Q1, Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop
        (nhds (reconstruct F))) ∧
      ∀ᵐ F ∂Q2, Tendsto (fun n ↦ tubeProbabilitySeq n F) atTop
        (nhds (reconstruct F)) := by
  exact MinkowskiLimit.exists_common_measurable_reconstruction_of_ae_hasLimit
    measurable_tubeProbabilitySeq hlim1 hlim2

/-- Two instances of the analytic reconstruction hypothesis give a single Borel map
which reconstructs the corresponding occupation measure from each compact Brownian
image almost surely. -/
theorem exists_common_borel_reconstruction_of_hypotheses
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K1 K2 : NonemptyCompacts ℝ} {mu1 mu2 : Measure ℝ}
    (h1 : TubeReconstructionHypothesis W P K1 mu1)
    (h2 : TubeReconstructionHypothesis W P K2 mu2) :
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (fun omega ↦ reconstruct (brownianImage W K1 omega)) =ᵐ[P]
        occupationProb W mu1 ∧
      (fun omega ↦ reconstruct (brownianImage W K2 omega)) =ᵐ[P]
        occupationProb W mu2 := by
  obtain ⟨reconstruct, hmeas, hlim1, hlim2⟩ :=
    exists_common_borel_tube_reconstruction h1.imageLaw h2.imageLaw
  have hpath1 : ∀ᵐ omega ∂P, Tendsto
      (fun n ↦ tubeProbabilitySeq n (brownianImage W K1 omega)) atTop
      (nhds (reconstruct (brownianImage W K1 omega))) :=
    ae_of_ae_map (hW.aemeasurable_brownianImage K1) hlim1
  have hpath2 : ∀ᵐ omega ∂P, Tendsto
      (fun n ↦ tubeProbabilitySeq n (brownianImage W K2 omega)) atTop
      (nhds (reconstruct (brownianImage W K2 omega))) :=
    ae_of_ae_map (hW.aemeasurable_brownianImage K2) hlim2
  refine ⟨reconstruct, hmeas, ?_, ?_⟩
  · filter_upwards [hpath1, h1.pathwise] with omega hrec hoccupation
    exact tendsto_nhds_unique hrec hoccupation
  · filter_upwards [hpath2, h2.pathwise] with omega hrec hoccupation
    exact tendsto_nhds_unique hrec hoccupation

/-- The two pathwise tube limits alone give one Borel map which reconstructs the
corresponding occupation measure from either compact Brownian image almost surely. -/
theorem exists_common_borel_reconstruction_of_pathwise
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K1 K2 : NonemptyCompacts ℝ} {mu1 mu2 : Measure ℝ}
    (hpath1 : TubeReconstructsOccupation W P K1 mu1)
    (hpath2 : TubeReconstructsOccupation W P K2 mu2) :
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (fun omega ↦ reconstruct (brownianImage W K1 omega)) =ᵐ[P]
        occupationProb W mu1 ∧
      (fun omega ↦ reconstruct (brownianImage W K2 omega)) =ᵐ[P]
        occupationProb W mu2 := by
  exact exists_common_borel_reconstruction_of_hypotheses hW
    ⟨hpath1, hpath1.imageLaw hW⟩ ⟨hpath2, hpath2.imageLaw hW⟩

/-- A paper-shaped one-system wrapper: pathwise tube convergence produces a Borel
map on compact plane sets which recovers the occupation probability almost surely. -/
theorem exists_borel_reconstruction_of_pathwise
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K : NonemptyCompacts ℝ} {mu : Measure ℝ}
    (hpath : TubeReconstructsOccupation W P K mu) :
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (fun omega ↦ reconstruct (brownianImage W K omega)) =ᵐ[P]
        occupationProb W mu := by
  obtain ⟨reconstruct, hmeas, hrec, _⟩ :=
    exists_common_borel_reconstruction_of_pathwise hW hpath hpath
  exact ⟨reconstruct, hmeas, hrec⟩

/-- A Borel separator of two occupation laws can be read directly from the measurable
tube sequence.  Thus pathwise tube convergence alone transfers occupation-law mutual
singularity to compact-image-law mutual singularity; no measurable limit map and no
image-law convergence hypothesis are required. -/
theorem brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {K1 K2 : NonemptyCompacts ℝ} {mu1 mu2 : Measure ℝ}
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    (hpath1 : TubeReconstructsOccupation W P K1 mu1)
    (hpath2 : TubeReconstructsOccupation W P K2 mu2)
    (hoccupation : (occupationLaw W P mu1).MutuallySingular
      (occupationLaw W P mu2)) :
    (brownianImageLaw W P K1).MutuallySingular (brownianImageLaw W P K2) := by
  letI : BorelSpace (ProbabilityMeasure Plane) :=
    ⟨borel_probabilityMeasure_eq_giry.symm⟩
  obtain ⟨E, hE, hlaw1, hlaw2⟩ := hoccupation
  obtain ⟨A, hA, hclassifier⟩ :=
    MinkowskiLimitClassifier.exists_measurableSet_limit_classifier
      tubeProbabilitySeq measurable_tubeProbabilitySeq hE
  have hlaw1' : P ((occupationProb W mu1) ⁻¹' E) = 0 := by
    simpa only [occupationLaw,
      Measure.map_apply_of_aemeasurable (hW.aemeasurable_occupationProb mu1) hE]
      using hlaw1
  have hlaw2' : P ((occupationProb W mu2) ⁻¹' Eᶜ) = 0 := by
    simpa only [occupationLaw,
      Measure.map_apply_of_aemeasurable (hW.aemeasurable_occupationProb mu2) hE.compl]
      using hlaw2
  have hoccupation1 : ∀ᵐ omega ∂P, occupationProb W mu1 omega ∉ E := by
    rw [ae_iff]
    rw [show {omega | ¬occupationProb W mu1 omega ∉ E} =
      (occupationProb W mu1) ⁻¹' E by ext; simp]
    exact hlaw1'
  have hoccupation2 : ∀ᵐ omega ∂P, occupationProb W mu2 omega ∈ E := by
    rw [ae_iff]
    rw [show {omega | ¬occupationProb W mu2 omega ∈ E} =
      (occupationProb W mu2) ⁻¹' Eᶜ by ext; simp]
    exact hlaw2'
  have himage1 : ∀ᵐ omega ∂P, brownianImage W K1 omega ∉ A := by
    filter_upwards [hpath1, hoccupation1] with omega hlim hnot
    exact fun himage ↦ hnot ((hclassifier _ _ hlim).mp himage)
  have himage2 : ∀ᵐ omega ∂P, brownianImage W K2 omega ∈ A := by
    filter_upwards [hpath2, hoccupation2] with omega hlim hmem
    exact (hclassifier _ _ hlim).mpr hmem
  refine ⟨A, hA, ?_, ?_⟩
  · rw [brownianImageLaw, Measure.map_apply_of_aemeasurable
      (hW.aemeasurable_brownianImage K1) hA]
    rw [show (brownianImage W K1) ⁻¹' A =
      {omega | ¬brownianImage W K1 omega ∉ A} by ext; simp]
    exact ae_iff.mp himage1
  · rw [brownianImageLaw, Measure.map_apply_of_aemeasurable
      (hW.aemeasurable_brownianImage K2) hA.compl]
    rw [show (brownianImage W K2) ⁻¹' Aᶜ =
      {omega | ¬brownianImage W K2 omega ∈ A} by ext; simp]
    exact ae_iff.mp himage2

/-- Classifier form of the parameter-uniform homogeneous-versus-paired application.
Only the two pathwise tube reconstruction assertions remain as analytic hypotheses. -/
theorem homogeneous_brownianImage_application_pair_of_pathwise
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {KA : Set ℝ} {muA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) muA)
    {KB : Set ℝ} {muB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) muB)
    (hnl : Irrational
      (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2))
    (hconvA : TubeReconstructsOccupation W P hA.compactAttractor muA)
    (hconvB : TubeReconstructsOccupation W P hB.compactAttractor muB) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hB.compactAttractor) := by
  letI := hA.isProbabilityMeasure
  letI := hB.isProbabilityMeasure
  exact brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction
    hW hconvA hconvB
      (BrownianImages.homogeneous_application_pair hW hlam0 hlam hA hB hnl)

end MinkowskiReconstruction

end BrownianImages
