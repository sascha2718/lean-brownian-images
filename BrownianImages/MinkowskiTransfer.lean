/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: the measurable descent from
occupation-measure laws to compact-range laws.

The analytic part of `thm:minkowski-reconstruction` constructs a Borel map from a
compact planar set to a probability measure and proves that it recovers the occupation
measure almost surely.  Once those two facts are available, the set-level singularity
statement is purely measure theoretic.  A separating set for the reconstructed laws
pulls back to a separating set for the original laws.

* `MinkowskiTransfer.mutuallySingular_of_map`: singularity of two pushforwards under a
  measurable map implies singularity of the original measures.
* `MinkowskiTransfer.mutuallySingular_laws_of_ae_reconstruction`: the corresponding
  statement for random variables reconstructed almost surely.
* `MinkowskiTransfer.rangeLaw_mutuallySingular_of_reconstructs_occupation`: the wrapper
  used for Brownian compact ranges and their occupation measures.
-/
import BrownianImages.Defs

namespace BrownianImages

open MeasureTheory
open scoped NNReal

namespace MinkowskiTransfer

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- If the images of two measures under a measurable map are mutually singular, then
the original measures are mutually singular.  The separating measurable set is the
preimage of a separating set for the image measures. -/
theorem mutuallySingular_of_map {mu nu : Measure X} {reconstruct : X → Y}
    (hreconstruct : Measurable reconstruct)
    (hsep : (mu.map reconstruct).MutuallySingular (nu.map reconstruct)) :
    mu.MutuallySingular nu := by
  obtain ⟨s, hs, hmus, hnus⟩ := hsep
  refine ⟨reconstruct ⁻¹' s, hs.preimage hreconstruct, ?_, ?_⟩
  · rwa [Measure.map_apply hreconstruct hs] at hmus
  · rw [← Set.preimage_compl, ← Measure.map_apply hreconstruct hs.compl]
    exact hnus

variable {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]

/-- Almost-sure reconstruction transfers mutual singularity from the reconstructed
laws to the original laws.  The two random variables may live on different probability
spaces, and no probability assumption on the base measures is needed for the descent. -/
theorem mutuallySingular_laws_of_ae_reconstruction
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    {range1 : Omega1 → X} {range2 : Omega2 → X}
    {reconstructed1 : Omega1 → Y} {reconstructed2 : Omega2 → Y}
    {reconstruct : X → Y} (hreconstruct : Measurable reconstruct)
    (hrange1 : AEMeasurable range1 P1) (hrange2 : AEMeasurable range2 P2)
    (hrec1 : (fun omega ↦ reconstruct (range1 omega)) =ᵐ[P1] reconstructed1)
    (hrec2 : (fun omega ↦ reconstruct (range2 omega)) =ᵐ[P2] reconstructed2)
    (hsep : (P1.map reconstructed1).MutuallySingular (P2.map reconstructed2)) :
    (P1.map range1).MutuallySingular (P2.map range2) := by
  change (reconstruct ∘ range1) =ᵐ[P1] reconstructed1 at hrec1
  change (reconstruct ∘ range2) =ᵐ[P2] reconstructed2 at hrec2
  apply mutuallySingular_of_map hreconstruct
  rw [AEMeasurable.map_map_of_aemeasurable hreconstruct.aemeasurable hrange1,
    AEMeasurable.map_map_of_aemeasurable hreconstruct.aemeasurable hrange2,
    Measure.map_congr hrec1, Measure.map_congr hrec2]
  exact hsep

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Paper-shaped form of the measurable descent.  Here `RangeSpace` is to be
instantiated with the measurable hyperspace of compact subsets of the plane,
`range1` and `range2` with the two Brownian image sets, and `reconstruct` with the
normalised-sausage limit from `thm:minkowski-reconstruction`.

If reconstruction returns the two occupation measures almost surely, singularity of
their occupation laws implies singularity of the compact-range laws. -/
theorem rangeLaw_mutuallySingular_of_reconstructs_occupation
    {RangeSpace : Type*} [MeasurableSpace RangeSpace] {P : Measure Omega}
    {W : ℝ≥0 → Omega → Plane} {mu1 mu2 : Measure ℝ}
    {range1 range2 : Omega → RangeSpace}
    {reconstruct : RangeSpace → ProbabilityMeasure Plane}
    (hreconstruct : Measurable reconstruct)
    (hrange1 : AEMeasurable range1 P) (hrange2 : AEMeasurable range2 P)
    (hrec1 : (fun omega ↦ reconstruct (range1 omega)) =ᵐ[P] occupationProb W mu1)
    (hrec2 : (fun omega ↦ reconstruct (range2 omega)) =ᵐ[P] occupationProb W mu2)
    (hsep : (occupationLaw W P mu1).MutuallySingular (occupationLaw W P mu2)) :
    (P.map range1).MutuallySingular (P.map range2) := by
  apply mutuallySingular_laws_of_ae_reconstruction hreconstruct hrange1 hrange2 hrec1 hrec2
  simpa only [occupationLaw] using hsep

end MinkowskiTransfer

end BrownianImages
