/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: measurability of the weak limit
used to define the reconstruction map.

The normalised neighbourhoods give measurable maps into `ProbabilityMeasure Plane`.  Their
limit is taken in the weak topology, whereas `ProbabilityMeasure Plane` initially
carries Mathlib's Giry measurable structure.  `borel_probabilityMeasure_eq_giry`
identifies the two structures, so the measurable-limit theorem for metrizable Borel
spaces applies to the weak limit.

* `MinkowskiLimit.exists_measurable_reconstruction_of_ae_hasLimit`: choose a measurable
  limit when only almost-everywhere existence is given.
* `MinkowskiLimit.exists_common_measurable_reconstruction_of_ae_hasLimit`: use the sum
  of two laws to choose one map which is a limit under both.
-/
import BrownianImages.WeakBorel
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

namespace BrownianImages

open Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace MinkowskiLimit

local instance : BorelSpace (ProbabilityMeasure Plane) :=
  ⟨borel_probabilityMeasure_eq_giry.symm⟩

variable {X : Type*} [MeasurableSpace X]

/-- If a measurable sequence has some weak limit almost everywhere, one can choose a
single measurable map which is that limit almost everywhere. -/
theorem exists_measurable_reconstruction_of_ae_hasLimit {Q : Measure X}
    {f : ℕ → X → ProbabilityMeasure Plane} (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂Q, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ f n x) atTop (nhds nu)) :
    ∃ reconstruct : X → ProbabilityMeasure Plane, Measurable reconstruct ∧
      ∀ᵐ x ∂Q, Tendsto (fun n ↦ f n x) atTop (nhds (reconstruct x)) :=
  measurable_limit_of_tendsto_metrizable_ae
    (L := atTop) (fun n ↦ (hf n).aemeasurable) hlim

/-- If the same measurable sequence has a weak limit almost everywhere under each of
two measures, there is one measurable reconstruction map which is the limit under both.
The proof applies the measurable-limit theorem to `Q1 + Q2`. -/
theorem exists_common_measurable_reconstruction_of_ae_hasLimit
    {Q1 Q2 : Measure X} {f : ℕ → X → ProbabilityMeasure Plane}
    (hf : ∀ n, Measurable (f n))
    (hlim1 : ∀ᵐ x ∂Q1, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ f n x) atTop (nhds nu))
    (hlim2 : ∀ᵐ x ∂Q2, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ f n x) atTop (nhds nu)) :
    ∃ reconstruct : X → ProbabilityMeasure Plane, Measurable reconstruct ∧
      (∀ᵐ x ∂Q1, Tendsto (fun n ↦ f n x) atTop (nhds (reconstruct x))) ∧
      ∀ᵐ x ∂Q2, Tendsto (fun n ↦ f n x) atTop (nhds (reconstruct x)) := by
  have hsum : ∀ᵐ x ∂Q1 + Q2, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ f n x) atTop (nhds nu) :=
    ae_add_measure_iff.mpr ⟨hlim1, hlim2⟩
  obtain ⟨reconstruct, hmeas, hconv⟩ :=
    exists_measurable_reconstruction_of_ae_hasLimit hf hsum
  exact ⟨reconstruct, hmeas, (ae_add_measure_iff.mp hconv).1,
    (ae_add_measure_iff.mp hconv).2⟩

end MinkowskiLimit

end BrownianImages
