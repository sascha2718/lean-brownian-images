/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: measurability of the weak limit
used to define the reconstruction map.

The normalised sausages give measurable maps into `ProbabilityMeasure Plane`.  Their
limit is taken in the weak topology, whereas `ProbabilityMeasure Plane` initially
carries Mathlib's Giry measurable structure.  `borel_probabilityMeasure_eq_giry`
identifies the two structures.  The standard measurable-limit theorem for metrizable
Borel spaces can therefore be applied to the weak limit.

* `MinkowskiLimit.aemeasurable_limit_of_ae_tendsto`: an almost-everywhere weak limit is
  almost everywhere measurable.
* `MinkowskiLimit.exists_measurable_reconstruction_of_ae_tendsto`: replace a specified
  almost-everywhere limit by a measurable map.
* `MinkowskiLimit.exists_measurable_reconstruction_of_ae_hasLimit`: choose a measurable
  limit when only almost-everywhere existence is given.
* `MinkowskiLimit.exists_common_measurable_reconstruction_of_ae_hasLimit`: use the sum
  of two laws to choose one map which is a limit under both.
* `MinkowskiLimit.exists_common_measurable_reconstruction_of_ae_tendsto`: the same
  common map agrees almost everywhere with two specified limits.
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

/-- A specified almost-everywhere weak limit of measurable probability-measure-valued
maps is almost everywhere measurable.  The local `BorelSpace` instance records that
the weak Borel structure is the Giry structure used by `ProbabilityMeasure Plane`. -/
theorem aemeasurable_limit_of_ae_tendsto {Q : Measure X}
    {f : ℕ → X → ProbabilityMeasure Plane} {limit : X → ProbabilityMeasure Plane}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂Q, Tendsto (fun n ↦ f n x) atTop (nhds (limit x))) :
    AEMeasurable limit Q :=
  aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hf n).aemeasurable) hlim

/-- A specified almost-everywhere weak limit has a measurable representative.  This is
the Borel reconstruction map used to pull separating events back to the hyperspace. -/
theorem exists_measurable_reconstruction_of_ae_tendsto {Q : Measure X}
    {f : ℕ → X → ProbabilityMeasure Plane} {limit : X → ProbabilityMeasure Plane}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂Q, Tendsto (fun n ↦ f n x) atTop (nhds (limit x))) :
    ∃ reconstruct : X → ProbabilityMeasure Plane,
      Measurable reconstruct ∧ reconstruct =ᵐ[Q] limit := by
  let hmeas := aemeasurable_limit_of_ae_tendsto hf hlim
  exact ⟨hmeas.mk limit, hmeas.measurable_mk, hmeas.ae_eq_mk.symm⟩

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

/-- Two almost-everywhere limits of the same measurable sequence have one measurable
representative.  It agrees with the first limit under `Q1` and with the second under
`Q2`; uniqueness of weak limits supplies both equalities. -/
theorem exists_common_measurable_reconstruction_of_ae_tendsto
    {Q1 Q2 : Measure X} {f : ℕ → X → ProbabilityMeasure Plane}
    {limit1 limit2 : X → ProbabilityMeasure Plane} (hf : ∀ n, Measurable (f n))
    (hlim1 : ∀ᵐ x ∂Q1, Tendsto (fun n ↦ f n x) atTop (nhds (limit1 x)))
    (hlim2 : ∀ᵐ x ∂Q2, Tendsto (fun n ↦ f n x) atTop (nhds (limit2 x))) :
    ∃ reconstruct : X → ProbabilityMeasure Plane, Measurable reconstruct ∧
      reconstruct =ᵐ[Q1] limit1 ∧ reconstruct =ᵐ[Q2] limit2 := by
  have hhas1 : ∀ᵐ x ∂Q1, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ f n x) atTop (nhds nu) := by
    filter_upwards [hlim1] with x hx
    exact ⟨limit1 x, hx⟩
  have hhas2 : ∀ᵐ x ∂Q2, ∃ nu : ProbabilityMeasure Plane,
      Tendsto (fun n ↦ f n x) atTop (nhds nu) := by
    filter_upwards [hlim2] with x hx
    exact ⟨limit2 x, hx⟩
  obtain ⟨reconstruct, hmeas, hrec1, hrec2⟩ :=
    exists_common_measurable_reconstruction_of_ae_hasLimit hf hhas1 hhas2
  refine ⟨reconstruct, hmeas, ?_, ?_⟩
  · filter_upwards [hrec1, hlim1] with x hrec hlim
    exact tendsto_nhds_unique hrec hlim
  · filter_upwards [hrec2, hlim2] with x hrec hlim
    exact tendsto_nhds_unique hrec hlim

end MinkowskiLimit

end BrownianImages
