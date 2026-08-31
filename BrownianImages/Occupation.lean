/-
`sec:introduction`: the occupation measure `ν = W_*μ` as a random point of `𝒫(ℝ²)`.

The paper takes the law of `ν` on the space of Borel probability measures on the plane.
Two things have to hold for that to be the object Lean builds: the path has to be
measurable, so that `Measure.map` is the pushforward and not the junk value it returns
otherwise, and the pushforward has to be a probability measure.  Both come from the
almost sure continuity of the Brownian paths, which is why `IsPlanarBrownian` is stated
with `IsBrownianReal`.

* `IsPlanarBrownian.ae_continuous`: almost every path is continuous as a map into the
  plane.
* `measurable_pathMap`: a continuous path gives a measurable time map.
* `IsPlanarBrownian.ae_isProbabilityMeasure_occupation`: almost surely the occupation
  measure of a probability measure has total mass one.
-/
import BrownianImages.Defs

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- A map into the plane is continuous as soon as both coordinates are. -/
theorem continuous_plane_of_coord {α : Type*} [TopologicalSpace α] {f : α → Plane}
    (h : ∀ i : Fin 2, Continuous (fun t => f t i)) : Continuous f := by
  have hpi : Continuous (fun t => (EuclideanSpace.equiv (Fin 2) ℝ) (f t)) := continuous_pi h
  have := (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp hpi
  simpa [Function.comp_def] using this

/-- Almost every planar Brownian path is continuous. -/
theorem IsPlanarBrownian.ae_continuous (hW : IsPlanarBrownian W P) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => W t ω) := by
  have h : ∀ᵐ ω ∂P, ∀ i : Fin 2, Continuous (fun t : ℝ≥0 => W t ω i) :=
    ae_all_iff.mpr fun i => (hW.coord i).cont
  filter_upwards [h] with ω hω
  exact continuous_plane_of_coord hω

omit [MeasurableSpace Ω] P in
/-- A continuous path gives a measurable time map, which is what `occupation` pushes
`μ` forward along. -/
theorem measurable_pathMap {ω : Ω} (h : Continuous (fun t : ℝ≥0 => W t ω)) :
    Measurable (fun t : ℝ => W t.toNNReal ω) :=
  (h.comp continuous_real_toNNReal).measurable

/-- Almost surely the occupation measure of a probability measure is a probability
measure, so `occupationProb` agrees with `occupation` almost surely and the fallback in
its definition never enters a conclusion. -/
theorem IsPlanarBrownian.ae_isProbabilityMeasure_occupation (hW : IsPlanarBrownian W P)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂P, IsProbabilityMeasure (occupation W μ ω) := by
  filter_upwards [hW.ae_continuous] with ω hω
  exact Measure.isProbabilityMeasure_map (measurable_pathMap hω).aemeasurable

/-- Consequently `occupationProb` is almost surely the occupation measure itself. -/
theorem IsPlanarBrownian.ae_occupationProb_toMeasure (hW : IsPlanarBrownian W P)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂P, (occupationProb W μ ω).toMeasure = occupation W μ ω := by
  filter_upwards [hW.ae_isProbabilityMeasure_occupation μ] with ω hω
  exact occupationProb_toMeasure W μ hω

end BrownianImages
