/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: Borel classification of the
limit of a measurable sequence without constructing the limit as a measurable map.

For every Borel set `E` in a pseudo-metrizable Borel space and every sequence of
measurable maps `f n`, there is a measurable set in the source which, at every point
where `f n` converges, records whether the limit belongs to `E`.  This is weaker than
constructing a Borel limit map, but it is exactly what is needed to pull a separating
event back from occupation-measure laws to compact-image laws.

The proof is by Borel induction.  For an open set `U`, membership of the limit in `U`
is detected by eventual positive distance from `Uᶜ`.  Complements and countable
unions become complements and countable unions of the classifiers.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace BrownianImages

open Filter Set TopologicalSpace
open scoped Topology

namespace MinkowskiLimitClassifier

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
  [PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Every Borel property of the limit of a measurable sequence has a measurable
classifier on the source, valid at all points where the sequence converges. -/
theorem exists_measurableSet_limit_classifier (f : ℕ → X → Y)
    (hf : ∀ n, Measurable (f n)) {E : Set Y} (hE : MeasurableSet E) :
    ∃ A : Set X, MeasurableSet A ∧
      ∀ x y, Tendsto (fun n ↦ f n x) atTop (nhds y) → (x ∈ A ↔ y ∈ E) := by
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  let C : ∀ E : Set Y, MeasurableSet E → Prop := fun E _ ↦
    ∃ A : Set X, MeasurableSet A ∧
      ∀ x y, Tendsto (fun n ↦ f n x) atTop (nhds y) → (x ∈ A ↔ y ∈ E)
  apply MeasurableSet.induction_on_open (C := C) (t := E) (ht := hE)
  · intro U hU
    by_cases hUuniv : U = Set.univ
    · subst U
      exact ⟨Set.univ, MeasurableSet.univ, fun _ _ _ ↦ by simp⟩
    · have hUc : Uᶜ.Nonempty := Set.nonempty_compl.mpr hUuniv
      let A : Set X := ⋃ k : ℕ, ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n},
        {x | 1 / ((k : ℝ) + 1) < Metric.infDist (f n.1 x) Uᶜ}
      have hA : MeasurableSet A := by
        apply MeasurableSet.iUnion
        intro k
        apply MeasurableSet.iUnion
        intro N
        apply MeasurableSet.iInter
        intro n
        exact measurableSet_lt measurable_const
          ((Metric.lipschitz_infDist_pt Uᶜ).continuous.measurable.comp (hf n.1))
      refine ⟨A, hA, ?_⟩
      intro x y hlim
      have hdist : Tendsto (fun n ↦ Metric.infDist (f n x) Uᶜ) atTop
          (nhds (Metric.infDist y Uᶜ)) :=
        (Metric.lipschitz_infDist_pt Uᶜ).continuous.continuousAt.tendsto.comp hlim
      constructor
      · intro hx
        simp only [A, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hx
        obtain ⟨k, N, hx⟩ := hx
        by_contra hy
        have hydist : Metric.infDist y Uᶜ = 0 :=
          Metric.infDist_zero_of_mem (Set.mem_compl hy)
        have hpositive : 0 < 1 / ((k : ℝ) + 1) := by positivity
        obtain ⟨N', hN'⟩ := (Metric.tendsto_atTop.mp (hydist ▸ hdist)) _ hpositive
        let n : ℕ := max N N'
        have hlarge := hx ⟨n, Nat.le_max_left N N'⟩
        have hsmall := hN' n (Nat.le_max_right N N')
        rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at hsmall
        exact (not_lt_of_ge hsmall.le) hlarge
      · intro hy
        have hydist : 0 < Metric.infDist y Uᶜ := by
          rw [← hU.isClosed_compl.notMem_iff_infDist_pos hUc]
          simpa using hy
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hydist
        have hevent : ∀ᶠ n in atTop,
            1 / ((k : ℝ) + 1) < Metric.infDist (f n x) Uᶜ :=
          hdist (Ioi_mem_nhds hk)
        obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
        simp only [A, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
        exact ⟨k, N, fun n ↦ hN n.1 n.2⟩
  · intro S hS hclass
    obtain ⟨A, hA, hlimit⟩ := hclass
    refine ⟨Aᶜ, hA.compl, ?_⟩
    intro x y hlim
    simpa only [Set.mem_compl_iff] using not_congr (hlimit x y hlim)
  · intro S hdisjoint hS hclass
    choose A hA hlimit using hclass
    refine ⟨⋃ i, A i, MeasurableSet.iUnion hA, ?_⟩
    intro x y hlim
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hlimit i x y hlim).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hlimit i x y hlim).mpr hi⟩

end MinkowskiLimitClassifier

end BrownianImages
