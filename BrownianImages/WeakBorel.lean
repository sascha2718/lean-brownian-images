/-
`sec:introduction`: the space `𝒫(ℝ²)` the paper takes laws on.

The paper equips the Borel probability measures on the plane with the Borel σ-algebra of
the weak topology; Mathlib's `ProbabilityMeasure` carries the Giry σ-algebra, generated
by the evaluations `ν ↦ ν s`.  On a second-countable pseudo-metrisable Borel space the
two agree, and that is proved here — Mathlib has no `BorelSpace (ProbabilityMeasure Ω)`
instance and no `borel (ProbabilityMeasure Ω) = _` lemma.

Giry ≤ Borel is lower semicontinuity of `ν ↦ ν U` for open `U` (portmanteau), extended
to all measurable sets by a Dynkin induction.  Borel ≤ Giry runs through the countable
π-system `piBasis` of finite intersections of basic opens: the induced topology is
pseudo-metrisable, hence sequential, and
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` turns convergence along that
π-system into weak convergence, so every weakly open set is induced-open.

Nothing here is special to `ℝ²`: the argument needs only second countability, pseudo
metrisability, and `BorelSpace`.
-/
import BrownianImages.Defs
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Metrizable.Basic

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

open TopologicalSpace MeasurableSpace

/-- Finite nonempty intersections of the countable basis of `Plane`. -/
def piBasis : Set (Set Plane) :=
  Set.sInter '' {T : Set (Set Plane) | T.Finite ∧ T ⊆ countableBasis Plane ∧ T.Nonempty}

/-- The π-system of finite intersections of basic open sets is countable. -/
theorem piBasis_countable : piBasis.Countable := by
  refine Set.Countable.image ?_ _
  refine (Set.countable_setOf_finite_subset (countable_countableBasis Plane)).mono ?_
  rintro T ⟨h1, h2, _⟩
  exact ⟨h1, h2⟩

/-- Every member of the π-system is open. -/
theorem piBasis_isOpen {s : Set Plane} (hs : s ∈ piBasis) : IsOpen s := by
  obtain ⟨T, ⟨hfin, hsub, _⟩, rfl⟩ := hs
  exact hfin.isOpen_sInter fun t ht => isOpen_of_mem_countableBasis (hsub ht)

/-- Every member of the π-system is measurable. -/
theorem piBasis_measurable : ∀ s ∈ piBasis, MeasurableSet s :=
  fun _ hs => (piBasis_isOpen hs).measurableSet

/-- Finite intersections of basic open sets form a π-system. -/
theorem piBasis_isPiSystem : IsPiSystem piBasis := by
  rintro s ⟨T, ⟨hT1, hT2, hT3⟩, rfl⟩ t ⟨R, ⟨hR1, hR2, hR3⟩, rfl⟩ hne
  refine ⟨T ∪ R, ⟨hT1.union hR1, Set.union_subset hT2 hR2, hT3.inl⟩, ?_⟩
  rw [Set.sInter_union]

/-- The π-system is a neighbourhood basis: every open set contains a member of it around
each of its points. -/
theorem piBasis_nhds :
    ∀ u : Set Plane, IsOpen u → ∀ x ∈ u, ∃ s ∈ piBasis, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hx
  obtain ⟨v, hv, hxv, hvu⟩ := (isBasis_countableBasis Plane).exists_subset_of_mem_open hx hu
  refine ⟨v, ⟨{v}, ⟨Set.finite_singleton v, by simpa using hv, Set.singleton_nonempty v⟩, ?_⟩, ?_, hvu⟩
  · exact Set.sInter_singleton v
  · exact (isOpen_of_mem_countableBasis hv).mem_nhds hxv

/-- The evaluation map into a countable product. -/
def evalPi (ν : ProbabilityMeasure Plane) : piBasis → ℝ≥0 := fun i => ν i.1

/-- Evaluation on the members of the π-system is measurable for the Giry σ-algebra. -/
theorem measurable_evalPi : Measurable evalPi := by
  refine measurable_pi_lambda _ fun i => ?_
  show Measurable fun ν : ProbabilityMeasure Plane => ((ν : Measure Plane) i.1).toNNReal
  exact ENNReal.measurable_toNNReal.comp
    ((Measure.measurable_coe (piBasis_measurable i.1 i.2)).comp measurable_subtype_coe)

/-! ### Direction 1: the Giry σ-algebra is Borel -/

theorem lowerSemicontinuous_apply {U : Set Plane} (hU : IsOpen U) :
    LowerSemicontinuous (fun ν : ProbabilityMeasure Plane => (ν : Measure Plane) U) := by
  intro ν y hy
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (μs := fun ν' : ProbabilityMeasure Plane => ν') (L := 𝓝 ν) tendsto_id hU
  exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hy h)

/-- Evaluation on a measurable set is Borel measurable for the weak topology, by a
Dynkin induction from the portmanteau lower semicontinuity on open sets. -/
theorem measurable_borel_apply {s : Set Plane} (hs : MeasurableSet s) :
    Measurable[borel (ProbabilityMeasure Plane)]
      (fun ν : ProbabilityMeasure Plane => (ν : Measure Plane) s) := by
  letI : MeasurableSpace (ProbabilityMeasure Plane) := borel (ProbabilityMeasure Plane)
  haveI : OpensMeasurableSpace (ProbabilityMeasure Plane) := ⟨le_rfl⟩
  induction s, hs using MeasurableSpace.induction_on_inter
    (h_eq := (BorelSpace.measurable_eq (α := Plane))) (h_inter := isPiSystem_isOpen) with
  | empty => simp
  | basic U hU => exact (lowerSemicontinuous_apply hU).measurable
  | compl t htm ih =>
      have : (fun ν : ProbabilityMeasure Plane => (ν : Measure Plane) tᶜ)
          = fun ν : ProbabilityMeasure Plane => 1 - (ν : Measure Plane) t := by
        funext ν
        exact measure_compl htm (measure_ne_top _ _) |>.trans (by rw [measure_univ])
      rw [this]
      exact ih.const_sub 1
  | iUnion f hd hfm ih =>
      have : (fun ν : ProbabilityMeasure Plane => (ν : Measure Plane) (⋃ i, f i))
          = fun ν : ProbabilityMeasure Plane => ∑' i, (ν : Measure Plane) (f i) := by
        funext ν
        exact measure_iUnion hd hfm
      rw [this]
      exact Measurable.tsum ih

/-! ### Direction 2: the Borel σ-algebra is Giry -/

theorem isOpen_induced_of_isOpen {U : Set (ProbabilityMeasure Plane)} (hU : IsOpen U) :
    IsOpen[TopologicalSpace.induced evalPi inferInstance] U := by
  haveI : Countable piBasis := piBasis_countable.to_subtype
  have wconv : ∀ (μs : ℕ → ProbabilityMeasure Plane) (ν : ProbabilityMeasure Plane),
      Tendsto (fun n => evalPi (μs n)) atTop (𝓝 (evalPi ν)) → Tendsto μs atTop (𝓝 ν) := by
    intro μs ν h
    refine piBasis_isPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
      piBasis_measurable piBasis_nhds ?_
    intro s hs
    exact tendsto_pi_nhds.mp h ⟨s, hs⟩
  have hmemnhds : ∀ ν ∈ U, U ∈ 𝓝 ν := fun ν hν => hU.mem_nhds hν
  letI : TopologicalSpace (ProbabilityMeasure Plane) :=
    TopologicalSpace.induced evalPi inferInstance
  have hind : Topology.IsInducing evalPi := ⟨rfl⟩
  haveI : PseudoMetrizableSpace (ProbabilityMeasure Plane) := hind.pseudoMetrizableSpace
  rw [← isClosed_compl_iff]
  apply IsSeqClosed.isClosed
  intro μs ν hmem hconv
  simp only [Set.mem_compl_iff] at hmem ⊢
  intro hνU
  have h1 := wconv μs ν (hind.tendsto_nhds_iff.mp hconv)
  have h2 : ∀ᶠ n in atTop, μs n ∈ U := h1 (hmemnhds ν hνU)
  obtain ⟨n, hn⟩ := h2.exists
  exact hmem n hn

/-- The law of the occupation measure lives on `𝒫(ℝ²)`, and the paper equips that space
with the Borel σ-algebra of the weak topology.  Mathlib's `ProbabilityMeasure` carries
the Giry σ-algebra, generated by the evaluations; on the Polish space `ℝ²` the two
agree. -/
theorem borel_probabilityMeasure_eq_giry :
    borel (ProbabilityMeasure Plane)
      = (inferInstance : MeasurableSpace (ProbabilityMeasure Plane)) := by
  haveI : Countable piBasis := piBasis_countable.to_subtype
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le fun U hU => ?_
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp (isOpen_induced_of_isOpen hU)
    exact measurable_evalPi hV.measurableSet
  · have hval : Measurable[borel (ProbabilityMeasure Plane)]
        (fun ν : ProbabilityMeasure Plane => (ν : Measure Plane)) := by
      letI : MeasurableSpace (ProbabilityMeasure Plane) := borel (ProbabilityMeasure Plane)
      exact Measure.measurable_of_measurable_coe _ fun s hs => measurable_borel_apply hs
    intro t ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact hval hu

end BrownianImages
