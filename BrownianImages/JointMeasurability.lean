/-
`sec:setup`: joint measurability of the planar Brownian process, and the two facts about
the occupation law it unlocks.

`IsPlanarBrownian` gives measurability of `ω ↦ W t ω` for each fixed `t` only up to a null
set, and continuity of `t ↦ W t ω` only for almost every `ω`.  Neither alone makes
`(t, ω) ↦ W t ω` measurable on the product.  The dyadic approximation
`W_n(t, ω) = W(⌈2ⁿ t⌉/2ⁿ, ω)` is measurable on the product, because it is constant in `t`
on each dyadic block and there are countably many blocks, and on the event where the path
is continuous and agrees with a measurable version at every dyadic time it converges to
`W t ω`.  Off that event the approximations are all zero, so the convergence is
everywhere and the limit is measurable.

* `IsPlanarBrownian.exists_jointlyMeasurable`: a jointly measurable modification of the
  process, equal to `W` at every time, almost surely.
* `JointMeasurability.measurable_occupation`: the occupation measure of such a
  modification is a measurable point of `Measure ℝ²` with the Giry structure.
* `IsPlanarBrownian.aemeasurable_occupationProb`: `audit_aemeasurable_occupation`.
* `IsPlanarBrownian.isProbabilityMeasure_occupationLaw`:
  `audit_isProbabilityMeasure_occupationLaw`.
-/
import BrownianImages.Occupation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Prod

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

namespace JointMeasurability

/-- A map into the plane is measurable as soon as both coordinates are.  The measurable
structure on `EuclideanSpace ℝ (Fin 2)` is the one comapped from `Fin 2 → ℝ`. -/
theorem measurable_plane_of_coord {α : Type*} [MeasurableSpace α] {f : α → Plane}
    (h : ∀ i : Fin 2, Measurable fun x => f x i) : Measurable f :=
  (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp (measurable_pi_lambda _ h)

/-- At each fixed time the process is almost everywhere measurable in the sample point.
This is the coordinatewise `IsPreBrownianReal.aemeasurable`, read in the plane. -/
theorem aemeasurable_eval (hW : IsPlanarBrownian W P) (t : ℝ≥0) : AEMeasurable (W t) P := by
  have h : ∀ i : Fin 2, AEMeasurable (fun ω => W t ω i) P := fun i => (hW.coord i).aemeasurable t
  refine ⟨fun ω => WithLp.toLp 2 fun i => (h i).mk _ ω, ?_, ?_⟩
  · exact measurable_plane_of_coord fun i => (h i).measurable_mk
  · have hall : ∀ᵐ ω ∂P, ∀ i : Fin 2, W t ω i = (h i).mk _ ω :=
      ae_all_iff.mpr fun i => (h i).ae_eq_mk
    filter_upwards [hall] with ω hω
    ext i
    exact hω i

/-- The dyadic times `⌈2ⁿ t⌉/2ⁿ` converge to `t`.  These are the times the approximating
processes read, and there are countably many of them. -/
theorem tendsto_approx (t : ℝ≥0) :
    Tendsto (fun n : ℕ => ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ≥0) / 2 ^ n)) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hpos : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => pow_pos two_pos n
  have hcoe : ∀ n : ℕ,
      ((((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ≥0) / 2 ^ n : ℝ≥0)) : ℝ)
        = (⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ) / 2 ^ n := by
    intro n
    push_cast
    ring
  simp only [hcoe]
  have hlb : ∀ n : ℕ, (t : ℝ) ≤ (⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ) / 2 ^ n := by
    intro n
    rw [le_div_iff₀ (hpos n)]
    calc (t : ℝ) * 2 ^ n = 2 ^ n * (t : ℝ) := by ring
      _ ≤ (⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hub : ∀ n : ℕ, (⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ) / 2 ^ n ≤ (t : ℝ) + (1 / 2 : ℝ) ^ n := by
    intro n
    rw [div_le_iff₀ (hpos n)]
    have h2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    have hrw : ((t : ℝ) + (1 / 2 : ℝ) ^ n) * 2 ^ n = 2 ^ n * (t : ℝ) + 1 := by
      rw [add_mul, h2]
      ring
    rw [hrw]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlb hub
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using tendsto_const_nhds.add hhalf

/-- The occupation measure of a jointly measurable process is a measurable point of the
space of measures on the plane, with the Giry structure.  The Giry criterion asks for
measurability of `ω ↦ (W_*μ)(s)` for measurable `s`, and that is the measure of a section
of a measurable set of `Ω × ℝ`. -/
theorem measurable_occupation {V : ℝ≥0 → Ω → Plane}
    (hV : Measurable (fun p : ℝ≥0 × Ω => V p.1 p.2)) (μ : Measure ℝ) [SFinite μ] :
    Measurable fun ω => μ.map fun t : ℝ => V t.toNNReal ω := by
  have hsec : ∀ ω, Measurable fun t : ℝ => V t.toNNReal ω := fun ω =>
    hV.comp ((continuous_real_toNNReal.measurable).prodMk measurable_const)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hS : MeasurableSet ((fun p : Ω × ℝ => V p.2.toNNReal p.1) ⁻¹' s) :=
    (hV.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      measurable_fst)) hs
  simp only [Measure.map_apply (hsec _) hs]
  exact measurable_measure_prodMk_left hS

end JointMeasurability

/-- Joint measurability of the process, up to a modification: there is a
`V : ℝ≥0 → Ω → ℝ²` measurable on the product which almost surely equals `W` at every
time.  This is what `sec:setup` needs and what `IsPlanarBrownian` does not say outright,
since it carries measurability in `ω` at each fixed `t` and continuity in `t` for almost
every `ω`, never the two at once. -/
theorem IsPlanarBrownian.exists_jointlyMeasurable (hW : IsPlanarBrownian W P) :
    ∃ V : ℝ≥0 → Ω → Plane, Measurable (fun p : ℝ≥0 × Ω => V p.1 p.2) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, V t ω = W t ω := by
  classical
  have haem : ∀ q : ℝ≥0, AEMeasurable (W q) P := fun q =>
    JointMeasurability.aemeasurable_eval hW q
  -- The null set off which some path fails to be continuous.
  obtain ⟨N₀, hN₀sub, hN₀meas, hN₀null⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hW.ae_continuous)
  -- The null set off which the process differs from its measurable version at time `q`.
  have hN : ∀ q : ℝ≥0, ∃ s : Set Ω,
      {ω | ¬ W q ω = (haem q).mk (W q) ω} ⊆ s ∧ MeasurableSet s ∧ P s = 0 := fun q =>
    exists_measurable_superset_of_null (ae_iff.mp (haem q).ae_eq_mk)
  choose N hNsub hNmeas hNnull using hN
  -- The good event: continuous paths, and agreement with the measurable versions at every
  -- dyadic time.
  set E : Set Ω := (N₀ ∪ ⋃ p : ℕ × ℕ, N ((p.1 : ℝ≥0) / 2 ^ p.2))ᶜ with hEdef
  have hEmeas : MeasurableSet E :=
    (hN₀meas.union (MeasurableSet.iUnion fun p => hNmeas _)).compl
  have hEnull : P Eᶜ = 0 := by
    rw [hEdef, compl_compl]
    exact measure_union_null hN₀null (measure_iUnion_null fun p => hNnull _)
  have hEcont : ∀ ω ∈ E, Continuous fun t : ℝ≥0 => W t ω := by
    intro ω hω
    by_contra h
    exact hω (Or.inl (hN₀sub h))
  have hEmk : ∀ k n : ℕ, ∀ ω ∈ E,
      W ((k : ℝ≥0) / 2 ^ n) ω = (haem ((k : ℝ≥0) / 2 ^ n)).mk (W ((k : ℝ≥0) / 2 ^ n)) ω := by
    intro k n ω hω
    by_contra h
    exact hω (Or.inr (mem_iUnion.mpr ⟨(k, n), hNsub _ h⟩))
  refine ⟨fun t ω => E.indicator (W t) ω, ?_, ?_⟩
  · -- The dyadic approximations, measurable on the product.
    have key : ∀ n k : ℕ, Measurable fun ω => E.indicator (W ((k : ℝ≥0) / 2 ^ n)) ω := by
      intro n k
      have hcongr : E.indicator (W ((k : ℝ≥0) / 2 ^ n))
          = E.indicator ((haem ((k : ℝ≥0) / 2 ^ n)).mk (W ((k : ℝ≥0) / 2 ^ n))) :=
        Set.indicator_congr fun ω hω => hEmk k n ω hω
      rw [hcongr]
      exact (haem _).measurable_mk.indicator hEmeas
    have hstep : ∀ n : ℕ, Measurable fun p : ℝ≥0 × Ω =>
        E.indicator (W ((⌈(2 : ℝ) ^ n * (p.1 : ℝ)⌉₊ : ℝ≥0) / 2 ^ n)) p.2 := by
      intro n
      have h1 : Measurable fun p : ℝ≥0 × Ω => ((⌈(2 : ℝ) ^ n * (p.1 : ℝ)⌉₊ : ℕ), p.2) :=
        Measurable.prodMk
          (Nat.measurable_ceil.comp (measurable_fst.coe_nnreal_real.const_mul _))
          measurable_snd
      exact (measurable_from_prod_countable_right
        (f := fun q : ℕ × Ω => E.indicator (W ((q.1 : ℝ≥0) / 2 ^ n)) q.2)
        fun k => key n k).comp h1
    refine measurable_of_tendsto_metrizable hstep (tendsto_pi_nhds.mpr ?_)
    rintro ⟨t, ω⟩
    by_cases hω : ω ∈ E
    · simp only [Set.indicator_of_mem hω]
      exact ((hEcont ω hω).tendsto t).comp (JointMeasurability.tendsto_approx t)
    · simp only [Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  · have hae : ∀ᵐ ω ∂P, ω ∈ E := by
      rw [ae_iff]
      exact hEnull
    filter_upwards [hae] with ω hω t
    exact Set.indicator_of_mem hω _

/-- `audit_aemeasurable_occupation`.  The occupation measure is an almost everywhere
measurable function of the sample path, so `occupationLaw` is the law of `W_*μ` and not
the junk value `Measure.map` returns on a non-measurable map. -/
theorem IsPlanarBrownian.aemeasurable_occupationProb (hW : IsPlanarBrownian W P)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    AEMeasurable (occupationProb W μ) P := by
  obtain ⟨V, hVmeas, hVae⟩ := hW.exists_jointlyMeasurable
  have hsec : ∀ ω, Measurable fun t : ℝ => V t.toNNReal ω := fun ω =>
    hVmeas.comp ((continuous_real_toNNReal.measurable).prodMk measurable_const)
  have hprob : ∀ ω, IsProbabilityMeasure (μ.map fun t : ℝ => V t.toNNReal ω) := fun ω =>
    Measure.isProbabilityMeasure_map (hsec ω).aemeasurable
  refine ⟨fun ω => ⟨μ.map fun t : ℝ => V t.toNNReal ω, hprob ω⟩, ?_, ?_⟩
  · exact (JointMeasurability.measurable_occupation hVmeas μ).subtype_mk
  · filter_upwards [hVae] with ω hω
    have hocc : occupation W μ ω = μ.map fun t : ℝ => V t.toNNReal ω := by
      unfold occupation
      exact congrArg (μ.map ·) (funext fun t => (hω _).symm)
    have hprob' : IsProbabilityMeasure (occupation W μ ω) := hocc ▸ hprob ω
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [occupationProb_toMeasure W μ hprob']
    exact hocc

/-- `audit_isProbabilityMeasure_occupationLaw`.  The law of the occupation measure is a
probability measure, so the object the paper calls `Law(W_*μ)` has total mass one. -/
theorem IsPlanarBrownian.isProbabilityMeasure_occupationLaw [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (occupationLaw W P μ) :=
  Measure.isProbabilityMeasure_map (hW.aemeasurable_occupationProb μ)

end BrownianImages
