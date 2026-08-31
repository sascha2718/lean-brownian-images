/-
`sec:reconstruction`: the compact Brownian image as a random point of the Hausdorff
hyperspace.

For a nonempty compact set `K`, uniform perturbation of a continuous map moves its
image by at most the same amount in Hausdorff distance.  This gives continuity, and
hence measurability, of the map from a continuous path to its compact image.
-/
import BrownianImages.JointMeasurability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.Closeds

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

universe u v

variable {T : Type u} {E : Type v}

section Deterministic

variable [TopologicalSpace T] [CompactSpace T] [Nonempty T] [MetricSpace E]

/-- The nonempty compact range of a continuous map on a compact space. -/
noncomputable def compactRange (f : C(T, E)) : NonemptyCompacts E :=
  (⊤ : NonemptyCompacts T).map f f.continuous

@[simp]
theorem coe_compactRange (f : C(T, E)) :
    (compactRange f : Set E) = Set.range f := by
  rw [compactRange, NonemptyCompacts.coe_map, NonemptyCompacts.coe_top]
  exact image_univ

/-- Taking the compact range is `1`-Lipschitz for the uniform metric on continuous
maps and the Hausdorff metric on nonempty compact sets. -/
theorem dist_compactRange_le (f g : C(T, E)) :
    dist (compactRange f) (compactRange g) ≤ dist f g := by
  rw [Metric.NonemptyCompacts.dist_eq, coe_compactRange, coe_compactRange]
  refine Metric.hausdorffDist_le_of_mem_dist dist_nonneg ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨g t, mem_range_self t, ContinuousMap.dist_apply_le_dist t⟩
  · rintro _ ⟨t, rfl⟩
    refine ⟨f t, mem_range_self t, ?_⟩
    simpa only [dist_comm] using
      (ContinuousMap.dist_apply_le_dist (f := g) (g := f) t)

/-- The compact-range map is `1`-Lipschitz. -/
theorem lipschitzWith_compactRange :
    LipschitzWith 1 (compactRange : C(T, E) → NonemptyCompacts E) := by
  exact LipschitzWith.mk_one (dist_compactRange_le (T := T) (E := E))

/-- The compact-range map is continuous for uniform convergence of paths and
Hausdorff convergence of compact sets. -/
theorem continuous_compactRange :
    Continuous (compactRange : C(T, E) → NonemptyCompacts E) :=
  lipschitzWith_compactRange.continuous

/-- The compact-range map is Borel measurable. -/
theorem measurable_compactRange [MeasurableSpace C(T, E)] [BorelSpace C(T, E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)] :
    Measurable (compactRange : C(T, E) → NonemptyCompacts E) :=
  continuous_compactRange.measurable

end Deterministic

section FiniteApproximation

variable [MetricSpace T] [CompactSpace T] [Nonempty T]

/-- A compact metric space has a nonempty finite subset within any prescribed
positive Hausdorff distance of the whole space. -/
theorem exists_finite_compactRange (e : ℝ) (he : 0 < e) :
    ∃ L : NonemptyCompacts T, (L : Set T).Finite ∧ dist L (⊤ : NonemptyCompacts T) ≤ e := by
  obtain ⟨s, hsuniv, hsfin, hcover⟩ :=
    finite_cover_balls_of_compact (s := (Set.univ : Set T)) isCompact_univ he
  have hsne : s.Nonempty := by
    let x : T := Classical.choice (inferInstance : Nonempty T)
    have hx := hcover (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨y, hy, -⟩ := hx
    exact ⟨y, hy⟩
  let L : NonemptyCompacts T := ⟨⟨s, hsfin.isCompact⟩, hsne⟩
  refine ⟨L, hsfin, ?_⟩
  rw [Metric.NonemptyCompacts.dist_eq, NonemptyCompacts.coe_top]
  refine Metric.hausdorffDist_le_of_mem_dist he.le ?_ ?_
  · intro x hx
    exact ⟨x, trivial, by simpa using he.le⟩
  · intro x _
    have hx := hcover (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, hy, hxy.le⟩

/-- A chosen sequence of nonempty finite subsets whose Hausdorff distance to the
whole compact space tends to zero. -/
noncomputable def finiteCompactApprox (n : ℕ) : NonemptyCompacts T :=
  Classical.choose (exists_finite_compactRange (T := T) ((n + 1 : ℝ)⁻¹) (by positivity))

theorem finite_finiteCompactApprox (n : ℕ) :
    (finiteCompactApprox (T := T) n : Set T).Finite :=
  (Classical.choose_spec
    (exists_finite_compactRange (T := T) ((n + 1 : ℝ)⁻¹) (by positivity))).1

theorem dist_finiteCompactApprox_le (n : ℕ) :
    dist (finiteCompactApprox (T := T) n) (⊤ : NonemptyCompacts T) ≤ (n + 1 : ℝ)⁻¹ :=
  (Classical.choose_spec
    (exists_finite_compactRange (T := T) ((n + 1 : ℝ)⁻¹) (by positivity))).2

theorem tendsto_finiteCompactApprox :
    Tendsto (finiteCompactApprox (T := T)) atTop (𝓝 (⊤ : NonemptyCompacts T)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hinv) ε hε
  refine ⟨N, fun n hn ↦ lt_of_le_of_lt (dist_finiteCompactApprox_le (T := T) n) ?_⟩
  have hn' := hN n hn
  rw [Real.dist_eq, sub_zero] at hn'
  exact (le_abs_self _).trans_lt hn'

end FiniteApproximation

section FiniteRanges

variable {I : Type u} [Nonempty I] [Finite I] [MetricSpace E]

/-- The range of a function on a nonempty finite type, bundled as a nonempty
compact set. -/
noncomputable def finiteRange (f : I → E) : NonemptyCompacts E :=
  ⟨⟨Set.range f, (Set.finite_range f).isCompact⟩, Set.range_nonempty f⟩

@[simp]
theorem coe_finiteRange (f : I → E) : (finiteRange f : Set E) = Set.range f := rfl

/-- The finite-range map is continuous from the finite product topology to the
Vietoris, equivalently Hausdorff, topology. -/
theorem continuous_finiteRange :
    Continuous (finiteRange : (I → E) → NonemptyCompacts E) := by
  letI : TopologicalSpace (Set E) := TopologicalSpace.vietoris E
  rw [NonemptyCompacts.isEmbedding_coe.continuous_iff]
  exact vietoris.continuous_range_of_finite

theorem measurable_finiteRange [MeasurableSpace (I → E)] [BorelSpace (I → E)]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)] :
    Measurable (finiteRange : (I → E) → NonemptyCompacts E) :=
  continuous_finiteRange.measurable

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- A finite collection of almost everywhere measurable points has an almost
everywhere measurable compact range. -/
theorem aemeasurable_finiteRange_process [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)] (X : I → Ω → E)
    (hX : ∀ i, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ finiteRange (fun i ↦ X i ω)) P := by
  apply measurable_finiteRange.comp_aemeasurable
  exact aemeasurable_pi_lambda _ hX

end FiniteRanges

section FiniteImages

variable [MetricSpace T] [MetricSpace E]

/-- The image of a nonempty finite compact set under an arbitrary function. -/
noncomputable def finiteImage (L : NonemptyCompacts T) (hL : (L : Set T).Finite)
    (f : T → E) : NonemptyCompacts E :=
  ⟨⟨f '' L, (hL.image f).isCompact⟩, L.nonempty.image f⟩

@[simp]
theorem coe_finiteImage (L : NonemptyCompacts T) (hL : (L : Set T).Finite)
    (f : T → E) : (finiteImage L hL f : Set E) = f '' L := rfl

/-- A finite image can equivalently be read as the range of the restriction to
the finite subtype. -/
theorem finiteImage_eq_finiteRange (L : NonemptyCompacts T) (hL : (L : Set T).Finite)
    [Finite L] (f : T → E) :
    finiteImage L hL f = finiteRange (fun t : L ↦ f t) := by
  apply NonemptyCompacts.ext
  rw [coe_finiteImage, coe_finiteRange]
  exact image_eq_range _ _

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Images of a fixed finite time set are almost everywhere measurable compact
sets whenever every fixed-time evaluation is almost everywhere measurable. -/
theorem aemeasurable_finiteImage_process [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)] (L : NonemptyCompacts T)
    (hL : (L : Set T).Finite) (X : T → Ω → E)
    (hX : ∀ t, AEMeasurable (X t) P) :
    AEMeasurable (fun ω ↦ finiteImage L hL (fun t ↦ X t ω)) P := by
  letI : Fintype L := hL.fintype
  simp_rw [finiteImage_eq_finiteRange]
  exact aemeasurable_finiteRange_process P (fun t : L ↦ X t) (fun t ↦ hX t)

end FiniteImages

section CompactImages

variable [MetricSpace T] [CompactSpace T] [Nonempty T] [MetricSpace E]

omit [CompactSpace T] [Nonempty T] in
/-- For a continuous function, its image of a finite compact set agrees with the
usual continuous image of that compact set. -/
theorem finiteImage_eq_map (L : NonemptyCompacts T) (hL : (L : Set T).Finite)
    (f : T → E) (hf : Continuous f) :
    finiteImage L hL f = L.map f hf := by
  apply NonemptyCompacts.ext
  rw [coe_finiteImage, NonemptyCompacts.coe_map]

/-- Finite time samples converging in Hausdorff distance to the whole compact time
space have images converging to the compact range of every continuous path. -/
theorem tendsto_finiteImage_of_continuous (f : T → E) (hf : Continuous f) :
    Tendsto
      (fun n ↦ finiteImage (finiteCompactApprox (T := T) n)
        (finite_finiteCompactApprox (T := T) n) f)
      atTop (𝓝 (compactRange ⟨f, hf⟩)) := by
  have hmap := (hf.nonemptyCompacts_map.tendsto (⊤ : NonemptyCompacts T)).comp
    (tendsto_finiteCompactApprox (T := T))
  have hseq :
      (fun n ↦ finiteImage (finiteCompactApprox (T := T) n)
        (finite_finiteCompactApprox (T := T) n) f) =
      fun n ↦ (finiteCompactApprox (T := T) n).map f hf := by
    funext n
    exact finiteImage_eq_map _ _ f hf
  rw [hseq]
  change Tendsto (NonemptyCompacts.map f hf ∘ finiteCompactApprox) atTop
    (𝓝 ((⊤ : NonemptyCompacts T).map f hf))
  exact hmap

/-- The compact range of a function, with a fixed singleton fallback when the
function is not continuous.  On continuous functions this is exactly the range. -/
noncomputable def compactImageOfFunction (x₀ : E) (f : T → E) : NonemptyCompacts E :=
  compactRange (ContinuousMap.mkD f (ContinuousMap.const T x₀))

theorem compactImageOfFunction_of_continuous (x₀ : E) {f : T → E}
    (hf : Continuous f) :
    compactImageOfFunction x₀ f = compactRange ⟨f, hf⟩ := by
  rw [compactImageOfFunction, ContinuousMap.mkD_of_continuous hf]

theorem coe_compactImageOfFunction_of_continuous (x₀ : E) {f : T → E}
    (hf : Continuous f) :
    (compactImageOfFunction x₀ f : Set E) = Set.range f := by
  rw [compactImageOfFunction_of_continuous x₀ hf, coe_compactRange]
  rfl

theorem tendsto_finiteImage_compactImageOfFunction (x₀ : E) {f : T → E}
    (hf : Continuous f) :
    Tendsto
      (fun n ↦ finiteImage (finiteCompactApprox (T := T) n)
        (finite_finiteCompactApprox (T := T) n) f)
      atTop (𝓝 (compactImageOfFunction x₀ f)) := by
  rw [compactImageOfFunction_of_continuous x₀ hf]
  exact tendsto_finiteImage_of_continuous f hf

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The compact image of a stochastic process, with a fixed fallback away from
continuous sample paths. -/
noncomputable def compactImageProcess (x₀ : E) (X : T → Ω → E) (ω : Ω) :
    NonemptyCompacts E :=
  compactImageOfFunction x₀ (fun t ↦ X t ω)

/-- A process with almost everywhere measurable evaluations and almost surely
continuous paths has an almost everywhere measurable compact image. -/
theorem aemeasurable_compactImageProcess (P : Measure Ω) [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    (x₀ : E) (X : T → Ω → E) (hX : ∀ t, AEMeasurable (X t) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) :
    AEMeasurable (compactImageProcess x₀ X) P := by
  let F : ℕ → Ω → NonemptyCompacts E := fun n ω ↦
    finiteImage (finiteCompactApprox (T := T) n)
      (finite_finiteCompactApprox (T := T) n) (fun t ↦ X t ω)
  apply aemeasurable_of_tendsto_metrizable_ae' (f := F)
  · intro n
    exact aemeasurable_finiteImage_process P _ _ X hX
  · filter_upwards [hcont] with ω hω
    exact tendsto_finiteImage_compactImageOfFunction x₀ hω

end CompactImages

/-! ### Brownian images -/

/-- The compact hyperspace of the plane carries its canonical Borel measurable
structure. -/
noncomputable instance measurableSpace_nonemptyCompacts_plane :
    MeasurableSpace (NonemptyCompacts Plane) :=
  borel (NonemptyCompacts Plane)

instance borelSpace_nonemptyCompacts_plane : BorelSpace (NonemptyCompacts Plane) :=
  ⟨rfl⟩

section Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {W : ℝ≥0 → Ω → Plane}

/-- The compact Brownian image of a nonempty compact real time set.  Times are
read through `Real.toNNReal`, as for `occupation`; away from continuous paths the
value is the singleton `{0}`. -/
noncomputable def brownianImage (W : ℝ≥0 → Ω → Plane)
    (K : NonemptyCompacts ℝ) (ω : Ω) : NonemptyCompacts Plane :=
  compactImageProcess (T := K) (0 : Plane)
    (fun t : K ↦ W t.1.toNNReal) ω

omit [MeasurableSpace Ω] in
/-- On a continuous sample path, `brownianImage` is exactly the set-theoretic
image of the prescribed compact time set. -/
theorem coe_brownianImage_of_continuous (K : NonemptyCompacts ℝ) {ω : Ω}
    (hω : Continuous (fun t : ℝ≥0 ↦ W t ω)) :
    (brownianImage W K ω : Set Plane) =
      (fun t : ℝ ↦ W t.toNNReal ω) '' K := by
  rw [brownianImage, compactImageProcess,
    coe_compactImageOfFunction_of_continuous]
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  · exact hω.comp (continuous_real_toNNReal.comp continuous_subtype_val)

/-- The compact image of planar Brownian motion is an almost everywhere
measurable random element of the Hausdorff hyperspace. -/
theorem IsPlanarBrownian.aemeasurable_brownianImage (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts ℝ) :
    AEMeasurable (brownianImage W K) P := by
  apply aemeasurable_compactImageProcess P (0 : Plane)
  · intro t
    exact JointMeasurability.aemeasurable_eval hW t.1.toNNReal
  · filter_upwards [hW.ae_continuous] with ω hω
    exact hω.comp (continuous_real_toNNReal.comp continuous_subtype_val)

/-- Almost surely, the bundled Brownian image has the expected underlying set. -/
theorem IsPlanarBrownian.ae_coe_brownianImage (hW : IsPlanarBrownian W P)
    (K : NonemptyCompacts ℝ) :
    ∀ᵐ ω ∂P, (brownianImage W K ω : Set Plane) =
      (fun t : ℝ ↦ W t.toNNReal ω) '' K := by
  filter_upwards [hW.ae_continuous] with ω hω
  exact coe_brownianImage_of_continuous K hω

/-- The law of the compact Brownian image on the Hausdorff hyperspace. -/
noncomputable def brownianImageLaw (W : ℝ≥0 → Ω → Plane) (P : Measure Ω)
    (K : NonemptyCompacts ℝ) : Measure (NonemptyCompacts Plane) :=
  P.map (brownianImage W K)

/-- The compact-image law has total mass one. -/
theorem IsPlanarBrownian.isProbabilityMeasure_brownianImageLaw [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) (K : NonemptyCompacts ℝ) :
    IsProbabilityMeasure (brownianImageLaw W P K) :=
  Measure.isProbabilityMeasure_map (hW.aemeasurable_brownianImage K)

end Brownian

end BrownianImages
