/-
`sec:renewal`: the difference mass `pairDiff μ T = (μ × μ){(x,y) : x - y ∈ T}` of a
measure on the line, the form in which `thm:homogeneous-nonconstancy` reads the
pair-distance distribution.  The exact computations of `HomogeneousNonconstancy` need
one-sided masses such as `P(X - Y ≥ δ)` as well as the symmetric `Φ(δ) = P(|X - Y| ≤ δ)`,
so the object is the mass of an arbitrary Borel set of differences, with `Φ` the
special case of a symmetric interval.

* `pairDiff`, `measurableSet_diffSet`, `pairDiff_ne_top`: the difference mass, the
  measurability of its defining set, and its finiteness for a probability measure.
* `phi_eq_pairDiff`: `Φ` is the difference mass of `[-δ, δ]`.
* `mk_preimage_diffSet`, `measurable_section`, `pairDiff_eq_lintegral`: the Fubini
  form `pairDiff μ T = ∫ μ{y : x - y ∈ T} dμ(x)`.
* `pairDiff_neg`: symmetry of the difference law, from `Measure.prod_swap`.
* `prod_compl_square`: the product measure is carried by the unit square.
-/
import BrownianImages.Recursion

namespace BrownianImages

open MeasureTheory
open scoped ENNReal NNReal

namespace PairDifference

variable {K : Set ℝ} {μ : Measure ℝ}

/-- The mass the difference `X - Y` of two independent `μ`-points gives to `T`. -/
noncomputable def pairDiff (μ : Measure ℝ) (T : Set ℝ) : ℝ≥0∞ :=
  (μ.prod μ) {p : ℝ × ℝ | p.1 - p.2 ∈ T}

/-- The defining set of `pairDiff` is measurable. -/
theorem measurableSet_diffSet {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet {p : ℝ × ℝ | p.1 - p.2 ∈ T} :=
  (measurable_fst.sub measurable_snd) hT

/-- The difference mass of a probability measure is finite. -/
theorem pairDiff_ne_top [IsProbabilityMeasure μ] (T : Set ℝ) : pairDiff μ T ≠ ⊤ :=
  measure_ne_top _ _

/-- `Φ` is the difference mass of a symmetric interval. -/
theorem phi_eq_pairDiff (μ : Measure ℝ) (δ : ℝ) :
    Phi μ δ = (pairDiff μ (Set.Icc (-δ) δ)).toReal := by
  unfold Phi pairDiff
  congr 2
  ext p
  simp [abs_le]

/-- The section of the difference set. -/
theorem mk_preimage_diffSet (x : ℝ) (T : Set ℝ) :
    Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ∈ T} = {y : ℝ | x - y ∈ T} := rfl

/-- The section mass `x ↦ μ{y : x - y ∈ T}` is measurable. -/
theorem measurable_section {T : Set ℝ} (hT : MeasurableSet T) (μ : Measure ℝ) [SFinite μ] :
    Measurable fun x : ℝ => μ {y : ℝ | x - y ∈ T} := by
  simpa only [mk_preimage_diffSet] using
    measurable_measure_prodMk_left (ν := μ) (measurableSet_diffSet hT)

/-- The Fubini form of the difference mass. -/
theorem pairDiff_eq_lintegral (μ : Measure ℝ) [SFinite μ] {T : Set ℝ} (hT : MeasurableSet T) :
    pairDiff μ T = ∫⁻ x, μ {y : ℝ | x - y ∈ T} ∂μ := by
  rw [pairDiff, Measure.prod_apply (measurableSet_diffSet hT)]
  simp only [mk_preimage_diffSet]

/-! ### Elementary properties of the difference mass -/

/-- Symmetry of the difference law, from `Measure.prod_swap`. -/
theorem pairDiff_neg (μ : Measure ℝ) [SFinite μ] {T : Set ℝ} (hT : MeasurableSet T) :
    pairDiff μ T = pairDiff μ ((fun u : ℝ => -u) ⁻¹' T) := by
  conv_lhs => rw [pairDiff, ← Measure.prod_swap (μ := μ) (ν := μ)]
  rw [Measure.map_apply measurable_swap (measurableSet_diffSet hT), pairDiff]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap, neg_sub]

/-! ### The unit square -/

/-- The product measure is carried by the unit square. -/
theorem prod_compl_square [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0) :
    (μ.prod μ) ((Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)ᶜ) = 0 := by
  refine measure_mono_null (t := (Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ)
      ∪ (Set.univ : Set ℝ) ×ˢ (Set.Icc (0:ℝ) 1)ᶜ) ?_ ?_
  · rintro ⟨x, y⟩ hxy
    by_cases hx : x ∈ Set.Icc (0:ℝ) 1
    · exact Or.inr ⟨Set.mem_univ _, fun hy => hxy ⟨hx, hy⟩⟩
    · exact Or.inl ⟨hx, Set.mem_univ _⟩
  · exact measure_union_null (by simp [Measure.prod_prod, hsupp])
      (by simp [Measure.prod_prod, hsupp])

end PairDifference

end BrownianImages
