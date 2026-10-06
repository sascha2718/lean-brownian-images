/-
`sec:introduction` and `sec:renewal` of `BrownianImagesComplete.tex`: the open set
condition for a self-similar system on `[0,1]`.

The definitions `System.IsFeasible`, `System.OpenSetCondition` and
`System.StrongOpenSetCondition` live in `Defs.lean`, where `Challenge.lean` copies
them.  This module carries the elementary geometry of a feasible open set that the
stopping-family and cross-piece arguments of `sec:renewal` consume.

* `IsFeasible.mapsTo_wordMap`: every composition of the similarities along an address
  maps a feasible set into itself.
* `IsFeasible.disjoint_image_closure_image`: `S_i U` is disjoint from the closure of
  `S_j U`, the form in which the disjointness of the first-level images is used.
* `IsFeasible.attractor_subset_closure`: `K ⊆ closure U`, since the orbit of any point
  of `U` under the maps of an address converges to the coded point.
* `IsFeasible.piece_subset_closure_image`: `S_j K ⊆ closure (S_j U)`.
* `StronglySeparated.strongOpenSetCondition`: strong separation gives the strong open
  set condition, with the `ρ/3`-neighbourhood of the attractor as feasible set.  This
  is how the two named systems of `sec:renewal` satisfy it.
-/
import BrownianImages.Hutchinson

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-! ### Nesting under words -/

/-- Every composition along an address maps a feasible set into itself. -/
theorem IsFeasible.mapsTo_wordMap {U : Set ℝ} (hU : S.IsFeasible U) (ω : ℕ → ι) :
    ∀ n : ℕ, MapsTo (Hutchinson.wordMap S ω n) U U
  | 0 => by simpa [Hutchinson.wordMap_zero] using Set.mapsTo_id U
  | n + 1 => by
      rw [Hutchinson.wordMap_succ]
      exact (hU.mapsTo_wordMap ω n).comp (hU.mapsTo (ω n))

/-- The image of a feasible set under a similarity of the system is open. -/
theorem IsFeasible.isOpen_image {U : Set ℝ} (hU : S.IsFeasible U) (i : ι) :
    IsOpen (S.map i '' U) := by
  rw [S.image_eq_preimage_inv]
  exact hU.isOpen.preimage (S.continuous_inv i)

/-- `S_i U` is disjoint from the closure of `S_j U` for `i ≠ j`. -/
theorem IsFeasible.disjoint_image_closure_image {U : Set ℝ} (hU : S.IsFeasible U)
    {i j : ι} (hij : i ≠ j) : Disjoint (S.map i '' U) (closure (S.map j '' U)) :=
  (hU.disjoint i j hij).closure_right (hU.isOpen_image S i)

/-! ### The attractor lies in the closure of a feasible set -/

/-- The orbit of any real point under the maps of an address converges to the coded
point: `tendsto_wordMap` without the restriction to `[0,1]`. -/
theorem tendsto_wordMap_of_real [Nonempty ι] (ω : ℕ → ι) (z : ℝ) :
    Tendsto (fun n => Hutchinson.wordMap S ω n z) atTop (𝓝 (Hutchinson.code S ω)) := by
  have hbound : ∀ n, ‖Hutchinson.wordMap S ω n z - Hutchinson.codeSeq S ω n‖
      ≤ |z| * Hutchinson.maxRatio S ^ n := by
    intro n
    rw [Real.norm_eq_abs, Hutchinson.codeSeq, Hutchinson.abs_wordMap_sub, sub_zero, mul_comm]
    exact mul_le_mul_of_nonneg_left (Hutchinson.wordRatio_le_pow S ω n) (abs_nonneg z)
  have hdiff : Tendsto (fun n => Hutchinson.wordMap S ω n z - Hutchinson.codeSeq S ω n)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    simpa using (Hutchinson.tendsto_pow_maxRatio S).const_mul |z|
  simpa using hdiff.add (Hutchinson.tendsto_codeSeq S ω)

/-- The attractor lies in the closure of every feasible set: the iterates of any point
of `U` along an address stay in `U` and converge to the coded point. -/
theorem IsFeasible.attractor_subset_closure [Nonempty ι] {U : Set ℝ} (hU : S.IsFeasible U)
    {K : Set ℝ} (hK : S.IsAttractor K) : K ⊆ closure U := by
  intro y hy
  rw [Hutchinson.eq_attractorSet S hK] at hy
  obtain ⟨ω, rfl⟩ := hy
  obtain ⟨z, hz⟩ := hU.nonempty
  exact mem_closure_of_tendsto (S.tendsto_wordMap_of_real ω z)
    (Eventually.of_forall fun n => hU.mapsTo_wordMap S ω n hz)

/-- Each first-level piece of the attractor lies in the closure of the corresponding
image of a feasible set. -/
theorem IsFeasible.piece_subset_closure_image [Nonempty ι] {U : Set ℝ}
    (hU : S.IsFeasible U) {K : Set ℝ} (hK : S.IsAttractor K) (j : ι) :
    S.map j '' K ⊆ closure (S.map j '' U) :=
  (Set.image_mono (hU.attractor_subset_closure S hK)).trans
    (image_closure_subset_closure_image (Hutchinson.continuous_systemMap S j))

/-- A point of `S_i U` is not in a piece `S_j K` with `j ≠ i`. -/
theorem IsFeasible.notMem_piece_of_mem_image [Nonempty ι] {U : Set ℝ}
    (hU : S.IsFeasible U) {K : Set ℝ} (hK : S.IsAttractor K) {i j : ι} (hij : i ≠ j)
    {x : ℝ} (hx : x ∈ S.map i '' U) : x ∉ S.map j '' K := fun hxK =>
  Set.disjoint_left.mp (hU.disjoint_image_closure_image S hij) hx
    (hU.piece_subset_closure_image S hK j hxK)

/-! ### Strong separation gives the strong open set condition -/

/-- A similarity of ratio `r` sends the `ε`-neighbourhood of a set into the
`rε`-neighbourhood of its image. -/
theorem map_thickening_subset (i : ι) (ε : ℝ) (E : Set ℝ) :
    S.map i '' Metric.thickening ε E ⊆ Metric.thickening (S.ratio i * ε) (S.map i '' E) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_thickening_iff] at hx ⊢
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨S.map i z, ⟨z, hz, rfl⟩, ?_⟩
  rw [Real.dist_eq, S.abs_map_sub]
  rw [Real.dist_eq] at hxz
  exact mul_lt_mul_of_pos_left hxz (S.ratio_pos i)

/-- Strong separation with gap `ρ` on the attractor gives the strong open set
condition, with the open `ρ/3`-neighbourhood of the attractor as feasible set: it is
mapped into itself by every similarity, its first-level images are disjoint because
points of `S_i K` and `S_j K` are `ρ` apart, and it contains the attractor. -/
theorem StronglySeparated.strongOpenSetCondition {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hK : S.IsAttractor K) :
    S.StrongOpenSetCondition K := by
  have hρ : 0 < ρ := hsep.1
  set ε : ℝ := ρ / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hKsub : K ⊆ Metric.thickening ε K := Metric.self_subset_thickening hε0 K
  refine ⟨Metric.thickening ε K, ⟨Metric.isOpen_thickening, hK.2.1.mono hKsub,
    (Metric.isBounded_Icc (0:ℝ) 1).subset hK.2.2.1 |>.thickening, ?_, ?_⟩,
    hK.2.1.mono fun x hx => ⟨hKsub hx, hx⟩⟩
  · intro i x hx
    have h1 := S.map_thickening_subset i ε K ⟨x, hx, rfl⟩
    have hsub : Metric.thickening (S.ratio i * ε) (S.map i '' K) ⊆ Metric.thickening ε K := by
      refine (Metric.thickening_mono ?_ _).trans (Metric.thickening_subset_of_subset ε ?_)
      · nlinarith [S.ratio_lt_one i, S.ratio_pos i]
      · intro y hy
        rw [hK.2.2.2]
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
    exact hsub h1
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hx' := S.map_thickening_subset i ε K ⟨x, hx, rfl⟩
    have hy' := S.map_thickening_subset j ε K ⟨y, hy, rfl⟩
    rw [Metric.mem_thickening_iff] at hx' hy'
    obtain ⟨a, ⟨a', ha', rfl⟩, hxa⟩ := hx'
    obtain ⟨b, ⟨b', hb', rfl⟩, hyb⟩ := hy'
    have hgap := hsep.2 i j hij a' ha' b' hb'
    have hri : S.ratio i * ε ≤ ε :=
      mul_le_of_le_one_left hε0.le (S.ratio_lt_one i).le
    have hrj : S.ratio j * ε ≤ ε :=
      mul_le_of_le_one_left hε0.le (S.ratio_lt_one j).le
    rw [Real.dist_eq] at hxa hyb
    rw [hxy] at hyb
    have htri : |S.map i a' - S.map j b'| ≤
        |S.map i x - S.map i a'| + |S.map i x - S.map j b'| := by
      calc |S.map i a' - S.map j b'|
          = |(S.map i a' - S.map i x) + (S.map i x - S.map j b')| := by ring_nf
        _ ≤ |S.map i a' - S.map i x| + |S.map i x - S.map j b'| := abs_add_le _ _
        _ = |S.map i x - S.map i a'| + |S.map i x - S.map j b'| := by
            rw [abs_sub_comm (S.map i a')]
    linarith

/-- The strong open set condition implies the open set condition. -/
theorem StrongOpenSetCondition.openSetCondition {K : Set ℝ}
    (h : S.StrongOpenSetCondition K) : S.OpenSetCondition :=
  let ⟨U, hU, _⟩ := h; ⟨U, hU⟩

end System

end BrownianImages
