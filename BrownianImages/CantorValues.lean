/-
`thm:cantor-values` of `sec:renewal`: the three exact values `eq:cantor-values` of the
middle-thirds pair-distance distribution, and the non-constancy of `G_A` they force.

The computation is the self-similar decomposition of `μ_A × μ_A` into its four blocks.
It runs on the difference mass `pairDiff μ T = (μ × μ){(x,y) : x - y ∈ T}` rather than on
`Φ` itself, since the proof needs the one-sided masses `P(X - Y ≥ 1/2)` and
`P(X - Y > 1/2)` as well as the symmetric ones, and it goes through the Fubini form of
`Recursion.lean`, never through `Measure.prod_sum`, which is stated for countable sums
and not for the `Finset` sums Hutchinson's identity produces.

The closed and the open half line satisfy the same pair of fixed point equations, so the
absence of an atom of the difference law at `1/2` is a consequence of the two equations
here rather than an input to them.

* `pairDiff`, `blockSet`: the difference mass, and the block `{u : u/3 + c ∈ T}` that the
  pair `(S_i, S_j)` of the middle-thirds system sends `T` to.
* `pairDiff_decomp`: the four-block decomposition, the engine of the computation.
* `pairDiff_neg`: symmetry of the difference law, from `Measure.prod_swap`.
* `measure_singleton_zero`: `μ_A{0} = 0`, read off the fixed point `S^A_0(0) = 0`; it is
  what kills the two off-diagonal blocks at `δ = 1/3`.
* `phi_cantor_one_third`, `phi_cantor_half`, `phi_cantor_one_sixth`: the three values of
  `eq:cantor-values`.
* `cantor_g_period`: `eq:g-recursion` for the middle-thirds system, the shift identity
  `G_A(w) = G_A(w - log 3)` of the proof.
* `cantor_values`, `thm_cantor_values`: the values alone, and the complete conclusion of
  the lemma.
-/
import BrownianImages.Recursion

namespace BrownianImages

open MeasureTheory
open scoped ENNReal NNReal

namespace CantorValues

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

/-- The difference law is a probability measure: a set and its complement carry the
complementary masses. -/
theorem pairDiff_add_compl [IsProbabilityMeasure μ] {T : Set ℝ} (hT : MeasurableSet T) :
    pairDiff μ T + pairDiff μ Tᶜ = 1 := by
  have h := measure_add_measure_compl (μ := μ.prod μ) (measurableSet_diffSet hT)
  rw [measure_univ] at h
  simpa only [pairDiff, Set.compl_setOf, Set.mem_compl_iff] using h

/-- The difference mass is additive on disjoint sets. -/
theorem pairDiff_union {T T' : Set ℝ} (hT' : MeasurableSet T') (hd : Disjoint T T') :
    pairDiff μ (T ∪ T') = pairDiff μ T + pairDiff μ T' := by
  have hset : {p : ℝ × ℝ | p.1 - p.2 ∈ T ∪ T'}
      = {p : ℝ × ℝ | p.1 - p.2 ∈ T} ∪ {p : ℝ × ℝ | p.1 - p.2 ∈ T'} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_union]
  rw [pairDiff, hset, measure_union ?_ (measurableSet_diffSet hT')]
  · rfl
  · rw [Set.disjoint_left]
    intro p hp hp'
    exact (Set.disjoint_left.mp hd) hp hp'

/-- Symmetry of the difference law, from `Measure.prod_swap`. -/
theorem pairDiff_neg (μ : Measure ℝ) [SFinite μ] {T : Set ℝ} (hT : MeasurableSet T) :
    pairDiff μ T = pairDiff μ ((fun u : ℝ => -u) ⁻¹' T) := by
  conv_lhs => rw [pairDiff, ← Measure.prod_swap (μ := μ) (ν := μ)]
  rw [Measure.map_apply measurable_swap (measurableSet_diffSet hT), pairDiff]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap, neg_sub]

/-! ### The unit square -/

/-- A probability measure carried by `[0,1]` gives it full mass. -/
theorem measure_Icc_eq_one [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0) :
    μ (Set.Icc (0:ℝ) 1) = 1 := by
  have h := measure_add_measure_compl (μ := μ) (measurableSet_Icc (a := (0:ℝ)) (b := 1))
  rw [hsupp, add_zero, measure_univ] at h
  exact h

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

/-- The difference mass reads only the unit square. -/
theorem pairDiff_eq_inter [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0)
    (T : Set ℝ) :
    pairDiff μ T
      = (μ.prod μ) ({p : ℝ × ℝ | p.1 - p.2 ∈ T} ∩ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) := by
  have hsq : MeasurableSet (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have h := measure_inter_add_sdiff (μ := μ.prod μ) {p : ℝ × ℝ | p.1 - p.2 ∈ T} hsq
  have hd : (μ.prod μ) ({p : ℝ × ℝ | p.1 - p.2 ∈ T} \ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1))
      = 0 := measure_mono_null (fun p hp => hp.2) (prod_compl_square hsupp)
  rw [hd, add_zero] at h
  exact h.symm

/-- A set the difference of two points of `[0,1]` never meets carries no mass. -/
theorem pairDiff_eq_zero [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0)
    {T : Set ℝ} (h : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, x - y ∉ T) :
    pairDiff μ T = 0 := by
  rw [pairDiff_eq_inter hsupp T]
  have hempty : {p : ℝ × ℝ | p.1 - p.2 ∈ T} ∩ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hp, hq⟩
    exact h p.1 hq.1 p.2 hq.2 hp
  rw [hempty, measure_empty]

/-- A set the difference of two points of `[0,1]` always meets carries full mass. -/
theorem pairDiff_eq_one [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0)
    {T : Set ℝ} (h : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, x - y ∈ T) :
    pairDiff μ T = 1 := by
  rw [pairDiff_eq_inter hsupp T]
  have hset : {p : ℝ × ℝ | p.1 - p.2 ∈ T} ∩ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
      = Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 :=
    Set.inter_eq_right.mpr fun p hp => h p.1 hp.1 p.2 hp.2
  rw [hset, Measure.prod_prod, measure_Icc_eq_one hsupp, one_mul]

/-- A block meeting the unit square only where the second coordinate is `0` carries no
mass, once `μ` has no atom at `0`. -/
theorem pairDiff_eq_zero_of_snd [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0)
    (h0 : μ {(0:ℝ)} = 0) {T : Set ℝ}
    (h : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, x - y ∈ T → y = 0) :
    pairDiff μ T = 0 := by
  rw [pairDiff_eq_inter hsupp T]
  refine measure_mono_null (t := (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) ?_ ?_
  · rintro ⟨x, y⟩ ⟨hp, hq⟩
    exact ⟨Set.mem_univ _, h x hq.1 y hq.2 hp⟩
  · rw [Measure.prod_prod, h0, mul_zero]

/-! ### The middle-thirds weights -/

/-- Both ratios of the middle-thirds system are `1/3`. -/
theorem cantorSystem_ratio (i : Fin 2) : cantorSystem.ratio i = 1/3 := rfl

/-- The translation part of `S^A_0`. -/
theorem cantorSystem_shift_zero : cantorSystem.shift 0 = 0 := by
  simp [cantorSystem]

/-- The translation part of `S^A_1`. -/
theorem cantorSystem_shift_one : cantorSystem.shift 1 = 2/3 := by
  simp [cantorSystem]

/-- The weight of each piece is `(1/3)^s = 1/2`. -/
theorem cantor_weight : ((1:ℝ)/3) ^ sCantor = 1/2 := by
  rw [one_div, Real.inv_rpow (by norm_num), rpow_three_sCantor]
  norm_num

/-- The weight as an extended non-negative real. -/
theorem ofReal_cantor_weight : ENNReal.ofReal (((1:ℝ)/3) ^ sCantor) = 2⁻¹ := by
  rw [cantor_weight, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-! ### The atom at the fixed point -/

/-- `μ_A{0} = 0`: the fixed point `S^A_0(0) = 0` read through Hutchinson's identity.
This is what makes the two off-diagonal blocks vanish at `δ = 1/3`. -/
theorem measure_singleton_zero (hA : cantorSystem.IsNatural K sCantor μ) :
    μ {(0:ℝ)} = 0 := by
  haveI := hA.isProbabilityMeasure
  have hsum := hA.measure_eq_sum cantorSystem (measurableSet_singleton (0:ℝ))
  have h0 : cantorSystem.map 0 ⁻¹' ({0} : Set ℝ) = {(0:ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, cantorSystem_map_zero]
    constructor <;> intro h <;> linarith
  have h1 : cantorSystem.map 1 ⁻¹' ({0} : Set ℝ) = {(-2:ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, cantorSystem_map_one]
    constructor <;> intro h <;> linarith
  have hneg : μ {(-2:ℝ)} = 0 := by
    refine measure_mono_null ?_ hA.support_Icc
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    simp [hx]
  rw [Fin.sum_univ_two, h0, h1, hneg, mul_zero, add_zero, cantorSystem_ratio,
    ofReal_cantor_weight] at hsum
  have hfin : μ {(0:ℝ)} ≠ ⊤ := measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul] at hreal
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hreal
  have : (μ {(0:ℝ)}).toReal = 0 := by linarith
  rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
  · exact h
  · exact absurd h hfin

/-! ### The four-block decomposition -/

/-- The block `{u : u/3 + c ∈ T}` that the pair `(S_i, S_j)` of the middle-thirds system
sends `T` to, with `c = b_i - b_j`. -/
def blockSet (c : ℝ) (T : Set ℝ) : Set ℝ := (fun u : ℝ => u / 3 + c) ⁻¹' T

/-- A block of a measurable set is measurable. -/
theorem measurableSet_blockSet (c : ℝ) {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet (blockSet c T) :=
  ((measurable_id.div_const 3).add_const c) hT

/-- One outer block: the inner Hutchinson decomposition, integrated. -/
theorem lintegral_map_decomp (hA : cantorSystem.IsNatural K sCantor μ) {T : Set ℝ}
    (hT : MeasurableSet T) (i : Fin 2) :
    ∫⁻ x, μ {y : ℝ | cantorSystem.map i x - y ∈ T} ∂μ
      = 2⁻¹ * pairDiff μ (blockSet (cantorSystem.shift i) T)
        + 2⁻¹ * pairDiff μ (blockSet (cantorSystem.shift i - 2/3) T) := by
  haveI := hA.isProbabilityMeasure
  have hstep : ∀ x : ℝ, μ {y : ℝ | cantorSystem.map i x - y ∈ T}
      = 2⁻¹ * μ {y : ℝ | x - y ∈ blockSet (cantorSystem.shift i) T}
        + 2⁻¹ * μ {y : ℝ | x - y ∈ blockSet (cantorSystem.shift i - 2/3) T} := by
    intro x
    have hmeas : MeasurableSet {y : ℝ | cantorSystem.map i x - y ∈ T} :=
      (measurable_const.sub measurable_id) hT
    have hj : ∀ j : Fin 2, cantorSystem.map j ⁻¹' {y : ℝ | cantorSystem.map i x - y ∈ T}
        = {y : ℝ | x - y ∈ blockSet (cantorSystem.shift i - cantorSystem.shift j) T} := by
      intro j
      ext y
      have hval : cantorSystem.map i x - cantorSystem.map j y
          = (x - y) / 3 + (cantorSystem.shift i - cantorSystem.shift j) := by
        simp only [System.map, cantorSystem_ratio]
        ring
      simp only [Set.mem_preimage, Set.mem_setOf_eq, blockSet, hval]
    rw [hA.measure_eq_sum cantorSystem hmeas, Fin.sum_univ_two, hj 0, hj 1]
    simp only [cantorSystem_ratio, ofReal_cantor_weight, cantorSystem_shift_zero,
      cantorSystem_shift_one, sub_zero]
  have hm : ∀ c : ℝ, Measurable fun x : ℝ => μ {y : ℝ | x - y ∈ blockSet c T} :=
    fun c => measurable_section (measurableSet_blockSet c hT) μ
  rw [lintegral_congr hstep,
    lintegral_add_left ((hm _).const_mul _),
    lintegral_const_mul _ (hm _), lintegral_const_mul _ (hm _),
    ← pairDiff_eq_lintegral μ (measurableSet_blockSet _ hT),
    ← pairDiff_eq_lintegral μ (measurableSet_blockSet _ hT)]

/-- The self-similar decomposition of `μ_A × μ_A` into its four blocks. -/
theorem pairDiff_decomp (hA : cantorSystem.IsNatural K sCantor μ) {T : Set ℝ}
    (hT : MeasurableSet T) :
    pairDiff μ T = 4⁻¹ * (pairDiff μ (blockSet 0 T) + pairDiff μ (blockSet (-(2/3)) T)
      + pairDiff μ (blockSet (2/3) T) + pairDiff μ (blockSet 0 T)) := by
  haveI := hA.isProbabilityMeasure
  have h4 : (4:ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  rw [pairDiff_eq_lintegral μ hT, hA.lintegral_eq_sum cantorSystem (measurable_section hT μ),
    Fin.sum_univ_two, lintegral_map_decomp hA hT 0, lintegral_map_decomp hA hT 1]
  simp only [cantorSystem_ratio, ofReal_cantor_weight, cantorSystem_shift_zero,
    cantorSystem_shift_one, zero_sub, sub_self]
  rw [h4]
  ring

/-! ### The blocks that carry no mass -/

/-- A block lying beyond the diameter of the unit interval carries no mass. -/
theorem pairDiff_eq_zero_of_gt_one [IsProbabilityMeasure μ] (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0)
    {T : Set ℝ} (hT : ∀ u ∈ T, 1 < u) : pairDiff μ T = 0 := by
  refine pairDiff_eq_zero hsupp ?_
  intro x hx y hy hmem
  have h := hT _ hmem
  exact absurd h (by simp only [not_lt]; linarith [hx.2, hy.1])

/-! ### `Φ_A(1/3) = 1/2`: the corner blocks -/

/-- The corner block: `x - y ∈ [1,3]` forces `y = 0` inside the unit square. -/
theorem pairDiff_Icc_one_three (hA : cantorSystem.IsNatural K sCantor μ) :
    pairDiff μ (Set.Icc (1:ℝ) 3) = 0 := by
  haveI := hA.isProbabilityMeasure
  refine pairDiff_eq_zero_of_snd hA.support_Icc (measure_singleton_zero hA) ?_
  intro x hx y hy hmem
  have h1 : (1:ℝ) ≤ x - y := hmem.1
  linarith [hx.2, hy.1]

/-- The reflected corner block, by the symmetry of the difference law. -/
theorem pairDiff_Icc_neg_three_neg_one (hA : cantorSystem.IsNatural K sCantor μ) :
    pairDiff μ (Set.Icc (-3:ℝ) (-1)) = 0 := by
  haveI := hA.isProbabilityMeasure
  have hneg : (fun u : ℝ => -u) ⁻¹' Set.Icc (-3:ℝ) (-1) = Set.Icc (1:ℝ) 3 := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [pairDiff_neg μ measurableSet_Icc, hneg, pairDiff_Icc_one_three hA]

/-! ### The one-sided masses at `1/2` -/

/-- Only the block `(S_1, S_0)` survives at level `1/2`: the event `X - Y ≥ 1/2` asks for
the first digit of `X` to be `2` and that of `Y` to be `0`. -/
theorem pairDiff_Ici_half (hA : cantorSystem.IsNatural K sCantor μ) :
    pairDiff μ (Set.Ici (1/2:ℝ)) = 4⁻¹ * pairDiff μ (Set.Ici (-(1/2):ℝ)) := by
  haveI := hA.isProbabilityMeasure
  have hb0 : blockSet 0 (Set.Ici (1/2:ℝ)) = Set.Ici (3/2:ℝ) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Ici, add_zero]
    constructor <;> intro h <;> linarith
  have hbm : blockSet (-(2/3)) (Set.Ici (1/2:ℝ)) = Set.Ici (7/2:ℝ) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  have hbp : blockSet (2/3) (Set.Ici (1/2:ℝ)) = Set.Ici (-(1/2):ℝ) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  have hz0 : pairDiff μ (Set.Ici (3/2:ℝ)) = 0 :=
    pairDiff_eq_zero_of_gt_one hA.support_Icc (by
      intro u hu; simp only [Set.mem_Ici] at hu; linarith)
  have hz1 : pairDiff μ (Set.Ici (7/2:ℝ)) = 0 :=
    pairDiff_eq_zero_of_gt_one hA.support_Icc (by
      intro u hu; simp only [Set.mem_Ici] at hu; linarith)
  rw [pairDiff_decomp hA measurableSet_Ici, hb0, hbm, hbp, hz0, hz1]
  simp only [zero_add, add_zero]

/-- The same block decomposition for the open half line. -/
theorem pairDiff_Ioi_half (hA : cantorSystem.IsNatural K sCantor μ) :
    pairDiff μ (Set.Ioi (1/2:ℝ)) = 4⁻¹ * pairDiff μ (Set.Ioi (-(1/2):ℝ)) := by
  haveI := hA.isProbabilityMeasure
  have hb0 : blockSet 0 (Set.Ioi (1/2:ℝ)) = Set.Ioi (3/2:ℝ) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Ioi, add_zero]
    constructor <;> intro h <;> linarith
  have hbm : blockSet (-(2/3)) (Set.Ioi (1/2:ℝ)) = Set.Ioi (7/2:ℝ) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hbp : blockSet (2/3) (Set.Ioi (1/2:ℝ)) = Set.Ioi (-(1/2):ℝ) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hz0 : pairDiff μ (Set.Ioi (3/2:ℝ)) = 0 :=
    pairDiff_eq_zero_of_gt_one hA.support_Icc (by
      intro u hu; simp only [Set.mem_Ioi] at hu; linarith)
  have hz1 : pairDiff μ (Set.Ioi (7/2:ℝ)) = 0 :=
    pairDiff_eq_zero_of_gt_one hA.support_Icc (by
      intro u hu; simp only [Set.mem_Ioi] at hu; linarith)
  rw [pairDiff_decomp hA measurableSet_Ioi, hb0, hbm, hbp, hz0, hz1]
  simp only [zero_add, add_zero]

/-- The difference law is symmetric: the two tails below `-1/2` and above `1/2` agree. -/
theorem pairDiff_Iio_neg_half (μ : Measure ℝ) [SFinite μ] :
    pairDiff μ (Set.Iio (-(1/2):ℝ)) = pairDiff μ (Set.Ioi (1/2:ℝ)) := by
  rw [pairDiff_neg μ measurableSet_Iio]
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- The closed tails below `-1/2` and above `1/2` agree. -/
theorem pairDiff_Iic_neg_half (μ : Measure ℝ) [SFinite μ] :
    pairDiff μ (Set.Iic (-(1/2):ℝ)) = pairDiff μ (Set.Ici (1/2:ℝ)) := by
  rw [pairDiff_neg μ measurableSet_Iic]
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
  constructor <;> intro h <;> linarith

end CantorValues

open CantorValues in
/-- `eq:cantor-values`, the first value: agreeing first ternary digits give
`|X - Y| ≤ 1/3`, differing ones give `|X - Y| ≥ 1/3`, with equality only at the corner
of the unit square, which carries no mass. -/
theorem phi_cantor_one_third {K : Set ℝ} {μ : Measure ℝ}
    (hA : cantorSystem.IsNatural K sCantor μ) : Phi μ (1/3) = 1/2 := by
  haveI := hA.isProbabilityMeasure
  have hb0 : blockSet 0 (Set.Icc (-(1/3):ℝ) (1/3)) = Set.Icc (-1:ℝ) 1 := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Icc, add_zero]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hbm : blockSet (-(2/3)) (Set.Icc (-(1/3):ℝ) (1/3)) = Set.Icc (1:ℝ) 3 := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hbp : blockSet (2/3) (Set.Icc (-(1/3):ℝ) (1/3)) = Set.Icc (-3:ℝ) (-1) := by
    ext u
    simp only [blockSet, Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hone : pairDiff μ (Set.Icc (-1:ℝ) 1) = 1 := by
    refine pairDiff_eq_one hA.support_Icc ?_
    intro x hx y hy
    exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  rw [phi_eq_pairDiff, pairDiff_decomp hA measurableSet_Icc, hb0, hbm, hbp, hone,
    pairDiff_Icc_one_three hA, pairDiff_Icc_neg_three_neg_one hA,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

open CantorValues in
/-- `eq:cantor-values`, the second value.  The mass `q = P(X - Y ≥ 1/2)` satisfies
`q = (1 - q)/4`, hence `q = 1/5` and `Φ_A(1/2) = 1 - 2q = 3/5`.  The closed and the open
half line satisfy the same pair of equations, which is what gives the absence of an atom
at `1/2` rather than assuming it. -/
theorem phi_cantor_half {K : Set ℝ} {μ : Measure ℝ}
    (hA : cantorSystem.IsNatural K sCantor μ) : Phi μ (1/2) = 3/5 := by
  haveI := hA.isProbabilityMeasure
  have hdisj : Disjoint (Set.Iio (-(1/2):ℝ)) (Set.Ioi (1/2:ℝ)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    simp only [Set.mem_Iio] at hu
    simp only [Set.mem_Ioi] at hu'
    linarith
  have hcompl : (Set.Icc (-(1/2):ℝ) (1/2))ᶜ = Set.Iio (-(1/2):ℝ) ∪ Set.Ioi (1/2:ℝ) := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      by_cases h1 : u < -(1/2 : ℝ)
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact h ⟨not_lt.mp h1, not_lt.mp h2⟩
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  have e1 := congrArg ENNReal.toReal (pairDiff_Ici_half hA)
  have e3 := congrArg ENNReal.toReal (pairDiff_Ioi_half hA)
  have e2 : pairDiff μ (Set.Ici (-(1/2):ℝ)) + pairDiff μ (Set.Ioi (1/2:ℝ)) = 1 := by
    have h := pairDiff_add_compl (μ := μ) (measurableSet_Ici (a := (-(1/2):ℝ)))
    rwa [Set.compl_Ici, pairDiff_Iio_neg_half μ] at h
  have e4 : pairDiff μ (Set.Ioi (-(1/2):ℝ)) + pairDiff μ (Set.Ici (1/2:ℝ)) = 1 := by
    have h := pairDiff_add_compl (μ := μ) (measurableSet_Ioi (a := (-(1/2):ℝ)))
    rwa [Set.compl_Ioi, pairDiff_Iic_neg_half μ] at h
  have e5 : pairDiff μ (Set.Icc (-(1/2):ℝ) (1/2))
      + (pairDiff μ (Set.Ioi (1/2:ℝ)) + pairDiff μ (Set.Ioi (1/2:ℝ))) = 1 := by
    have h := pairDiff_add_compl (μ := μ)
      (measurableSet_Icc (a := (-(1/2):ℝ)) (b := (1/2:ℝ)))
    rwa [hcompl, pairDiff_union measurableSet_Ioi hdisj, pairDiff_Iio_neg_half μ] at h
  have e2' := congrArg ENNReal.toReal e2
  have e4' := congrArg ENNReal.toReal e4
  have e5' := congrArg ENNReal.toReal e5
  rw [ENNReal.toReal_add (pairDiff_ne_top _) (pairDiff_ne_top _), ENNReal.toReal_one] at e2' e4'
  rw [ENNReal.toReal_add (pairDiff_ne_top _)
      (ENNReal.add_ne_top.mpr ⟨pairDiff_ne_top _, pairDiff_ne_top _⟩),
    ENNReal.toReal_add (pairDiff_ne_top _) (pairDiff_ne_top _), ENNReal.toReal_one] at e5'
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at e1 e3
  simp only [ENNReal.toReal_ofNat] at e1 e3
  rw [phi_eq_pairDiff]
  linarith

open CantorValues in
/-- `eq:cantor-values`, the third value.  Since `1/6` lies below the separation gap,
`eq:phi-recursion` gives `Φ_A(1/6) = ½ Φ_A(1/2) = 3/10`. -/
theorem phi_cantor_one_sixth {K : Set ℝ} {μ : Measure ℝ}
    (hA : cantorSystem.IsNatural K sCantor μ) : Phi μ (1/6) = 3/10 := by
  haveI := hA.isProbabilityMeasure
  have hsep : cantorSystem.StronglySeparated K (1/3) :=
    cantorSystem_stronglySeparated hA.attractor.2.2.1
  have hval : ((1:ℝ)/3) ^ (2 * sCantor) = 1/4 := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/3), cantor_weight,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h := phi_recursion cantorSystem hsep hA (by norm_num : (0:ℝ) < 1/6)
    (by norm_num : (1:ℝ)/6 < 1/3)
  rw [Fin.sum_univ_two] at h
  simp only [cantorSystem_ratio, hval, show (1:ℝ)/6/(1/3) = 1/2 by norm_num,
    phi_cantor_half hA] at h
  rw [h]
  norm_num

open CantorValues in
/-- `eq:g-recursion` for the middle-thirds system: the two pieces carry the same
log-ratio `log 3`, so the profile satisfies `G_A(w) = G_A(w - log 3)` for `w > log 3`. -/
theorem cantor_g_period {K : Set ℝ} {μ : Measure ℝ}
    (hA : cantorSystem.IsNatural K sCantor μ) :
    ∀ w, Real.log 3 < w → G sCantor μ w = G sCantor μ (w - Real.log 3) := by
  have hsep : cantorSystem.StronglySeparated K (1/3) :=
    cantorSystem_stronglySeparated hA.attractor.2.2.1
  have hlr : ∀ i : Fin 2, cantorSystem.logRatio i = Real.log 3 := by
    intro i
    rw [System.logRatio, cantorSystem_ratio]
    norm_num
  intro w hw
  have h := g_recursion cantorSystem hsep hA (w := w)
    (by rw [show ((1:ℝ)/3)⁻¹ = 3 by norm_num]; exact hw)
  rw [Fin.sum_univ_two, hlr 0, hlr 1] at h
  simp only [cantorSystem_ratio, cantor_weight] at h
  linarith

/-- `thm:cantor-values`, `eq:cantor-values`: the three exact values of the middle-thirds
pair-distance distribution. -/
theorem cantor_values {KA : Set ℝ} {μA : Measure ℝ}
    (hA : cantorSystem.IsNatural KA sCantor μA) :
    Phi μA (1/3) = 1/2 ∧ Phi μA (1/2) = 3/5 ∧ Phi μA (1/6) = 3/10 :=
  ⟨phi_cantor_one_third hA, phi_cantor_half hA, phi_cantor_one_sixth hA⟩

/-- `thm:cantor-values` as one statement: the three exact values together with the
non-constancy they force on every period of `G_A`. -/
theorem thm_cantor_values {KA : Set ℝ} {μA : Measure ℝ}
    (hA : cantorSystem.IsNatural KA sCantor μA) :
    (Phi μA (1/3) = 1/2 ∧ Phi μA (1/2) = 3/5 ∧ Phi μA (1/6) = 3/10) ∧
      ∀ w, Real.log 3 ≤ w →
        ∃ w₁ ∈ Set.Icc w (w + Real.log 3), ∃ w₂ ∈ Set.Icc w (w + Real.log 3),
          G sCantor μA w₁ ≠ G sCantor μA w₂ :=
  ⟨cantor_values hA, fun _ hw =>
    G_nonconstant_on_period (phi_cantor_one_third hA) (phi_cantor_one_sixth hA)
      (cantor_g_period hA) hw⟩

end BrownianImages
