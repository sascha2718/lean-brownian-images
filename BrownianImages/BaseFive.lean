/-
`sec:examples` of `BrownianImagesComplete.tex`, `thm:base-five-profiles`: the two
base-five missing-digit sets with digit sets `D₁ = {0,1,4}` and `D₂ = {0,2,4}`.

Both systems have three maps of ratio `1/5`, dimension `s = log 3 / log 5`, and the
open set condition with `U = (0,1)`.  Conditioning on the first digits turns
Hutchinson's identity into `eq:base-five-recursion`,
`Φ₁(δ) = Φ₁(5δ)/3 + 2Ψ(5δ)/9` and `Φ₂(δ) = Φ₂(5δ)/3` for `0 < δ ≤ 1/5`, where
`Ψ(a) = P((1 - X) + Y ≤ a)` is the mass near the contact of the pieces `f₀K₁` and
`f₁K₁`; `Ψ` satisfies `Ψ(a) = Ψ(5a)/9` and `Ψ(1) = 1/2`, and the exact values
`eq:base-five-distances` follow.  In logarithmic coordinates the recursion says that
`G₁(w) - G₁(w - p)` is non-negative and `O(e^{-sw})` while `G₂` is exactly periodic, so
both profiles converge along the period `p = log 5` to continuous periodic limits, with
`G̃₁(0) = 3/2` and `G̃₂(0) = 1`.  The expected profiles `H_j` then converge to the
smoothed limits, which `thm:smoothing-injective` keeps apart.

* `baseFiveSystem`, `baseFiveDigitsA`, `baseFiveDigitsB`, `baseFiveDim`: the systems.
* `baseFiveSystem_isDimension`, `baseFiveSystem_openSetCondition`: their dimension and
  the open set condition.
* `IsNatural.prod_apply_eq_double_sum`: Hutchinson's identity for `μ × μ` on any set.
* `Psi`, `psi_recursion`, `psi_one`, `psi_five_pow`: the contact mass.
* `phiA_recursion`, `phiB_recursion`, `phiA_five_pow`, `phiB_five_pow`:
  `eq:base-five-recursion` and `eq:base-five-distances`.
-/
import BrownianImages.Schief
import BrownianImages.Recursion
import BrownianImages.Asymptotics
import BrownianImages.FourierMultiplier
import BrownianImages.Periodic

namespace BrownianImages

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ### The two systems -/

/-- The base-five system with digit set `D`: the maps `x ↦ (x + d)/5`, `d ∈ D`. -/
noncomputable def baseFiveSystem (D : Fin 3 → ℕ) (hD : ∀ i, D i ≤ 4) : System (Fin 3) where
  ratio _ := 1 / 5
  sign _ := 1
  shift i := (D i : ℝ) / 5
  ratio_pos _ := by norm_num
  ratio_lt_one _ := by norm_num
  sign_eq _ := Or.inl rfl
  mapsTo i x hx := by
    obtain ⟨hx0, hx1⟩ := hx
    have hd0 : (0:ℝ) ≤ (D i : ℝ) := by exact_mod_cast Nat.zero_le _
    have hd4 : (D i : ℝ) ≤ 4 := by exact_mod_cast hD i
    constructor
    · show (0:ℝ) ≤ 1 * (1 / 5) * x + (D i : ℝ) / 5
      linarith
    · show 1 * (1 / 5) * x + (D i : ℝ) / 5 ≤ 1
      linarith

/-- The digit set `D₁ = {0, 1, 4}`. -/
def baseFiveDigitsA : Fin 3 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 4

/-- The digit set `D₂ = {0, 2, 4}`. -/
def baseFiveDigitsB : Fin 3 → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 4

theorem baseFiveDigitsA_le : ∀ i, baseFiveDigitsA i ≤ 4 := by decide

theorem baseFiveDigitsB_le : ∀ i, baseFiveDigitsB i ≤ 4 := by decide

theorem baseFiveDigitsA_injective : Function.Injective baseFiveDigitsA := by decide

theorem baseFiveDigitsB_injective : Function.Injective baseFiveDigitsB := by decide

/-- The common dimension `s = log 3 / log 5`. -/
noncomputable def baseFiveDim : ℝ := Real.log 3 / Real.log 5

theorem log_five_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)

theorem baseFiveDim_pos : 0 < baseFiveDim :=
  div_pos (Real.log_pos (by norm_num)) log_five_pos

theorem baseFiveDim_lt_one : baseFiveDim < 1 := by
  rw [baseFiveDim, div_lt_one log_five_pos]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `5^s = 3`. -/
theorem five_rpow_baseFiveDim : (5:ℝ) ^ baseFiveDim = 3 := by
  rw [baseFiveDim, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5),
    mul_div_cancel₀ _ log_five_pos.ne', Real.exp_log (by norm_num)]

/-- `(1/5)^s = 1/3`. -/
theorem inv_five_rpow_baseFiveDim : (1 / 5 : ℝ) ^ baseFiveDim = 1 / 3 := by
  rw [one_div, Real.inv_rpow (by norm_num), five_rpow_baseFiveDim, one_div]

theorem baseFiveSystem_ratio (D : Fin 3 → ℕ) (hD : ∀ i, D i ≤ 4) (i : Fin 3) :
    (baseFiveSystem D hD).ratio i = 1 / 5 := rfl

theorem baseFiveSystem_map (D : Fin 3 → ℕ) (hD : ∀ i, D i ≤ 4) (i : Fin 3) (x : ℝ) :
    (baseFiveSystem D hD).map i x = (x + D i) / 5 := by
  show 1 * (1 / 5) * x + (D i : ℝ) / 5 = (x + D i) / 5
  ring

/-- Both systems have dimension `s`: `3 · 5^{-s} = 1`. -/
theorem baseFiveSystem_isDimension (D : Fin 3 → ℕ) (hD : ∀ i, D i ≤ 4) :
    (baseFiveSystem D hD).IsDimension baseFiveDim := by
  show ∑ i : Fin 3, (baseFiveSystem D hD).ratio i ^ baseFiveDim = 1
  simp only [baseFiveSystem_ratio, inv_five_rpow_baseFiveDim, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- Both systems satisfy the open set condition with `U = (0,1)`. -/
theorem baseFiveSystem_openSetCondition (D : Fin 3 → ℕ) (hD : ∀ i, D i ≤ 4)
    (hinj : Function.Injective D) : (baseFiveSystem D hD).OpenSetCondition := by
  refine ⟨Ioo 0 1, isOpen_Ioo, ⟨1/2, by norm_num, by norm_num⟩, Metric.isBounded_Ioo 0 1,
    ?_, ?_⟩
  · intro i x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hd0 : (0:ℝ) ≤ (D i : ℝ) := by exact_mod_cast Nat.zero_le _
    have hd4 : (D i : ℝ) ≤ 4 := by exact_mod_cast hD i
    rw [baseFiveSystem_map]
    constructor <;> linarith
  · intro i j hij
    have hne : D i ≠ D j := fun h => hij (hinj h)
    rw [Set.disjoint_left]
    rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩ ⟨y, ⟨hy0, hy1⟩, hxy⟩
    rw [baseFiveSystem_map, baseFiveSystem_map] at hxy
    have hdiff : (x + D i) = (y + D j) := by linarith
    rcases lt_or_gt_of_ne hne with h | h
    · have : (D i : ℝ) + 1 ≤ D j := by exact_mod_cast h
      linarith
    · have : (D j : ℝ) + 1 ≤ D i := by exact_mod_cast h
      linarith

/-! ### Hutchinson's identity for the product measure -/

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- Hutchinson's identity in both coordinates, on an arbitrary measurable set:
`(μ × μ)(E) = ∑_{i,j} p_i p_j ((S_i)_* μ × (S_j)_* μ)(E)`. -/
theorem IsNatural.prod_apply_eq_double_sum {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    (μ.prod μ) E = ∑ i, ∑ j, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio j ^ s) *
      ((μ.map (S.map i)).prod (μ.map (S.map j))) E := by
  have := hμ.isProbabilityMeasure
  have hsec : Measurable fun x => μ (Prod.mk x ⁻¹' E) := measurable_measure_prodMk_left hE
  rw [Measure.prod_apply hE, hμ.lintegral_eq_sum S hsec]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmeas : ∀ j : ι, Measurable fun x =>
      (μ.map (S.map j)) (Prod.mk (S.map i x) ⁻¹' E) := fun j =>
    (measurable_measure_prodMk_left (ν := μ.map (S.map j)) hE).comp (S.measurable_map i)
  have hpt : ∀ x, μ (Prod.mk (S.map i x) ⁻¹' E)
      = ∑ j, ENNReal.ofReal (S.ratio j ^ s) * (μ.map (S.map j)) (Prod.mk (S.map i x) ⁻¹' E) := by
    intro x
    rw [hμ.measure_eq_sum S (measurable_prodMk_left hE)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Measure.map_apply (S.measurable_map j) (measurable_prodMk_left hE)]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun j _ => (hmeas j).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_const_mul _ (hmeas j), mul_assoc]
  congr 1
  rw [Measure.prod_apply hE, lintegral_map (measurable_measure_prodMk_left hE)
    (S.measurable_map i)]

/-- An off-diagonal product block is the product measure of the pulled-back set. -/
theorem IsNatural.prod_map_apply {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (i j : ι) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    ((μ.map (S.map i)).prod (μ.map (S.map j))) E
      = (μ.prod μ) {p : ℝ × ℝ | (S.map i p.1, S.map j p.2) ∈ E} := by
  have := hμ.isProbabilityMeasure
  rw [Measure.map_prod_map _ _ (S.measurable_map i) (S.measurable_map j),
    Measure.map_apply ((S.measurable_map i).prodMap (S.measurable_map j)) hE]
  rfl

end System

/-! ### The unit square carries the product measure -/

/-- For a measure on `[0,1]`, two sets that agree on the unit square have the same
product mass. -/
theorem prod_measure_eq_of_eqOn_unitSquare {μ : Measure ℝ} [SFinite μ]
    (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0) {A B : Set (ℝ × ℝ)}
    (h : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p ∈ A ↔ p ∈ B) : (μ.prod μ) A = (μ.prod μ) B := by
  set Q : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 with hQ
  have hQm : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hQc : (μ.prod μ) Qᶜ = 0 := by
    have hsub : Qᶜ ⊆ ((Icc (0:ℝ) 1)ᶜ ×ˢ univ) ∪ (univ ×ˢ (Icc (0:ℝ) 1)ᶜ) := by
      intro p hp
      simp only [hQ, Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [Measure.prod_prod, hμ, zero_mul]
    · rw [Measure.prod_prod, hμ, mul_zero]
  have hAQ : A ∩ Q = B ∩ Q := by
    ext p
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨hA, hQ'⟩
      exact ⟨(h p hQ').mp hA, hQ'⟩
    · rintro ⟨hB, hQ'⟩
      exact ⟨(h p hQ').mpr hB, hQ'⟩
  have key : ∀ C : Set (ℝ × ℝ), (μ.prod μ) C = (μ.prod μ) (C ∩ Q) := by
    intro C
    rw [← measure_inter_add_sdiff C hQm]
    have : (μ.prod μ) (C \ Q) = 0 := measure_mono_null (Set.sdiff_subset_compl _ _) hQc
    rw [this, add_zero]
  rw [key A, key B, hAQ]

/-! ### The contact mass `Ψ` -/

/-- `Ψ(a) = (μ × μ){(x,y) : (1 - x) + y ≤ a}`, the mass near the contact point of the
pieces `f₀K` and `f₁K`. -/
noncomputable def Psi (μ : Measure ℝ) (a : ℝ) : ℝ :=
  ((μ.prod μ) {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ a}).toReal

theorem measurableSet_psiSet (a : ℝ) :
    MeasurableSet {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ a} :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem Psi_nonneg (μ : Measure ℝ) (a : ℝ) : 0 ≤ Psi μ a := ENNReal.toReal_nonneg

/-- The swapped contact set has the same mass. -/
theorem prod_measure_swap_contact {μ : Measure ℝ} [SFinite μ] (a : ℝ) :
    (μ.prod μ) {p : ℝ × ℝ | (1 - p.2) + p.1 ≤ a} = (μ.prod μ) {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ a} := by
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage
    (measurableSet_psiSet a).nullMeasurableSet
  rw [← h]
  rfl

/-! ### The first-level decomposition for a base-five system -/

/-- Hutchinson's identity for a base-five system, with the maps written out. -/
theorem baseFive_prod_eq {D : Fin 3 → ℕ} {hD : ∀ i, D i ≤ 4} {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (baseFiveSystem D hD).IsNatural K baseFiveDim μ) {E : Set (ℝ × ℝ)}
    (hE : MeasurableSet E) :
    ((μ.prod μ) E).toReal = ∑ i, ∑ j, (1 / 9 : ℝ) *
      ((μ.prod μ) {p : ℝ × ℝ | ((p.1 + D i) / 5, (p.2 + D j) / 5) ∈ E}).toReal := by
  have := hμ.isProbabilityMeasure
  rw [hμ.prod_apply_eq_double_sum _ hE, ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr
    fun j _ => ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hμ.prod_map_apply _ i j hE, ENNReal.toReal_mul, ENNReal.toReal_mul, baseFiveSystem_ratio,
    baseFiveSystem_ratio, inv_five_rpow_baseFiveDim, ENNReal.toReal_ofReal (by norm_num)]
  simp only [baseFiveSystem_map]
  ring

/-- The pulled-back pair-distance set. -/
theorem pullback_phiSet (d d' δ : ℝ) :
    {p : ℝ × ℝ | ((p.1 + d) / 5, (p.2 + d') / 5) ∈ {q : ℝ × ℝ | |q.1 - q.2| ≤ δ}}
      = {p : ℝ × ℝ | |p.1 - p.2 + (d - d')| ≤ 5 * δ} := by
  ext p
  simp only [Set.mem_ofPred_eq]
  rw [show (p.1 + d) / 5 - (p.2 + d') / 5 = (p.1 - p.2 + (d - d')) / 5 by ring, abs_div,
    abs_of_pos (by norm_num : (0:ℝ) < 5), div_le_iff₀ (by norm_num), mul_comm]

/-- The pulled-back contact set. -/
theorem pullback_psiSet (d d' a : ℝ) :
    {p : ℝ × ℝ | ((p.1 + d) / 5, (p.2 + d') / 5) ∈ {q : ℝ × ℝ | (1 - q.1) + q.2 ≤ a}}
      = {p : ℝ × ℝ | (5 - d + d') + (p.2 - p.1) ≤ 5 * a} := by
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Mass is monotone along inclusions that hold on the unit square. -/
theorem prod_measure_le_of_subset_on_unitSquare {μ : Measure ℝ} [SFinite μ]
    (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0) {A B : Set (ℝ × ℝ)}
    (h : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p ∈ A → p ∈ B) : (μ.prod μ) A ≤ (μ.prod μ) B := by
  have hAQ : (μ.prod μ) A = (μ.prod μ) (A ∩ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    prod_measure_eq_of_eqOn_unitSquare hμ fun p hp => ⟨fun hA => ⟨hA, hp⟩, fun hA => hA.1⟩
  rw [hAQ]
  exact measure_mono fun p ⟨hA, hQ⟩ => h p hQ hA

/-- A set missing the unit square is null. -/
theorem prod_measure_eq_zero_of_gap {μ : Measure ℝ} [SFinite μ] (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0)
    {A : Set (ℝ × ℝ)} (h : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p ∉ A) : (μ.prod μ) A = 0 :=
  le_antisymm ((prod_measure_le_of_subset_on_unitSquare hμ (B := ∅) fun p hp hA =>
    (h p hp hA).elim).trans (by rw [measure_empty])) zero_le

/-- A set meeting the unit square in one point is null for an atomless measure. -/
theorem prod_measure_eq_zero_of_subset_singleton {μ : Measure ℝ} [SFinite μ]
    (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0) (hatom : ∀ x, μ {x} = 0) {A : Set (ℝ × ℝ)} (x₀ y₀ : ℝ)
    (h : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p ∈ A → p = (x₀, y₀)) : (μ.prod μ) A = 0 := by
  refine le_antisymm ((prod_measure_le_of_subset_on_unitSquare hμ (B := {(x₀, y₀)})
    fun p hp hA => h p hp hA).trans ?_) zero_le
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, hatom, zero_mul]

/-- The unit square has full mass. -/
theorem prod_measure_eq_one_of_unitSquare_subset {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0) {A : Set (ℝ × ℝ)}
    (h : Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 ⊆ A) : (μ.prod μ) A = 1 := by
  have hIcc : μ (Icc (0:ℝ) 1) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp hμ
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = (μ.prod μ) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
        rw [Measure.prod_prod, hIcc, mul_one]
    _ ≤ (μ.prod μ) A := measure_mono h

/-! ### `eq:base-five-recursion` -/

section Recursion

variable {K : Set ℝ} {μ : Measure ℝ} {A : ℝ}

/-- `Φ(1) = 1` for a measure on `[0,1]`. -/
theorem phi_one_of_support [IsProbabilityMeasure μ] (hsupp : μ (Icc (0:ℝ) 1)ᶜ = 0) :
    Phi μ 1 = 1 := by
  unfold Phi
  rw [prod_measure_eq_one_of_unitSquare_subset hsupp, ENNReal.toReal_one]
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  simp only [Set.mem_ofPred_eq]
  rw [abs_le]
  constructor <;> linarith

/-- Shifting the pair-distance set by at least `3` empties it on the unit square. -/
theorem phiSet_shift_null [SFinite μ] (hsupp : μ (Icc (0:ℝ) 1)ᶜ = 0) {δ : ℝ}
    (hδ1 : δ ≤ 1 / 5) {k : ℝ} (hk : 3 ≤ |k|) :
    (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2 + k| ≤ 5 * δ} = 0 := by
  refine prod_measure_eq_zero_of_gap hsupp ?_
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hxy
  simp only [Set.mem_ofPred_eq] at hxy
  dsimp only at hx0 hx1 hy0 hy1
  have h1 : |x - y + k| ≥ |k| - |x - y| := by
    have := abs_sub_abs_le_abs_sub k (-(x - y))
    rw [sub_neg_eq_add, abs_neg, add_comm] at this
    linarith
  have h2 : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **`eq:base-five-recursion` for `D₂ = {0,2,4}`**: `Φ₂(δ) = Φ₂(5δ)/3` for `0 < δ ≤ 1/5`,
since distinct first digits keep the pieces at distance at least `1/5`, with equality
only at endpoints. -/
theorem phiB_recursion (hμ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K
    baseFiveDim μ) (hFrost : IsFrostman baseFiveDim A μ) {δ : ℝ} (hδ1 : δ ≤ 1 / 5) :
    Phi μ δ = 1 / 3 * Phi μ (5 * δ) := by
  have := hμ.isProbabilityMeasure
  have hsupp := hFrost.support
  have hatom : ∀ x, μ {x} = 0 := fun x => hFrost.measure_singleton baseFiveDim_pos x
  unfold Phi
  rw [baseFive_prod_eq hμ (measurableSet_phiSet δ), Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [baseFiveDigitsB, Nat.cast_zero, Nat.cast_ofNat, pullback_phiSet]
  -- the off-diagonal terms vanish
  have hgap : ∀ k : ℝ, 3 ≤ |k| →
      (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2 + k| ≤ 5 * δ} = 0 :=
    fun k hk => phiSet_shift_null hsupp hδ1 hk
  have hcorner : ∀ k : ℝ, |k| = 2 →
      (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2 + k| ≤ 5 * δ} = 0 := by
    intro k hk
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 2) |>.mp hk with rfl | rfl
    · refine prod_measure_eq_zero_of_subset_singleton hsupp hatom 0 1 ?_
      rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hxy
      simp only [Set.mem_ofPred_eq] at hxy
      dsimp only at hx0 hx1 hy0 hy1
      have := abs_le.mp hxy
      have hx : x = 0 := by linarith
      have hy : y = 1 := by linarith
      rw [hx, hy]
    · refine prod_measure_eq_zero_of_subset_singleton hsupp hatom 1 0 ?_
      rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hxy
      simp only [Set.mem_ofPred_eq] at hxy
      dsimp only at hx0 hx1 hy0 hy1
      have := abs_le.mp hxy
      have hx : x = 1 := by linarith
      have hy : y = 0 := by linarith
      rw [hx, hy]
  rw [hcorner (0 - 2) (by norm_num), hcorner (2 - 0) (by norm_num), hcorner (2 - 4) (by norm_num),
    hcorner (4 - 2) (by norm_num), hgap (0 - 4) (by norm_num), hgap (4 - 0) (by norm_num)]
  simp only [ENNReal.toReal_zero]
  ring

/-- Shifting the contact set by at least `3` empties it on the unit square. -/
theorem psiSet_shift_null [SFinite μ] (hsupp : μ (Icc (0:ℝ) 1)ᶜ = 0) {a : ℝ}
    (ha1 : a ≤ 1 / 5) {c : ℝ} (hc : 3 ≤ c) :
    (μ.prod μ) {p : ℝ × ℝ | c + (p.2 - p.1) ≤ 5 * a} = 0 := by
  refine prod_measure_eq_zero_of_gap hsupp ?_
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hxy
  simp only [Set.mem_ofPred_eq] at hxy
  dsimp only at hx0 hx1 hy0 hy1
  linarith

/-- **`eq:base-five-recursion` for `D₁ = {0,1,4}`**: `Φ₁(δ) = Φ₁(5δ)/3 + 2Ψ(5δ)/9` for
`0 < δ ≤ 1/5`; the digits `0` and `1` contribute `Ψ(5δ)` in each order and the digit
`4` is too far from the others. -/
theorem phiA_recursion (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K
    baseFiveDim μ) (hFrost : IsFrostman baseFiveDim A μ) {δ : ℝ} (hδ1 : δ ≤ 1 / 5) :
    Phi μ δ = 1 / 3 * Phi μ (5 * δ) + 2 / 9 * Psi μ (5 * δ) := by
  have := hμ.isProbabilityMeasure
  have hsupp := hFrost.support
  unfold Phi Psi
  rw [baseFive_prod_eq hμ (measurableSet_phiSet δ), Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [baseFiveDigitsA, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, pullback_phiSet]
  -- the two contact terms
  have h01 : (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2 + (0 - 1)| ≤ 5 * δ}
      = (μ.prod μ) {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ 5 * δ} := by
    refine prod_measure_eq_of_eqOn_unitSquare hsupp ?_
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    simp only [Set.mem_ofPred_eq]
    dsimp only at hx0 hx1 hy0 hy1
    rw [abs_of_nonpos (by linarith)]
    constructor <;> intro h <;> linarith
  have h10 : (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2 + (1 - 0)| ≤ 5 * δ}
      = (μ.prod μ) {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ 5 * δ} := by
    rw [← prod_measure_swap_contact]
    refine prod_measure_eq_of_eqOn_unitSquare hsupp ?_
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    simp only [Set.mem_ofPred_eq]
    dsimp only at hx0 hx1 hy0 hy1
    rw [abs_of_nonneg (by linarith)]
    constructor <;> intro h <;> linarith
  rw [h01, h10, phiSet_shift_null hsupp hδ1 (k := 0 - 4) (by norm_num),
    phiSet_shift_null hsupp hδ1 (k := 4 - 0) (by norm_num),
    phiSet_shift_null hsupp hδ1 (k := 1 - 4) (by norm_num),
    phiSet_shift_null hsupp hδ1 (k := 4 - 1) (by norm_num)]
  simp only [ENNReal.toReal_zero]
  ring

/-- **The contact mass rescales**: `Ψ(a) = Ψ(5a)/9` for `0 < a ≤ 1/5`, since the event
forces the first digits `4` and `0`, apart from the null corner event. -/
theorem psi_recursion (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K
    baseFiveDim μ) (hFrost : IsFrostman baseFiveDim A μ) {a : ℝ} (ha1 : a ≤ 1 / 5) :
    Psi μ a = 1 / 9 * Psi μ (5 * a) := by
  have := hμ.isProbabilityMeasure
  have hsupp := hFrost.support
  have hatom : ∀ x, μ {x} = 0 := fun x => hFrost.measure_singleton baseFiveDim_pos x
  unfold Psi
  rw [baseFive_prod_eq hμ (measurableSet_psiSet a), Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [baseFiveDigitsA, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, pullback_psiSet]
  have h40 : (μ.prod μ) {p : ℝ × ℝ | (5 - 4 + 0) + (p.2 - p.1) ≤ 5 * a}
      = (μ.prod μ) {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ 5 * a} := by
    congr 1
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  have h41 : (μ.prod μ) {p : ℝ × ℝ | (5 - 4 + 1) + (p.2 - p.1) ≤ 5 * a} = 0 := by
    refine prod_measure_eq_zero_of_subset_singleton hsupp hatom 1 0 ?_
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hxy
    simp only [Set.mem_ofPred_eq] at hxy
    dsimp only at hx0 hx1 hy0 hy1
    have hx : x = 1 := by linarith
    have hy : y = 0 := by linarith
    rw [hx, hy]
  rw [h40, h41, psiSet_shift_null hsupp ha1 (c := 5 - 0 + 0) (by norm_num),
    psiSet_shift_null hsupp ha1 (c := 5 - 0 + 1) (by norm_num),
    psiSet_shift_null hsupp ha1 (c := 5 - 0 + 4) (by norm_num),
    psiSet_shift_null hsupp ha1 (c := 5 - 1 + 0) (by norm_num),
    psiSet_shift_null hsupp ha1 (c := 5 - 1 + 1) (by norm_num),
    psiSet_shift_null hsupp ha1 (c := 5 - 1 + 4) (by norm_num),
    psiSet_shift_null hsupp ha1 (c := 5 - 4 + 4) (by norm_num)]
  simp only [ENNReal.toReal_zero]
  ring

/-- `Ψ(1) = P(Y ≤ X) = 1/2`, by exchangeability and the absence of atoms. -/
theorem psi_one [IsProbabilityMeasure μ] (hFrost : IsFrostman baseFiveDim A μ) :
    Psi μ 1 = 1 / 2 := by
  set Aset : Set (ℝ × ℝ) := {p | p.2 ≤ p.1} with hAset
  set Bset : Set (ℝ × ℝ) := {p | p.1 ≤ p.2} with hBset
  have hAm : MeasurableSet Aset := (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hBm : MeasurableSet Bset := (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hpsi : {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ 1} = Aset := by
    ext p
    simp only [hAset, Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  have hswap : (μ.prod μ) Bset = (μ.prod μ) Aset := by
    have h := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage
      hAm.nullMeasurableSet
    rw [← h]
    rfl
  have hunion : Aset ∪ Bset = Set.univ := by
    ext p
    simp only [hAset, hBset, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total _ _
  have hdiag : (μ.prod μ) (Aset ∩ Bset) = 0 := by
    have h0 := pairLaw_measure_singleton baseFiveDim_pos hFrost 0
    rw [pairLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at h0
    refine measure_mono_null ?_ h0
    rintro ⟨x, y⟩ ⟨hA, hB⟩
    simp only [hAset, hBset, Set.mem_ofPred_eq] at hA hB
    simp only [Set.mem_preimage, Set.mem_singleton_iff, abs_eq_zero, sub_eq_zero]
    exact le_antisymm hB hA
  have hsum := measure_union_add_inter Aset hBm (μ := μ.prod μ)
  rw [hunion, measure_univ, hdiag, add_zero, hswap] at hsum
  have hfin : (μ.prod μ) Aset ≠ ⊤ := measure_ne_top _ _
  have hreal : (1 : ℝ) = ((μ.prod μ) Aset).toReal + ((μ.prod μ) Aset).toReal := by
    rw [← ENNReal.toReal_add hfin hfin, ← hsum, ENNReal.toReal_one]
  unfold Psi
  rw [hpsi]
  linarith

/-! ### `eq:base-five-distances` -/

/-- `Ψ(5^{-m}) = 9^{-m}/2`. -/
theorem psi_five_pow (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K
    baseFiveDim μ) (hFrost : IsFrostman baseFiveDim A μ) (m : ℕ) :
    Psi μ ((1 / 5 : ℝ) ^ m) = 1 / 2 * (1 / 9 : ℝ) ^ m := by
  have := hμ.isProbabilityMeasure
  induction m with
  | zero => simp [psi_one hFrost]
  | succ m ih =>
    have ha1 : (1 / 5 : ℝ) ^ (m + 1) ≤ 1 / 5 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
    rw [psi_recursion hμ hFrost ha1, show (5:ℝ) * (1 / 5) ^ (m + 1) = (1 / 5) ^ m by
      rw [pow_succ]; ring, ih, pow_succ]
    ring

/-- **`eq:base-five-distances` for `D₂`**: `Φ₂(5^{-n}) = 3^{-n}`. -/
theorem phiB_five_pow (hμ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K
    baseFiveDim μ) (hFrost : IsFrostman baseFiveDim A μ) (n : ℕ) :
    Phi μ ((1 / 5 : ℝ) ^ n) = (1 / 3 : ℝ) ^ n := by
  have := hμ.isProbabilityMeasure
  induction n with
  | zero => simp [phi_one_of_support hFrost.support]
  | succ n ih =>
    have hδ1 : (1 / 5 : ℝ) ^ (n + 1) ≤ 1 / 5 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
    rw [phiB_recursion hμ hFrost hδ1, show (5:ℝ) * (1 / 5) ^ (n + 1) = (1 / 5) ^ n by
      rw [pow_succ]; ring, ih, pow_succ]
    ring

/-- **`eq:base-five-distances` for `D₁`**: `Φ₁(5^{-n}) = (3/2) 3^{-n} - (1/2) 9^{-n}`. -/
theorem phiA_five_pow (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K
    baseFiveDim μ) (hFrost : IsFrostman baseFiveDim A μ) (n : ℕ) :
    Phi μ ((1 / 5 : ℝ) ^ n) = 3 / 2 * (1 / 3 : ℝ) ^ n - 1 / 2 * (1 / 9 : ℝ) ^ n := by
  have := hμ.isProbabilityMeasure
  induction n with
  | zero => simp [phi_one_of_support hFrost.support]; norm_num
  | succ n ih =>
    have hδ1 : (1 / 5 : ℝ) ^ (n + 1) ≤ 1 / 5 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
    rw [phiA_recursion hμ hFrost hδ1, show (5:ℝ) * (1 / 5) ^ (n + 1) = (1 / 5) ^ n by
      rw [pow_succ]; ring, ih, psi_five_pow hμ hFrost n, pow_succ, pow_succ]
    ring

end Recursion

/-! ### Periodic limits of a profile with summable increments -/

/-- **Periodic limits.**  A continuous function whose increments over a period `p` are
non-negative and `O(e^{-γw})` converges along the period to a continuous `p`-periodic
function, exponentially fast. -/
theorem exists_periodic_limit {G : ℝ → ℝ} (hG : Continuous G) {p C γ : ℝ} (hp : 0 < p)
    (hC : 0 ≤ C) (hγ : 0 < γ)
    (hinc : ∀ w, p ≤ w → 0 ≤ G w - G (w - p) ∧ G w - G (w - p) ≤ C * Real.exp (-γ * w)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g p ∧
      (∀ w, 0 ≤ w → |G w - g w| ≤ C / (1 - Real.exp (-γ * p)) * Real.exp (-γ * w)) ∧
      ∀ w, 0 ≤ w → Tendsto (fun n : ℕ => G (w + n * p)) atTop (𝓝 (g w)) := by
  set r : ℝ := Real.exp (-γ * p) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    nlinarith
  have hr1' : 0 < 1 - r := by linarith
  set B : ℝ := C / (1 - r) with hB
  have hB0 : 0 ≤ B := div_nonneg hC hr1'.le
  -- the increments along the period
  have hstep : ∀ w, 0 ≤ w → ∀ n : ℕ,
      0 ≤ G (w + (n + 1 : ℕ) * p) - G (w + n * p) ∧
      G (w + (n + 1 : ℕ) * p) - G (w + n * p) ≤ C * Real.exp (-γ * w) * r ^ n := by
    intro w hw n
    have h := hinc (w + (n + 1 : ℕ) * p) (by push_cast; nlinarith)
    have heq : w + (n + 1 : ℕ) * p - p = w + n * p := by push_cast; ring
    rw [heq] at h
    refine ⟨h.1, h.2.trans ?_⟩
    rw [hr, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
    push_cast
    nlinarith
  -- the limits
  have hcauchy : ∀ w, 0 ≤ w → CauchySeq (fun n : ℕ => G (w + n * p)) := by
    intro w hw
    refine cauchySeq_of_le_geometric r (C * Real.exp (-γ * w)) hr1 fun n => ?_
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (hstep w hw n).1]
    exact (hstep w hw n).2
  have hlim : ∀ w, 0 ≤ w → ∃ L, Tendsto (fun n : ℕ => G (w + n * p)) atTop (𝓝 L) :=
    fun w hw => cauchySeq_tendsto_of_complete (hcauchy w hw)
  classical
  set L : ℝ → ℝ := fun w => if hw : 0 ≤ w then Classical.choose (hlim w hw) else 0 with hL
  have hLt : ∀ w, 0 ≤ w → Tendsto (fun n : ℕ => G (w + n * p)) atTop (𝓝 (L w)) := by
    intro w hw
    simp only [hL, hw, ↓reduceDIte]
    exact Classical.choose_spec (hlim w hw)
  -- the partial sums of the increments
  have hpartial : ∀ w, 0 ≤ w → ∀ n : ℕ,
      G w ≤ G (w + n * p) ∧ G (w + n * p) ≤ G w + B * Real.exp (-γ * w) := by
    intro w hw n
    have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range n, r ^ k ≤ (1 - r)⁻¹ := by
      intro n
      rw [← tsum_geometric_of_lt_one hr0.le hr1]
      exact (summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum _
        fun k _ => pow_nonneg hr0.le k
    have key : ∀ n : ℕ, G w ≤ G (w + n * p) ∧
        G (w + n * p) ≤ G w + C * Real.exp (-γ * w) * ∑ k ∈ Finset.range n, r ^ k := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        obtain ⟨h1, h2⟩ := hstep w hw n
        rw [Finset.sum_range_succ]
        constructor <;> linarith [ih.1, ih.2]
    refine ⟨(key n).1, (key n).2.trans ?_⟩
    have hmul : C * Real.exp (-γ * w) * ∑ k ∈ Finset.range n, r ^ k
        ≤ C * Real.exp (-γ * w) * (1 - r)⁻¹ :=
      mul_le_mul_of_nonneg_left (hgeom n) (mul_nonneg hC (Real.exp_pos _).le)
    have hBeq : B * Real.exp (-γ * w) = C * Real.exp (-γ * w) * (1 - r)⁻¹ := by
      rw [hB, div_eq_mul_inv]; ring
    rw [hBeq]
    linarith
  have hbound : ∀ w, 0 ≤ w → |G w - L w| ≤ B * Real.exp (-γ * w) := by
    intro w hw
    have hlow : G w ≤ L w :=
      ge_of_tendsto (hLt w hw) (Eventually.of_forall fun n => (hpartial w hw n).1)
    have hupp : L w ≤ G w + B * Real.exp (-γ * w) :=
      le_of_tendsto (hLt w hw) (Eventually.of_forall fun n => (hpartial w hw n).2)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  -- the shift
  have hshift : ∀ w, 0 ≤ w → L (w + p) = L w := by
    intro w hw
    have h1 := hLt (w + p) (by linarith)
    have h2 : Tendsto (fun n : ℕ => G (w + (n + 1 : ℕ) * p)) atTop (𝓝 (L w)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (hLt w hw)
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    push_cast
    ring_nf
  have hshiftn : ∀ w, 0 ≤ w → ∀ n : ℕ, L (w + n * p) = L w := by
    intro w hw n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, show w + (n + 1 : ℕ) * p = w + n * p + p by push_cast; ring]
      exact hshift _ (by positivity)
  -- continuity on the half line, by uniform approximation
  have hcont : ContinuousOn L (Ici 0) := by
    have hcF : ∀ᶠ n : ℕ in atTop, ContinuousOn (fun w : ℝ => G (w + n * p)) (Ici 0) :=
      Eventually.of_forall fun n =>
        (by fun_prop : Continuous fun w : ℝ => G (w + n * p)).continuousOn
    refine TendstoUniformlyOn.continuousOn (F := fun (n : ℕ) (w : ℝ) => G (w + n * p))
      ?_ hcF.frequently
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hgeo : Tendsto (fun n : ℕ => B * r ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul B
    filter_upwards [(hgeo.eventually (gt_mem_nhds hε))] with n hn w hw
    have hw0 : (0:ℝ) ≤ w := hw
    have hwn : (0:ℝ) ≤ w + n * p := by positivity
    have := hbound (w + n * p) hwn
    rw [hshiftn w hw0 n] at this
    rw [Real.dist_eq, abs_sub_comm]
    calc |G (w + n * p) - L w| ≤ B * Real.exp (-γ * (w + n * p)) := this
      _ ≤ B * r ^ n := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          rw [hr, ← Real.exp_nat_mul]
          exact Real.exp_le_exp.2 (by nlinarith)
      _ < ε := hn
  obtain ⟨g, hgc, hgper, hgeq⟩ := exists_periodic_extension_of_shift hp hcont
    fun w hw => by
      have hw' : 0 ≤ w - p := by linarith
      rw [← hshift (w - p) hw', sub_add_cancel]
  refine ⟨g, hgc, hgper, fun w hw => ?_, fun w hw => ?_⟩
  · rw [hgeq w hw]
    exact hbound w hw
  · rw [hgeq w hw]
    exact hLt w hw

/-! ### The expected profile follows the periodic limit -/

/-- If the profile `G` approaches a bounded continuous function `g` at infinity, the
expected profile `H` approaches the smoothed function `Tg`: dominated convergence in
`eq:h-definition`. -/
theorem tendsto_H_sub_smoothOp {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hlim : Tendsto (fun w => G s μ w - g w) atTop (𝓝 0)) :
    Tendsto (fun v => H s μ v - smoothOp s g v) atTop (𝓝 0) := by
  have hkint := kern_integrableOn (s := s) hs0 hs1
  have hGm : Measurable (G s μ) := measurable_G
  have hint1 : ∀ v : ℝ, IntegrableOn
      (fun η : ℝ => kern s η * G s μ (2 * v - Real.log η)) (Set.Ioi 0) := by
    intro v
    refine Integrable.mono' (hkint.const_mul A) (((continuousOn_kern s).aestronglyMeasurable
      measurableSet_Ioi).mul
      (hGm.comp (measurable_const.sub Real.measurable_log)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
    have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc kern s η * |G s μ (2 * v - Real.log η)| ≤ kern s η * A :=
          mul_le_mul_of_nonneg_left (abs_G_le hs0 hμ _) hk
      _ = A * kern s η := mul_comm _ _
  have hint2 : ∀ v : ℝ, IntegrableOn
      (fun η : ℝ => kern s η * g (2 * v - Real.log η)) (Set.Ioi 0) :=
    fun v => smoothOp_integrableOn hs0 hs1 hg hM v
  have hsub : ∀ v, H s μ v - smoothOp s g v
      = ∫ η in Set.Ioi (0:ℝ), kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)) := by
    intro v
    unfold H smoothOp
    rw [← integral_sub (hint1 v) (hint2 v)]
    refine setIntegral_congr_fun measurableSet_Ioi fun η _ => ?_
    ring
  simp_rw [hsub]
  have hzero : (∫ η in Set.Ioi (0:ℝ), kern s η * (0:ℝ)) = 0 := by simp
  have key : Tendsto (fun v : ℝ => ∫ η in Set.Ioi (0:ℝ),
      kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η))) atTop
      (𝓝 (∫ η in Set.Ioi (0:ℝ), kern s η * (0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (l := atTop)
      (F := fun (v : ℝ) (η : ℝ) => kern s η * (G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)))
      (f := fun η : ℝ => kern s η * (0:ℝ)) (fun η => (A + M) * kern s η)
      (Eventually.of_forall fun v => ?_) (Eventually.of_forall fun v => ?_)
      (hkint.const_mul (A + M)) ?_
    · exact ((measurable_kern s).mul
        ((hGm.comp (measurable_const.sub Real.measurable_log)).sub
          (hg.measurable.comp (measurable_const.sub Real.measurable_log)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
      have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
      calc kern s η * |G s μ (2 * v - Real.log η) - g (2 * v - Real.log η)|
          ≤ kern s η * (A + M) := by
            refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hk
            exact add_le_add (abs_G_le hs0 hμ _) (hM _)
        _ = (A + M) * kern s η := mul_comm _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
      have htop : Tendsto (fun v : ℝ => 2 * v - Real.log η) atTop atTop := by
        have h : Tendsto (fun v : ℝ => 2 * v + -Real.log η) atTop atTop :=
          tendsto_atTop_add_const_right _ _
            (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
        simpa [sub_eq_add_neg] using h
      exact (hlim.comp htop).const_mul (kern s η)
  rw [hzero] at key
  exact key

/-- **Distinct periodic limits separate the expected profiles.**  If `H_j - T g_j → 0`
for continuous `p`-periodic `g₁ ≠ g₂`, then `|H₁ - H₂|` stays bounded away from zero
along a sequence tending to infinity, `eq:profile-separation`, since `T g₁ - T g₂` is a
non-zero continuous `p/2`-periodic function by `thm:smoothing-injective`. -/
theorem exists_separation_of_periodic_limits {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hp : 0 < p) {μ₁ μ₂ : Measure ℝ} {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) (hper₁ : Function.Periodic g₁ p) (hper₂ : Function.Periodic g₂ p)
    (hne : g₁ 0 ≠ g₂ 0)
    (hH₁ : Tendsto (fun v => H s μ₁ v - smoothOp s g₁ v) atTop (𝓝 0))
    (hH₂ : Tendsto (fun v => H s μ₂ v - smoothOp s g₂ v) atTop (𝓝 0)) :
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t| := by
  -- a point where the smoothed limits differ
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, smoothOp s g₁ v₀ ≠ smoothOp s g₂ v₀ := by
    by_contra h
    exact hne (smoothOp_injective hs0 hs1 hp hg₁ hg₂ hper₁ hper₂
      (fun v => by by_contra hv; exact h ⟨v, hv⟩) 0)
  set ε₀ : ℝ := |smoothOp s g₁ v₀ - smoothOp s g₂ v₀| with hε₀
  have hε₀pos : 0 < ε₀ := abs_pos.mpr (sub_ne_zero.mpr hv₀)
  have hperT₁ := smoothOp_periodic (s := s) hper₁
  have hperT₂ := smoothOp_periodic (s := s) hper₂
  have hgrid : ∀ n : ℕ, |smoothOp s g₁ (v₀ + n * (p / 2)) - smoothOp s g₂ (v₀ + n * (p / 2))|
      = ε₀ := by
    intro n
    rw [hε₀]
    congr 1
    rw [hperT₁.nat_mul n v₀, hperT₂.nat_mul n v₀]
  refine ⟨ε₀ / 2, by positivity, fun V => ?_⟩
  have hev : ∀ᶠ v in atTop, |H s μ₁ v - smoothOp s g₁ v| < ε₀ / 4 ∧
      |H s μ₂ v - smoothOp s g₂ v| < ε₀ / 4 := by
    have h₁ := (Metric.tendsto_nhds.mp hH₁) (ε₀ / 4) (by positivity)
    have h₂ := (Metric.tendsto_nhds.mp hH₂) (ε₀ / 4) (by positivity)
    filter_upwards [h₁, h₂] with v hv₁ hv₂
    rw [Real.dist_eq, sub_zero] at hv₁ hv₂
    exact ⟨hv₁, hv₂⟩
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp hev
  obtain ⟨n, hn⟩ := exists_nat_ge ((max V V₀ - v₀) / (p / 2))
  have hn' : max V V₀ ≤ v₀ + n * (p / 2) := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < p / 2)).mp hn
    linarith
  refine ⟨v₀ + n * (p / 2), (le_max_left _ _).trans hn', ?_⟩
  obtain ⟨h₁, h₂⟩ := hV₀ _ ((le_max_right _ _).trans hn')
  have hg := hgrid n
  set t := v₀ + n * (p / 2)
  have e1 := abs_sub_le (smoothOp s g₁ t) (H s μ₁ t) (smoothOp s g₂ t)
  have e2 := abs_sub_le (H s μ₁ t) (H s μ₂ t) (smoothOp s g₂ t)
  rw [abs_sub_comm (smoothOp s g₁ t) (H s μ₁ t)] at e1
  linarith

/-! ### The two profiles in logarithmic coordinates -/

section Profiles

variable {K : Set ℝ} {μ : Measure ℝ} {A : ℝ}

/-- `5^s = 3` in exponential form. -/
theorem exp_baseFiveDim_mul_log_five : Real.exp (baseFiveDim * Real.log 5) = 3 := by
  rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5), five_rpow_baseFiveDim]

/-- The scale `e^{-w}` lies below `1/5` once `w ≥ log 5`. -/
theorem exp_neg_le_fifth {w : ℝ} (hw : Real.log 5 ≤ w) : Real.exp (-w) ≤ 1 / 5 := by
  have h : Real.exp (-Real.log 5) = 1 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [← h]
  exact Real.exp_le_exp.2 (by linarith)

/-- The Frostman bound on the contact functional, `Ψ(a) ≤ (A a^s)²` for `0 < a ≤ 1`: the
event `(1-X)+Y ≤ a` forces `X ∈ [1-a,1]` and `Y ∈ [0,a]`. -/
theorem psi_le [IsProbabilityMeasure μ] (hFrost : IsFrostman baseFiveDim A μ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) : Psi μ a ≤ (A * a ^ baseFiveDim) ^ 2 := by
  have hAa : 0 ≤ A * a ^ baseFiveDim :=
    mul_nonneg (zero_le_one.trans hFrost.one_le_const) (Real.rpow_nonneg ha0.le _)
  unfold Psi
  refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) ?_
  calc (μ.prod μ) {p : ℝ × ℝ | (1 - p.1) + p.2 ≤ a}
      ≤ (μ.prod μ) (Metric.closedBall 1 a ×ˢ Metric.closedBall 0 a) := by
        refine prod_measure_le_of_subset_on_unitSquare hFrost.support ?_
        rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ h
        dsimp only at hx0 hx1 hy0 hy1
        change 1 - x + y ≤ a at h
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, Real.dist_eq, abs_le]; constructor <;> linarith
        · rw [Metric.mem_closedBall, Real.dist_eq, abs_le]; constructor <;> linarith
    _ = μ (Metric.closedBall 1 a) * μ (Metric.closedBall 0 a) := Measure.prod_prod _ _
    _ ≤ ENNReal.ofReal (A * a ^ baseFiveDim) * ENNReal.ofReal (A * a ^ baseFiveDim) :=
        mul_le_mul' (hFrost.measure_closedBall_le 1 a ha0 ha1)
          (hFrost.measure_closedBall_le 0 a ha0 ha1)
    _ = ENNReal.ofReal ((A * a ^ baseFiveDim) ^ 2) := by
        rw [sq, ENNReal.ofReal_mul hAa]

/-- The profile one period back, `G(w - log 5) = ⅓ e^{sw} Φ(5 e^{-w})`. -/
theorem G_sub_log_five (μ : Measure ℝ) (w : ℝ) :
    G baseFiveDim μ (w - Real.log 5)
      = 1 / 3 * (Real.exp (baseFiveDim * w) * Phi μ (5 * Real.exp (-w))) := by
  unfold G
  have h1 : Real.exp (baseFiveDim * (w - Real.log 5)) = Real.exp (baseFiveDim * w) / 3 := by
    rw [mul_sub, Real.exp_sub, exp_baseFiveDim_mul_log_five]
  have h2 : Real.exp (-(w - Real.log 5)) = 5 * Real.exp (-w) := by
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
  rw [h1, h2]
  ring

/-- The profile at the lattice points, `G(n log 5) = 3ⁿ Φ(5⁻ⁿ)`. -/
theorem G_nat_mul_log_five (μ : Measure ℝ) (n : ℕ) :
    G baseFiveDim μ (n * Real.log 5) = 3 ^ n * Phi μ ((1 / 5 : ℝ) ^ n) := by
  unfold G
  have h1 : Real.exp (baseFiveDim * (n * Real.log 5)) = 3 ^ n := by
    rw [← mul_assoc, mul_comm baseFiveDim, mul_assoc, Real.exp_nat_mul,
      exp_baseFiveDim_mul_log_five]
  have h2 : Real.exp (-(n * Real.log 5)) = (1 / 5 : ℝ) ^ n := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div, inv_pow]
  rw [h1, h2]

/-- `G₂(w) = G₂(w - p)` for `w ≥ p`: the second profile has no increments. -/
theorem baseFiveB_G_increment
    (hμ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K baseFiveDim μ)
    (hFrost : IsFrostman baseFiveDim A μ) {w : ℝ} (hw : Real.log 5 ≤ w) :
    G baseFiveDim μ w - G baseFiveDim μ (w - Real.log 5) = 0 := by
  have := hμ.isProbabilityMeasure
  rw [G_sub_log_five]
  unfold G
  rw [phiB_recursion hμ hFrost (exp_neg_le_fifth hw)]
  ring

/-- `G₁(w) - G₁(w - p) = (2/9) e^{sw} Ψ(5 e^{-w})` for `w ≥ p`. -/
theorem baseFiveA_G_increment
    (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K baseFiveDim μ)
    (hFrost : IsFrostman baseFiveDim A μ) {w : ℝ} (hw : Real.log 5 ≤ w) :
    G baseFiveDim μ w - G baseFiveDim μ (w - Real.log 5)
      = 2 / 9 * Real.exp (baseFiveDim * w) * Psi μ (5 * Real.exp (-w)) := by
  have := hμ.isProbabilityMeasure
  rw [G_sub_log_five]
  unfold G
  rw [phiA_recursion hμ hFrost (exp_neg_le_fifth hw)]
  ring

/-- The increments of the first profile are non-negative and `O(e^{-sw})`. -/
theorem baseFiveA_G_increment_bounds
    (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K baseFiveDim μ)
    (hFrost : IsFrostman baseFiveDim A μ) {w : ℝ} (hw : Real.log 5 ≤ w) :
    0 ≤ G baseFiveDim μ w - G baseFiveDim μ (w - Real.log 5) ∧
    G baseFiveDim μ w - G baseFiveDim μ (w - Real.log 5)
      ≤ 2 * A ^ 2 * Real.exp (-baseFiveDim * w) := by
  have := hμ.isProbabilityMeasure
  rw [baseFiveA_G_increment hμ hFrost hw]
  have hexp := Real.exp_pos (baseFiveDim * w)
  have hψ0 := Psi_nonneg μ (5 * Real.exp (-w))
  refine ⟨by positivity, ?_⟩
  have h5 : 0 < 5 * Real.exp (-w) := by positivity
  have h51 : 5 * Real.exp (-w) ≤ 1 := by have := exp_neg_le_fifth hw; linarith
  have hψ := psi_le hFrost h5 h51
  have hpow : (5 * Real.exp (-w)) ^ baseFiveDim = 3 * Real.exp (-(baseFiveDim * w)) := by
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, five_rpow_baseFiveDim, ← Real.exp_mul]
    ring_nf
  rw [hpow] at hψ
  have hA0 : 0 ≤ A := zero_le_one.trans hFrost.one_le_const
  calc 2 / 9 * Real.exp (baseFiveDim * w) * Psi μ (5 * Real.exp (-w))
      ≤ 2 / 9 * Real.exp (baseFiveDim * w) * (A * (3 * Real.exp (-(baseFiveDim * w)))) ^ 2 := by
        gcongr
    _ = 2 * A ^ 2 * (Real.exp (baseFiveDim * w) * Real.exp (-(baseFiveDim * w)))
          * Real.exp (-(baseFiveDim * w)) := by ring
    _ = 2 * A ^ 2 * Real.exp (-baseFiveDim * w) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, neg_mul]

/-- An exponentially small defect tends to zero. -/
theorem tendsto_sub_of_abs_le_exp {F g : ℝ → ℝ} {B γ : ℝ} (hγ : 0 < γ)
    (h : ∀ w, 0 ≤ w → |F w - g w| ≤ B * Real.exp (-γ * w)) :
    Tendsto (fun w => F w - g w) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun w => B * Real.exp (-γ * w))
    ((eventually_ge_atTop 0).mono fun w hw => ?_) ?_
  · rw [Real.norm_eq_abs]; exact h w hw
  · have h1 : Tendsto (fun w : ℝ => Real.exp (-γ * w)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hγ))
      refine this.congr fun w => ?_
      simp [Function.comp, neg_mul]
    simpa using h1.const_mul B

/-- The periodic limit of the first profile: `G₁ - g₁ → 0` with `g₁(0) = 3/2`. -/
theorem baseFiveA_exists_periodic_limit
    (hμ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K baseFiveDim μ)
    (hFrost : IsFrostman baseFiveDim A μ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log 5) ∧
      Tendsto (fun w => G baseFiveDim μ w - g w) atTop (𝓝 0) ∧ g 0 = 3 / 2 := by
  have := hμ.isProbabilityMeasure
  obtain ⟨g, hgc, hgper, hbound, hlim⟩ := exists_periodic_limit
    (continuous_G baseFiveDim_pos hFrost) log_five_pos (by positivity : (0:ℝ) ≤ 2 * A ^ 2)
    baseFiveDim_pos (fun w hw => baseFiveA_G_increment_bounds hμ hFrost hw)
  refine ⟨g, hgc, hgper, tendsto_sub_of_abs_le_exp baseFiveDim_pos hbound, ?_⟩
  have h1 := hlim 0 le_rfl
  have h2 : Tendsto (fun n : ℕ => G baseFiveDim μ (0 + n * Real.log 5)) atTop (𝓝 (3 / 2)) := by
    have heq : ∀ n : ℕ, G baseFiveDim μ (0 + n * Real.log 5)
        = 3 / 2 - 1 / 2 * (1 / 3 : ℝ) ^ n := by
      intro n
      rw [zero_add, G_nat_mul_log_five, phiA_five_pow hμ hFrost]
      have e1 : (3:ℝ) ^ n * (1 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
      have e2 : (3:ℝ) ^ n * (1 / 9) ^ n = (1 / 3) ^ n := by rw [← mul_pow]; norm_num
      linear_combination (3 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e2
    simp_rw [heq]
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 3)
      (by norm_num)).const_mul (1 / 2 : ℝ)).const_sub (3 / 2 : ℝ)
    simpa using this
  exact tendsto_nhds_unique h1 h2

/-- The periodic limit of the second profile: `G₂ - g₂ → 0` with `g₂(0) = 1`. -/
theorem baseFiveB_exists_periodic_limit
    (hμ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K baseFiveDim μ)
    (hFrost : IsFrostman baseFiveDim A μ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log 5) ∧
      Tendsto (fun w => G baseFiveDim μ w - g w) atTop (𝓝 0) ∧ g 0 = 1 := by
  have := hμ.isProbabilityMeasure
  obtain ⟨g, hgc, hgper, hbound, hlim⟩ := exists_periodic_limit
    (continuous_G baseFiveDim_pos hFrost) log_five_pos le_rfl
    baseFiveDim_pos (fun w hw => by
      rw [baseFiveB_G_increment hμ hFrost hw]
      exact ⟨le_rfl, by positivity⟩)
  refine ⟨g, hgc, hgper, tendsto_sub_of_abs_le_exp baseFiveDim_pos hbound, ?_⟩
  have h1 := hlim 0 le_rfl
  have h2 : Tendsto (fun n : ℕ => G baseFiveDim μ (0 + n * Real.log 5)) atTop (𝓝 1) := by
    have heq : ∀ n : ℕ, G baseFiveDim μ (0 + n * Real.log 5) = 1 := by
      intro n
      rw [zero_add, G_nat_mul_log_five, phiB_five_pow hμ hFrost, ← mul_pow]
      norm_num
    simp_rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end Profiles

/-! ### `thm:base-five-profiles` -/

/-- **`thm:base-five-profiles`.**  For the natural measures `μ₁`, `μ₂` of the two base-five
systems, the pair-distance distributions take the values `eq:base-five-distances` at the
scales `5⁻ⁿ`, and the expected profiles `H_{μ₁}^s`, `H_{μ₂}^s` stay a fixed distance apart along
a sequence tending to infinity. -/
theorem baseFive_profiles {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K₁ baseFiveDim μ₁)
    (hμ₂ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K₂ baseFiveDim μ₂) :
    (∀ n : ℕ, Phi μ₁ ((1 / 5 : ℝ) ^ n) = 3 / 2 * (1 / 3 : ℝ) ^ n - 1 / 2 * (1 / 9 : ℝ) ^ n ∧
      Phi μ₂ ((1 / 5 : ℝ) ^ n) = (1 / 3 : ℝ) ^ n) ∧
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H baseFiveDim μ₁ t - H baseFiveDim μ₂ t| := by
  have := hμ₁.isProbabilityMeasure
  have := hμ₂.isProbabilityMeasure
  obtain ⟨A₁, hF₁⟩ := System.OpenSetCondition.exists_isFrostman _
    (baseFiveSystem_openSetCondition _ _ baseFiveDigitsA_injective) baseFiveDim_pos.le hμ₁
  obtain ⟨A₂, hF₂⟩ := System.OpenSetCondition.exists_isFrostman _
    (baseFiveSystem_openSetCondition _ _ baseFiveDigitsB_injective) baseFiveDim_pos.le hμ₂
  refine ⟨fun n => ⟨phiA_five_pow hμ₁ hF₁ n, phiB_five_pow hμ₂ hF₂ n⟩, ?_⟩
  obtain ⟨g₁, hg₁c, hg₁p, hg₁lim, hg₁0⟩ := baseFiveA_exists_periodic_limit hμ₁ hF₁
  obtain ⟨g₂, hg₂c, hg₂p, hg₂lim, hg₂0⟩ := baseFiveB_exists_periodic_limit hμ₂ hF₂
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_continuous_periodic log_five_pos hg₁c hg₁p
  obtain ⟨M₂, hM₂⟩ := exists_bound_of_continuous_periodic log_five_pos hg₂c hg₂p
  exact exists_separation_of_periodic_limits baseFiveDim_pos baseFiveDim_lt_one log_five_pos
    hg₁c hg₂c hg₁p hg₂p (by rw [hg₁0, hg₂0]; norm_num)
    (tendsto_H_sub_smoothOp baseFiveDim_pos baseFiveDim_lt_one hF₁ hg₁c hM₁ hg₁lim)
    (tendsto_H_sub_smoothOp baseFiveDim_pos baseFiveDim_lt_one hF₂ hg₂c hM₂ hg₂lim)

end BrownianImages
