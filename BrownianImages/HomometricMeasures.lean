/-
`sec:obstruction`: the two homometric measures of `thm:homometric-example`.

`Homometric.lean` carries the finite content, the homometry of the digit sets and the
common dimension `t = log 6 / log 30`.  This module carries the measures themselves.
The natural measures `σ_A` and `σ_B` come from `System.exists_unique_isNatural`, and
they are distinct because the interval of the digit `4`, which lies in `𝒜` and not in
`ℬ`, has mass `(1/30)^t` for one and mass zero for the other.

The equality of the signed convolutions is a fixed point argument.  The law of
`(X - X' + 1)/2`, for `X` and `X'` independent with law `σ_D`, satisfies Hutchinson's
identity for the system of thirty-six similarities `u ↦ u/30 + (k/36 + 29/60)` indexed
by the ordered pairs of digits, at the dimension `2t` that makes the weights `1/36`.
That sum depends on the digit set only through the multiset of the differences
`d_i - d_j`, which is the same for `𝒜` and for `ℬ`, so the two laws solve the same
identity and `Hutchinson.eq_of_selfSimilar` identifies them.

* `cyl`, `le_measure_cyl`, `measure_eq_zero_of_avoid`: the first-level intervals and the
  mass they carry, which is what makes the two measures distinct.
* `subShift`, `diffLaw`, `diffMap`, `diffSystem`: the rescaled difference, its law, and
  the system of thirty-six similarities it is self-similar for.
* `prod_selfSimilar`, `diffLaw_selfSimilar`: Hutchinson's identity for `σ × σ` and the
  identity it induces on the difference law.
* `diffMultiset_fin_eq`, `sum_diffMap_congr`, `diffLaw_eq`: the homometry as an equality
  of sums over ordered pairs, and the equality of the two difference laws.
* `homometric_example`: `thm:homometric-example`, the endpoint
  `audit_homometric_example`.
-/
import BrownianImages.AhlforsRegular
import BrownianImages.Homometric
import BrownianImages.Hutchinson

namespace BrownianImages

open MeasureTheory
open scoped ENNReal NNReal

namespace HomometricMeasures

/-- The common dimension of `thm:homometric-example` is positive. -/
theorem tHom_pos : 0 < tHom := lt_trans (by norm_num) tHom_mem_Ioo.1

/-- `thm:homometric-example`: `t = log 6 / log 30` is the similarity dimension of
both systems, since all six ratios are `1/30`. -/
theorem homSystem_isDimension (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17) :
    (homSystem d h0 h17).IsDimension tHom := by
  have h : ∀ i : Fin 6, (homSystem d h0 h17).ratio i = 1/30 := fun _ => rfl
  simp only [System.IsDimension, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]
  exact six_mul_rpow_tHom

/-! ### The first-level intervals -/

/-- The first-level interval `S_d([0,1]) = [d/18, d/18 + 1/30]`. -/
def cyl (k : ℤ) : Set ℝ := Set.Icc ((k : ℝ)/18) ((k : ℝ)/18 + 1/30)

/-- The first-level intervals are measurable. -/
theorem measurableSet_cyl (k : ℤ) : MeasurableSet (cyl k) := measurableSet_Icc

/-- The `i`-th similarity carries `[0,1]` into the interval of its digit. -/
theorem map_mem_cyl {d : Fin 6 → ℤ} {h0 : ∀ i, 0 ≤ d i} {h17 : ∀ i, d i ≤ 17} (i : Fin 6)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : (homSystem d h0 h17).map i x ∈ cyl (d i) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hval : (homSystem d h0 h17).map i x = 1/30 * x + (d i : ℝ)/18 := rfl
  rw [cyl, hval]
  constructor <;> [linarith; linarith]

/-- Distinct digits give disjoint first-level intervals: the intervals have length
`1/30` and distinct left endpoints are `1/18` apart. -/
theorem notMem_cyl {k l : ℤ} (hkl : k ≠ l) {x : ℝ} (hxk : x ∈ cyl k) : x ∉ cyl l := by
  obtain ⟨hk1, hk2⟩ := hxk
  rintro ⟨hl1, hl2⟩
  have hd : (1:ℝ) ≤ |(k:ℝ) - (l:ℝ)| := by
    have h1 : (1:ℤ) ≤ |k - l| := Int.one_le_abs (sub_ne_zero.mpr hkl)
    have h2 : ((1:ℤ):ℝ) ≤ ((|k - l| : ℤ):ℝ) := Int.cast_le.mpr h1
    rwa [Int.cast_abs, Int.cast_sub, Int.cast_one] at h2
  rcases le_abs.mp hd with h | h
  · linarith
  · linarith

/-! ### The mass of a first-level interval -/

/-- The natural measure gives the unit interval full mass. -/
theorem measure_Icc_eq_one {ι : Type*} [Fintype ι] {S : System ι} {K : Set ℝ} {s : ℝ}
    {σ : Measure ℝ} (hσ : S.IsNatural K s σ) : σ (Set.Icc (0:ℝ) 1) = 1 := by
  haveI := hσ.isProbability
  have h := measure_add_measure_compl (μ := σ) (measurableSet_Icc (a := (0:ℝ)) (b := 1))
  rw [hσ.support_Icc, add_zero, measure_univ] at h
  exact h

/-- Hutchinson's identity read at a measurable set. -/
theorem measure_eq_sum {ι : Type*} [Fintype ι] {S : System ι} {K : Set ℝ} {s : ℝ}
    {σ : Measure ℝ} (hσ : S.IsNatural K s σ) {E : Set ℝ} (hE : MeasurableSet E) :
    σ E = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * σ (S.map i ⁻¹' E) := by
  conv_lhs => rw [hσ.selfSimilar]
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (S.measurable_map i) hE]

/-- Each first-level interval carries at least the weight of its own piece.  This is
what makes the two measures of `thm:homometric-example` distinct. -/
theorem le_measure_cyl {d : Fin 6 → ℤ} {h0 : ∀ i, 0 ≤ d i} {h17 : ∀ i, d i ≤ 17} {K : Set ℝ}
    {σ : Measure ℝ} (hσ : (homSystem d h0 h17).IsNatural K tHom σ) (i : Fin 6) :
    ENNReal.ofReal ((1/30 : ℝ) ^ tHom) ≤ σ (cyl (d i)) := by
  haveI := hσ.isProbability
  have hpre : σ ((homSystem d h0 h17).map i ⁻¹' cyl (d i)) = 1 := by
    refine le_antisymm (by
      simpa using prob_le_one (μ := σ) (s := (homSystem d h0 h17).map i ⁻¹' cyl (d i))) ?_
    rw [← measure_Icc_eq_one hσ]
    exact measure_mono fun x hx => map_mem_cyl i hx
  rw [measure_eq_sum hσ (measurableSet_cyl (d i))]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun j => ENNReal.ofReal ((homSystem d h0 h17).ratio j ^ tHom) *
      σ ((homSystem d h0 h17).map j ⁻¹' cyl (d i))) (fun j _ => bot_le) (Finset.mem_univ i))
  rw [hpre, mul_one]
  rfl

/-- A set missed by every first-level interval is null. -/
theorem measure_eq_zero_of_avoid {d : Fin 6 → ℤ} {h0 : ∀ i, 0 ≤ d i} {h17 : ∀ i, d i ≤ 17}
    {K : Set ℝ} {σ : Measure ℝ} (hσ : (homSystem d h0 h17).IsNatural K tHom σ) {E : Set ℝ}
    (hE : ∀ i : Fin 6, ∀ x ∈ Set.Icc (0:ℝ) 1, (homSystem d h0 h17).map i x ∉ E) :
    σ E = 0 := by
  refine measure_mono_null ?_ hσ.support
  intro z hzE hzK
  rw [hσ.attractor.2.2.2, Set.mem_iUnion] at hzK
  obtain ⟨i, x, hxK, hx⟩ := hzK
  exact hE i x (hσ.attractor.2.2.1 hxK) (hx ▸ hzE)

/-! ### The difference system -/

/-- The rescaled difference `(x - y + 1)/2`, which carries `[0,1]²` into `[0,1]`. -/
noncomputable def subShift (p : ℝ × ℝ) : ℝ := (p.1 - p.2 + 1)/2

/-- The rescaled difference is measurable. -/
theorem measurable_subShift : Measurable subShift := by
  unfold subShift; fun_prop

/-- The law of the rescaled difference of two independent samples with law `σ`. -/
noncomputable def diffLaw (σ : Measure ℝ) : Measure ℝ := (σ.prod σ).map subShift

/-- The similarity `u ↦ u/30 + (k/36 + 29/60)` attached to a digit difference `k`. -/
noncomputable def diffMap (k : ℤ) (x : ℝ) : ℝ := 1/30 * x + ((k : ℝ)/36 + 29/60)

/-- Each similarity of the difference system is measurable. -/
theorem measurable_diffMap (k : ℤ) : Measurable (diffMap k) := by
  unfold diffMap; fun_prop

/-- The difference system: thirty-six similarities of ratio `1/30`, one for each ordered
pair of digits, the shift determined by the difference of the two digits. -/
noncomputable def diffSystem (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17) :
    System (Fin 6 × Fin 6) where
  ratio _ := 1/30
  shift p := ((d p.1 - d p.2 : ℤ) : ℝ)/36 + 29/60
  ratio_pos _ := by norm_num
  ratio_lt_one _ := by norm_num
  mapsTo p x hx := by
    obtain ⟨hx0, hx1⟩ := hx
    have e1 : (0:ℝ) ≤ ((d p.1 : ℤ) : ℝ) := by exact_mod_cast h0 p.1
    have e2 : ((d p.1 : ℤ) : ℝ) ≤ 17 := by exact_mod_cast h17 p.1
    have e3 : (0:ℝ) ≤ ((d p.2 : ℤ) : ℝ) := by exact_mod_cast h0 p.2
    have e4 : ((d p.2 : ℤ) : ℝ) ≤ 17 := by exact_mod_cast h17 p.2
    have hc : ((d p.1 - d p.2 : ℤ) : ℝ) = ((d p.1 : ℤ) : ℝ) - ((d p.2 : ℤ) : ℝ) := by
      push_cast; ring
    constructor
    · show (0:ℝ) ≤ 1/30 * x + (((d p.1 - d p.2 : ℤ) : ℝ)/36 + 29/60)
      rw [hc]; linarith
    · show 1/30 * x + (((d p.1 - d p.2 : ℤ) : ℝ)/36 + 29/60) ≤ 1
      rw [hc]; linarith

/-- The similarity of the difference system at an ordered pair of positions depends on
the pair only through the difference of the two digits. -/
theorem diffSystem_map (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17)
    (p : Fin 6 × Fin 6) : (diffSystem d h0 h17).map p = diffMap (d p.1 - d p.2) := rfl

/-- `thm:homometric-example`: the weight of a single piece is `1/6`. -/
theorem rpow_tHom : ((1:ℝ)/30) ^ tHom = 1/6 := by
  have h := six_mul_rpow_tHom; linarith

/-- The weight of a single piece of the difference system is `1/36`. -/
theorem rpow_two_tHom : ((1:ℝ)/30) ^ (2 * tHom) = 1/36 := by
  rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/30), rpow_tHom,
    show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The difference system has similarity dimension `2t`: `36·(1/30)^{2t} = 1`. -/
theorem diffSystem_isDimension (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17) :
    (diffSystem d h0 h17).IsDimension (2 * tHom) := by
  have h : ∀ p : Fin 6 × Fin 6, (diffSystem d h0 h17).ratio p = 1/30 := fun _ => rfl
  simp only [System.IsDimension, h, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, rpow_two_tHom]
  norm_num

/-! ### The difference law is self-similar -/

/-- `Measure.map` distributes over a finite sum of measures. -/
theorem map_finsetSum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype ι]
    (m : ι → Measure α) {f : α → β} (hf : Measurable f) :
    (∑ i, m i).map f = ∑ i, (m i).map f := by
  rw [← Measure.sum_fintype, Measure.map_sum hf.aemeasurable, Measure.sum_fintype]

/-- The product of a self-similar measure with itself is self-similar for the product
system, with weights the products of the weights. -/
theorem prod_selfSimilar {ι : Type*} [Fintype ι] (S : System ι) {s : ℝ} {σ : Measure ℝ}
    [IsProbabilityMeasure σ]
    (hσ : σ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • σ.map (S.map i)) :
    σ.prod σ = ∑ p : ι × ι,
      (ENNReal.ofReal (S.ratio p.1 ^ s) * ENNReal.ofReal (S.ratio p.2 ^ s))
        • (σ.prod σ).map (Prod.map (S.map p.1) (S.map p.2)) := by
  classical
  set m : ι → Measure ℝ := fun i => ENNReal.ofReal (S.ratio i ^ s) • σ.map (S.map i) with hm
  have hsum : σ = Measure.sum m := by rw [Measure.sum_fintype]; exact hσ
  calc σ.prod σ = (Measure.sum m).prod (Measure.sum m) := by rw [← hsum]
    _ = Measure.sum (fun p : ι × ι => (m p.1).prod (m p.2)) := Measure.prod_sum m m
    _ = ∑ p : ι × ι, (m p.1).prod (m p.2) := Measure.sum_fintype _
    _ = _ := Finset.sum_congr rfl fun p _ => by
          simp only [hm]
          rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
            Measure.map_prod_map σ σ (S.measurable_map p.1) (S.measurable_map p.2)]

/-- The rescaled difference law is a probability measure. -/
theorem isProbabilityMeasure_diffLaw (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (diffLaw σ) :=
  Measure.isProbabilityMeasure_map measurable_subShift.aemeasurable

/-- The rescaled difference law sits on `[0,1]`, which is what the uniqueness step
`Hutchinson.eq_of_selfSimilar` asks of it. -/
theorem diffLaw_support {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hs : σ (Set.Icc (0:ℝ) 1)ᶜ = 0) : diffLaw σ (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
  have hnull : (σ.prod σ) ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1))ᶜ = 0 := by
    have h1 : (σ.prod σ) ((Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, hs, zero_mul]
    have h2 : (σ.prod σ) ((Set.univ : Set ℝ) ×ˢ (Set.Icc (0:ℝ) 1)ᶜ) = 0 := by
      rw [Measure.prod_prod, hs, mul_zero]
    refine measure_mono_null ?_ (measure_union_null h1 h2)
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, h⟩
  rw [diffLaw, Measure.map_apply measurable_subShift measurableSet_Icc.compl]
  refine measure_mono_null ?_ hnull
  intro z hz hzin
  refine hz ?_
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hzin
  exact ⟨by simp only [subShift]; linarith, by simp only [subShift]; linarith⟩

/-- The rescaled difference law is self-similar for the difference system: this is the
identity the homometry of the digit sets acts on. -/
theorem diffLaw_selfSimilar {d : Fin 6 → ℤ} {h0 : ∀ i, 0 ≤ d i} {h17 : ∀ i, d i ≤ 17}
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hσ : σ = ∑ i, ENNReal.ofReal ((homSystem d h0 h17).ratio i ^ tHom)
      • σ.map ((homSystem d h0 h17).map i)) :
    diffLaw σ = ∑ p : Fin 6 × Fin 6,
      ENNReal.ofReal ((diffSystem d h0 h17).ratio p ^ (2 * tHom))
        • (diffLaw σ).map ((diffSystem d h0 h17).map p) := by
  have hprod := prod_selfSimilar (homSystem d h0 h17) hσ
  rw [diffLaw]
  conv_lhs => rw [hprod]
  rw [map_finsetSum _ measurable_subShift]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Measure.map_smul]
  congr 1
  · have hr : ∀ i : Fin 6, (homSystem d h0 h17).ratio i = 1/30 := fun _ => rfl
    have hr' : (diffSystem d h0 h17).ratio p = 1/30 := rfl
    rw [hr, hr, hr', ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), two_mul,
      Real.rpow_add (by norm_num)]
  · have hcomp : subShift ∘ Prod.map ((homSystem d h0 h17).map p.1) ((homSystem d h0 h17).map p.2)
        = diffMap (d p.1 - d p.2) ∘ subShift := by
      funext z
      obtain ⟨x, y⟩ := z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, subShift, diffMap,
        homSystem_map, hommap]
      push_cast
      ring
    rw [Measure.map_map measurable_subShift
        (((homSystem d h0 h17).measurable_map p.1).prodMap
          ((homSystem d h0 h17).measurable_map p.2)),
      diffSystem_map,
      Measure.map_map (measurable_diffMap _) measurable_subShift, hcomp]

/-! ### The homometry, as an equality of sums over ordered pairs -/

/-- The two digit sets have the same difference multiset, indexed by ordered pairs of
positions.  This is `diffMultiset_eq` in the form the sum over the difference system
consumes. -/
theorem diffMultiset_fin_eq :
    (Finset.univ.val.map fun p : Fin 6 × Fin 6 => digitFunA p.1 - digitFunA p.2)
      = (Finset.univ.val.map fun p : Fin 6 × Fin 6 => digitFunB p.1 - digitFunB p.2) := by
  decide

/-- Every ratio of the difference system is `1/30`. -/
theorem diffSystem_ratio (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17)
    (p : Fin 6 × Fin 6) : (diffSystem d h0 h17).ratio p = 1/30 := rfl

/-- Equal difference multisets give equal sums over the difference system. -/
theorem sum_diffMap_congr (ν : Measure ℝ) (c : ℝ≥0∞) :
    ∑ p : Fin 6 × Fin 6, c • ν.map (diffMap (digitFunA p.1 - digitFunA p.2))
      = ∑ p : Fin 6 × Fin 6, c • ν.map (diffMap (digitFunB p.1 - digitFunB p.2)) := by
  have h : ∀ g : Fin 6 × Fin 6 → ℤ,
      ∑ p : Fin 6 × Fin 6, c • ν.map (diffMap (g p))
        = ((Finset.univ.val.map g).map (fun k => c • ν.map (diffMap k))).sum := by
    intro g
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [h, h, diffMultiset_fin_eq]

/-- The two rescaled difference laws agree.  The homometry of the digit sets makes them
solutions of one and the same self-similar identity, and `Hutchinson.eq_of_selfSimilar`
makes that solution unique. -/
theorem diffLaw_eq {KA KB : Set ℝ} {σA σB : Measure ℝ}
    (hA : (homSystem digitFunA digitFunA_nonneg digitFunA_le).IsNatural KA tHom σA)
    (hB : (homSystem digitFunB digitFunB_nonneg digitFunB_le).IsNatural KB tHom σB) :
    diffLaw σA = diffLaw σB := by
  haveI := hA.isProbability
  haveI := hB.isProbability
  haveI := isProbabilityMeasure_diffLaw σA
  haveI := isProbabilityMeasure_diffLaw σB
  have hidA := diffLaw_selfSimilar hA.selfSimilar
  have hidB := diffLaw_selfSimilar hB.selfSimilar
  have hconv : ∑ p : Fin 6 × Fin 6,
      ENNReal.ofReal ((diffSystem digitFunB digitFunB_nonneg digitFunB_le).ratio p ^ (2 * tHom))
        • (diffLaw σB).map ((diffSystem digitFunB digitFunB_nonneg digitFunB_le).map p)
      = ∑ p : Fin 6 × Fin 6,
      ENNReal.ofReal ((diffSystem digitFunA digitFunA_nonneg digitFunA_le).ratio p ^ (2 * tHom))
        • (diffLaw σB).map ((diffSystem digitFunA digitFunA_nonneg digitFunA_le).map p) := by
    simp only [diffSystem_map, diffSystem_ratio]
    exact (sum_diffMap_congr (diffLaw σB) _).symm
  exact Hutchinson.eq_of_selfSimilar (diffSystem digitFunA digitFunA_nonneg digitFunA_le)
    (diffSystem_isDimension _ _ _) hidA (hidB.trans hconv)
    (diffLaw_support hA.support_Icc) (diffLaw_support hB.support_Icc)

/-- The unscaled difference law read off the rescaled one. -/
theorem map_sub_eq (σ : Measure ℝ) [SFinite σ] :
    (σ.prod σ).map (fun p : ℝ × ℝ => p.1 - p.2) = (diffLaw σ).map (fun u : ℝ => 2 * u - 1) := by
  rw [diffLaw, Measure.map_map (by fun_prop) measurable_subShift]
  congr 1
  funext z
  simp only [Function.comp_apply, subShift]
  ring

/-- The digit `4` of `𝒜` is not a digit of `ℬ`. -/
theorem digitFunB_ne_four : ∀ i, digitFunB i ≠ 4 := by decide

/-- The digit `4` lies in `𝒜` and not in `ℬ`, so its first-level interval is charged by
`σ_A` and null for `σ_B`. -/
theorem measure_cyl_four_pos {KA : Set ℝ} {σA : Measure ℝ}
    (hA : (homSystem digitFunA digitFunA_nonneg digitFunA_le).IsNatural KA tHom σA) :
    σA (cyl 4) ≠ 0 := by
  have h := le_measure_cyl hA 2
  have h4 : digitFunA 2 = 4 := rfl
  rw [h4] at h
  have hne : ENNReal.ofReal ((1/30:ℝ) ^ tHom) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (by norm_num) _
  intro hz
  rw [hz, le_zero_iff] at h
  exact hne h

/-- `thm:homometric-example`: the interval of the digit `4` is null for `σ_B`. -/
theorem measure_cyl_four_zero {KB : Set ℝ} {σB : Measure ℝ}
    (hB : (homSystem digitFunB digitFunB_nonneg digitFunB_le).IsNatural KB tHom σB) :
    σB (cyl 4) = 0 :=
  measure_eq_zero_of_avoid hB fun i _ hx =>
    notMem_cyl (digitFunB_ne_four i) (map_mem_cyl i hx)

end HomometricMeasures

/-- `thm:homometric-example`.  Two distinct strongly separated self-similar measures,
Ahlfors regular of the same dimension `t = log 6 / log 30 ∈ (1/2,1)`, with equal signed
convolutions `σ * σ̃`, hence identical pair-distance distributions and identical
expected profiles. -/
theorem homometric_example :
    ∃ (KA KB : Set ℝ) (σA σB : Measure ℝ) (A : ℝ),
      (homSystem digitFunA digitFunA_nonneg digitFunA_le).IsNatural KA tHom σA ∧
      (homSystem digitFunB digitFunB_nonneg digitFunB_le).IsNatural KB tHom σB ∧
      σA ≠ σB ∧
      (homSystem digitFunA digitFunA_nonneg digitFunA_le).StronglySeparated KA (1/45) ∧
      (homSystem digitFunB digitFunB_nonneg digitFunB_le).StronglySeparated KB (1/45) ∧
      tHom ∈ Set.Ioo (1/2 : ℝ) 1 ∧
      IsAhlfors tHom A σA ∧ IsAhlfors tHom A σB ∧
      σA.conv (reflect σA) = σB.conv (reflect σB) ∧
      (∀ δ : ℝ, Phi σA δ = Phi σB δ) ∧
      (∀ v : ℝ, H tHom σA v = H tHom σB v) := by
  classical
  obtain ⟨⟨KA, σA⟩, hA, -⟩ :=
    (homSystem digitFunA digitFunA_nonneg digitFunA_le).exists_unique_isNatural
      (HomometricMeasures.homSystem_isDimension _ _ _)
  obtain ⟨⟨KB, σB⟩, hB, -⟩ :=
    (homSystem digitFunB digitFunB_nonneg digitFunB_le).exists_unique_isNatural
      (HomometricMeasures.homSystem_isDimension _ _ _)
  haveI := hA.isProbability
  haveI := hB.isProbability
  have hsepA := homSystem_stronglySeparated digitFunA digitFunA_nonneg digitFunA_le
    digitFunA_injective hA.attractor.2.2.1
  have hsepB := homSystem_stronglySeparated digitFunB digitFunB_nonneg digitFunB_le
    digitFunB_injective hB.attractor.2.2.1
  obtain ⟨A₁, hA₁⟩ := exists_isAhlforsClosed _ HomometricMeasures.tHom_pos hsepA
    (HomometricMeasures.homSystem_isDimension _ _ _) hA
  obtain ⟨A₂, hA₂⟩ := exists_isAhlforsClosed _ HomometricMeasures.tHom_pos hsepB
    (HomometricMeasures.homSystem_isDimension _ _ _) hB
  have hconv : σA.conv (reflect σA) = σB.conv (reflect σB) := by
    rw [conv_reflect_eq_map_sub, conv_reflect_eq_map_sub, HomometricMeasures.map_sub_eq,
      HomometricMeasures.map_sub_eq, HomometricMeasures.diffLaw_eq hA hB]
  have hphi : ∀ δ : ℝ, Phi σA δ = Phi σB δ := by
    intro δ
    have hmeas : MeasurableSet {u : ℝ | |u| ≤ δ} :=
      (isClosed_le (by fun_prop) continuous_const).measurableSet
    have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := by fun_prop
    have h := congrArg (fun m : Measure ℝ => m {u : ℝ | |u| ≤ δ})
      ((conv_reflect_eq_map_sub σA).symm.trans (hconv.trans (conv_reflect_eq_map_sub σB)))
    simp only [Measure.map_apply hsub hmeas] at h
    exact congrArg ENNReal.toReal h
  refine ⟨KA, KB, σA, σB, max (2 ^ tHom * A₁) (2 ^ tHom * A₂), hA, hB, ?_, hsepA, hsepB,
    tHom_mem_Ioo,
    AhlforsRegular.isAhlfors_mono (hA₁.isAhlfors HomometricMeasures.tHom_pos.le)
      (le_max_left _ _),
    AhlforsRegular.isAhlfors_mono (hA₂.isAhlfors HomometricMeasures.tHom_pos.le)
      (le_max_right _ _),
    hconv, hphi, fun v => by simp only [H, G, hphi]⟩
  intro hab
  exact HomometricMeasures.measure_cyl_four_pos hA
    (hab ▸ HomometricMeasures.measure_cyl_four_zero hB)

end BrownianImages

