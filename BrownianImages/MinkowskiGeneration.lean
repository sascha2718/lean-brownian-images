/-
`sec:reconstruction` of `BrownianImagesComplete.tex`: deterministic generation
cylinders for a finite self-similar system.

The word type is recursive.  At generation zero it has one empty word; appending a
letter produces a word of the next generation.  The corresponding similarity is
obtained by composing the new letter on the outside.  This convention makes the
finite-word sum exactly the iterate of Hutchinson's test-function operator.

The main outputs are:

* `GenerationWord`, `System.generationMap`, `System.generationRatio`, and
  `System.generationWeight`: finite words and their deterministic data;
* `System.IsAttractor.generationCompactUnion_eq`: every generation covers the
  attractor exactly;
* `System.IsAttractor.diam_generationCylinder_le`: all generation-`k` cylinders have
  diameter at most `maxRatio S ^ k`;
* `System.IsNatural.tendsto_generationQuadrature`: weighted anchors converge against
  every bounded continuous test function, with an explicit Lipschitz error bound in
  `System.IsNatural.abs_integral_sub_generationQuadrature_le`.
-/
import BrownianImages.Hutchinson
import BrownianImages.MinkowskiReconstruction
import BrownianImages.MinkowskiSystem

namespace BrownianImages

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

noncomputable section

universe u

/-! ### Finite words and their similarities -/

/-- Words of exactly `k` letters.  A successor word consists of a word of length
`k` and one new outer letter. -/
abbrev GenerationWord (iota : Type u) : ℕ → Type u
  | 0 => PUnit
  | Nat.succ k => GenerationWord iota k × iota

instance {iota : Type*} [Fintype iota] (k : ℕ) :
    Fintype (GenerationWord iota k) := by
  induction k with
  | zero =>
      change Fintype PUnit
      infer_instance
  | succ k ih =>
      change Fintype (GenerationWord iota k × iota)
      letI : Fintype (GenerationWord iota k) := ih
      infer_instance

instance {iota : Type*} [Nonempty iota] (k : ℕ) :
    Nonempty (GenerationWord iota k) := by
  induction k with
  | zero =>
      change Nonempty PUnit
      infer_instance
  | succ k ih =>
      change Nonempty (GenerationWord iota k × iota)
      letI : Nonempty (GenerationWord iota k) := ih
      infer_instance

namespace System

variable {iota : Type*} [Fintype iota] [Nonempty iota] (S : System iota)

/-- The similarity represented by a generation word.  The empty word is the
identity and a new letter is composed on the outside. -/
def generationMap (S : System iota) : (k : ℕ) → GenerationWord iota k → ℝ → ℝ
  | 0, _ => id
  | Nat.succ k, w => S.map w.2 ∘ S.generationMap k w.1

omit [Nonempty iota] in
@[simp]
theorem generationMap_zero (w : GenerationWord iota 0) :
    S.generationMap 0 w = id := rfl

omit [Nonempty iota] in
@[simp]
theorem generationMap_succ (k : ℕ) (w : GenerationWord iota (Nat.succ k)) :
    S.generationMap (Nat.succ k) w = S.map w.2 ∘ S.generationMap k w.1 := rfl

omit [Nonempty iota] in
/-- Every finite-word similarity is continuous. -/
theorem continuous_generationMap :
  ∀ (k : ℕ) (w : GenerationWord iota k), Continuous (S.generationMap k w)
  | 0, _ => continuous_id
  | Nat.succ k, w => (S.continuous_map w.2).comp (continuous_generationMap k w.1)

/-- The product contraction ratio represented by a generation word. -/
def generationRatio (S : System iota) : (k : ℕ) → GenerationWord iota k → ℝ
  | 0, _ => 1
  | Nat.succ k, w => S.generationRatio k w.1 * S.ratio w.2

/-- The product natural weight represented by a generation word. -/
def generationWeight (S : System iota) (s : ℝ) :
    (k : ℕ) → GenerationWord iota k → ℝ
  | 0, _ => 1
  | Nat.succ k, w => S.generationWeight s k w.1 * S.tubeWeight s w.2

omit [Nonempty iota] in
/-- A finite-word similarity has the advertised product ratio. -/
theorem generationMap_sub :
    ∀ (k : ℕ) (w : GenerationWord iota k) (x y : ℝ),
      S.generationMap k w x - S.generationMap k w y =
        S.generationRatio k w * (x - y)
  | 0, _, x, y => by simp [generationMap, generationRatio]
  | Nat.succ k, ⟨w, i⟩, x, y => by
      change
        (S.ratio i * S.generationMap k w x + S.shift i) -
            (S.ratio i * S.generationMap k w y + S.shift i) =
          (S.generationRatio k w * S.ratio i) * (x - y)
      calc
        (S.ratio i * S.generationMap k w x + S.shift i) -
            (S.ratio i * S.generationMap k w y + S.shift i) =
            S.ratio i *
              (S.generationMap k w x - S.generationMap k w y) := by ring
        _ = S.ratio i * (S.generationRatio k w * (x - y)) := by
          rw [generationMap_sub k w x y]
        _ = (S.generationRatio k w * S.ratio i) * (x - y) := by ring

omit [Nonempty iota] in
/-- Product contraction ratios are strictly positive. -/
theorem generationRatio_pos :
    ∀ (k : ℕ) (w : GenerationWord iota k), 0 < S.generationRatio k w
  | 0, _ => by simp [generationRatio]
  | Nat.succ k, ⟨w, i⟩ =>
      mul_pos (generationRatio_pos k w) (S.ratio_pos i)

/-- Product contraction ratios are uniformly bounded by the corresponding power of
the largest one-letter ratio. -/
theorem generationRatio_le_maxRatio_pow :
    ∀ (k : ℕ) (w : GenerationWord iota k),
      S.generationRatio k w ≤ Hutchinson.maxRatio S ^ k
  | 0, _ => by simp [generationRatio]
  | Nat.succ k, ⟨w, i⟩ => by
      rw [generationRatio, pow_succ]
      exact mul_le_mul (generationRatio_le_maxRatio_pow k w)
        (Hutchinson.ratio_le_maxRatio S i) (S.ratio_pos i).le
        (pow_nonneg (Hutchinson.maxRatio_pos S).le k)

omit [Nonempty iota] in
/-- Product natural weights are strictly positive. -/
theorem generationWeight_pos (s : ℝ) :
    ∀ (k : ℕ) (w : GenerationWord iota k), 0 < S.generationWeight s k w
  | 0, _ => by simp [generationWeight]
  | Nat.succ k, ⟨w, i⟩ =>
      mul_pos (generationWeight_pos s k w) (S.tubeWeight_pos s i)

omit [Nonempty iota] in
/-- Product natural weights are nonnegative. -/
theorem generationWeight_nonneg (s : ℝ) (k : ℕ) (w : GenerationWord iota k) :
    0 ≤ S.generationWeight s k w :=
  (S.generationWeight_pos s k w).le

omit [Nonempty iota] in
/-- The recursive product weight is the `s`-power of the product similarity ratio. -/
theorem generationWeight_eq_ratio_rpow (s : ℝ) :
    ∀ (k : ℕ) (w : GenerationWord iota k),
      S.generationWeight s k w = S.generationRatio k w ^ s
  | 0, _ => by simp [generationWeight, generationRatio]
  | Nat.succ k, ⟨w, i⟩ => by
      rw [generationWeight, generationRatio, Real.mul_rpow
        (S.generationRatio_pos k w).le (S.ratio_pos i).le,
        ← generationWeight_eq_ratio_rpow s k w]
      rfl

omit [Nonempty iota] in
/-- At the similarity dimension, the weights at every generation sum to one. -/
theorem sum_generationWeight {s : ℝ} (hdim : S.IsDimension s) :
    ∀ k : ℕ, ∑ w : GenerationWord iota k, S.generationWeight s k w = 1
  | 0 => by simp [GenerationWord, generationWeight]
  | Nat.succ k => by
      change (∑ w : GenerationWord iota k × iota,
        S.generationWeight s k w.1 * S.tubeWeight s w.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        (∑ w : GenerationWord iota k,
            ∑ i : iota, S.generationWeight s k w * S.tubeWeight s i) =
            ∑ w : GenerationWord iota k,
              S.generationWeight s k w * (∑ i : iota, S.tubeWeight s i) := by
                apply Finset.sum_congr rfl
                intro w _
                rw [Finset.mul_sum]
        _ = ∑ w : GenerationWord iota k, S.generationWeight s k w := by
          rw [S.sum_tubeWeight hdim]
          simp
        _ = 1 := sum_generationWeight hdim k

/-! ### Generation cylinders of an attractor -/

omit [Nonempty iota] in
/-- Each one-letter similarity maps an invariant attractor into itself. -/
theorem IsAttractor.mapsTo_map {K : Set ℝ} (hK : S.IsAttractor K) (i : iota) :
    MapsTo (S.map i) K K := by
  intro x hx
  rw [hK.2.2.2]
  exact Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩

omit [Nonempty iota] in
/-- Every finite-word similarity maps the attractor into itself. -/
theorem IsAttractor.mapsTo_generationMap {K : Set ℝ} (hK : S.IsAttractor K) :
    ∀ (k : ℕ) (w : GenerationWord iota k), MapsTo (S.generationMap k w) K K
  | 0, _ => by simpa [generationMap] using Set.mapsTo_id K
  | Nat.succ k, ⟨w, i⟩ =>
      (hK.mapsTo_map S i).comp
        (mapsTo_generationMap hK k w)

/-- The compact cylinder obtained by applying a finite-word similarity to the
attractor. -/
def IsAttractor.generationCylinder {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) (w : GenerationWord iota k) : NonemptyCompacts ℝ :=
  hK.toNonemptyCompacts.map (S.generationMap k w)
    (S.continuous_generationMap k w)

omit [Nonempty iota] in
@[simp]
theorem IsAttractor.coe_generationCylinder {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) (w : GenerationWord iota k) :
    (hK.generationCylinder S k w : Set ℝ) = S.generationMap k w '' K := by
  rw [IsAttractor.generationCylinder, NonemptyCompacts.coe_map,
    IsAttractor.coe_toNonemptyCompacts]

omit [Nonempty iota] in
/-- Every generation cylinder is contained in the attractor. -/
theorem IsAttractor.generationCylinder_subset {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) (w : GenerationWord iota k) :
    (hK.generationCylinder S k w : Set ℝ) ⊆ K := by
  rw [hK.coe_generationCylinder S k w]
  rintro _ ⟨x, hx, rfl⟩
  exact hK.mapsTo_generationMap S k w hx

omit [Nonempty iota] in
/-- Every point of the attractor has a preimage in some cylinder at every fixed
generation. -/
theorem IsAttractor.exists_generation_preimage {K : Set ℝ} (hK : S.IsAttractor K) :
    ∀ (k : ℕ) {x : ℝ}, x ∈ K →
      ∃ w : GenerationWord iota k, ∃ y ∈ K, S.generationMap k w y = x
  | 0, x, hx => ⟨PUnit.unit, x, hx, rfl⟩
  | Nat.succ k, x, hx => by
      have hx' : x ∈ ⋃ i, S.map i '' K := hK.2.2.2 ▸ hx
      obtain ⟨i, y, hy, hiy⟩ := Set.mem_iUnion.1 hx'
      obtain ⟨w, z, hz, hwz⟩ := exists_generation_preimage hK k hy
      refine ⟨(w, i), z, hz, ?_⟩
      rw [generationMap_succ, Function.comp_apply, hwz, hiy]

omit [Nonempty iota] in
/-- The set-theoretic union of all generation-`k` cylinders is exactly the
attractor. -/
theorem IsAttractor.iUnion_generationCylinder {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) :
    (⋃ w : GenerationWord iota k, (hK.generationCylinder S k w : Set ℝ)) = K := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨w, hxw⟩ := Set.mem_iUnion.1 hx
    exact hK.generationCylinder_subset S k w hxw
  · intro x hx
    obtain ⟨w, y, hy, hwy⟩ := hK.exists_generation_preimage S k hx
    exact Set.mem_iUnion.2 ⟨w, by
      rw [hK.coe_generationCylinder S k w]
      exact ⟨y, hy, hwy⟩⟩

/-- The bundled compact union of all generation-`k` cylinders. -/
def IsAttractor.generationCompactUnion {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) : NonemptyCompacts ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun w : GenerationWord iota k => hK.generationCylinder S k w)

/-- The bundled compact union of all generation-`k` cylinders is exactly the bundled
attractor. -/
theorem IsAttractor.generationCompactUnion_eq {K : Set ℝ}
    (hK : S.IsAttractor K) (k : ℕ) :
    hK.generationCompactUnion S k = hK.toNonemptyCompacts := by
  unfold IsAttractor.generationCompactUnion
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro w _
    exact hK.generationCylinder_subset S k w
  · intro x hx
    obtain ⟨w, y, hy, hwy⟩ := hK.exists_generation_preimage S k hx
    apply (Finset.le_sup'
      (fun w : GenerationWord iota k => hK.generationCylinder S k w)
      (Finset.mem_univ w))
    change x ∈ (hK.generationCylinder S k w : Set ℝ)
    rw [hK.coe_generationCylinder S k w]
    exact ⟨y, hy, hwy⟩

/-- A fixed point of the attractor used to choose one anchor in every cylinder. -/
def IsAttractor.baseAnchor {K : Set ℝ} (hK : S.IsAttractor K) : ℝ :=
  Classical.choose hK.2.1

omit [Nonempty iota] in
theorem IsAttractor.baseAnchor_mem {K : Set ℝ} (hK : S.IsAttractor K) :
    hK.baseAnchor S ∈ K :=
  Classical.choose_spec hK.2.1

/-- The anchor in a cylinder is the image of one fixed attractor point under the
word similarity. -/
def IsAttractor.generationAnchor {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) (w : GenerationWord iota k) : ℝ :=
  S.generationMap k w (hK.baseAnchor S)

omit [Nonempty iota] in
/-- The chosen anchor belongs to its cylinder. -/
theorem IsAttractor.generationAnchor_mem {K : Set ℝ} (hK : S.IsAttractor K)
    (k : ℕ) (w : GenerationWord iota k) :
    hK.generationAnchor S k w ∈ hK.generationCylinder S k w := by
  change hK.generationAnchor S k w ∈
    (hK.generationCylinder S k w : Set ℝ)
  rw [hK.coe_generationCylinder S k w]
  exact ⟨hK.baseAnchor S, hK.baseAnchor_mem S, rfl⟩

/-- Every generation-`k` cylinder has diameter at most `maxRatio S ^ k`.  The factor
`diam K` can be omitted because every attractor is contained in `[0,1]`. -/
theorem IsAttractor.diam_generationCylinder_le {K : Set ℝ}
    (hK : S.IsAttractor K) (k : ℕ) (w : GenerationWord iota k) :
    Metric.diam (hK.generationCylinder S k w : Set ℝ) ≤
      Hutchinson.maxRatio S ^ k := by
  apply Metric.diam_le_of_forall_dist_le
    (pow_nonneg (Hutchinson.maxRatio_pos S).le k)
  intro x hx y hy
  rw [hK.coe_generationCylinder S k w] at hx hy
  obtain ⟨x0, hx0, rfl⟩ := hx
  obtain ⟨y0, hy0, rfl⟩ := hy
  have hxI := hK.2.2.1 hx0
  have hyI := hK.2.2.1 hy0
  have hxy : |x0 - y0| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hxI.1, hxI.2, hyI.1, hyI.2]
  rw [Real.dist_eq, S.generationMap_sub k w x0 y0, abs_mul,
    abs_of_pos (S.generationRatio_pos k w)]
  calc
    S.generationRatio k w * |x0 - y0| ≤
        (Hutchinson.maxRatio S ^ k) * 1 :=
      mul_le_mul (S.generationRatio_le_maxRatio_pow k w) hxy
        (abs_nonneg _) (pow_nonneg (Hutchinson.maxRatio_pos S).le k)
    _ = Hutchinson.maxRatio S ^ k := mul_one _

/-! ### Weighted anchor quadrature -/

/-- Weighted evaluation at one chosen anchor in every generation cylinder. -/
def IsAttractor.generationQuadrature {K : Set ℝ} (hK : S.IsAttractor K)
    (s : ℝ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ w : GenerationWord iota k,
    S.generationWeight s k w * f (hK.generationAnchor S k w)

omit [Nonempty iota] in
/-- Iterating Hutchinson's test-function operator expands as the finite sum over
generation words. -/
theorem iterate_testOp_apply_eq_generationSum (s : ℝ)
    (f : BoundedContinuousFunction ℝ ℝ) :
    ∀ (k : ℕ) (x : ℝ),
      (Hutchinson.testOp S s)^[k] f x =
        ∑ w : GenerationWord iota k,
          S.generationWeight s k w * f (S.generationMap k w x)
    := by
  intro k x
  induction k generalizing f x with
  | zero => simp [GenerationWord, generationWeight, generationMap]
  | succ k ih =>
      rw [Function.iterate_succ_apply,
        ih (Hutchinson.testOp S s f) x]
      simp_rw [Hutchinson.testOp_apply]
      change (∑ w : GenerationWord iota k,
          S.generationWeight s k w *
            ∑ i : iota, S.tubeWeight s i * f (S.map i (S.generationMap k w x))) =
        ∑ w : GenerationWord iota k × iota,
          (S.generationWeight s k w.1 * S.tubeWeight s w.2) *
            f (S.map w.2 (S.generationMap k w.1 x))
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

omit [Nonempty iota] in
/-- The generation quadrature is exactly the corresponding iterate of Hutchinson's
operator at the fixed base anchor. -/
theorem IsAttractor.generationQuadrature_eq_iterate_testOp {K : Set ℝ}
    (hK : S.IsAttractor K) (s : ℝ) (k : ℕ)
    (f : BoundedContinuousFunction ℝ ℝ) :
    hK.generationQuadrature S s k f =
      (Hutchinson.testOp S s)^[k] f (hK.baseAnchor S) := by
  rw [S.iterate_testOp_apply_eq_generationSum s f]
  rfl

/-- A modulus of continuity on `[0,1]` gives the same error for the generation
quadrature once `maxRatio S ^ k` is below the input scale. -/
theorem IsNatural.abs_integral_sub_generationQuadrature_le_of_modulus
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hdim : S.IsDimension s) (f : BoundedContinuousFunction ℝ ℝ)
    {epsilon delta : ℝ} (_hepsilon : 0 ≤ epsilon)
    (hmod : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      |a - b| ≤ delta → |f a - f b| ≤ epsilon)
    {k : ℕ} (hk : Hutchinson.maxRatio S ^ k ≤ delta) :
    |(∫ x, f x ∂mu) - hmu.attractor.generationQuadrature S s k f| ≤ epsilon := by
  letI := hmu.isProbabilityMeasure
  let z : ℝ := hmu.attractor.baseAnchor S
  let g : BoundedContinuousFunction ℝ ℝ := (Hutchinson.testOp S s)^[k] f
  have hquad : hmu.attractor.generationQuadrature S s k f = g z := by
    exact hmu.attractor.generationQuadrature_eq_iterate_testOp S s k f
  have hint : (∫ x, f x ∂mu) = ∫ x, g x ∂mu := by
    exact Hutchinson.integral_iterate_testOp S hmu.selfSimilar f k
  have hdiff : (∫ x, g x - g z ∂mu) = (∫ x, g x ∂mu) - g z := by
    rw [integral_sub (BoundedContinuousFunction.integrable mu g)
      (integrable_const (g z))]
    simp
  have hKae : ∀ᵐ x ∂mu, x ∈ K := ae_iff.2 hmu.support
  have hae : ∀ᵐ x ∂mu, ‖g x - g z‖ ≤ epsilon := by
    filter_upwards [hKae] with x hx
    rw [Real.norm_eq_abs]
    apply Hutchinson.abs_sub_iterate_testOp_le S hdim f hmod k x
      (hmu.attractor.2.2.1 hx) z
      (hmu.attractor.2.2.1 (hmu.attractor.baseAnchor_mem S))
    have hxI := hmu.attractor.2.2.1 hx
    have hzI := hmu.attractor.2.2.1 (hmu.attractor.baseAnchor_mem S)
    have hxz : |x - z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hxI.1, hxI.2, hzI.1, hzI.2]
    calc
      |x - z| * Hutchinson.maxRatio S ^ k ≤
          1 * Hutchinson.maxRatio S ^ k :=
        mul_le_mul_of_nonneg_right hxz
          (pow_nonneg (Hutchinson.maxRatio_pos S).le k)
      _ ≤ delta := by simpa using hk
  rw [hquad, hint, ← hdiff, ← Real.norm_eq_abs]
  have hbound := norm_integral_le_of_norm_le_const hae
  simpa using hbound

/-- Explicit quadrature error for a bounded Lipschitz test function. -/
theorem IsNatural.abs_integral_sub_generationQuadrature_le
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hdim : S.IsDimension s) {L : ℝ≥0} (f : BoundedContinuousFunction ℝ ℝ)
    (hf : LipschitzWith L f) (k : ℕ) :
    |(∫ x, f x ∂mu) - hmu.attractor.generationQuadrature S s k f| ≤
      (L : ℝ) * Hutchinson.maxRatio S ^ k := by
  apply hmu.abs_integral_sub_generationQuadrature_le_of_modulus S hdim f
    (mul_nonneg L.coe_nonneg (pow_nonneg (Hutchinson.maxRatio_pos S).le k))
    (delta := Hutchinson.maxRatio S ^ k) (k := k)
  · intro a _ b _ hab
    rw [← Real.dist_eq] at hab ⊢
    exact hf.dist_le_mul_of_le hab
  · exact le_rfl

/-- Weighted anchor quadrature converges to integration against the natural measure
for every bounded continuous test function. -/
theorem IsNatural.tendsto_generationQuadrature
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hdim : S.IsDimension s) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun k : ℕ => hmu.attractor.generationQuadrature S s k f) atTop
      (nhds (∫ x, f x ∂mu)) := by
  apply Metric.tendsto_atTop.2
  intro epsilon hepsilon
  have huc : UniformContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨delta, hdelta, hmod⟩ :=
    Metric.uniformContinuousOn_iff_le.1 huc (epsilon / 2) (by linarith)
  have hpow := Hutchinson.tendsto_pow_maxRatio S
  rw [Metric.tendsto_atTop] at hpow
  obtain ⟨N, hN⟩ := hpow delta hdelta
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hkdelta : Hutchinson.maxRatio S ^ k ≤ delta := by
    have hdist := hN k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (pow_nonneg (Hutchinson.maxRatio_pos S).le k)] at hdist
    exact hdist.le
  have hbound := hmu.abs_integral_sub_generationQuadrature_le_of_modulus S hdim f
    (show 0 ≤ epsilon / 2 by linarith)
    (fun a ha b hb hab => by
      have := hmod a ha b hb (by simpa only [Real.dist_eq] using hab)
      simpa only [Real.dist_eq] using this)
    hkdelta
  linarith

/-! ### Continuous images of generation cylinders -/

/-- A continuous image of the generation cylinders has vanishing weighted mean
diameter.  This is the deterministic compact-uniform-continuity input needed when the
continuous map is a Brownian sample path. -/
theorem IsAttractor.tendsto_sum_generationWeight_mul_diam_image
    {K : Set ℝ} {s : ℝ} (hK : S.IsAttractor K) (hdim : S.IsDimension s)
    {X : Type*} [PseudoMetricSpace X] (g : ℝ → X) (hg : Continuous g) :
    Tendsto
      (fun k : ℕ => ∑ w : GenerationWord iota k,
        S.generationWeight s k w *
          Metric.diam (g '' (hK.generationCylinder S k w : Set ℝ)))
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro epsilon hepsilon
  have huc : UniformContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨delta, hdelta, hmod⟩ :=
    Metric.uniformContinuousOn_iff_le.1 huc (epsilon / 2) (by linarith)
  have hpow := Hutchinson.tendsto_pow_maxRatio S
  rw [Metric.tendsto_atTop] at hpow
  obtain ⟨N, hN⟩ := hpow delta hdelta
  refine ⟨N, fun k hk => ?_⟩
  have hkdelta : Hutchinson.maxRatio S ^ k ≤ delta := by
    have hdist := hN k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (pow_nonneg (Hutchinson.maxRatio_pos S).le k)] at hdist
    exact hdist.le
  have hcyl : ∀ w : GenerationWord iota k,
      Metric.diam (g '' (hK.generationCylinder S k w : Set ℝ)) ≤ epsilon / 2 := by
    intro w
    apply Metric.diam_le_of_forall_dist_le (by linarith)
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    apply hmod a (hK.2.2.1 (hK.generationCylinder_subset S k w ha))
      b (hK.2.2.1 (hK.generationCylinder_subset S k w hb))
    calc
      dist a b ≤ Metric.diam (hK.generationCylinder S k w : Set ℝ) :=
        Metric.dist_le_diam_of_mem
          (hK.generationCylinder S k w).isCompact.isBounded ha hb
      _ ≤ Hutchinson.maxRatio S ^ k := hK.diam_generationCylinder_le S k w
      _ ≤ delta := hkdelta
  have hsum_nonneg : 0 ≤ ∑ w : GenerationWord iota k,
      S.generationWeight s k w *
        Metric.diam (g '' (hK.generationCylinder S k w : Set ℝ)) := by
    exact Finset.sum_nonneg fun w _ =>
      mul_nonneg (S.generationWeight_nonneg s k w) Metric.diam_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nonneg]
  calc
    (∑ w : GenerationWord iota k,
        S.generationWeight s k w *
          Metric.diam (g '' (hK.generationCylinder S k w : Set ℝ))) ≤
        ∑ w : GenerationWord iota k,
          S.generationWeight s k w * (epsilon / 2) := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (hcyl w)
        (S.generationWeight_nonneg s k w)
    _ = epsilon / 2 := by
      rw [← Finset.sum_mul, S.sum_generationWeight hdim k, one_mul]
    _ < epsilon := by linarith

/-! ### Brownian generation cylinders -/

section BrownianGeneration

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} {W : ℝ≥0 → Omega → Plane}

/-- The Brownian image of one deterministic generation cylinder. -/
noncomputable def IsAttractor.brownianGenerationCylinder {K : Set ℝ}
    (hK : S.IsAttractor K) (W : ℝ≥0 → Omega → Plane) (omega : Omega)
    (k : ℕ) (w : GenerationWord iota k) : CompactPlane :=
  brownianImage W (hK.generationCylinder S k w) omega

/-- The Brownian image of the chosen deterministic anchor of a generation cylinder. -/
def IsAttractor.brownianGenerationAnchor {K : Set ℝ} (hK : S.IsAttractor K)
    (W : ℝ≥0 → Omega → Plane) (omega : Omega) (k : ℕ)
    (w : GenerationWord iota k) : Plane :=
  W (hK.generationAnchor S k w).toNNReal omega

omit [MeasurableSpace Omega] in
/-- On a continuous path, the finite union of the Brownian generation cylinders is
exactly the Brownian image of the whole attractor. -/
theorem IsAttractor.compactUnion_brownianGenerationCylinder_eq
    {K : Set ℝ} (hK : S.IsAttractor K) {omega : Omega}
    (homega : Continuous (fun t : ℝ≥0 => W t omega)) (k : ℕ) :
    compactUnion (hK.brownianGenerationCylinder S W omega k) =
      brownianImage W hK.toNonemptyCompacts omega := by
  apply le_antisymm
  · unfold compactUnion
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro w _ x hx
    change x ∈ (brownianImage W (hK.generationCylinder S k w) omega : Set Plane) at hx
    change x ∈ (brownianImage W hK.toNonemptyCompacts omega : Set Plane)
    rw [coe_brownianImage_of_continuous _ homega] at hx
    rw [coe_brownianImage_of_continuous _ homega]
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨t, hK.generationCylinder_subset S k w ht, rfl⟩
  · intro x hx
    change x ∈ (brownianImage W hK.toNonemptyCompacts omega : Set Plane) at hx
    rw [coe_brownianImage_of_continuous _ homega] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨w, y, hy, hwy⟩ := hK.exists_generation_preimage S k ht
    apply Finset.le_sup'
      (hK.brownianGenerationCylinder S W omega k) (Finset.mem_univ w)
    change W t.toNNReal omega ∈
      (hK.brownianGenerationCylinder S W omega k w : Set Plane)
    rw [IsAttractor.brownianGenerationCylinder,
      coe_brownianImage_of_continuous _ homega]
    refine ⟨t, ?_, rfl⟩
    rw [hK.coe_generationCylinder S k w]
    exact ⟨y, hy, hwy⟩

omit [MeasurableSpace Omega] in
omit [Nonempty iota] in
/-- On a continuous path, the chosen Brownian anchor belongs to its Brownian
generation cylinder. -/
theorem IsAttractor.brownianGenerationAnchor_mem {K : Set ℝ}
    (hK : S.IsAttractor K) {omega : Omega}
    (homega : Continuous (fun t : ℝ≥0 => W t omega)) (k : ℕ)
    (w : GenerationWord iota k) :
    hK.brownianGenerationAnchor S W omega k w ∈
      hK.brownianGenerationCylinder S W omega k w := by
  change hK.brownianGenerationAnchor S W omega k w ∈
    (brownianImage W (hK.generationCylinder S k w) omega : Set Plane)
  rw [coe_brownianImage_of_continuous _ homega]
  unfold IsAttractor.brownianGenerationAnchor
  exact ⟨hK.generationAnchor S k w, hK.generationAnchor_mem S k w, rfl⟩

omit [MeasurableSpace Omega] in
/-- On a continuous path, the generation cylinders in the Brownian image have
vanishing weighted mean diameter. -/
theorem IsAttractor.tendsto_weighted_diam_brownianGenerationCylinder
    {K : Set ℝ} {s : ℝ} (hK : S.IsAttractor K) (hdim : S.IsDimension s)
    {omega : Omega} (homega : Continuous (fun t : ℝ≥0 => W t omega)) :
    Tendsto
      (fun k : ℕ => ∑ w : GenerationWord iota k,
        S.generationWeight s k w * Metric.diam
          (hK.brownianGenerationCylinder S W omega k w : Set Plane))
      atTop (nhds 0) := by
  have h := hK.tendsto_sum_generationWeight_mul_diam_image S hdim
    (fun t : ℝ => W t.toNNReal omega)
    (homega.comp continuous_real_toNNReal)
  simpa only [IsAttractor.brownianGenerationCylinder,
    coe_brownianImage_of_continuous _ homega] using h

omit [MeasurableSpace Omega] in
/-- The weighted Brownian anchors converge against every bounded continuous test
function to its occupation integral. -/
theorem IsNatural.tendsto_brownianGenerationAnchor
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hdim : S.IsDimension s) {omega : Omega}
    (homega : Continuous (fun t : ℝ≥0 => W t omega))
    (hoccupation : (occupationProb W mu omega).toMeasure = occupation W mu omega)
    (f : Plane →ᵇ ℝ) :
    Tendsto
      (fun k : ℕ => ∑ w : GenerationWord iota k,
        S.generationWeight s k w *
          f (hmu.attractor.brownianGenerationAnchor S W omega k w))
      atTop
      (nhds (∫ x, f x ∂(occupationProb W mu omega : Measure Plane))) := by
  let path : C(ℝ, Plane) :=
    ⟨fun t : ℝ => W t.toNNReal omega, homega.comp continuous_real_toNNReal⟩
  have hquad := hmu.tendsto_generationQuadrature S hdim
    (f.compContinuous path)
  have hint :
      (∫ x, f x ∂(occupationProb W mu omega : Measure Plane)) =
        ∫ t, f (W t.toNNReal omega) ∂mu := by
    rw [hoccupation, occupation,
      integral_map (measurable_pathMap homega).aemeasurable
        f.continuous.aestronglyMeasurable]
  rw [hint]
  simpa only [IsAttractor.generationQuadrature,
    IsAttractor.brownianGenerationAnchor,
    BoundedContinuousFunction.compContinuous_apply, path,
    ContinuousMap.coe_mk] using hquad

/-- Paper-shaped generation-cylinder specialization of the abstract reconstruction
theorem.  All deterministic cylinder data and all consequences of Brownian path
continuity are discharged here.  The sole remaining analytic hypothesis is the
fixed-generation convergence of the normalised tube masses to the natural cylinder
weights. -/
theorem IsNatural.tubeReconstructsOccupation_of_generation_tubeMassRatio
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hdim : S.IsDimension s) (hW : IsPlanarBrownian W P)
    (hratio : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hmu.attractor.brownianGenerationCylinder S W omega k) w)
        atTop (nhds (S.generationWeight s k w))) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  letI : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  have hcont := hW.ae_continuous
  have hoccupation := hW.ae_occupationProb_toMeasure mu
  have hunion : ∀ᵐ omega ∂P, ∀ k,
      compactUnion (hmu.attractor.brownianGenerationCylinder S W omega k) =
        brownianImage W hmu.compactAttractor omega := by
    filter_upwards [hcont] with omega homega
    intro k
    simpa only [IsNatural.compactAttractor] using
      hmu.attractor.compactUnion_brownianGenerationCylinder_eq S homega k
  have hanchor : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota k),
      hmu.attractor.brownianGenerationAnchor S W omega k w ∈
        hmu.attractor.brownianGenerationCylinder S W omega k w := by
    filter_upwards [hcont] with omega homega
    intro k w
    exact hmu.attractor.brownianGenerationAnchor_mem S homega k w
  have hdiam : ∀ᵐ omega ∂P, Tendsto
      (fun k => ∑ w : GenerationWord iota k,
        S.generationWeight s k w * Metric.diam
          (hmu.attractor.brownianGenerationCylinder S W omega k w : Set Plane))
      atTop (nhds 0) := by
    filter_upwards [hcont] with omega homega
    exact hmu.attractor.tendsto_weighted_diam_brownianGenerationCylinder
      S hdim homega
  have hatomic : ∀ᵐ omega ∂P,
      ∀ (f : Plane →ᵇ ℝ) {L : ℝ≥0}, LipschitzWith L f →
        Tendsto
          (fun k => ∑ w : GenerationWord iota k,
            S.generationWeight s k w *
              f (hmu.attractor.brownianGenerationAnchor S W omega k w))
          atTop
          (nhds (∫ x, f x ∂(occupationProb W mu omega : Measure Plane))) := by
    filter_upwards [hcont, hoccupation] with omega homega hoccupationOmega
    intro f L _hf
    exact hmu.tendsto_brownianGenerationAnchor S hdim homega
      hoccupationOmega f
  exact
    MinkowskiReconstruction.tubeReconstructsOccupation_of_ae_cylinder_approximation
      (P := P) (W := W) (K := hmu.compactAttractor) (mu := mu)
      (fun k => GenerationWord iota k)
      (fun omega k => hmu.attractor.brownianGenerationCylinder S W omega k)
      (fun omega k => hmu.attractor.brownianGenerationAnchor S W omega k)
      (fun k => S.generationWeight s k)
      (fun k w => S.generationWeight_nonneg s k w)
      (S.sum_generationWeight hdim) hunion hanchor hratio hdiam hatomic

end BrownianGeneration

end System

namespace MinkowskiReconstruction

/-- Set-law singularity in the exact generation-cylinder form: once the tube-mass
ratios converge to the natural weights for two self-similar time sets, any
singularity already proved for their Brownian occupation laws descends to the laws
of the compact Brownian images themselves. -/
theorem brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : ℝ≥0 -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    {iota1 iota2 : Type*}
    [Fintype iota1] [Nonempty iota1] [Fintype iota2] [Nonempty iota2]
    (S1 : System iota1) (S2 : System iota2)
    {K1 K2 : Set ℝ} {s1 s2 : ℝ} {mu1 mu2 : Measure ℝ}
    (hmu1 : S1.IsNatural K1 s1 mu1) (hdim1 : S1.IsDimension s1)
    (hmu2 : S2.IsNatural K2 s2 mu2) (hdim2 : S2.IsDimension s2)
    (hratio1 : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota1 k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hmu1.attractor.brownianGenerationCylinder S1 W omega k) w)
        atTop (nhds (S1.generationWeight s1 k w)))
    (hratio2 : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota2 k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hmu2.attractor.brownianGenerationCylinder S2 W omega k) w)
        atTop (nhds (S2.generationWeight s2 k w)))
    (hoccupation : (occupationLaw W P mu1).MutuallySingular
      (occupationLaw W P mu2)) :
    (brownianImageLaw W P hmu1.compactAttractor).MutuallySingular
      (brownianImageLaw W P hmu2.compactAttractor) := by
  letI := hmu1.isProbabilityMeasure
  letI := hmu2.isProbabilityMeasure
  exact brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction hW
    (hmu1.tubeReconstructsOccupation_of_generation_tubeMassRatio S1 hdim1 hW hratio1)
    (hmu2.tubeReconstructsOccupation_of_generation_tubeMassRatio S2 hdim2 hW hratio2)
    hoccupation

/-- The homogeneous-versus-paired application in its final analytic interface.
All occupation-law separation and all set-level descent are discharged; only the
two systems' generation-cylinder tube-mass ratio limits remain as hypotheses. -/
theorem homogeneous_brownianImage_application_pair_of_generation_tubeMassRatio
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 -> Omega -> Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {KA : Set ℝ} {muA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural
      KA (homogeneousDim lam) muA)
    {KB : Set ℝ} {muB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural
          KB (homogeneousDim lam) muB)
    (hnl : Irrational
      (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2))
    (hratioA : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord (Fin 2) k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hA.attractor.brownianGenerationCylinder
            (homogeneousSystem lam hlam0 hlam) W omega k) w)
        atTop
        (nhds ((homogeneousSystem lam hlam0 hlam).generationWeight
          (homogeneousDim lam) k w)))
    (hratioB : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord (Fin 2) k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hB.attractor.brownianGenerationCylinder
            (pairSystem (pairRatio (homogeneousDim lam))
              (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
              (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
                (homogeneousDim_lt_one hlam0 hlam))) W omega k) w)
        atTop
        (nhds ((pairSystem (pairRatio (homogeneousDim lam))
          (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
          (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
            (homogeneousDim_lt_one hlam0 hlam))).generationWeight
              (homogeneousDim lam) k w))) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hB.compactAttractor) := by
  exact brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio hW
    (homogeneousSystem lam hlam0 hlam)
    (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam)))
    hA (homogeneousSystem_isDimension hlam0 hlam)
    hB (pairSystem_isDimension (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam))
    hratioA hratioB
    (BrownianImages.homogeneous_application_pair hW hlam0 hlam hA hB hnl)

end MinkowskiReconstruction

end

end BrownianImages
