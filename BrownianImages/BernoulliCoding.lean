module

/-
Bernoulli measures on two-letter words, the coding measures of `sec:fixed-dimension-family`
and `sec:small-dimension`: the letter law `(1-v)δ₀ + vδ₁`, the product measure on words,
and the splitting off of the first letter that the self-similarity of a coded point
consumes, in `eq:initial-symbol-decomposition` and in the level sums `Λ_n^{(m)}` of
`thm:remainder-derivative`.

* `measurable_cons'`, `measure_eq_sum_indicator`: prefixing a letter is measurable, and a
  measure on a finite alphabet is the sum of its atoms.
* `infinitePi_eq_sum_map_cons`, `integral_infinitePi_cons`: a product measure on words
  splits off its first letter, as a measure and as an integral.
* `twoDigit v`, `twoBern v`: the letter law and the Bernoulli measure on words,
  probability measures for `0 ≤ v ≤ 1`.
* `fin_two_cases`: every letter of `Fin 2` is `0` or `1`.
* `integrable_of_abs_le`, `iterated_integral_mono`: a bounded measurable function is
  integrable, and iterated integrals of bounded integrands are monotone.
-/
public import BrownianImages.Hutchinson
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology ENNReal

noncomputable section

/-! ### Splitting off the first letter -/

section Split

variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

omit [Fintype α] [DiscreteMeasurableSpace α] in
/-- Prefixing a letter is measurable. -/
theorem measurable_cons' (i : α) : Measurable (cons i : (ℕ → α) → ℕ → α) := by
  refine Measurable.of_eval fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

/-- A measure on a finite discrete type is the sum of its atoms. -/
theorem measure_eq_sum_indicator (ρ : Measure α) (A : Set α) :
    ρ A = ∑ i, ρ {i} * A.indicator 1 i := by
  classical
  have hρ : ρ = ∑ i, ρ {i} • Measure.dirac i := by
    rw [Measure.ext_iff_singleton]
    intro a
    rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single a]
    · simp [Measure.dirac_apply' _ (measurableSet_singleton a)]
    · intro b _ hb
      simp [Measure.dirac_apply' _ (measurableSet_singleton a), Ne.symm hb]
    · simp
  conv_lhs => rw [hρ]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.of_discrete]

/-- **A product measure on words splits off its first letter.**  This is the
independence of the first letter from the rest, in the form the self-similarity of the
coded point consumes. -/
theorem infinitePi_eq_sum_map_cons (ρ : Measure α) [IsProbabilityMeasure ρ] :
    Measure.infinitePi (fun _ : ℕ => ρ)
      = ∑ i, ρ {i} • (Measure.infinitePi (fun _ : ℕ => ρ)).map (cons i) := by
  classical
  set Q : Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ => ρ) with hQ
  have hsum : ∑ i, ρ {i} = 1 := by simp
  have hQpi : ∀ (F : Finset ℕ) (t : ℕ → Set α), Q (Set.pi ↑F t) = ∏ n ∈ F, ρ (t n) :=
    fun F t => Measure.infinitePi_pi _ (fun n _ => MeasurableSet.of_discrete)
  set R : Measure (ℕ → α) := ∑ i, ρ {i} • Q.map (cons i) with hR
  have key : ∀ (n : ℕ) (u : ℕ → Set α),
      R (Set.pi ↑(Finset.range n) u) = ∏ k ∈ Finset.range n, ρ (u k) := by
    intro n u
    cases n with
    | zero =>
      have huniv : Set.pi (↑(Finset.range 0) : Set ℕ) u = Set.univ := by simp
      have h1 : ∀ i : α, (Q.map (cons i)) Set.univ = 1 := by
        intro i
        rw [Measure.map_apply (measurable_cons' i) MeasurableSet.univ, Set.preimage_univ,
          measure_univ]
      rw [huniv, Finset.range_zero, Finset.prod_empty, hR]
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
        h1, mul_one]
      exact hsum
    | succ n =>
      have hms : MeasurableSet (Set.pi ↑(Finset.range (n + 1)) u) :=
        MeasurableSet.pi (Finset.range (n + 1)).countable_toSet
          fun k _ => MeasurableSet.of_discrete
      have hpre : ∀ i : α, (cons i) ⁻¹' (Set.pi ↑(Finset.range (n + 1)) u)
          = if i ∈ u 0 then Set.pi ↑(Finset.range n) (fun k => u (k + 1)) else ∅ := by
        intro i
        by_cases hi : i ∈ u 0
        · rw [ite_eq_left_iff.2 (fun h => absurd hi h)]
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
          constructor
          · intro h k hk; exact h (k + 1) (by omega)
          · intro h k hk
            cases k with
            | zero => exact hi
            | succ m => exact h m (by omega)
        · rw [ite_eq_right_iff.2 (fun h => absurd h hi)]
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
            Set.mem_empty_iff_false, iff_false]
          intro h
          exact hi (h 0 (by omega))
      have hstep : ∀ i : α, (Q.map (cons i)) (Set.pi ↑(Finset.range (n + 1)) u)
          = (u 0).indicator 1 i * ∏ k ∈ Finset.range n, ρ (u (k + 1)) := by
        intro i
        rw [Measure.map_apply (measurable_cons' i) hms, hpre i]
        by_cases hi : i ∈ u 0
        · rw [ite_eq_left hi, Set.indicator_of_mem hi, Pi.one_apply, one_mul, hQpi]
        · rw [ite_eq_right hi, Set.indicator_of_notMem hi, measure_empty, zero_mul]
      simp only [hR, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
        hstep, ← mul_assoc]
      rw [← Finset.sum_mul, ← measure_eq_sum_indicator, Finset.prod_range_succ']
      ring
  symm
  refine Measure.eq_infinitePi _ ?_
  intro F t _
  obtain ⟨N, hN⟩ := F.exists_nat_subset_range
  set t' : ℕ → Set α := fun k => if k ∈ F then t k else Set.univ with ht'
  have hpi : Set.pi (↑F) t = Set.pi ↑(Finset.range N) t' := by
    ext x
    simp only [Set.mem_pi, Finset.mem_coe, Finset.mem_range, ht']
    constructor
    · intro h k _
      by_cases hk : k ∈ F
      · simpa [hk] using h k hk
      · simp [hk]
    · intro h k hk
      have := h k (Finset.mem_range.1 (hN hk))
      simpa [hk] using this
  have hprod : ∏ n ∈ Finset.range N, ρ (t' n) = ∏ n ∈ F, ρ (t n) := by
    refine (Finset.prod_subset hN ?_).symm.trans ?_
    · intro k _ hk
      simp [ht', hk]
    · exact Finset.prod_congr rfl fun k hk => by simp [ht', hk]
  rw [hpi, ← hprod]
  exact key N t'

/-- The integral form of `infinitePi_eq_sum_map_cons`, for a bounded measurable
function. -/
theorem integral_infinitePi_cons (ρ : Measure α) [IsProbabilityMeasure ρ]
    {f : (ℕ → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    ∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => ρ)
      = ∑ i, (ρ {i}).toReal * ∫ ω, f (cons i ω) ∂(Measure.infinitePi fun _ : ℕ => ρ) := by
  set Q : Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ => ρ) with hQ
  have hQint : Integrable f Q := Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have hsplit := infinitePi_eq_sum_map_cons ρ
  rw [← hQ] at hsplit
  have hparts : ∀ i ∈ (Finset.univ : Finset α), Integrable f (ρ {i} • Q.map (cons i)) := by
    have h := hQint
    rw [hsplit, integrable_finsetSum_measure] at h
    exact h
  conv_lhs => rw [hsplit]
  rw [integral_finsetSum_measure hparts]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_map (measurable_cons' i).aemeasurable
    hf.aestronglyMeasurable, smul_eq_mul]

end Split

/-! ### The coding map -/

/-- The letter law `(1-v)δ₀ + vδ₁` of the Bernoulli coding with right-letter
probability `v`. -/
def twoDigit (v : ℝ) : Measure (Fin 2) :=
  ENNReal.ofReal (1 - v) • Measure.dirac 0 + ENNReal.ofReal v • Measure.dirac 1

/-- The Bernoulli measure on words with right-letter probability `v`. -/
def twoBern (v : ℝ) : Measure (ℕ → Fin 2) := Measure.infinitePi fun _ : ℕ => twoDigit v

/-- The letter law has the two masses `1 - v` and `v`. -/
theorem twoDigit_zero (v : ℝ) : twoDigit v {0} = ENNReal.ofReal (1 - v) := by
  simp [twoDigit, Measure.dirac_apply' _ (measurableSet_singleton _)]

/-- The letter law has the two masses `1 - v` and `v`. -/
theorem twoDigit_one (v : ℝ) : twoDigit v {1} = ENNReal.ofReal v := by
  simp [twoDigit, Measure.dirac_apply' _ (measurableSet_singleton _)]

/-- For `0 ≤ v ≤ 1` the letter law is a probability measure. -/
theorem isProbabilityMeasure_twoDigit {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    IsProbabilityMeasure (twoDigit v) := by
  constructor
  rw [measure_eq_sum_indicator]
  simp only [Fin.sum_univ_two, twoDigit_zero, twoDigit_one, Set.indicator_univ, Pi.one_apply,
    mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hv0]
  simp

/-- For `0 ≤ v ≤ 1` the Bernoulli measure is a probability measure. -/
theorem isProbabilityMeasure_twoBern {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    IsProbabilityMeasure (twoBern v) := by
  have := isProbabilityMeasure_twoDigit hv0 hv1
  unfold twoBern
  infer_instance


/-- Every letter of `Fin 2` is `0` or `1`. -/
theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-! ### Elementary integration lemmas -/

section Integration

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_abs_le {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ a, |f a| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hC a)

/-- Monotonicity of an iterated integral of bounded jointly measurable integrands. -/
theorem iterated_integral_mono {P : Measure Ω} [IsProbabilityMeasure P] {F G : Ω → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G)) {C : ℝ}
    (hFb : ∀ a b, |F a b| ≤ C) (hGb : ∀ a b, |G a b| ≤ C) (hle : ∀ a b, F a b ≤ G a b) :
    ∫ b, ∫ a, F a b ∂P ∂P ≤ ∫ b, ∫ a, G a b ∂P ∂P := by
  have hFi : ∀ b, Integrable (fun a => F a b) P := fun b =>
    integrable_of_abs_le (hF.comp (measurable_id.prodMk measurable_const)) fun a => hFb a b
  have hGi : ∀ b, Integrable (fun a => G a b) P := fun b =>
    integrable_of_abs_le (hG.comp (measurable_id.prodMk measurable_const)) fun a => hGb a b
  have hFo : Integrable (fun b => ∫ a, F a b ∂P) P :=
    Integrable.of_bound (hF.stronglyMeasurable.integral_prod_left).aestronglyMeasurable C
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ a, |F a b| ∂P ≤ ∫ _a, C ∂P :=
              integral_mono (hFi b).abs (integrable_const _) fun a => hFb a b
          _ = C := by rw [integral_const, probReal_univ, one_smul])
  have hGo : Integrable (fun b => ∫ a, G a b ∂P) P :=
    Integrable.of_bound (hG.stronglyMeasurable.integral_prod_left).aestronglyMeasurable C
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ a, |G a b| ∂P ≤ ∫ _a, C ∂P :=
              integral_mono (hGi b).abs (integrable_const _) fun a => hGb a b
          _ = C := by rw [integral_const, probReal_univ, one_smul])
  exact integral_mono hFo hGo fun b => integral_mono (hFi b) (hGi b) fun a => hle a b

end Integration

end

end BrownianImages
