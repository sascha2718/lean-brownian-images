/-
The coding of the family `x ↦ x/2`, `x ↦ bx + 1 - b` with general weights, used in the
proof of `thm:two-contraction-distinction` to vary the contraction `b` and the weight `v`
of the second map separately, as the tex does with Bernoulli codings.

The coded point of a word `ω : ℕ → Fin 2` is the library's coding map of `pairSystem b`;
the law of the word is the Bernoulli product with right-letter probability `v`.  All
comparisons are made word by word, through the orbits `codeSeq` of the origin and the
recursion `code_cons`, and passed to the limit.

* `twoCode b`, `twoDigit v`, `twoBern v`: the coded point, the letter law
  `(1-v)δ₀ + vδ₁` and the Bernoulli measure on words.
* `infinitePi_eq_sum_map_cons`, `integral_infinitePi_cons`: a product measure on words
  splits off its first letter.
* `twoCode_mono`: the coded point is monotone in the word.
* `twoCode_sub_le`: changing the letters of a word moves its coded point by at most
  `∑ (1-b) 2^{-n}` over the changed positions, up to a tail `2^{-N}`.
* `twoCode_param`: `0 ≤ π_b - π_{b'} ≤ b' - b` for `b ≤ b'`.
* `integral_twoCode`: `𝔼 π_b = v(1-b)/((1+v)/2 - vb)`.
* `map_twoCode_twoBern`: at the natural weights the law of the coded point is the
  natural measure.
-/
import BrownianImages.TwoContraction.Formula

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

/-- The coding map of the IFS `x ↦ x/2`, `x ↦ bx + 1 - b` on words `ℕ → Fin 2`, for
`0 < b < 1/2`, and `0` for other `b`. -/
def twoCode (b : ℝ) (ω : ℕ → Fin 2) : ℝ :=
  if h : 0 < b ∧ b < 1/2 then code (pairSystem b h.1 h.2) ω else 0

theorem twoCode_eq {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (ω : ℕ → Fin 2) :
    twoCode b ω = code (pairSystem b hb0 hb) ω := dite_eq_left ⟨hb0, hb⟩

/-- The coding map is measurable. -/
theorem measurable_twoCode (b : ℝ) : Measurable (twoCode b) := by
  unfold twoCode
  split_ifs with h
  · exact measurable_code _
  · exact measurable_const

/-- The coded point lies in the unit interval. -/
theorem twoCode_mem_Icc {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (ω : ℕ → Fin 2) :
    twoCode b ω ∈ Icc (0:ℝ) 1 := by
  rw [twoCode_eq hb0 hb]; exact code_mem_Icc _ ω

/-- The coded point of `0ω` is half that of `ω`. -/
theorem twoCode_cons_zero {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (ω : ℕ → Fin 2) :
    twoCode b (cons 0 ω) = 1/2 * twoCode b ω := by
  rw [twoCode_eq hb0 hb, twoCode_eq hb0 hb, code_cons, pairSystem_map_zero]

/-- The coded point of `1ω` is `b π(ω) + 1 - b`. -/
theorem twoCode_cons_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (ω : ℕ → Fin 2) :
    twoCode b (cons 1 ω) = b * twoCode b ω + (1 - b) := by
  rw [twoCode_eq hb0 hb, twoCode_eq hb0 hb, code_cons, pairSystem_map_one]

/-- Every letter of `Fin 2` is `0` or `1`. -/
theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- The orbit of the origin peels off the first letter. -/
theorem codeSeq_succ {ι : Type*} [Fintype ι] (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    codeSeq S ω (n + 1) = S.map (ω 0) (codeSeq S (tail ω) n) := by
  rw [codeSeq, wordMap_peel]; rfl

/-- The orbit starts at the origin. -/
theorem codeSeq_zero {ι : Type*} [Fintype ι] (S : System ι) (ω : ℕ → ι) :
    codeSeq S ω 0 = 0 := rfl

/-! ### Monotonicity in the word -/

/-- The orbit is monotone in the word, letter by letter. -/
theorem codeSeq_mono {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) :
    ∀ (n : ℕ) (ω ω' : ℕ → Fin 2), (∀ k, ω k ≤ ω' k) →
      codeSeq (pairSystem b hb0 hb) ω n ≤ codeSeq (pairSystem b hb0 hb) ω' n := by
  intro n
  induction n with
  | zero => intro ω ω' _; simp [codeSeq_zero]
  | succ n ih =>
    intro ω ω' hle
    rw [codeSeq_succ, codeSeq_succ]
    have hih := ih (tail ω) (tail ω') (fun k => hle (k + 1))
    have hx := codeSeq_mem_Icc (pairSystem b hb0 hb) (tail ω) n
    have hx' := codeSeq_mem_Icc (pairSystem b hb0 hb) (tail ω') n
    have h0 := hle 0
    rcases fin_two_cases (ω 0) with h | h <;> rcases fin_two_cases (ω' 0) with h' | h' <;>
      rw [h] at h0 ⊢ <;> rw [h'] at h0 ⊢ <;>
      simp only [pairSystem_map_zero, pairSystem_map_one]
    · linarith
    · nlinarith [hx.1, hx.2, hx'.1, hx'.2]
    · exact absurd h0 (by decide)
    · nlinarith

/-- **The coded point is monotone in the word**: a word whose letters are all at least
those of another codes a point at least as large. -/
theorem twoCode_mono {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) {ω ω' : ℕ → Fin 2}
    (hle : ∀ k, ω k ≤ ω' k) : twoCode b ω ≤ twoCode b ω' := by
  rw [twoCode_eq hb0 hb, twoCode_eq hb0 hb]
  exact le_of_tendsto_of_tendsto' (tendsto_codeSeq _ ω) (tendsto_codeSeq _ ω')
    fun n => codeSeq_mono hb0 hb n ω ω' hle

/-- The indicator `1{ω_k ≠ ω'_k}` of a changed letter. -/
def letterDiff (ω ω' : ℕ → Fin 2) (k : ℕ) : ℝ := if ω k = ω' k then 0 else 1

/-- **Changing letters moves the coded point by a controlled amount**: the letter at
depth `k` contributes at most `(1-b) 2^{-k}`, and the letters beyond depth `N` at most
`2^{-N}` together. -/
theorem twoCode_sub_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) :
    ∀ (N : ℕ) (ω ω' : ℕ → Fin 2), twoCode b ω' - twoCode b ω
      ≤ ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k * letterDiff ω ω' k + (1/2) ^ N := by
  intro N
  induction N with
  | zero =>
    intro ω ω'
    have h1 := twoCode_mem_Icc hb0 hb ω
    have h2 := twoCode_mem_Icc hb0 hb ω'
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, zero_add]
    linarith [h1.1, h2.2]
  | succ N ih =>
    intro ω ω'
    have hih := ih (tail ω) (tail ω')
    have hB : 0 ≤ ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k * letterDiff (tail ω) (tail ω') k
        + (1/2) ^ N := by
      refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) (by positivity)
      refine mul_nonneg (mul_nonneg (by linarith) (by positivity)) ?_
      unfold letterDiff; split_ifs <;> norm_num
    set B := ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k * letterDiff (tail ω) (tail ω') k
        + (1/2) ^ N with hBdef
    have hrhs : ∑ k ∈ Finset.range (N + 1), (1 - b) * (1/2) ^ k * letterDiff ω ω' k
        + (1/2) ^ (N + 1) = (1 - b) * letterDiff ω ω' 0 + 1/2 * B := by
      rw [Finset.sum_range_succ', hBdef]
      simp only [pow_zero, mul_one, letterDiff, tail, pow_succ]
      rw [mul_add, Finset.mul_sum]
      have : ∀ k ∈ Finset.range N, (1 - b) * ((1/2) ^ k * (1/2)) *
          (if ω (k + 1) = ω' (k + 1) then (0:ℝ) else 1)
          = 1/2 * ((1 - b) * (1/2) ^ k * (if ω (k + 1) = ω' (k + 1) then (0:ℝ) else 1)) :=
        fun k _ => by ring
      rw [Finset.sum_congr rfl this]
      ring
    rw [hrhs]
    have hy := twoCode_mem_Icc hb0 hb (tail ω)
    have hy' := twoCode_mem_Icc hb0 hb (tail ω')
    rw [← cons_head_tail ω, ← cons_head_tail ω']
    simp only [letterDiff, cons]
    rcases fin_two_cases (ω 0) with h | h <;> rcases fin_two_cases (ω' 0) with h' | h' <;>
      rw [h, h'] <;>
      simp only [twoCode_cons_zero hb0 hb, twoCode_cons_one hb0 hb, ite_true,
        show ((0 : Fin 2) = 1) = False from by decide,
        show ((1 : Fin 2) = 0) = False from by decide, ite_false]
    · linarith
    · nlinarith [hy.1, hy.2, hy'.1, hy'.2]
    · nlinarith [hy.1, hy.2, hy'.1, hy'.2]
    · nlinarith

/-! ### Varying the contraction -/

/-- The orbit comparison behind `twoCode_param`: for `b ≤ b'` the orbits satisfy
`0 ≤ x_b - x_{b'} ≤ b' - b` and `b'(x_b - x_{b'}) ≤ (b' - b) x_b` at every depth.  The
third bound is what carries the second through the map `x ↦ bx + 1 - b`. -/
theorem codeSeq_param {b b' : ℝ} (hb0 : 0 < b) (hbb : b ≤ b') (hb' : b' < 1/2) :
    ∀ (n : ℕ) (ω : ℕ → Fin 2),
      0 ≤ codeSeq (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) ω n
          - codeSeq (pairSystem b' (lt_of_lt_of_le hb0 hbb) hb') ω n ∧
      codeSeq (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) ω n
          - codeSeq (pairSystem b' (lt_of_lt_of_le hb0 hbb) hb') ω n ≤ b' - b ∧
      b' * (codeSeq (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) ω n
          - codeSeq (pairSystem b' (lt_of_lt_of_le hb0 hbb) hb') ω n)
        ≤ (b' - b) * codeSeq (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) ω n := by
  intro n
  induction n with
  | zero => intro ω; simp [codeSeq_zero]; linarith
  | succ n ih =>
    intro ω
    obtain ⟨h1, h2, h3⟩ := ih (tail ω)
    rw [codeSeq_succ, codeSeq_succ]
    set x := codeSeq (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) (tail ω) n
    set x' := codeSeq (pairSystem b' (lt_of_lt_of_le hb0 hbb) hb') (tail ω) n
    have hx := codeSeq_mem_Icc (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) (tail ω) n
    have hx' := codeSeq_mem_Icc (pairSystem b' (lt_of_lt_of_le hb0 hbb) hb') (tail ω) n
    rcases fin_two_cases (ω 0) with h | h <;> rw [h] <;>
      simp only [pairSystem_map_zero, pairSystem_map_one]
    · refine ⟨by linarith, by linarith, by nlinarith⟩
    · have hΔ : 0 ≤ b * x + (1 - b) - (b' * x' + (1 - b')) := by nlinarith [hx'.2]
      have hΔ2 : b * x + (1 - b) - (b' * x' + (1 - b')) ≤ b' - b := by nlinarith
      refine ⟨hΔ, hΔ2, ?_⟩
      have hbx : b' ≤ b * x + (1 - b) := by nlinarith [hx.1]
      calc b' * (b * x + (1 - b) - (b' * x' + (1 - b'))) ≤ b' * (b' - b) :=
            mul_le_mul_of_nonneg_left hΔ2 (by linarith)
        _ = (b' - b) * b' := by ring
        _ ≤ (b' - b) * (b * x + (1 - b)) :=
            mul_le_mul_of_nonneg_left hbx (by linarith)

/-- **Varying the contraction**: for `b ≤ b'`, `0 ≤ π_b - π_{b'} ≤ b' - b` word by word.
This is the finite-difference form of the coding derivative bound `-1 ≤ ∂_b x_b ≤ 0` of
the proof of `thm:two-contraction-distinction`. -/
theorem twoCode_param {b b' : ℝ} (hb0 : 0 < b) (hbb : b ≤ b') (hb' : b' < 1/2)
    (ω : ℕ → Fin 2) :
    0 ≤ twoCode b ω - twoCode b' ω ∧ twoCode b ω - twoCode b' ω ≤ b' - b := by
  rw [twoCode_eq hb0 (lt_of_le_of_lt hbb hb'), twoCode_eq (lt_of_lt_of_le hb0 hbb) hb']
  have hlim := (tendsto_codeSeq (pairSystem b hb0 (lt_of_le_of_lt hbb hb')) ω).sub
    (tendsto_codeSeq (pairSystem b' (lt_of_lt_of_le hb0 hbb) hb') ω)
  exact ⟨ge_of_tendsto' hlim fun n => (codeSeq_param hb0 hbb hb' n ω).1,
    le_of_tendsto' hlim fun n => (codeSeq_param hb0 hbb hb' n ω).2.1⟩

/-! ### The law of the coded point -/

/-- **The mean of the coded point**: `𝔼 π_b = v(1-b)/((1+v)/2 - vb)` under the Bernoulli
measure with right-letter probability `v`, from `𝔼 π = (1-v) 𝔼π/2 + v(b 𝔼π + 1 - b)`. -/
theorem integral_twoCode {b v : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) :
    ∫ ω, twoCode b ω ∂twoBern v = v * (1 - b) / ((1 + v) / 2 - v * b) := by
  have := isProbabilityMeasure_twoDigit hv0 hv1
  have hsplit := integral_infinitePi_cons (twoDigit v) (measurable_twoCode b) (C := 1)
    (fun ω => by
      have := twoCode_mem_Icc hb0 hb ω
      rw [abs_of_nonneg this.1]; exact this.2)
  rw [show (Measure.infinitePi fun _ : ℕ => twoDigit v) = twoBern v from rfl] at hsplit
  rw [Fin.sum_univ_two, twoDigit_zero, twoDigit_one, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal hv0] at hsplit
  simp only [twoCode_cons_zero hb0 hb, twoCode_cons_one hb0 hb] at hsplit
  have := isProbabilityMeasure_twoBern hv0 hv1
  have hint : Integrable (twoCode b) (twoBern v) := Integrable.of_bound
    (measurable_twoCode b).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      have := twoCode_mem_Icc hb0 hb ω
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  rw [integral_const_mul, integral_add (hint.const_mul b) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hsplit
  have hden : 0 < (1 + v) / 2 - v * b := by nlinarith
  rw [eq_div_iff hden.ne']
  linarith

/-- At the natural weights the Bernoulli measure is the library's code-space measure. -/
theorem twoBern_eq_codeLaw {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hdim : (pairSystem c hc0 hc).IsDimension s) :
    twoBern (c ^ s) = codeLaw (pairSystem c hc0 hc) s := by
  have hsum : (1/2 : ℝ) ^ s + c ^ s = 1 := by
    simpa [System.IsDimension, Fin.sum_univ_two] using hdim
  unfold twoBern codeLaw
  congr 1
  funext _
  simp only [twoDigit, digitLaw, Fin.sum_univ_two, pairSystem_ratio_zero, pairSystem_ratio_one]
  rw [show 1 - c ^ s = (1/2 : ℝ) ^ s by linarith]

/-- **At the natural weights the law of the coded point is the natural measure**, by
Hutchinson uniqueness. -/
theorem map_twoCode_twoBern {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hdim : (pairSystem c hc0 hc).IsDimension s) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (pairSystem c hc0 hc).IsNatural K s μ) :
    (twoBern (c ^ s)).map (twoCode c) = μ := by
  have hcode : twoCode c = code (pairSystem c hc0 hc) := funext (twoCode_eq hc0 hc)
  rw [twoBern_eq_codeLaw hc0 hc hdim, hcode]
  show naturalMeasure (pairSystem c hc0 hc) s = μ
  have hnat := isNatural_naturalMeasure (pairSystem c hc0 hc) hdim
  have := hnat.isProbabilityMeasure
  have := hμ.isProbabilityMeasure
  exact eq_of_selfSimilar _ hdim hnat.selfSimilar hμ.selfSimilar hnat.support_Icc
    hμ.support_Icc

end

end BrownianImages
