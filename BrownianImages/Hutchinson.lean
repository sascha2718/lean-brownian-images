/-
`sec:setup`: Hutchinson's theorem for a self-similar system on `[0,1]`.

Mathlib carries no iterated function systems, so the existence and uniqueness of the
attractor and of the natural measure are built here, through the code space `ℕ → ι`.
The coding map sends a word to the point cut out by the nested compositions
`S_{ω_0} ∘ ... ∘ S_{ω_{n-1}}`; the attractor is its range and the natural measure is the
push-forward of the Bernoulli measure with weights `p_i = r_i^s`.

* `wordMap`, `wordRatio`, `codeSeq`, `code`: the composition of the first `n` letters of
  a word, its contraction ratio, the orbit of the origin under it, and the coding map.
* `attractorSet`, `eq_attractorSet`: the attractor and the uniqueness of the invariant
  compact set.
* `digitLaw`, `codeLaw`, `codeLaw_eq_sum`, `naturalMeasure`: the Bernoulli measure on the
  code space, its splitting off the first letter, and the measure it carries to the line.
* `testOp`, `eq_of_selfSimilar`: the adjoint operator on bounded continuous test
  functions and the uniqueness of the self-similar probability measure on `[0,1]`.
* `System.exists_unique_isNatural`: the pair `(K, μ)` of `System.IsNatural` exists and is
  unique, which is Hutchinson's theorem in the shape `audit_exists_cantor_measure` asks
  for.
* `exists_unique_isNatural_cantorSystem`, `exists_unique_isNatural_pairSystem`: the two
  systems of `sec:setup`.
-/
import BrownianImages.SelfSimilar
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace BrownianImages

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Hutchinson

variable {ι : Type*} [Fintype ι]

/-! ### The compositions along a word -/

/-- The composition `S_{ω_0} ∘ ... ∘ S_{ω_{n-1}}` of the first `n` letters of `ω`. -/
noncomputable def wordMap (S : System ι) (ω : ℕ → ι) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => wordMap S ω n ∘ S.map (ω n)

/-- The empty word acts as the identity. -/
theorem wordMap_zero (S : System ι) (ω : ℕ → ι) : wordMap S ω 0 = id := rfl

/-- One more letter is appended on the inside. -/
theorem wordMap_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    wordMap S ω (n + 1) = wordMap S ω n ∘ S.map (ω n) := rfl

/-- The contraction ratio `r_{ω_0} ⋯ r_{ω_{n-1}}` of `wordMap S ω n`. -/
noncomputable def wordRatio (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, S.ratio (ω k)

/-- The ratio of a composition is positive. -/
theorem wordRatio_pos (S : System ι) (ω : ℕ → ι) (n : ℕ) : 0 < wordRatio S ω n :=
  Finset.prod_pos fun k _ => S.ratio_pos (ω k)

/-- `wordMap S ω n` is the similarity of ratio `wordRatio S ω n`. -/
theorem wordMap_sub (S : System ι) (ω : ℕ → ι) (n : ℕ) (x y : ℝ) :
    wordMap S ω n x - wordMap S ω n y = wordRatio S ω n * (x - y) := by
  induction n generalizing x y with
  | zero => simp [wordMap_zero, wordRatio]
  | succ n ih =>
    rw [wordMap_succ, Function.comp_apply, Function.comp_apply, ih]
    simp only [wordRatio, Finset.prod_range_succ, System.map]
    ring

/-- Every composition maps the unit interval into itself. -/
theorem wordMap_mapsTo (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    Set.MapsTo (wordMap S ω n) (Set.Icc 0 1) (Set.Icc 0 1) := by
  induction n with
  | zero => simpa [wordMap_zero] using Set.mapsTo_id _
  | succ n ih => exact ih.comp (S.mapsTo (ω n))

/-- Each similarity of the system is continuous. -/
theorem continuous_systemMap (S : System ι) (i : ι) : Continuous (S.map i) := by
  unfold System.map; fun_prop

/-! ### The shift on the code space -/

/-- The shift `ω ↦ (ω_1, ω_2, …)` on the code space. -/
def tail (ω : ℕ → ι) : ℕ → ι := fun n => ω (n + 1)

/-- Prefixing a word with one letter. -/
def cons (i : ι) (ω : ℕ → ι) : ℕ → ι
  | 0 => i
  | n + 1 => ω n

omit [Fintype ι] in
/-- The shift undoes the prefixing. -/
theorem tail_cons (i : ι) (ω : ℕ → ι) : tail (cons i ω) = ω := rfl

omit [Fintype ι] in
/-- A word is its first letter prefixed to its tail. -/
theorem cons_head_tail (ω : ℕ → ι) : cons (ω 0) (tail ω) = ω := by
  funext n; cases n <;> rfl

/-- The composition along `ω` peels from the left: the first letter comes out. -/
theorem wordMap_peel (S : System ι) (ω : ℕ → ι) (n : ℕ) (x : ℝ) :
    wordMap S ω (n + 1) x = S.map (ω 0) (wordMap S (tail ω) n x) := by
  induction n generalizing x with
  | zero => simp [wordMap_succ, wordMap_zero]
  | succ n ih => rw [wordMap_succ, Function.comp_apply, ih]; rfl

/-- The orbit `S_{ω_0} ∘ ... ∘ S_{ω_{n-1}} (0)` of the origin along the word. -/
noncomputable def codeSeq (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ := wordMap S ω n 0

/-- The orbit of the origin stays in the unit interval. -/
theorem codeSeq_mem_Icc (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    codeSeq S ω n ∈ Set.Icc (0:ℝ) 1 :=
  wordMap_mapsTo S ω n ⟨le_rfl, zero_le_one⟩

/-- Prefixing a letter applies the corresponding similarity to the orbit. -/
theorem codeSeq_cons (S : System ι) (i : ι) (ω : ℕ → ι) (n : ℕ) :
    codeSeq S (cons i ω) (n + 1) = S.map i (codeSeq S ω n) := by
  rw [codeSeq, wordMap_peel]; rfl

/-- The largest contraction ratio of the system, which is `< 1`. -/
noncomputable def maxRatio [Nonempty ι] (S : System ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty S.ratio

/-! ### The coding map -/

variable [Nonempty ι]

/-- Every ratio is at most the maximal one. -/
theorem ratio_le_maxRatio (S : System ι) (i : ι) : S.ratio i ≤ maxRatio S :=
  Finset.le_sup' _ (Finset.mem_univ i)

/-- The maximal ratio is positive. -/
theorem maxRatio_pos (S : System ι) : 0 < maxRatio S := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact lt_of_lt_of_le (S.ratio_pos i) (ratio_le_maxRatio S i)

/-- The maximal ratio is a contraction factor. -/
theorem maxRatio_lt_one (S : System ι) : maxRatio S < 1 :=
  (Finset.sup'_lt_iff _).2 fun i _ => S.ratio_lt_one i

/-- A word of length `n` contracts by at least `maxRatio ^ n`. -/
theorem wordRatio_le_pow (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    wordRatio S ω n ≤ maxRatio S ^ n := by
  have : wordRatio S ω n ≤ ∏ _k ∈ Finset.range n, maxRatio S :=
    Finset.prod_le_prod (fun k _ => (S.ratio_pos (ω k)).le)
      (fun k _ => ratio_le_maxRatio S (ω k))
  simpa using this

/-- Consecutive orbit points are `maxRatio ^ n` apart. -/
theorem dist_codeSeq_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    dist (codeSeq S ω n) (codeSeq S ω (n + 1)) ≤ 1 * maxRatio S ^ n := by
  have hmem : S.map (ω n) 0 ∈ Set.Icc (0:ℝ) 1 := S.mapsTo (ω n) ⟨le_rfl, zero_le_one⟩
  have h1 : |S.map (ω n) 0| ≤ 1 := abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩
  have hcode : codeSeq S ω (n + 1) = wordMap S ω n (S.map (ω n) 0) := rfl
  rw [Real.dist_eq, codeSeq, hcode, wordMap_sub]
  rw [abs_mul, abs_of_pos (wordRatio_pos S ω n), zero_sub, abs_neg]
  calc wordRatio S ω n * |S.map (ω n) 0|
      ≤ maxRatio S ^ n * 1 :=
        mul_le_mul (wordRatio_le_pow S ω n) h1 (abs_nonneg _)
          (pow_nonneg (maxRatio_pos S).le n)
    _ = 1 * maxRatio S ^ n := by ring

/-- The orbit of the origin is a Cauchy sequence. -/
theorem cauchySeq_codeSeq (S : System ι) (ω : ℕ → ι) : CauchySeq (codeSeq S ω) :=
  cauchySeq_of_le_geometric (maxRatio S) 1 (maxRatio_lt_one S) (dist_codeSeq_succ S ω)

/-- The coding map: the point of the attractor cut out by the word `ω`. -/
noncomputable def code (S : System ι) (ω : ℕ → ι) : ℝ := limUnder atTop (codeSeq S ω)

/-- The orbit of the origin converges to the coded point. -/
theorem tendsto_codeSeq (S : System ι) (ω : ℕ → ι) :
    Tendsto (codeSeq S ω) atTop (𝓝 (code S ω)) :=
  (cauchySeq_codeSeq S ω).tendsto_limUnder

/-- The orbit approaches the coded point at a geometric rate, uniformly in the word. -/
theorem dist_codeSeq_code (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    dist (codeSeq S ω n) (code S ω) ≤ 1 * maxRatio S ^ n / (1 - maxRatio S) :=
  dist_le_of_le_geometric_of_tendsto (maxRatio S) 1 (maxRatio_lt_one S)
    (dist_codeSeq_succ S ω) (tendsto_codeSeq S ω) n

/-- The coded point lies in the unit interval. -/
theorem code_mem_Icc (S : System ι) (ω : ℕ → ι) : code S ω ∈ Set.Icc (0:ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (tendsto_codeSeq S ω)
    (Eventually.of_forall (codeSeq_mem_Icc S ω))

/-- The contraction factors vanish. -/
theorem tendsto_pow_maxRatio (S : System ι) :
    Tendsto (fun n : ℕ => maxRatio S ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (maxRatio_pos S).le (maxRatio_lt_one S)

/-- Every point of `[0,1]` is dragged to the same limit by the compositions. -/
theorem tendsto_wordMap (S : System ι) (ω : ℕ → ι) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun n => wordMap S ω n z) atTop (𝓝 (code S ω)) := by
  have hz1 : |z| ≤ 1 := abs_le.2 ⟨by linarith [hz.1], hz.2⟩
  have hbound : ∀ n, ‖wordMap S ω n z - codeSeq S ω n‖ ≤ maxRatio S ^ n := by
    intro n
    rw [Real.norm_eq_abs, codeSeq, wordMap_sub, abs_mul,
      abs_of_pos (wordRatio_pos S ω n), sub_zero]
    calc wordRatio S ω n * |z|
        ≤ maxRatio S ^ n * 1 :=
          mul_le_mul (wordRatio_le_pow S ω n) hz1 (abs_nonneg _)
            (pow_nonneg (maxRatio_pos S).le n)
      _ = maxRatio S ^ n := by ring
  have hdiff : Tendsto (fun n => wordMap S ω n z - codeSeq S ω n) atTop (𝓝 0) :=
    squeeze_zero_norm hbound (tendsto_pow_maxRatio S)
  simpa using hdiff.add (tendsto_codeSeq S ω)

/-- `sec:setup`: the coding map intertwines the shift with `S_i`, which is what makes
its range the attractor. -/
theorem code_cons (S : System ι) (i : ι) (ω : ℕ → ι) :
    code S (cons i ω) = S.map i (code S ω) := by
  have h1 : Tendsto (fun n => codeSeq S (cons i ω) (n + 1)) atTop (𝓝 (code S (cons i ω))) :=
    (tendsto_codeSeq S (cons i ω)).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => S.map i (codeSeq S ω n)) atTop (𝓝 (S.map i (code S ω))) :=
    ((continuous_systemMap S i).tendsto _).comp (tendsto_codeSeq S ω)
  refine tendsto_nhds_unique ?_ h2
  simpa only [codeSeq_cons] using h1

/-! ### The attractor -/

/-- The attractor of the system: the range of the coding map. -/
def attractorSet (S : System ι) : Set ℝ := Set.range (code S)

/-- The attractor sits inside `[0,1]`, as `System.IsAttractor` demands. -/
theorem attractorSet_subset_Icc (S : System ι) : attractorSet S ⊆ Set.Icc 0 1 := by
  rintro _ ⟨ω, rfl⟩; exact code_mem_Icc S ω

/-- The attractor is non-empty. -/
theorem attractorSet_nonempty (S : System ι) : (attractorSet S).Nonempty :=
  Set.range_nonempty _

/-- The attractor is invariant: `K = ⋃ i S_i K`. -/
theorem attractorSet_eq_iUnion (S : System ι) :
    attractorSet S = ⋃ i, S.map i '' attractorSet S := by
  ext x
  constructor
  · rintro ⟨ω, rfl⟩
    refine Set.mem_iUnion.2 ⟨ω 0, code S (tail ω), ⟨tail ω, rfl⟩, ?_⟩
    rw [← code_cons, cons_head_tail]
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, ⟨ω, rfl⟩, rfl⟩ := hi
    exact ⟨cons i ω, code_cons S i ω⟩

/-- Every attractor of the system is the range of the coding map: this is the uniqueness
half of Hutchinson's theorem for the invariant compact set. -/
theorem eq_attractorSet (S : System ι) {K : Set ℝ} (hK : S.IsAttractor K) :
    K = attractorSet S := by
  classical
  obtain ⟨hcomp, hne, hsub, hself⟩ := hK
  have hmapsTo : ∀ i, Set.MapsTo (S.map i) K K := by
    intro i x hx
    rw [hself]
    exact Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩
  have hword : ∀ (ω : ℕ → ι) (n : ℕ), ∀ z ∈ K, wordMap S ω n z ∈ K := by
    intro ω n
    induction n with
    | zero => intro z hz; simpa [wordMap_zero] using hz
    | succ n ih => intro z hz; exact ih _ (hmapsTo (ω n) hz)
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have hnext : ∀ y : ℝ, ∃ q : ι × ℝ, y ∈ K → (q.2 ∈ K ∧ S.map q.1 q.2 = y) := by
      intro y
      by_cases hy : y ∈ K
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hself ▸ hy)
        obtain ⟨z, hz, hzy⟩ := hi
        exact ⟨(i, z), fun _ => ⟨hz, hzy⟩⟩
      · exact ⟨(Classical.arbitrary ι, 0), fun h => absurd h hy⟩
    choose F hF using hnext
    set orbit : ℕ → ℝ := fun n => Nat.rec x (fun _ y => (F y).2) n with horbit
    set ω : ℕ → ι := fun n => (F (orbit n)).1 with hω
    have horb0 : orbit 0 = x := rfl
    have hA : ∀ n, orbit n ∈ K := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih => exact (hF (orbit n) ih).1
    have hB : ∀ n, wordMap S ω n (orbit n) = x := by
      intro n
      induction n with
      | zero => exact horb0
      | succ n ih =>
        rw [wordMap_succ, Function.comp_apply]
        have hstep : S.map (ω n) (orbit (n + 1)) = orbit n := (hF (orbit n) (hA n)).2
        rw [hstep, ih]
    have hbd : ∀ n, ‖x - codeSeq S ω n‖ ≤ maxRatio S ^ n := by
      intro n
      have hz : orbit n ∈ Set.Icc (0:ℝ) 1 := hsub (hA n)
      have hz1 : |orbit n| ≤ 1 := abs_le.2 ⟨by linarith [hz.1], hz.2⟩
      have hxe : x - codeSeq S ω n = wordRatio S ω n * (orbit n - 0) := by
        rw [← hB n, codeSeq]; exact wordMap_sub S ω n (orbit n) 0
      rw [Real.norm_eq_abs, hxe, sub_zero, abs_mul, abs_of_pos (wordRatio_pos S ω n)]
      calc wordRatio S ω n * |orbit n|
          ≤ maxRatio S ^ n * 1 :=
            mul_le_mul (wordRatio_le_pow S ω n) hz1 (abs_nonneg _)
              (pow_nonneg (maxRatio_pos S).le n)
        _ = maxRatio S ^ n := by ring
    have hlim : Tendsto (fun n => codeSeq S ω n) atTop (𝓝 x) := by
      have h0 : Tendsto (fun n => x - codeSeq S ω n) atTop (𝓝 0) :=
        squeeze_zero_norm hbd (tendsto_pow_maxRatio S)
      have h1 : Tendsto (fun n => x - (x - codeSeq S ω n)) atTop (𝓝 (x - 0)) :=
        tendsto_const_nhds.sub h0
      simpa using h1
    exact ⟨ω, tendsto_nhds_unique (tendsto_codeSeq S ω) hlim⟩
  · rintro _ ⟨ω, rfl⟩
    obtain ⟨z, hz⟩ := hne
    exact hcomp.isClosed.mem_of_tendsto (tendsto_wordMap S ω (hsub hz))
      (Eventually.of_forall fun n => hword ω n z hz)

/-! ### Continuity of the coding map -/

section CodeSpaceTopology

variable [TopologicalSpace ι] [DiscreteTopology ι]

omit [Nonempty ι] in
/-- The compositions depend continuously on the word. -/
theorem continuous_wordMap (S : System ι) (n : ℕ) {g : (ℕ → ι) → ℝ} (hg : Continuous g) :
    Continuous (fun ω => wordMap S ω n (g ω)) := by
  induction n generalizing g with
  | zero => simpa [wordMap_zero] using hg
  | succ n ih =>
    have hstep : Continuous (fun ω : ℕ → ι => S.map (ω n) (g ω)) := by
      simp only [System.map]
      exact ((continuous_of_discreteTopology.comp (continuous_apply n)).mul hg).add
        (continuous_of_discreteTopology.comp (continuous_apply n))
    exact ih hstep

omit [Nonempty ι] in
/-- The orbit of the origin depends continuously on the word. -/
theorem continuous_codeSeq (S : System ι) (n : ℕ) :
    Continuous (fun ω : ℕ → ι => codeSeq S ω n) :=
  continuous_wordMap S n continuous_const

/-- The coding map is continuous, being a uniform limit of continuous maps. -/
theorem continuous_code (S : System ι) : Continuous (code S) := by
  have huc : TendstoUniformly (fun n (ω : ℕ → ι) => codeSeq S ω n) (code S) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hpow : Tendsto (fun n : ℕ => 1 * maxRatio S ^ n / (1 - maxRatio S)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_maxRatio S).div_const (1 - maxRatio S)
    filter_upwards [hpow.eventually (gt_mem_nhds hε)] with n hn ω
    calc dist (code S ω) (codeSeq S ω n) = dist (codeSeq S ω n) (code S ω) := dist_comm _ _
      _ ≤ 1 * maxRatio S ^ n / (1 - maxRatio S) := dist_codeSeq_code S ω n
      _ < ε := hn
  exact huc.continuous ((Eventually.of_forall (continuous_codeSeq S)).frequently)

/-- The attractor is compact: it is the continuous image of the compact code space. -/
theorem isCompact_attractorSet (S : System ι) : IsCompact (attractorSet S) :=
  isCompact_range (continuous_code S)

end CodeSpaceTopology

/-! ### The Bernoulli measure on the code space -/

section CodeSpaceMeasure

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

/-- The one-letter law `∑ p_i δ_i` with weights `p_i = r_i^s`. -/
noncomputable def digitLaw (S : System ι) (s : ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac i

omit [Nonempty ι] in
/-- The one-letter law of a set is the sum of the weights it carries. -/
theorem digitLaw_apply (S : System ι) (s : ℝ) (A : Set ι) :
    digitLaw S s A = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * A.indicator 1 i := by
  simp only [digitLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.of_discrete]

omit [Nonempty ι] in
/-- The weights sum to one exactly at the similarity dimension. -/
theorem isProbabilityMeasure_digitLaw (S : System ι) {s : ℝ} (hdim : S.IsDimension s) :
    IsProbabilityMeasure (digitLaw S s) := by
  constructor
  rw [digitLaw_apply]
  simpa using S.sum_ofReal_ratio_rpow hdim

omit [Fintype ι] [Nonempty ι] [DiscreteMeasurableSpace ι] in
/-- Prefixing a letter is measurable. -/
theorem measurable_cons (i : ι) : Measurable (cons i : (ℕ → ι) → ℕ → ι) := by
  refine measurable_pi_lambda _ fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

/-- The Bernoulli measure on the code space with weights `p_i = r_i^s`. -/
noncomputable def codeLaw (S : System ι) (s : ℝ) : Measure (ℕ → ι) :=
  Measure.infinitePi (fun _ : ℕ => digitLaw S s)

omit [Nonempty ι] in
/-- The Bernoulli measure is a probability measure. -/
theorem isProbabilityMeasure_codeLaw (S : System ι) {s : ℝ} (hdim : S.IsDimension s) :
    IsProbabilityMeasure (codeLaw S s) := by
  haveI := isProbabilityMeasure_digitLaw S hdim
  exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))

omit [Nonempty ι] in
/-- The Bernoulli measure of a cylinder is the product of the weights. -/
theorem codeLaw_pi (S : System ι) {s : ℝ} (hdim : S.IsDimension s) (F : Finset ℕ)
    (t : ℕ → Set ι) :
    codeLaw S s (Set.pi ↑F t) = ∏ n ∈ F, digitLaw S s (t n) := by
  haveI := isProbabilityMeasure_digitLaw S hdim
  exact Measure.infinitePi_pi _ (fun n _ => MeasurableSet.of_discrete)

omit [Nonempty ι] in
/-- The Bernoulli measure splits off its first letter.  This is the independence of the
first coordinate from the rest, in the form the Hutchinson identity consumes. -/
theorem codeLaw_eq_sum (S : System ι) {s : ℝ} (hdim : S.IsDimension s) :
    codeLaw S s = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • (codeLaw S s).map (cons i) := by
  classical
  haveI := isProbabilityMeasure_digitLaw S hdim
  haveI := isProbabilityMeasure_codeLaw S hdim
  set ρ : Measure (ℕ → ι) := ∑ i, ENNReal.ofReal (S.ratio i ^ s) • (codeLaw S s).map (cons i)
    with hρ
  have key : ∀ (n : ℕ) (u : ℕ → Set ι),
      ρ (Set.pi ↑(Finset.range n) u) = ∏ k ∈ Finset.range n, digitLaw S s (u k) := by
    intro n u
    cases n with
    | zero =>
      have huniv : Set.pi (↑(Finset.range 0) : Set ℕ) u = Set.univ := by simp
      have h1 : ∀ i : ι, ((codeLaw S s).map (cons i)) Set.univ = 1 := by
        intro i
        rw [Measure.map_apply (measurable_cons i) MeasurableSet.univ, Set.preimage_univ,
          measure_univ]
      rw [huniv, Finset.range_zero, Finset.prod_empty, hρ]
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
        h1, mul_one]
      exact S.sum_ofReal_ratio_rpow hdim
    | succ n =>
      have hms : MeasurableSet (Set.pi ↑(Finset.range (n + 1)) u) :=
        MeasurableSet.pi (Finset.range (n + 1)).countable_toSet
          fun k _ => MeasurableSet.of_discrete
      have hpre : ∀ i : ι, (cons i) ⁻¹' (Set.pi ↑(Finset.range (n + 1)) u)
          = if i ∈ u 0 then Set.pi ↑(Finset.range n) (fun k => u (k + 1)) else ∅ := by
        intro i
        by_cases hi : i ∈ u 0
        · rw [if_pos hi]
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
          constructor
          · intro h k hk; exact h (k + 1) (by omega)
          · intro h k hk
            cases k with
            | zero => exact hi
            | succ m => exact h m (by omega)
        · rw [if_neg hi]
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
            Set.mem_empty_iff_false, iff_false]
          intro h
          exact hi (h 0 (by omega))
      have hstep : ∀ i : ι,
          ((codeLaw S s).map (cons i)) (Set.pi ↑(Finset.range (n + 1)) u)
            = (u 0).indicator 1 i * ∏ k ∈ Finset.range n, digitLaw S s (u (k + 1)) := by
        intro i
        rw [Measure.map_apply (measurable_cons i) hms, hpre i]
        by_cases hi : i ∈ u 0
        · rw [if_pos hi, Set.indicator_of_mem hi, Pi.one_apply, one_mul, codeLaw_pi S hdim]
        · rw [if_neg hi, Set.indicator_of_notMem hi, measure_empty, zero_mul]
      simp only [hρ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
        hstep, ← mul_assoc]
      rw [← Finset.sum_mul, ← digitLaw_apply, Finset.prod_range_succ']
      ring
  symm
  show ρ = Measure.infinitePi (fun _ : ℕ => digitLaw S s)
  refine Measure.eq_infinitePi _ ?_
  intro F t _
  obtain ⟨N, hN⟩ := F.exists_nat_subset_range
  set t' : ℕ → Set ι := fun k => if k ∈ F then t k else Set.univ with ht'
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
  have hprod : ∏ n ∈ Finset.range N, digitLaw S s (t' n) = ∏ n ∈ F, digitLaw S s (t n) := by
    refine (Finset.prod_subset hN ?_).symm.trans ?_
    · intro k _ hk
      simp [ht', hk]
    · exact Finset.prod_congr rfl fun k hk => by simp [ht', hk]
  rw [hpi, ← hprod]
  exact key N t'

/-! ### The natural measure -/

omit [Nonempty ι] in
/-- The compositions depend measurably on the word. -/
theorem measurable_wordMap (S : System ι) (n : ℕ) {g : (ℕ → ι) → ℝ} (hg : Measurable g) :
    Measurable (fun ω => wordMap S ω n (g ω)) := by
  induction n generalizing g with
  | zero => simpa [wordMap_zero] using hg
  | succ n ih =>
    have hstep : Measurable (fun ω : ℕ → ι => S.map (ω n) (g ω)) := by
      simp only [System.map]
      exact ((Measurable.of_discrete.comp (measurable_pi_apply n)).mul hg).add
        (Measurable.of_discrete.comp (measurable_pi_apply n))
    exact ih hstep

/-- The coding map is measurable, being a pointwise limit of measurable maps. -/
theorem measurable_code (S : System ι) : Measurable (code S) :=
  measurable_of_tendsto_metrizable' atTop
    (fun n => measurable_wordMap S n measurable_const)
    (tendsto_pi_nhds.2 fun ω => tendsto_codeSeq S ω)

/-- The natural measure of the system: the push-forward of the Bernoulli measure with
weights `p_i = r_i^s` under the coding map. -/
noncomputable def naturalMeasure (S : System ι) (s : ℝ) : Measure ℝ :=
  (codeLaw S s).map (code S)

/-- The natural measure is a probability measure. -/
theorem isProbabilityMeasure_naturalMeasure (S : System ι) {s : ℝ} (hdim : S.IsDimension s) :
    IsProbabilityMeasure (naturalMeasure S s) := by
  haveI := isProbabilityMeasure_codeLaw S hdim
  exact Measure.isProbabilityMeasure_map (measurable_code S).aemeasurable

/-- `sec:setup`: the push-forward of the Bernoulli measure satisfies Hutchinson's
identity `μ = ∑ r_i^s (S_i)_* μ`, the defining property of `System.IsNatural`. -/
theorem naturalMeasure_selfSimilar (S : System ι) {s : ℝ} (hdim : S.IsDimension s) :
    naturalMeasure S s
      = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • (naturalMeasure S s).map (S.map i) := by
  have hmc := measurable_code S
  have hmi : ∀ i, Measurable (S.map i) := fun i => (continuous_systemMap S i).measurable
  refine Measure.ext fun A hA => ?_
  have hsetEq : ∀ i : ι, (cons i) ⁻¹' (code S ⁻¹' A) = code S ⁻¹' (S.map i ⁻¹' A) := by
    intro i
    ext ω
    simp only [Set.mem_preimage, code_cons]
  calc naturalMeasure S s A = codeLaw S s (code S ⁻¹' A) := Measure.map_apply hmc hA
    _ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * codeLaw S s ((cons i) ⁻¹' (code S ⁻¹' A)) := by
        conv_lhs => rw [codeLaw_eq_sum S hdim]
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Measure.map_apply (measurable_cons i) (hmc hA)]
    _ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * naturalMeasure S s (S.map i ⁻¹' A) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hsetEq i, naturalMeasure, Measure.map_apply hmc (hmi i hA)]
    _ = (∑ i, ENNReal.ofReal (S.ratio i ^ s) • (naturalMeasure S s).map (S.map i)) A := by
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Measure.map_apply (hmi i) hA]

end CodeSpaceMeasure

/-! ### Hutchinson's theorem -/

section Natural

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  [TopologicalSpace ι] [DiscreteTopology ι]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
/-- The attractor is measurable, being compact. -/
theorem measurableSet_attractorSet (S : System ι) : MeasurableSet (attractorSet S) :=
  (isCompact_attractorSet S).isClosed.measurableSet

/-- The natural measure is carried by the attractor. -/
theorem naturalMeasure_compl_attractorSet (S : System ι) (s : ℝ) :
    naturalMeasure S s (attractorSet S)ᶜ = 0 := by
  rw [naturalMeasure, Measure.map_apply (measurable_code S)
    (measurableSet_attractorSet S).compl]
  convert measure_empty (μ := codeLaw S s)
  ext ω
  simp [attractorSet]

/-- The attractor and the push-forward of the Bernoulli measure form a natural pair. -/
theorem isNatural_naturalMeasure (S : System ι) {s : ℝ} (hdim : S.IsDimension s) :
    S.IsNatural (attractorSet S) s (naturalMeasure S s) where
  isProbability := isProbabilityMeasure_naturalMeasure S hdim
  attractor := ⟨isCompact_attractorSet S, attractorSet_nonempty S, attractorSet_subset_Icc S,
    attractorSet_eq_iUnion S⟩
  support := naturalMeasure_compl_attractorSet S s
  selfSimilar := naturalMeasure_selfSimilar S hdim

end Natural

/-! ### Uniqueness of the natural measure -/

/-- The Hutchinson operator on bounded continuous test functions,
`(T f)(x) = ∑ p_i f(S_i x)`. -/
noncomputable def testOp (S : System ι) (s : ℝ) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  ∑ i, (S.ratio i ^ s) • f.compContinuous ⟨S.map i, continuous_systemMap S i⟩

omit [Nonempty ι] in
/-- The value of the adjoint operator at a point. -/
theorem testOp_apply (S : System ι) (s : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    testOp S s f x = ∑ i, S.ratio i ^ s * f (S.map i x) := by
  simp [testOp]

omit [Nonempty ι] in
/-- Hutchinson's identity read against a test function: the measure is invariant under the
adjoint operator `T`. -/
theorem integral_testOp (S : System ι) {s : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i)) (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂μ = ∫ x, testOp S s f x ∂μ := by
  have hmi : ∀ i, Measurable (S.map i) := fun i => (continuous_systemMap S i).measurable
  have hpos : ∀ i : ι, (0:ℝ) < S.ratio i ^ s := fun i => Real.rpow_pos_of_pos (S.ratio_pos i) s
  have hpm : ∀ i, IsProbabilityMeasure (μ.map (S.map i)) := fun i =>
    Measure.isProbabilityMeasure_map (hmi i).aemeasurable
  have hint : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun x => f x) (ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i)) := by
    intro i _
    haveI := hpm i
    refine (integrable_smul_measure ?_ ENNReal.ofReal_ne_top).2
      (BoundedContinuousFunction.integrable _ f)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos i
  have hgi : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun x => S.ratio i ^ s * f (S.map i x)) μ := fun i _ =>
    (BoundedContinuousFunction.integrable μ
      (f.compContinuous ⟨S.map i, continuous_systemMap S i⟩)).const_mul _
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure hint]
  have hterm : ∀ i : ι,
      ∫ x, f x ∂(ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i))
        = ∫ x, S.ratio i ^ s * f (S.map i x) ∂μ := by
    intro i
    haveI := hpm i
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hpos i).le, smul_eq_mul,
      integral_map (hmi i).aemeasurable f.continuous.aestronglyMeasurable, ← integral_const_mul]
  simp only [hterm]
  rw [← integral_finsetSum _ hgi]
  exact integral_congr_ae (Eventually.of_forall fun x => (testOp_apply S s f x).symm)

omit [Nonempty ι] in
/-- Hutchinson's identity iterated `n` times. -/
theorem integral_iterate_testOp (S : System ι) {s : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i)) (f : ℝ →ᵇ ℝ) (n : ℕ) :
    ∫ x, f x ∂μ = ∫ x, (testOp S s)^[n] f x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, Function.iterate_succ_apply', integral_testOp S hμ]

/-- The iterates of `T` have oscillation on `[0,1]` controlled by the modulus of
continuity of `f` at scale `maxRatio ^ n`. -/
theorem abs_sub_iterate_testOp_le (S : System ι) {s : ℝ} (hdim : S.IsDimension s)
    (f : ℝ →ᵇ ℝ) {ε δ : ℝ}
    (hf : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ b ∈ Set.Icc (0:ℝ) 1, |a - b| ≤ δ → |f a - f b| ≤ ε) :
    ∀ (n : ℕ), ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |x - y| * maxRatio S ^ n ≤ δ →
        |(testOp S s)^[n] f x - (testOp S s)^[n] f y| ≤ ε := by
  intro n
  induction n with
  | zero =>
    intro x hx y hy hxy
    simpa using hf x hx y hy (by simpa using hxy)
  | succ n ih =>
    intro x hx y hy hxy
    have hkey : ∀ i : ι,
        |(testOp S s)^[n] f (S.map i x) - (testOp S s)^[n] f (S.map i y)| ≤ ε := by
      intro i
      refine ih (S.map i x) (S.mapsTo i hx) (S.map i y) (S.mapsTo i hy) ?_
      have hd : |S.map i x - S.map i y| = S.ratio i * |x - y| := by
        simp only [System.map]
        rw [show S.ratio i * x + S.shift i - (S.ratio i * y + S.shift i)
              = S.ratio i * (x - y) by ring, abs_mul, abs_of_pos (S.ratio_pos i)]
      have hb : (0:ℝ) ≤ |x - y| := abs_nonneg _
      have hp : (0:ℝ) ≤ maxRatio S ^ n := pow_nonneg (maxRatio_pos S).le n
      have hr := ratio_le_maxRatio S i
      have h1 : S.ratio i * |x - y| * maxRatio S ^ n ≤ |x - y| * maxRatio S ^ (n + 1) := by
        calc S.ratio i * |x - y| * maxRatio S ^ n
            ≤ maxRatio S * |x - y| * maxRatio S ^ n :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hb) hp
          _ = |x - y| * maxRatio S ^ (n + 1) := by ring
      rw [hd]
      linarith
    rw [Function.iterate_succ_apply', testOp_apply, testOp_apply]
    have hsum : ∑ i, S.ratio i ^ s * (testOp S s)^[n] f (S.map i x)
          - ∑ i, S.ratio i ^ s * (testOp S s)^[n] f (S.map i y)
        = ∑ i, S.ratio i ^ s
            * ((testOp S s)^[n] f (S.map i x) - (testOp S s)^[n] f (S.map i y)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    calc |∑ i, S.ratio i ^ s
            * ((testOp S s)^[n] f (S.map i x) - (testOp S s)^[n] f (S.map i y))|
        ≤ ∑ i, |S.ratio i ^ s
            * ((testOp S s)^[n] f (S.map i x) - (testOp S s)^[n] f (S.map i y))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.ratio i ^ s * ε := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (S.ratio_pos i) s)]
          exact mul_le_mul_of_nonneg_left (hkey i) (Real.rpow_pos_of_pos (S.ratio_pos i) s).le
      _ = ε := by rw [← Finset.sum_mul, hdim, one_mul]

/-- Uniqueness in Hutchinson's theorem: a probability measure on `[0,1]` satisfying
`μ = ∑ r_i^s (S_i)_* μ` is determined by the system. -/
theorem eq_of_selfSimilar (S : System ι) {s : ℝ} (hdim : S.IsDimension s)
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i))
    (hν : ν = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • ν.map (S.map i))
    (hμs : μ (Set.Icc (0:ℝ) 1)ᶜ = 0) (hνs : ν (Set.Icc (0:ℝ) 1)ᶜ = 0) :
    μ = ν := by
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have habs : ∀ ε > 0, |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 2 * ε := by
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
      (isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn) ε hε
    have hf : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ b ∈ Set.Icc (0:ℝ) 1, |a - b| ≤ δ → |f a - f b| ≤ ε := by
      intro a ha b hb hab
      have := hδ a ha b hb (by rwa [Real.dist_eq])
      rwa [Real.dist_eq] at this
    obtain ⟨n, hn⟩ : ∃ n : ℕ, maxRatio S ^ n ≤ δ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ0 (maxRatio_lt_one S)
      exact ⟨n, hn.le⟩
    set g : ℝ →ᵇ ℝ := (testOp S s)^[n] f with hg
    have hgb : ∀ x ∈ Set.Icc (0:ℝ) 1, |g x - g 0| ≤ ε := by
      intro x hx
      refine abs_sub_iterate_testOp_le S hdim f hf n x hx 0 ⟨le_rfl, zero_le_one⟩ ?_
      have hx1 : |x - 0| ≤ 1 := by
        rw [sub_zero, abs_of_nonneg hx.1]; exact hx.2
      have hp : (0:ℝ) ≤ maxRatio S ^ n := pow_nonneg (maxRatio_pos S).le n
      nlinarith
    have key : ∀ (m : Measure ℝ) (_ : IsProbabilityMeasure m),
        m = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • m.map (S.map i) →
        m (Set.Icc (0:ℝ) 1)ᶜ = 0 → |∫ x, f x ∂m - g 0| ≤ ε := by
      intro m hm hmself hms
      haveI := hm
      have hae : ∀ᵐ x ∂m, ‖g x - g 0‖ ≤ ε := by
        have hIcc : ∀ᵐ x ∂m, x ∈ Set.Icc (0:ℝ) 1 := ae_iff.2 hms
        filter_upwards [hIcc] with x hx
        rw [Real.norm_eq_abs]
        exact hgb x hx
      have hgint : Integrable (fun x => g x) m := BoundedContinuousFunction.integrable m g
      have h3 : ∫ x, (g x - g 0) ∂m = (∫ x, g x ∂m) - g 0 := by
        rw [integral_sub hgint (integrable_const _)]
        simp
      rw [integral_iterate_testOp S hmself f n, ← hg]
      calc |(∫ x, g x ∂m) - g 0| = ‖∫ x, (g x - g 0) ∂m‖ := by rw [h3, Real.norm_eq_abs]
        _ ≤ ε * (m Set.univ).toReal := norm_integral_le_of_norm_le_const hae
        _ = ε := by rw [measure_univ]; simp
    have h1 := abs_le.1 (key μ ‹IsProbabilityMeasure μ› hμ hμs)
    have h2 := abs_le.1 (key ν ‹IsProbabilityMeasure ν› hν hνs)
    rw [abs_le]
    constructor <;> linarith
  have hle : |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := habs (ε / 2) (by linarith)
    linarith
  have := le_antisymm hle (abs_nonneg _)
  linarith [sub_eq_zero.1 (abs_eq_zero.1 this)]

end Hutchinson

/-! ### Hutchinson's theorem -/

/-- Hutchinson's theorem for a self-similar system on `[0,1]`: the attractor and the
natural `s`-dimensional measure exist and are unique, as a pair.  This is what
`audit_exists_cantor_measure` and `audit_exists_pair_measure` assert for the two systems
of `sec:setup`. -/
theorem System.exists_unique_isNatural {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {s : ℝ} (hdim : S.IsDimension s) :
    ∃! p : Set ℝ × Measure ℝ, S.IsNatural p.1 s p.2 := by
  classical
  letI : MeasurableSpace ι := ⊤
  haveI : DiscreteMeasurableSpace ι := ⟨fun _ => trivial⟩
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  have hnat := Hutchinson.isNatural_naturalMeasure S hdim
  refine ⟨(Hutchinson.attractorSet S, Hutchinson.naturalMeasure S s), hnat, ?_⟩
  rintro ⟨K, μ⟩ hKμ
  haveI := hKμ.isProbability
  haveI := hnat.isProbability
  refine Prod.ext ?_ ?_
  · exact Hutchinson.eq_attractorSet S hKμ.attractor
  · exact Hutchinson.eq_of_selfSimilar S hdim hKμ.selfSimilar
      (Hutchinson.naturalMeasure_selfSimilar S hdim) hKμ.support_Icc hnat.support_Icc

/-- `sec:setup`, existence of `μ_A`: the middle-thirds attractor and its natural measure
exist and are unique. -/
theorem exists_unique_isNatural_cantorSystem :
    ∃! p : Set ℝ × Measure ℝ, cantorSystem.IsNatural p.1 sCantor p.2 :=
  cantorSystem.exists_unique_isNatural cantorSystem_isDimension

/-- Existence and uniqueness of the homogeneous equal-weight natural measure for every
`0 < λ < 1/2`. -/
theorem exists_unique_isNatural_homogeneousSystem {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) :
    ∃! p : Set ℝ × Measure ℝ,
      (homogeneousSystem lam hlam0 hlam).IsNatural p.1 (homogeneousDim lam) p.2 :=
  (homogeneousSystem lam hlam0 hlam).exists_unique_isNatural
    (homogeneousSystem_isDimension hlam0 hlam)

/-- `sec:setup`, existence of `μ_B`: the paired attractor and its natural measure exist
and are unique. -/
theorem exists_unique_isNatural_pairSystem {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃! p : Set ℝ × Measure ℝ,
      (pairSystem (pairRatio s) (pairRatio_pos hs0)
        (pairRatio_lt_half hs0 hs1)).IsNatural p.1 s p.2 :=
  (pairSystem (pairRatio s) (pairRatio_pos hs0)
    (pairRatio_lt_half hs0 hs1)).exists_unique_isNatural (pairSystem_isDimension hs0 hs1)

end BrownianImages
