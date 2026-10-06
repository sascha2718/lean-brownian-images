/-
Level sums over words of length `m` for the proofs of `thm:remainder-derivative` and
`thm:second-derivative-small-s`: `Λ^{(m)}(z) = ∑_{u,v} P_u(z) P_v(z) φ_z(x_u(z), x_v(z))`,
their telescoping, the geometric bound on the increments, the uniform limit with its
holomorphy and continuity, and the identification of a level sum at a real parameter with
the Bernoulli double integral of the kernel at the coded points of the first `m` letters.

* `letterWeight`, `levelSum`: the weight of a letter and the level sums.
* `levelSum_succ`, `norm_levelSum_succ_sub_le`: the last-letter decomposition of
  `Λ^{(m+1)}` and the bound `‖Λ^{(m+1)} - Λ^{(m)}‖ ≤ 4 L B^{2m+2} ρ^m`.
* `limitSum`, `tendsto_levelSum`, `norm_limitSum_sub_le`, `differentiableOn_limitSum`,
  `continuousOn_limitSum`: the limit of the level sums.
* `integral_infinitePi_cons'`, `integral_eq_sum_weight`, `integral_integral_eq_sum_weight`:
  a Bernoulli integral of a function of the first `m` letters is the weighted sum over the
  words of length `m`.
-/
import BrownianImages.FixedDimension.ComplexCoding
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology ENNReal

noncomputable section

/-! ### The level sums -/

/-- The weight of a letter, `z` for `0` and `1 - z` for `1`. -/
def letterWeight {R : Type*} [CommRing R] (z : R) (i : Fin 2) : R := if i = 0 then z else 1 - z

theorem sum_letterWeight {R : Type*} [CommRing R] (z : R) : ∑ i, letterWeight z i = 1 := by
  simp [Fin.sum_univ_two, letterWeight]

theorem weightSeq_cons' {R : Type*} [CommRing R] (z : R) (m : ℕ) (i : Fin 2) (ω : ℕ → Fin 2) :
    weightSeq z (m + 1) (cons i ω) = letterWeight z i * weightSeq z m ω :=
  weightSeq_cons z m i ω

/-- Appending a letter multiplies the weight by the weight of that letter. -/
theorem weightSeq_succ_eq {R : Type*} [CommRing R] (z : R) (m : ℕ) (ω : ℕ → Fin 2) :
    weightSeq z (m + 1) ω = weightSeq z m ω * letterWeight z (ω m) := by
  induction m generalizing ω with
  | zero => simp [weightSeq_succ, letterWeight]
  | succ m ih =>
    rw [weightSeq_succ, ih (tail ω), weightSeq_succ]
    simp only [tail]
    ring

theorem weightSeq_extend_snoc {R : Type*} [CommRing R] (z : R) {m : ℕ} (u : Fin m → Fin 2)
    (i : Fin 2) :
    weightSeq z (m + 1) (extend (Fin.snoc u i : Fin (m + 1) → Fin 2))
      = weightSeq z m (extend u) * letterWeight z i := by
  rw [weightSeq_succ_eq, extend_snoc_last, weightSeq_congr z m (extend_snoc_agree u i)]

theorem cpointSeq_extend_snoc (a b : ℂ) {m : ℕ} (u : Fin m → Fin 2) (i : Fin 2) :
    cpointSeq a b (m + 1) (extend (Fin.snoc u i : Fin (m + 1) → Fin 2))
      = cpointSeq a b m (extend u) + cratioSeq a b m (extend u) * cshiftOf b i := by
  rw [cpointSeq_succ_eq, extend_snoc_last, cpointSeq_congr a b m (extend_snoc_agree u i),
    cratioSeq_congr a b m (extend_snoc_agree u i)]

/-- The level sum `Λ^{(m)}(z) = ∑_{u,v} P_u(z) P_v(z) φ_z(x_u(z), x_v(z))` over words of
length `m`, for contractions `a z`, `b z` and a kernel `φ z`. -/
def levelSum (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
    weightSeq z m (extend u) * weightSeq z m (extend v) *
      φ z (cpointSeq (a z) (b z) m (extend u)) (cpointSeq (a z) (b z) m (extend v))

theorem levelSum_zero (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (z : ℂ) :
    levelSum a b φ 0 z = φ z 0 0 := by
  simp [levelSum]

/-- The last-letter decomposition of `Λ^{(m+1)}`. -/
theorem levelSum_succ (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (m : ℕ) (z : ℂ) :
    levelSum a b φ (m + 1) z
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          weightSeq z m (extend u) * weightSeq z m (extend v) *
            ∑ i : Fin 2, ∑ j : Fin 2, letterWeight z i * letterWeight z j *
              φ z (cpointSeq (a z) (b z) m (extend u) + cratioSeq (a z) (b z) m (extend u) * cshiftOf (b z) i)
                (cpointSeq (a z) (b z) m (extend v) + cratioSeq (a z) (b z) m (extend v) * cshiftOf (b z) j) := by
  set W : (Fin m → Fin 2) → ℂ := fun u => weightSeq z m (extend u) with hW
  set X : (Fin m → Fin 2) → ℂ := fun u => cpointSeq (a z) (b z) m (extend u) with hX
  set Rr : (Fin m → Fin 2) → ℂ := fun u => cratioSeq (a z) (b z) m (extend u) with hR
  set F : Fin 2 → (Fin m → Fin 2) → Fin 2 → (Fin m → Fin 2) → ℂ := fun i u j v =>
    (W u * letterWeight z i) * (W v * letterWeight z j) *
      φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j) with hF
  have e1 : levelSum a b φ (m + 1) z = ∑ i, ∑ u, ∑ j, ∑ v, F i u j v := by
    unfold levelSum
    rw [sum_succ_snoc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    rw [sum_succ_snoc]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
    rw [weightSeq_extend_snoc, weightSeq_extend_snoc, cpointSeq_extend_snoc,
      cpointSeq_extend_snoc]
  have e2 : ∑ i, ∑ u, ∑ j, ∑ v, F i u j v = ∑ u, ∑ v, ∑ i, ∑ j, F i u j v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    calc ∑ i, ∑ j, ∑ v, F i u j v = ∑ i, ∑ v, ∑ j, F i u j v :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ v, ∑ i, ∑ j, F i u j v := Finset.sum_comm
  rw [e1, e2]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hF]
  ring

/-- `Λ^{(m)}` with the inner weights inserted, since `∑_{i,j} w_i w_j = 1`. -/
theorem levelSum_eq_with_letters (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (m : ℕ) (z : ℂ) :
    levelSum a b φ m z
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          weightSeq z m (extend u) * weightSeq z m (extend v) *
            ∑ i : Fin 2, ∑ j : Fin 2, letterWeight z i * letterWeight z j *
              φ z (cpointSeq (a z) (b z) m (extend u)) (cpointSeq (a z) (b z) m (extend v)) := by
  unfold levelSum
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  congr 1
  simp only [Fin.sum_univ_two, letterWeight]
  simp
  ring

theorem sum_norm_letterWeight (z : ℂ) : ∑ i, ‖letterWeight z i‖ = ‖z‖ + ‖1 - z‖ := by
  simp [Fin.sum_univ_two, letterWeight]

/-- The increment bound `‖Λ^{(m+1)}(z) - Λ^{(m)}(z)‖ ≤ 4 L B^{2m+2} ρ^m`, for a kernel
with the Lipschitz bound `L` on the disc of radius `R₀ ≥ 2/(1 - |a z|)`. -/
theorem norm_levelSum_succ_sub_le (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (m : ℕ) {z : ℂ}
    {ρ B R₀ L : ℝ} (ha : ‖a z‖ < 1) (hb : ‖b z‖ ≤ 1) (hρ : max ‖a z‖ ‖b z‖ ≤ ρ)
    (hB : ‖z‖ + ‖1 - z‖ ≤ B) (hR₀ : 2 / (1 - ‖a z‖) ≤ R₀) (hL0 : 0 ≤ L)
    (hL : ∀ x y x' y' : ℂ, ‖x‖ ≤ R₀ → ‖y‖ ≤ R₀ → ‖x'‖ ≤ R₀ → ‖y'‖ ≤ R₀ →
      ‖φ z x' y' - φ z x y‖ ≤ L * (‖x' - x‖ + ‖y' - y‖)) :
    ‖levelSum a b φ (m + 1) z - levelSum a b φ m z‖ ≤ 4 * L * B ^ (2 * m + 2) * ρ ^ m := by
  have hρ0 : 0 ≤ ρ := le_trans (le_max_left _ _) hρ |>.trans' (norm_nonneg _)
  have hB0 : 0 ≤ B := le_trans (add_nonneg (norm_nonneg _) (norm_nonneg _)) hB
  rw [levelSum_succ, levelSum_eq_with_letters, ← Finset.sum_sub_distrib]
  set W : (Fin m → Fin 2) → ℂ := fun u => weightSeq z m (extend u) with hW
  set X : (Fin m → Fin 2) → ℂ := fun u => cpointSeq (a z) (b z) m (extend u) with hX
  set Rr : (Fin m → Fin 2) → ℂ := fun u => cratioSeq (a z) (b z) m (extend u) with hR
  -- the inner difference, at fixed `u`, `v`
  have hinner : ∀ u v : Fin m → Fin 2,
      ‖(∑ i : Fin 2, ∑ j : Fin 2, letterWeight z i * letterWeight z j *
          φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j))
        - ∑ i : Fin 2, ∑ j : Fin 2, letterWeight z i * letterWeight z j * φ z (X u) (X v)‖
        ≤ B ^ 2 * (4 * L * ρ ^ m) := by
    intro u v
    rw [← Finset.sum_sub_distrib]
    have hpt : ∀ (w : Fin m → Fin 2) (i : Fin 2), ‖X w + Rr w * cshiftOf (b z) i‖ ≤ R₀ := by
      intro w i
      have := norm_cpointSeq_le ha hb (m + 1) (extend (Fin.snoc w i : Fin (m + 1) → Fin 2))
      rw [cpointSeq_extend_snoc] at this
      exact this.trans hR₀
    have hpt0 : ∀ w : Fin m → Fin 2, ‖X w‖ ≤ R₀ := fun w =>
      (norm_cpointSeq_le ha hb m (extend w)).trans hR₀
    have hinc : ∀ (w : Fin m → Fin 2) (i : Fin 2), ‖Rr w * cshiftOf (b z) i‖ ≤ 2 * ρ ^ m := by
      intro w i
      rw [norm_mul]
      calc ‖Rr w‖ * ‖cshiftOf (b z) i‖ ≤ ρ ^ m * 2 :=
            mul_le_mul ((norm_cratioSeq_le _ _ _ _).trans (pow_le_pow_left₀ (by positivity) hρ m))
              (norm_cshiftOf_le hb i) (norm_nonneg _) (by positivity)
        _ = 2 * ρ ^ m := by ring
    have hφ : ∀ i j : Fin 2,
        ‖φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j) - φ z (X u) (X v)‖
          ≤ 4 * L * ρ ^ m := by
      intro i j
      calc ‖φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j) - φ z (X u) (X v)‖
          ≤ L * (‖X u + Rr u * cshiftOf (b z) i - X u‖ + ‖X v + Rr v * cshiftOf (b z) j - X v‖) :=
            hL _ _ _ _ (hpt0 u) (hpt0 v) (hpt u i) (hpt v j)
        _ ≤ L * (2 * ρ ^ m + 2 * ρ ^ m) := by
            apply mul_le_mul_of_nonneg_left _ hL0
            simp only [add_sub_cancel_left]
            exact add_le_add (hinc u i) (hinc v j)
        _ = 4 * L * ρ ^ m := by ring
    calc ‖∑ i : Fin 2, (∑ j : Fin 2, letterWeight z i * letterWeight z j *
            φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j)
          - ∑ j : Fin 2, letterWeight z i * letterWeight z j * φ z (X u) (X v))‖
        ≤ ∑ i : Fin 2, ‖∑ j : Fin 2, letterWeight z i * letterWeight z j *
            φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j)
          - ∑ j : Fin 2, letterWeight z i * letterWeight z j * φ z (X u) (X v)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖letterWeight z i‖ * ‖letterWeight z j‖ * (4 * L * ρ ^ m) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [← mul_sub, norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left (hφ i j) (by positivity)
      _ = (∑ i : Fin 2, ‖letterWeight z i‖) * (∑ j : Fin 2, ‖letterWeight z j‖) * (4 * L * ρ ^ m) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
      _ ≤ B ^ 2 * (4 * L * ρ ^ m) := by
          rw [sum_norm_letterWeight]
          have : (‖z‖ + ‖1 - z‖) * (‖z‖ + ‖1 - z‖) ≤ B ^ 2 := by
            rw [pow_two]; exact mul_le_mul hB hB (by positivity) hB0
          exact mul_le_mul_of_nonneg_right this (by positivity)
  -- sum over `u`, `v`
  calc ‖∑ u, (∑ v, W u * W v * ∑ i, ∑ j, letterWeight z i * letterWeight z j *
          φ z (X u + Rr u * cshiftOf (b z) i) (X v + Rr v * cshiftOf (b z) j)
        - ∑ v, W u * W v * ∑ i, ∑ j, letterWeight z i * letterWeight z j * φ z (X u) (X v))‖
      ≤ ∑ u, ∑ v, ‖W u‖ * ‖W v‖ * (B ^ 2 * (4 * L * ρ ^ m)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        rw [← mul_sub, norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hinner u v) (by positivity)
    _ = (∑ u, ‖W u‖) * (∑ v, ‖W v‖) * (B ^ 2 * (4 * L * ρ ^ m)) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
    _ ≤ B ^ m * B ^ m * (B ^ 2 * (4 * L * ρ ^ m)) := by
        simp only [hW, sum_norm_weightSeq]
        have : (‖z‖ + ‖1 - z‖) ^ m ≤ B ^ m := pow_le_pow_left₀ (by positivity) hB m
        exact mul_le_mul_of_nonneg_right (mul_le_mul this this (by positivity) (by positivity))
          (by positivity)
    _ = 4 * L * B ^ (2 * m + 2) * ρ ^ m := by ring

/-! ### The limit of the level sums -/

/-- The limit of the level sums, as the telescoping series. -/
def limitSum (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  levelSum a b φ 0 z + ∑' m : ℕ, (levelSum a b φ (m + 1) z - levelSum a b φ m z)

section Limit

variable {a b : ℂ → ℂ} {φ : ℂ → ℂ → ℂ → ℂ} {S : Set ℂ} {C r : ℝ}

/-- The geometric increment bound, as a hypothesis on a set `S`. -/
def IncrementBound (a b : ℂ → ℂ) (φ : ℂ → ℂ → ℂ → ℂ) (S : Set ℂ) (C r : ℝ) : Prop :=
  ∀ z ∈ S, ∀ m : ℕ, ‖levelSum a b φ (m + 1) z - levelSum a b φ m z‖ ≤ C * r ^ m

theorem summable_levelSum_sub (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hinc : IncrementBound a b φ S C r) {z : ℂ} (hz : z ∈ S) :
    Summable fun m : ℕ => levelSum a b φ (m + 1) z - levelSum a b φ m z :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    fun m => hinc z hz m

theorem tendsto_levelSum (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hinc : IncrementBound a b φ S C r) {z : ℂ} (hz : z ∈ S) :
    Tendsto (fun m => levelSum a b φ m z) atTop (𝓝 (limitSum a b φ z)) := by
  have hsum := (summable_levelSum_sub hr0 hr1 hinc hz).hasSum
  have h := hsum.tendsto_sum_nat.const_add (levelSum a b φ 0 z)
  refine h.congr fun m => ?_
  rw [Finset.sum_range_sub (fun k => levelSum a b φ k z)]
  ring

theorem norm_limitSum_sub_le (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hinc : IncrementBound a b φ S C r) {z : ℂ} (hz : z ∈ S) :
    ‖limitSum a b φ z - φ z 0 0‖ ≤ C / (1 - r) := by
  unfold limitSum
  rw [levelSum_zero, add_sub_cancel_left]
  calc ‖∑' m : ℕ, (levelSum a b φ (m + 1) z - levelSum a b φ m z)‖
      ≤ ∑' m : ℕ, ‖levelSum a b φ (m + 1) z - levelSum a b φ m z‖ :=
        norm_tsum_le_tsum_norm (summable_levelSum_sub hr0 hr1 hinc hz).norm
    _ ≤ ∑' m : ℕ, C * r ^ m :=
        (summable_levelSum_sub hr0 hr1 hinc hz).norm.tsum_le_tsum (fun m => hinc z hz m)
          ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    _ = C / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- The limit is holomorphic on an open set where the level sums are. -/
theorem differentiableOn_limitSum (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hinc : IncrementBound a b φ S C r) {U : Set ℂ} (hU : IsOpen U) (hUS : U ⊆ S)
    (hdiff : ∀ m, DifferentiableOn ℂ (levelSum a b φ m) U) :
    DifferentiableOn ℂ (limitSum a b φ) U := by
  unfold limitSum
  refine (hdiff 0).add ?_
  exact Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    (fun m => (hdiff (m + 1)).sub (hdiff m)) hU fun m z hz => hinc z (hUS hz) m

/-- The limit is continuous where the level sums are. -/
theorem continuousOn_limitSum (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hinc : IncrementBound a b φ S C r)
    (hcont : ∀ m, ContinuousOn (levelSum a b φ m) S) :
    ContinuousOn (limitSum a b φ) S := by
  unfold limitSum
  refine (hcont 0).add ?_
  exact continuousOn_tsum (fun m => (hcont (m + 1)).sub (hcont m))
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C) fun m z hz => hinc z hz m

end Limit

/-! ### Bernoulli integrals of functions of the first `m` letters -/

section Split

variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- `integral_infinitePi_cons` for a complex-valued function. -/
theorem integral_infinitePi_cons' (ρ : Measure α) [IsProbabilityMeasure ρ]
    {f : (ℕ → α) → ℂ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    ∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => ρ)
      = ∑ i, ((ρ {i}).toReal : ℂ) * ∫ ω, f (cons i ω) ∂(Measure.infinitePi fun _ : ℕ => ρ) := by
  set Q : Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ => ρ) with hQ
  have hQint : Integrable f Q := Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall hC)
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
    hf.aestronglyMeasurable, Complex.real_smul]

end Split

theorem twoDigit_toReal_zero {p : ℝ} (hp0 : 0 ≤ p) :
    (twoDigit (1 - p) {0}).toReal = p := by
  rw [twoDigit_zero, sub_sub_cancel, ENNReal.toReal_ofReal hp0]

theorem twoDigit_toReal_one {p : ℝ} (hp1 : p ≤ 1) :
    (twoDigit (1 - p) {1}).toReal = 1 - p := by
  rw [twoDigit_one, ENNReal.toReal_ofReal (by linarith)]

theorem twoDigit_toReal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin 2) :
    (twoDigit (1 - p) {i}).toReal = letterWeight p i := by
  rcases fin_two_cases i with h | h
  · rw [h, twoDigit_toReal_zero hp0]; simp [letterWeight]
  · rw [h, twoDigit_toReal_one hp1]; simp [letterWeight]

/-- A Bernoulli integral of a bounded measurable function of the first `m` letters is the
weighted sum over the words of length `m`, with letter weights `p` and `1 - p`. -/
theorem integral_eq_sum_weight {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    {g : (ℕ → Fin 2) → ℂ} (hg : Measurable g) {C : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C)
    (hdep : ∀ ω ω' : ℕ → Fin 2, (∀ k < m, ω k = ω' k) → g ω = g ω') :
    ∫ ω, g ω ∂twoBern (1 - p)
      = ∑ u : Fin m → Fin 2, ((weightSeq p m (extend u) : ℝ) : ℂ) * g (extend u) := by
  have hprob : IsProbabilityMeasure (twoDigit (1 - p)) :=
    isProbabilityMeasure_twoDigit (by linarith) (by linarith)
  induction m generalizing g with
  | zero =>
    have hconst : ∀ ω, g ω = g (extend (fun i : Fin 0 => (0 : Fin 2))) := fun ω =>
      hdep _ _ fun k hk => absurd hk (Nat.not_lt_zero k)
    have : IsProbabilityMeasure (twoBern (1 - p)) :=
      isProbabilityMeasure_twoBern (by linarith) (by linarith)
    rw [integral_congr_ae (Eventually.of_forall hconst), integral_const]
    rw [Fintype.sum_eq_single (fun i : Fin 0 => (0 : Fin 2)) (fun u hu => absurd (Subsingleton.elim u _) hu)]
    simp
  | succ m ih =>
    unfold twoBern
    rw [integral_infinitePi_cons' (twoDigit (1 - p)) hg hC]
    rw [sum_succ_cons]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdep' : ∀ ω ω' : ℕ → Fin 2, (∀ k < m, ω k = ω' k) → g (cons i ω) = g (cons i ω') := by
      intro ω ω' h
      refine hdep _ _ fun k hk => ?_
      cases k with
      | zero => rfl
      | succ k => exact h k (Nat.lt_of_succ_lt_succ hk)
    have hih := ih (g := fun ω => g (cons i ω)) (hg.comp (measurable_cons' i)) (fun ω => hC _) hdep'
    unfold twoBern at hih
    rw [hih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [extend_cons, weightSeq_cons', twoDigit_toReal hp0 hp1]
    push_cast
    ring

/-- The double integral of a bounded measurable function of the first `m` letters of each
word is the double weighted sum over pairs of words of length `m`. -/
theorem integral_integral_eq_sum_weight {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    {G : (ℕ → Fin 2) → (ℕ → Fin 2) → ℂ} (hG : Measurable (Function.uncurry G)) {C : ℝ}
    (hC : ∀ ω ω', ‖G ω ω'‖ ≤ C)
    (hdep : ∀ ω₁ ω₁' ω₂ ω₂' : ℕ → Fin 2, (∀ k < m, ω₁ k = ω₁' k) → (∀ k < m, ω₂ k = ω₂' k) →
      G ω₁ ω₂ = G ω₁' ω₂') :
    ∫ ω', ∫ ω, G ω ω' ∂twoBern (1 - p) ∂twoBern (1 - p)
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          ((weightSeq p m (extend u) : ℝ) : ℂ) * ((weightSeq p m (extend v) : ℝ) : ℂ) *
            G (extend u) (extend v) := by
  have hmeas1 : ∀ ω', Measurable fun ω => G ω ω' := fun ω' =>
    hG.comp (measurable_id.prodMk measurable_const)
  have hmeas2 : ∀ ω, Measurable fun ω' => G ω ω' := fun ω =>
    hG.comp (measurable_const.prodMk measurable_id)
  have hinner : ∀ ω', ∫ ω, G ω ω' ∂twoBern (1 - p)
      = ∑ u : Fin m → Fin 2, ((weightSeq p m (extend u) : ℝ) : ℂ) * G (extend u) ω' := fun ω' =>
    integral_eq_sum_weight hp0 hp1 m (hmeas1 ω') (fun ω => hC ω ω')
      fun ω₁ ω₁' h => hdep ω₁ ω₁' ω' ω' h fun _ _ => rfl
  have : IsProbabilityMeasure (twoBern (1 - p)) :=
    isProbabilityMeasure_twoBern (by linarith) (by linarith)
  simp_rw [hinner]
  rw [integral_finsetSum _ fun u _ => ?_]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_const_mul, integral_eq_sum_weight hp0 hp1 m (hmeas2 _) (fun ω' => hC _ ω')
      fun ω₂ ω₂' h => hdep _ _ ω₂ ω₂' (fun _ _ => rfl) h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  · exact (Integrable.of_bound ((hmeas2 _).aestronglyMeasurable) C
      (Eventually.of_forall fun ω' => hC _ ω')).const_mul _

end

end BrownianImages
