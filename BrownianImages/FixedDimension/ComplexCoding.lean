/-
Complex coded points for the proofs of `thm:remainder-derivative` and
`thm:second-derivative-small-s`: the maps `x ↦ ax`, `x ↦ bx + 1 - b` with complex
contractions `a`, `b`, the coded point of the first `m` letters of a word, the weights
`P_u(z) = z^{N₀(u)} (1-z)^{N₁(u)}` of a finite word, and the sums over words of length `m`.

* `cmap`, `cpointSeq`, `cratioSeq`, `weightSeq`: the coding along a word, letter by letter.
* `cpointSeq_succ_eq`: appending a letter moves the coded point by `r_u S_i(0)`.
* `cpointSeq_congr`, `cratioSeq_congr`, `weightSeq_congr`: only the first `m` letters matter.
* `norm_cratioSeq_le`, `norm_cpointSeq_le`: `|r_u| ≤ ρ^m` and `|x_u| ≤ 2/(1 - |a|)`.
* `extend`, `sum_succ_cons`, `sum_succ_snoc`: finite words as infinite ones, and the
  decompositions of a sum over words of length `m + 1` by the first or the last letter.
* `sum_weightSeq`, `sum_norm_weightSeq`: `∑_u P_u = 1` and `∑_u |P_u| = (|z| + |1-z|)^m`.
* `cpointSeq_ofReal`: for real parameters the complex coded point is the library's.
-/
import BrownianImages.FixedDimension.System

namespace BrownianImages

open Filter Set Hutchinson
open scoped Topology

noncomputable section

/-! ### The coding along a word -/

/-- The contraction of a letter. -/
def cratioOf (a b : ℂ) (i : Fin 2) : ℂ := if i = 0 then a else b

/-- The shift of a letter: `S_0(0) = 0`, `S_1(0) = 1 - b`. -/
def cshiftOf (b : ℂ) (i : Fin 2) : ℂ := if i = 0 then 0 else 1 - b

/-- The map of a letter, `S_0(x) = ax` and `S_1(x) = bx + 1 - b`. -/
def cmap (a b : ℂ) (i : Fin 2) (x : ℂ) : ℂ := cratioOf a b i * x + cshiftOf b i

/-- The coded point `S_{ω₀} ∘ ⋯ ∘ S_{ω_{m-1}}(0)` of the first `m` letters. -/
def cpointSeq (a b : ℂ) : ℕ → (ℕ → Fin 2) → ℂ
  | 0, _ => 0
  | m + 1, ω => cmap a b (ω 0) (cpointSeq a b m (tail ω))

/-- The contraction `r_u` of the first `m` letters. -/
def cratioSeq (a b : ℂ) : ℕ → (ℕ → Fin 2) → ℂ
  | 0, _ => 1
  | m + 1, ω => cratioOf a b (ω 0) * cratioSeq a b m (tail ω)

/-- The weight `P_u(z) = z^{N₀(u)} (1 - z)^{N₁(u)}` of the first `m` letters, over any
commutative ring, so that it serves both the real Bernoulli weights and their complex
extension. -/
def weightSeq {R : Type*} [CommRing R] (z : R) : ℕ → (ℕ → Fin 2) → R
  | 0, _ => 1
  | m + 1, ω => (if ω 0 = 0 then z else 1 - z) * weightSeq z m (tail ω)

@[simp] theorem cpointSeq_zero (a b : ℂ) (ω : ℕ → Fin 2) : cpointSeq a b 0 ω = 0 := rfl

theorem cpointSeq_succ (a b : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    cpointSeq a b (m + 1) ω = cmap a b (ω 0) (cpointSeq a b m (tail ω)) := rfl

@[simp] theorem cratioSeq_zero (a b : ℂ) (ω : ℕ → Fin 2) : cratioSeq a b 0 ω = 1 := rfl

theorem cratioSeq_succ (a b : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    cratioSeq a b (m + 1) ω = cratioOf a b (ω 0) * cratioSeq a b m (tail ω) := rfl

@[simp] theorem weightSeq_zero {R : Type*} [CommRing R] (z : R) (ω : ℕ → Fin 2) :
    weightSeq z 0 ω = 1 := rfl

theorem weightSeq_succ {R : Type*} [CommRing R] (z : R) (m : ℕ) (ω : ℕ → Fin 2) :
    weightSeq z (m + 1) ω = (if ω 0 = 0 then z else 1 - z) * weightSeq z m (tail ω) := rfl

theorem tail_cons {ι : Type*} (i : ι) (ω : ℕ → ι) : tail (cons i ω) = ω := by
  funext n; rfl

theorem cons_zero' {ι : Type*} (i : ι) (ω : ℕ → ι) : cons i ω 0 = i := rfl

theorem cpointSeq_cons (a b : ℂ) (m : ℕ) (i : Fin 2) (ω : ℕ → Fin 2) :
    cpointSeq a b (m + 1) (cons i ω) = cmap a b i (cpointSeq a b m ω) := by
  rw [cpointSeq_succ, cons_zero', tail_cons]

theorem cratioSeq_cons (a b : ℂ) (m : ℕ) (i : Fin 2) (ω : ℕ → Fin 2) :
    cratioSeq a b (m + 1) (cons i ω) = cratioOf a b i * cratioSeq a b m ω := by
  rw [cratioSeq_succ, cons_zero', tail_cons]

theorem weightSeq_cons {R : Type*} [CommRing R] (z : R) (m : ℕ) (i : Fin 2) (ω : ℕ → Fin 2) :
    weightSeq z (m + 1) (cons i ω) = (if i = 0 then z else 1 - z) * weightSeq z m ω := by
  rw [weightSeq_succ, cons_zero', tail_cons]

theorem cmap_zero (a b : ℂ) (x : ℂ) : cmap a b 0 x = a * x := by
  simp [cmap, cratioOf, cshiftOf]

theorem cmap_one (a b : ℂ) (x : ℂ) : cmap a b 1 x = b * x + (1 - b) := by
  simp [cmap, cratioOf, cshiftOf]

/-- `cmap` is affine: `S_i(x + y) = S_i(x) + r_i y`. -/
theorem cmap_add (a b : ℂ) (i : Fin 2) (x y : ℂ) :
    cmap a b i (x + y) = cmap a b i x + cratioOf a b i * y := by
  unfold cmap; ring

/-- Appending a letter moves the coded point by `r_u S_i(0)`. -/
theorem cpointSeq_succ_eq (a b : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    cpointSeq a b (m + 1) ω = cpointSeq a b m ω + cratioSeq a b m ω * cshiftOf b (ω m) := by
  induction m generalizing ω with
  | zero =>
    simp [cpointSeq_succ, cmap]
  | succ m ih =>
    rw [cpointSeq_succ, ih (tail ω), cmap_add, cratioSeq_succ, cpointSeq_succ]
    simp only [tail]
    ring

/-- The coded point of the first `m` letters depends on those letters only. -/
theorem cpointSeq_congr (a b : ℂ) (m : ℕ) {ω ω' : ℕ → Fin 2} (h : ∀ k < m, ω k = ω' k) :
    cpointSeq a b m ω = cpointSeq a b m ω' := by
  induction m generalizing ω ω' with
  | zero => rfl
  | succ m ih =>
    rw [cpointSeq_succ, cpointSeq_succ, h 0 (Nat.succ_pos m)]
    congr 1
    exact ih fun k hk => h (k + 1) (Nat.succ_lt_succ hk)

theorem cratioSeq_congr (a b : ℂ) (m : ℕ) {ω ω' : ℕ → Fin 2} (h : ∀ k < m, ω k = ω' k) :
    cratioSeq a b m ω = cratioSeq a b m ω' := by
  induction m generalizing ω ω' with
  | zero => rfl
  | succ m ih =>
    rw [cratioSeq_succ, cratioSeq_succ, h 0 (Nat.succ_pos m)]
    congr 1
    exact ih fun k hk => h (k + 1) (Nat.succ_lt_succ hk)

theorem weightSeq_congr {R : Type*} [CommRing R] (z : R) (m : ℕ) {ω ω' : ℕ → Fin 2}
    (h : ∀ k < m, ω k = ω' k) : weightSeq z m ω = weightSeq z m ω' := by
  induction m generalizing ω ω' with
  | zero => rfl
  | succ m ih =>
    rw [weightSeq_succ, weightSeq_succ, h 0 (Nat.succ_pos m)]
    congr 1
    exact ih fun k hk => h (k + 1) (Nat.succ_lt_succ hk)

/-! ### Bounds -/

theorem norm_cratioOf_le (a b : ℂ) (i : Fin 2) : ‖cratioOf a b i‖ ≤ max ‖a‖ ‖b‖ := by
  unfold cratioOf; split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem norm_cratioSeq_le (a b : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    ‖cratioSeq a b m ω‖ ≤ (max ‖a‖ ‖b‖) ^ m := by
  induction m generalizing ω with
  | zero => simp
  | succ m ih =>
    rw [cratioSeq_succ, norm_mul, pow_succ']
    exact mul_le_mul (norm_cratioOf_le a b _) (ih _) (norm_nonneg _) (by positivity)

theorem norm_cshiftOf_le {b : ℂ} (hb : ‖b‖ ≤ 1) (i : Fin 2) : ‖cshiftOf b i‖ ≤ 2 := by
  unfold cshiftOf; split_ifs
  · simp
  · calc ‖(1:ℂ) - b‖ ≤ ‖(1:ℂ)‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith

/-- `|x_u - 1| ≤ (1 + |a|)/(1 - |a|)`, by `S_1(x) - 1 = b(x - 1)` and `S_0(x) = ax`. -/
theorem norm_cpointSeq_sub_one_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) (m : ℕ)
    (ω : ℕ → Fin 2) : ‖cpointSeq a b m ω - 1‖ ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  have hY : 1 ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
    rw [le_div_iff₀ ha0]; linarith [norm_nonneg a]
  induction m generalizing ω with
  | zero => simpa using hY
  | succ m ih =>
    rw [cpointSeq_succ]
    set x := cpointSeq a b m (tail ω) with hx
    have ihx := ih (tail ω)
    rw [← hx] at ihx
    rcases fin_two_cases (ω 0) with h | h
    · rw [h, cmap_zero]
      have hxn : ‖x‖ ≤ (1 + ‖a‖) / (1 - ‖a‖) + 1 := by
        calc ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ ≤ _ := by rw [norm_one]; linarith
      calc ‖a * x - 1‖ ≤ ‖a * x‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = ‖a‖ * ‖x‖ + 1 := by rw [norm_mul, norm_one]
        _ ≤ ‖a‖ * ((1 + ‖a‖) / (1 - ‖a‖) + 1) + 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hxn (norm_nonneg _)) le_rfl
        _ = (1 + ‖a‖) / (1 - ‖a‖) := by field_simp; ring
    · rw [h, cmap_one]
      have e : b * x + (1 - b) - 1 = b * (x - 1) := by ring
      rw [e, norm_mul]
      calc ‖b‖ * ‖x - 1‖ ≤ 1 * ((1 + ‖a‖) / (1 - ‖a‖)) :=
            mul_le_mul hb ihx (norm_nonneg _) zero_le_one
        _ = _ := one_mul _

/-- `|x_u| ≤ 2/(1 - |a|)`. -/
theorem norm_cpointSeq_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) (m : ℕ) (ω : ℕ → Fin 2) :
    ‖cpointSeq a b m ω‖ ≤ 2 / (1 - ‖a‖) := by
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  calc ‖cpointSeq a b m ω‖ = ‖(cpointSeq a b m ω - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖cpointSeq a b m ω - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ (1 + ‖a‖) / (1 - ‖a‖) + 1 := by
        rw [norm_one]; exact add_le_add (norm_cpointSeq_sub_one_le ha hb m ω) le_rfl
    _ = 2 / (1 - ‖a‖) := by field_simp; ring

/-! ### Finite words -/

/-- A finite word as an infinite one, padded with zeros. -/
def extend {m : ℕ} (u : Fin m → Fin 2) : ℕ → Fin 2 :=
  fun k => if h : k < m then u ⟨k, h⟩ else 0

theorem extend_apply_of_lt {m : ℕ} (u : Fin m → Fin 2) {k : ℕ} (hk : k < m) :
    extend u k = u ⟨k, hk⟩ := by
  simp [extend, hk]

theorem extend_apply_of_not_lt {m : ℕ} (u : Fin m → Fin 2) {k : ℕ} (hk : ¬ k < m) :
    extend u k = 0 := by
  simp [extend, hk]

theorem extend_cons {m : ℕ} (i : Fin 2) (u : Fin m → Fin 2) :
    extend (Fin.cons i u : Fin (m + 1) → Fin 2) = cons i (extend u) := by
  funext k
  cases k with
  | zero => simp [extend, cons]
  | succ k =>
    show extend (Fin.cons i u) (k + 1) = extend u k
    by_cases hk : k < m
    · rw [extend_apply_of_lt _ (Nat.succ_lt_succ hk), extend_apply_of_lt _ hk]
      exact Fin.cons_succ (α := fun _ => Fin 2) i u ⟨k, hk⟩
    · rw [extend_apply_of_not_lt _ (fun h => hk (Nat.lt_of_succ_lt_succ h)),
        extend_apply_of_not_lt _ hk]

/-- The first `m` letters of `extend (snoc u i)` are those of `extend u`. -/
theorem extend_snoc_agree {m : ℕ} (u : Fin m → Fin 2) (i : Fin 2) :
    ∀ k < m, extend (Fin.snoc u i : Fin (m + 1) → Fin 2) k = extend u k := by
  intro k hk
  rw [extend_apply_of_lt _ (Nat.lt_succ_of_lt hk), extend_apply_of_lt _ hk]
  exact Fin.snoc_castSucc (α := fun _ => Fin 2) (p := u) (x := i) (i := ⟨k, hk⟩)

theorem extend_snoc_last {m : ℕ} (u : Fin m → Fin 2) (i : Fin 2) :
    extend (Fin.snoc u i : Fin (m + 1) → Fin 2) m = i := by
  rw [extend_apply_of_lt _ (Nat.lt_succ_self m)]
  exact Fin.snoc_last (α := fun _ => Fin 2) (p := u) (x := i)

/-- A sum over words of length `m + 1`, split by the first letter. -/
theorem sum_succ_cons {M : Type*} [AddCommMonoid M] {m : ℕ} (G : (Fin (m + 1) → Fin 2) → M) :
    ∑ u, G u = ∑ i : Fin 2, ∑ u : Fin m → Fin 2, G (Fin.cons i u) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun p => rfl).symm

/-- A sum over words of length `m + 1`, split by the last letter. -/
theorem sum_succ_snoc {M : Type*} [AddCommMonoid M] {m : ℕ} (G : (Fin (m + 1) → Fin 2) → M) :
    ∑ u, G u = ∑ i : Fin 2, ∑ u : Fin m → Fin 2, G (Fin.snoc u i) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 2) _ _ fun p => rfl).symm

/-- `∑_u P_u(z) = 1`. -/
theorem sum_weightSeq {R : Type*} [CommRing R] (z : R) (m : ℕ) :
    ∑ u : Fin m → Fin 2, weightSeq z m (extend u) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_succ_cons]
    simp only [extend_cons, weightSeq_cons, ← Finset.mul_sum, ih, Fin.sum_univ_two]
    simp

/-- `∑_u |P_u(z)| = (|z| + |1 - z|)^m`. -/
theorem sum_norm_weightSeq (z : ℂ) (m : ℕ) :
    ∑ u : Fin m → Fin 2, ‖weightSeq z m (extend u)‖ = (‖z‖ + ‖1 - z‖) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_succ_cons]
    simp only [extend_cons, weightSeq_cons, norm_mul, ← Finset.mul_sum, ih, Fin.sum_univ_two]
    simp [pow_succ]
    ring

theorem norm_weightSeq_nonneg (z : ℂ) (m : ℕ) (ω : ℕ → Fin 2) : 0 ≤ ‖weightSeq z m ω‖ :=
  norm_nonneg _

/-! ### Real parameters -/

/-- For real contractions the complex coded point is the library's coded point of the
system. -/
theorem cpointSeq_ofReal {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ)
    (ω : ℕ → Fin 2) :
    cpointSeq (fixedA s p) (fixedB s p) m ω = (codeSeq (fixedSystem s p hs hp0 hp1) ω m : ℂ) := by
  induction m generalizing ω with
  | zero => simp [codeSeq, wordMap_zero]
  | succ m ih =>
    rw [cpointSeq_succ, ih (tail ω)]
    conv_rhs => rw [← cons_head_tail ω, codeSeq_cons]
    rcases fin_two_cases (ω 0) with h | h
    · rw [h, fixedSystem_map_zero, cmap_zero]; push_cast; ring
    · rw [h, fixedSystem_map_one, cmap_one]; push_cast; ring

/-- The real weights are the complex ones. -/
theorem weightSeq_ofReal (p : ℝ) (m : ℕ) (ω : ℕ → Fin 2) :
    weightSeq (p : ℂ) m ω = Complex.ofReal (weightSeq (R := ℝ) p m ω) := by
  induction m generalizing ω with
  | zero => simp
  | succ m ih =>
    rw [weightSeq_succ, weightSeq_succ, ih]
    split_ifs <;> push_cast <;> ring

end

end BrownianImages
