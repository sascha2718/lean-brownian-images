/-
`thm:non-lattice-limit` of `sec:renewal`: Choquet-Deny for a step law whose harmonicity
is available only on a half line, and the convergence of `G` it gives.

`eq:g-recursion` holds for `G` only above `log ρ⁻¹`, so `G` is not harmonic on the line
and the Choquet-Deny theorem for the whole line does not apply to it.  What is proved here is the
Choquet-Deny statement with the recursion restricted to a tail: a function bounded and
continuous on `[T, ∞)` and satisfying `f(w) = ∑ p_i f(w - a_i)` at every `w > T`
converges at `+∞`, as soon as the weights are positive with sum `1`, the steps are
positive, and the additive group they generate is dense.  Nothing is assumed about `f`
below `T`.

Three points carry the restriction to the half line.  The maximum principle is run above
a barrier, placed far enough to the right that a whole word of the walk stays inside
`[T, ∞)`.  The level the function is compared against is the limit `⨅ₙ sup_{[T+n,∞)} f`
of the tail suprema, not the supremum over `[T, ∞)`, whose near maximisers may all sit
at the left end, where the walk has no room.  And uniform continuity, which the argument
consumes and which continuity alone does not give on an unbounded set, comes from the
recursion itself: the difference of the values at `w` and `w'` is a convex average of the
differences one step lower, so it is inherited downwards until the pair falls into a
compact window, where Heine-Cantor supplies the modulus.

Applied to `G` this closes `thm:non-lattice-limit`, the continuity of `G` coming from
`continuous_G` and the Frostman bound from Ahlfors regularity of the natural measure.

* `TailHarmonic.stepVal_le`: a word of at most `n` steps moves by at most `nA`.
* `TailHarmonic.step_le`, `TailHarmonic.iterate_le`, `TailHarmonic.propagate_le`: the
  maximum principle along one step and along a word, and the upward propagation of a
  bound, all above a barrier.
* `TailHarmonic.uc_of_continuousOn`: a continuous tail-harmonic function is uniformly
  continuous on the tail.
* `TailHarmonic.exists_tendsto_atTop`, `.exists_tendsto_atTop_of_continuousOn`: the
  theorem itself, with the modulus of continuity supplied in the elementary shape, and
  not at all.
* `exists_tendsto_G`, `nonLatticeLimit`: `eq:g-non-lattice-limit`.
-/
import BrownianImages.KeyRenewal

namespace BrownianImages

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace TailHarmonic

variable {ι : Type*} [Fintype ι] {p a : ι → ℝ} {d : ℝ → ℝ}

/-- A word of at most `n` steps of the walk moves by at most `nA`, where `A` bounds the
steps.  This is what keeps the whole word inside the half line on which the recursion
`eq:g-recursion` is available. -/
theorem stepVal_le {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ i, a i ≤ A) {k : ι → ℕ} {n : ℕ}
    (hk : (∑ i, k i) ≤ n) : KeyRenewal.stepVal a k ≤ (n : ℝ) * A := by
  have h1 : KeyRenewal.stepVal a k ≤ ∑ i, (k i : ℝ) * A :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA i) (Nat.cast_nonneg _)
  have h2 : ∑ i, (k i : ℝ) * A = ((∑ i, k i : ℕ) : ℝ) * A := by
    rw [← Finset.sum_mul]
    push_cast
    ring
  have h3 : ((∑ i, k i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  calc KeyRenewal.stepVal a k ≤ ∑ i, (k i : ℝ) * A := h1
    _ = ((∑ i, k i : ℕ) : ℝ) * A := h2
    _ ≤ (n : ℝ) * A := by gcongr

/-- One step of the maximum principle above the barrier `u`.  A function non-negative on
`[u, ∞)` and harmonic there for the step law `∑ p_i δ_{a_i}` loses at most a factor
`q ≤ min_i p_i` along one step taken from a point at height `u + A` or above, which is
what keeps the step inside `[u, ∞)`. -/
theorem step_le {q u A : ℝ} (hp : ∀ i, 0 ≤ p i) (hqle : ∀ i, q ≤ p i)
    (hA : ∀ i, a i ≤ A) (hd0 : ∀ x, u ≤ x → 0 ≤ d x)
    (hharm : ∀ x, u + A ≤ x → d x = ∑ i, p i * d (x - a i))
    {x : ℝ} (hx : u + A ≤ x) (i : ι) : q * d (x - a i) ≤ d x := by
  have hmem : ∀ j : ι, u ≤ x - a j := fun j => by linarith [hA j]
  refine le_trans (mul_le_mul_of_nonneg_right (hqle i) (hd0 _ (hmem i))) ?_
  rw [hharm x hx]
  exact Finset.single_le_sum (f := fun j => p j * d (x - a j))
    (fun j _ => mul_nonneg (hp j) (hd0 _ (hmem j))) (Finset.mem_univ i)

/-- The maximum principle along a whole word, above the barrier `u`.  A word of at most
`n` steps costs at most a factor `q^n`, provided it starts at height `u + nA` or above,
so that it never leaves `[u, ∞)`. -/
theorem iterate_le {q u A : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hA0 : 0 < A)
    (hp : ∀ i, 0 ≤ p i) (hqle : ∀ i, q ≤ p i) (hA : ∀ i, a i ≤ A)
    (hd0 : ∀ x, u ≤ x → 0 ≤ d x)
    (hharm : ∀ x, u + A ≤ x → d x = ∑ i, p i * d (x - a i)) :
    ∀ (n : ℕ) (k : ι → ℕ), (∑ i, k i) ≤ n → ∀ x : ℝ, u + (n : ℝ) * A ≤ x →
      q ^ n * d (x - KeyRenewal.stepVal a k) ≤ d x := by
  classical
  intro n
  induction n with
  | zero =>
      intro k hk x _
      have hk0 : ∀ i, k i = 0 := fun i =>
        (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hk)) i (Finset.mem_univ i)
      have hv : KeyRenewal.stepVal a k = 0 := by simp [KeyRenewal.stepVal, hk0]
      rw [hv, pow_zero, one_mul, sub_zero]
  | succ n ih =>
      intro k hk x hx
      have hn0 : (0 : ℝ) ≤ (n : ℝ) * A := mul_nonneg (Nat.cast_nonneg n) hA0.le
      have hcast : ((n : ℝ) + 1) * A = (n : ℝ) * A + A := by ring
      rw [Nat.cast_succ, hcast] at hx
      have hxA : u + A ≤ x := by linarith
      by_cases h0 : ∑ i, k i = 0
      · have hk0 : ∀ i, k i = 0 := fun i =>
          (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
        have hv : KeyRenewal.stepVal a k = 0 := by simp [KeyRenewal.stepVal, hk0]
        rw [hv, sub_zero]
        exact mul_le_of_le_one_left (hd0 x (by linarith)) (pow_le_one₀ hq0.le hq1)
      · obtain ⟨i₀, hi₀⟩ : ∃ i, k i ≠ 0 := by
          by_contra hc
          exact h0 (Finset.sum_eq_zero fun i _ => not_not.mp fun hne => hc ⟨i, hne⟩)
        set k' : ι → ℕ := Function.update k i₀ (k i₀ - 1) with hk'
        have hupd : ∀ i, i ≠ i₀ → k' i = k i := fun i hi => by
          simp [hk', Function.update_of_ne hi]
        have hupd₀ : k' i₀ = k i₀ - 1 := by simp [hk']
        have hsum' : ∑ i, k' i ≤ n := by
          have e1 : ∑ i, k i = k i₀ + ∑ i ∈ Finset.univ.erase i₀, k i :=
            (Finset.add_sum_erase _ k (Finset.mem_univ i₀)).symm
          have e2 : ∑ i, k' i = k' i₀ + ∑ i ∈ Finset.univ.erase i₀, k' i :=
            (Finset.add_sum_erase _ k' (Finset.mem_univ i₀)).symm
          have e3 : ∑ i ∈ Finset.univ.erase i₀, k' i = ∑ i ∈ Finset.univ.erase i₀, k i :=
            Finset.sum_congr rfl fun i hi => hupd i (Finset.ne_of_mem_erase hi)
          rw [e2, e3, hupd₀]
          omega
        have hV : KeyRenewal.stepVal a k = a i₀ + KeyRenewal.stepVal a k' := by
          have e1 : ∑ i, (k i : ℝ) * a i
              = (k i₀ : ℝ) * a i₀ + ∑ i ∈ Finset.univ.erase i₀, (k i : ℝ) * a i :=
            (Finset.add_sum_erase _ (fun i => (k i : ℝ) * a i) (Finset.mem_univ i₀)).symm
          have e2 : ∑ i, (k' i : ℝ) * a i
              = (k' i₀ : ℝ) * a i₀ + ∑ i ∈ Finset.univ.erase i₀, (k' i : ℝ) * a i :=
            (Finset.add_sum_erase _ (fun i => (k' i : ℝ) * a i) (Finset.mem_univ i₀)).symm
          have e3 : ∑ i ∈ Finset.univ.erase i₀, (k' i : ℝ) * a i
              = ∑ i ∈ Finset.univ.erase i₀, (k i : ℝ) * a i :=
            Finset.sum_congr rfl fun i hi => by rw [hupd i (Finset.ne_of_mem_erase hi)]
          have e4 : ((k' i₀ : ℕ) : ℝ) = (k i₀ : ℝ) - 1 := by
            rw [hupd₀, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi₀), Nat.cast_one]
          rw [KeyRenewal.stepVal, KeyRenewal.stepVal, e1, e2, e3, e4]
          ring
        have hrw : q ^ (n + 1) * d (x - KeyRenewal.stepVal a k)
            = q * (q ^ n * d ((x - a i₀) - KeyRenewal.stepVal a k')) := by
          rw [hV, sub_add_eq_sub_sub, pow_succ]
          ring
        have hstep : u + (n : ℝ) * A ≤ x - a i₀ := by linarith [hA i₀]
        rw [hrw]
        exact le_trans (mul_le_mul_of_nonneg_left (ih k' hsum' (x - a i₀) hstep) hq0.le)
          (step_le hp hqle hA hd0 hharm hxA i₀)

/-- Upward propagation above the barrier `u`.  Harmonicity expresses a value through
values strictly below it, so a bound on the window `[u, u + A]` spreads to the whole half
line `[u, ∞)`, using only the recursion at heights `u + A` and above. -/
theorem propagate_le [Nonempty ι] {u A η : ℝ} (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (ha : ∀ i, 0 < a i) (hA : ∀ i, a i ≤ A)
    (hharm : ∀ x, u + A ≤ x → d x = ∑ i, p i * d (x - a i))
    (hbase : ∀ y ∈ Set.Icc u (u + A), d y ≤ η) :
    ∀ z, u ≤ z → d z ≤ η := by
  classical
  obtain ⟨i₁, -, hmin⟩ := Finset.exists_min_image Finset.univ a
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have he : 0 < a i₁ := ha i₁
  have key : ∀ n : ℕ, ∀ y ∈ Set.Icc u (u + A + (n : ℝ) * a i₁), d y ≤ η := by
    intro n
    induction n with
    | zero => intro y hy; exact hbase y ⟨hy.1, by simpa using hy.2⟩
    | succ n ih =>
        rintro y ⟨hy1, hy2⟩
        have hcast : ((n : ℝ) + 1) * a i₁ = (n : ℝ) * a i₁ + a i₁ := by ring
        rw [Nat.cast_succ, hcast] at hy2
        rcases le_or_gt y (u + A + (n : ℝ) * a i₁) with hle | hgt
        · exact ih y ⟨hy1, hle⟩
        · have hn0 : (0 : ℝ) ≤ (n : ℝ) * a i₁ := mul_nonneg (Nat.cast_nonneg n) he.le
          rw [hharm y (by linarith)]
          calc ∑ i, p i * d (y - a i) ≤ ∑ i, p i * η := by
                refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp i)
                refine ih (y - a i) ⟨?_, ?_⟩
                · have := hA i
                  linarith
                · have := hmin i (Finset.mem_univ i)
                  linarith
            _ = η := by rw [← Finset.sum_mul, hpsum, one_mul]
  intro z hz
  obtain ⟨N, hN⟩ := exists_nat_ge ((z - u - A) / a i₁)
  refine key N z ⟨hz, ?_⟩
  rw [div_le_iff₀ he] at hN
  linarith

/-- A function continuous on `[T, ∞)` and harmonic there is *uniformly* continuous on
`[T, ∞)`.  The recursion writes the difference of the values at `w` and at `w'` as a
convex average of the differences at `w - a_i` and `w' - a_i`, and a convex average does
not exceed the largest term, so the modulus at height `w` is inherited from the modulus
one step lower.  Iterating drops the pair into the compact window `[T, T + 3A]`, where
Heine-Cantor supplies the modulus.  Nothing is assumed about `f` below `T`: the
descending pair is stopped before it can leave the half line. -/
theorem uc_of_continuousOn [Nonempty ι] {f : ℝ → ℝ} {T A : ℝ} (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (ha : ∀ i, 0 < a i) (hA0 : 0 < A) (hA : ∀ i, a i ≤ A)
    (hcont : ContinuousOn f (Set.Icc T (T + 3 * A)))
    (hharm : ∀ w, T < w → f w = ∑ i, p i * f (w - a i)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, T ≤ x → ∀ y, T ≤ y → |x - y| ≤ δ → |f x - f y| ≤ ε := by
  classical
  obtain ⟨i₁, -, hmin⟩ := Finset.exists_min_image Finset.univ a
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have he : 0 < a i₁ := ha i₁
  intro ε hε
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := Metric.uniformContinuousOn_iff_le.mp
    ((isCompact_Icc (a := T) (b := T + 3 * A)).uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min δ₀ (A / 2), lt_min hδ₀0 (by linarith), ?_⟩
  set δ : ℝ := min δ₀ (A / 2) with hδdef
  have hδA : δ ≤ A / 2 := min_le_right _ _
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hbase : ∀ w w' : ℝ, T ≤ w → T ≤ w' → w ≤ T + 2 * A → |w - w'| ≤ δ →
      |f w - f w'| ≤ ε := by
    intro w w' hw1 hw'1 hw2 hww
    have habs := abs_le.mp hww
    refine hδ₀ w (Set.mem_Icc.mpr ⟨hw1, by linarith⟩) w'
      (Set.mem_Icc.mpr ⟨hw'1, by linarith [habs.1]⟩) ?_
    rw [Real.dist_eq]
    linarith
  have key : ∀ n : ℕ, ∀ w w' : ℝ, T ≤ w → T ≤ w' → w ≤ T + 2 * A + (n : ℝ) * a i₁ →
      |w - w'| ≤ δ → |f w - f w'| ≤ ε := by
    intro n
    induction n with
    | zero => intro w w' h1 h1' h2 h3; exact hbase w w' h1 h1' (by simpa using h2) h3
    | succ n ih =>
        intro w w' h1 h1' h2 h3
        rcases le_or_gt w (T + 2 * A) with hle | hgt
        · exact hbase w w' h1 h1' hle h3
        · have hcast : ((n : ℝ) + 1) * a i₁ = (n : ℝ) * a i₁ + a i₁ := by ring
          rw [Nat.cast_succ, hcast] at h2
          have habs := abs_le.mp h3
          have hw' : T + A < w' := by linarith [habs.2]
          rw [hharm w (by linarith), hharm w' (by linarith), ← Finset.sum_sub_distrib]
          calc |∑ i, (p i * f (w - a i) - p i * f (w' - a i))|
              ≤ ∑ i, |p i * f (w - a i) - p i * f (w' - a i)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, p i * ε := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [← mul_sub, abs_mul, abs_of_nonneg (hp i)]
                refine mul_le_mul_of_nonneg_left ?_ (hp i)
                refine ih (w - a i) (w' - a i) (by linarith [hA i]) (by linarith [hA i])
                  (by linarith [hmin i (Finset.mem_univ i)]) ?_
                rw [show w - a i - (w' - a i) = w - w' from by ring]
                exact h3
            _ = ε := by rw [← Finset.sum_mul, hpsum, one_mul]
  intro x hx y hy hxy
  obtain ⟨N, hN⟩ := exists_nat_ge ((x - T - 2 * A) / a i₁)
  rw [div_le_iff₀ he] at hN
  exact key N x y hx hy (by linarith) hxy

/-- **Choquet-Deny on a tail.**  Let the weights `p` be positive with `∑ p_i = 1`, let
the steps `a` be positive, and let the additive group they generate be dense in `ℝ`.  A
function bounded and uniformly continuous on `[T, ∞)` and satisfying
`f(w) = ∑ p_i f(w - a_i)` at every `w > T` converges at `+∞`.

The recursion is used only at heights where the whole word of the walk stays inside
`[T, ∞)`, so nothing is assumed about `f` below `T`.  The limit is the limit of the tail
suprema of `f`: a near maximiser of that level can be taken arbitrarily far to the right,
which is the room the maximum principle needs, and the supremum over `[T, ∞)` itself
would not supply it. -/
theorem exists_tendsto_atTop [Nonempty ι] {f : ℝ → ℝ} {T B : ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) (ha : ∀ i, 0 < a i)
    (hdense : Dense ((AddSubgroup.closure (Set.range a) : AddSubgroup ℝ) : Set ℝ))
    (hbdd : ∀ x, T ≤ x → |f x| ≤ B)
    (huc : ∀ ε > 0, ∃ δ > 0, ∀ x, T ≤ x → ∀ y, T ≤ y → |x - y| ≤ δ → |f x - f y| ≤ ε)
    (hharm : ∀ w, T < w → f w = ∑ i, p i * f (w - a i)) :
    ∃ C : ℝ, Tendsto f atTop (𝓝 C) := by
  classical
  obtain ⟨i₂, -, hamax⟩ := Finset.exists_max_image Finset.univ a
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set A : ℝ := a i₂ with hAdef
  have hA0 : 0 < A := ha i₂
  have hAle : ∀ i, a i ≤ A := fun i => hamax i (Finset.mem_univ i)
  obtain ⟨i₀, -, hqmin⟩ := Finset.exists_min_image Finset.univ p
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set q : ℝ := p i₀ with hqdef
  have hq0 : 0 < q := hp i₀
  have hqle : ∀ i, q ≤ p i := fun i => hqmin i (Finset.mem_univ i)
  have hq1 : q ≤ 1 := by
    calc q ≤ ∑ i, p i := Finset.single_le_sum (fun i _ => (hp i).le) (Finset.mem_univ i₀)
      _ = 1 := hpsum
  -- The tail suprema and their limit.
  set g : ℕ → ℝ := fun n => sSup (f '' Set.Ici (T + (n : ℝ))) with hg
  have hTn : ∀ (n : ℕ) (x : ℝ), T + (n : ℝ) ≤ x → T ≤ x := by
    intro n x hx
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne : ∀ n : ℕ, (f '' Set.Ici (T + (n : ℝ))).Nonempty :=
    fun n => ⟨f (T + (n : ℝ)), ⟨T + (n : ℝ), Set.self_mem_Ici, rfl⟩⟩
  have hbd : ∀ n : ℕ, BddAbove (f '' Set.Ici (T + (n : ℝ))) := by
    intro n
    refine ⟨B, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hbdd x (hTn n x hx))
  have hgge : ∀ n : ℕ, -B ≤ g n := by
    intro n
    refine le_trans ?_ (le_csSup (hbd n) ⟨T + (n : ℝ), Set.self_mem_Ici, rfl⟩)
    have := abs_le.mp (hbdd (T + (n : ℝ)) (hTn n _ le_rfl))
    linarith [this.1]
  have hMbdd : BddBelow (Set.range g) := ⟨-B, by rintro _ ⟨n, rfl⟩; exact hgge n⟩
  set M : ℝ := ⨅ n : ℕ, g n with hM
  have hMle : ∀ n : ℕ, M ≤ g n := fun n => ciInf_le hMbdd n
  have hMlt : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, g n < M + ε := by
    intro ε hε
    exact exists_lt_of_ciInf_lt (by linarith : M < M + ε)
  -- The core estimate: `f` sits within `η` of `M` on a tail.
  have core : ∀ η : ℝ, 0 < η → ∃ u : ℝ, ∀ z : ℝ, u ≤ z → |f z - M| ≤ η := by
    intro η hη
    obtain ⟨δ, hδ0, hδ⟩ := huc (η / 2) (by linarith)
    obtain ⟨c, m, hnet⟩ := KeyRenewal.exists_net (a := a) (R := A) hdense hδ0
    set ε₁ : ℝ := η / 4 * q ^ m with hε₁
    have hqm : 0 < q ^ m := pow_pos hq0 m
    have hqm1 : q ^ m ≤ 1 := pow_le_one₀ hq0.le hq1
    have hε₁0 : 0 < ε₁ := by positivity
    have hε₁η : ε₁ ≤ η := by
      have : ε₁ ≤ η / 4 * 1 := by
        rw [hε₁]
        exact mul_le_mul_of_nonneg_left hqm1 (by linarith)
      linarith
    -- the height above which `f ≤ M + ε₁`
    obtain ⟨n₁, hn₁⟩ := hMlt ε₁ hε₁0
    set U : ℝ := T + (n₁ : ℝ) with hU
    have hUT : T ≤ U := by
      have : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg n₁
      rw [hU]; linarith
    have hfU : ∀ x : ℝ, U ≤ x → f x ≤ M + ε₁ := fun x hx =>
      le_trans (le_csSup (hbd n₁) ⟨x, hx, rfl⟩) hn₁.le
    -- the room the walk needs to the left of a near maximiser
    set W : ℝ := |c| + A + (m : ℝ) * A with hW
    have hmA : (0 : ℝ) ≤ (m : ℝ) * A := mul_nonneg (Nat.cast_nonneg m) hA0.le
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((n₁ : ℝ) + W)
    obtain ⟨v, hv, hvlt⟩ := exists_lt_of_lt_csSup (hne n₂)
      (lt_of_lt_of_le (by linarith : M - ε₁ < M) (hMle n₂))
    obtain ⟨x₀, hx₀mem, rfl⟩ := hv
    have hx₀ : U + W ≤ x₀ := by
      have h1 : T + (n₂ : ℝ) ≤ x₀ := hx₀mem
      have h2 : (n₁ : ℝ) + W ≤ (n₂ : ℝ) := hn₂
      rw [hU]
      linarith
    -- the defect `d = (M + ε₁) - f`
    set d : ℝ → ℝ := fun x => (M + ε₁) - f x with hd
    have hd0 : ∀ x : ℝ, U ≤ x → 0 ≤ d x := fun x hx => sub_nonneg.mpr (hfU x hx)
    have hdharm : ∀ x : ℝ, T < x → d x = ∑ i, p i * d (x - a i) := by
      intro x hx
      have hrw : ∑ i, p i * d (x - a i)
          = (∑ i, p i) * (M + ε₁) - ∑ i, p i * f (x - a i) := by
        simp only [hd, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hrw, hpsum, one_mul, ← hharm x hx, hd]
    -- the barrier for the walk, and the barrier for the base window
    have hbar : ∀ u : ℝ, U ≤ u → ∀ x : ℝ, u + A ≤ x → d x = ∑ i, p i * d (x - a i) := by
      intro u hu x hx
      exact hdharm x (by linarith [hUT])
    have hd0' : ∀ u : ℝ, U ≤ u → ∀ x : ℝ, u ≤ x → 0 ≤ d x :=
      fun u hu x hx => hd0 x (le_trans hu hx)
    have habs : ∀ x : ℝ, U ≤ x → T ≤ x := fun x hx => le_trans hUT hx
    -- the near maximiser is small for `d`
    have hdx₀ : d x₀ ≤ η / 2 * q ^ m := by
      rw [hd]
      have : M - ε₁ < f x₀ := hvlt
      have h2 : (M + ε₁) - f x₀ < 2 * ε₁ := by linarith
      have h3 : 2 * ε₁ = η / 2 * q ^ m := by rw [hε₁]; ring
      linarith
    -- the walk barrier
    set u₂ : ℝ := x₀ - (m : ℝ) * A with hu₂
    have hu₂U : U ≤ u₂ := by
      rw [hu₂]
      have : (0 : ℝ) ≤ |c| := abs_nonneg c
      have hWge : (m : ℝ) * A ≤ W := by rw [hW]; linarith [hA0.le]
      linarith
    have hword : ∀ k : ι → ℕ, (∑ i, k i) ≤ m → d (x₀ - KeyRenewal.stepVal a k) ≤ η / 2 := by
      intro k hk
      have h1 : q ^ m * d (x₀ - KeyRenewal.stepVal a k) ≤ d x₀ :=
        iterate_le hq0 hq1 hA0 (fun i => (hp i).le) hqle hAle (hd0' u₂ hu₂U)
          (hbar u₂ hu₂U) m k hk x₀ (by rw [hu₂]; linarith)
      refine le_of_mul_le_mul_left ?_ hqm
      calc q ^ m * d (x₀ - KeyRenewal.stepVal a k) ≤ d x₀ := h1
        _ ≤ η / 2 * q ^ m := hdx₀
        _ = q ^ m * (η / 2) := by ring
    -- the base window
    set u₁ : ℝ := x₀ - c - A with hu₁
    have hu₁U : U ≤ u₁ := by
      rw [hu₁]
      have hc : c ≤ |c| := le_abs_self c
      have hWge : c + A ≤ W := by rw [hW]; linarith
      linarith
    have hbase : ∀ y ∈ Set.Icc u₁ (u₁ + A), d y ≤ η := by
      rintro y ⟨hy1, hy2⟩
      rw [hu₁] at hy1 hy2
      obtain ⟨k, hk, hkd⟩ := hnet (x₀ - y) ⟨by linarith, by linarith⟩
      have hstep : KeyRenewal.stepVal a k ≤ (m : ℝ) * A := stepVal_le hA0.le hAle hk
      have hxk : U ≤ x₀ - KeyRenewal.stepVal a k := by
        have : u₂ ≤ x₀ - KeyRenewal.stepVal a k := by rw [hu₂]; linarith
        linarith [hu₂U]
      have hyU : U ≤ y := le_trans hu₁U (by rw [hu₁]; exact hy1)
      have h3 : |f (x₀ - KeyRenewal.stepVal a k) - f y| ≤ η / 2 := by
        refine hδ _ (habs _ hxk) _ (habs _ hyU) ?_
        rw [show x₀ - KeyRenewal.stepVal a k - y = (x₀ - y) - KeyRenewal.stepVal a k from
          by ring]
        exact hkd
      have h4 : d y - d (x₀ - KeyRenewal.stepVal a k)
          = f (x₀ - KeyRenewal.stepVal a k) - f y := by simp only [hd]; ring
      have h5 := (abs_le.mp h3).2
      have h6 := hword k hk
      linarith
    have hprop : ∀ z : ℝ, u₁ ≤ z → d z ≤ η :=
      propagate_le (fun i => (hp i).le) hpsum ha hAle (hbar u₁ hu₁U) hbase
    refine ⟨u₁, fun z hz => ?_⟩
    have h1 : d z ≤ η := hprop z hz
    have h2 : f z ≤ M + ε₁ := hfU z (le_trans hu₁U hz)
    rw [hd] at h1
    rw [abs_le]
    constructor <;> linarith
  refine ⟨M, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨u, hu⟩ := core (ε / 2) (by linarith)
  refine ⟨u, fun z hz => ?_⟩
  rw [Real.dist_eq]
  have := hu z hz
  linarith

/-- **Choquet-Deny on a tail**, with continuity in place of uniform continuity.  A
function bounded and continuous on `[T, ∞)` and satisfying `f(w) = ∑ p_i f(w - a_i)` at
every `w > T` converges at `+∞`: the recursion supplies its own modulus of continuity
through `uc_of_continuousOn`, so no equicontinuity has to be assumed. -/
theorem exists_tendsto_atTop_of_continuousOn [Nonempty ι] {f : ℝ → ℝ} {T B : ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) (ha : ∀ i, 0 < a i)
    (hdense : Dense ((AddSubgroup.closure (Set.range a) : AddSubgroup ℝ) : Set ℝ))
    (hbdd : ∀ x, T ≤ x → |f x| ≤ B)
    (hcont : ContinuousOn f (Set.Ici T))
    (hharm : ∀ w, T < w → f w = ∑ i, p i * f (w - a i)) :
    ∃ C : ℝ, Tendsto f atTop (𝓝 C) := by
  classical
  obtain ⟨i₂, -, hamax⟩ := Finset.exists_max_image Finset.univ a
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hA0 : 0 < a i₂ := ha i₂
  refine exists_tendsto_atTop hp hpsum ha hdense hbdd ?_ hharm
  refine uc_of_continuousOn (fun i => (hp i).le) hpsum ha hA0
    (fun i => hamax i (Finset.mem_univ i)) (hcont.mono ?_) hharm
  exact fun x hx => hx.1

end TailHarmonic

/-- `thm:non-lattice-limit`: the normalised profile converges at `+∞`.  Everything the
key renewal theorem would supply is replaced by Choquet-Deny above the threshold
`log ρ⁻¹` of `eq:g-recursion`: the weights `r_i^s` sum to `1` by `S.IsDimension`, the
steps `S.logRatio i` are positive, the group they generate is dense by
`S.NonArithmetic`, `eq:phi-frostman` bounds `G` on the whole line, and `G` is continuous
because the pair-distance law has no atoms.  The Frostman constant comes from Ahlfors
regularity of the natural measure. -/
theorem exists_tendsto_G {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hs0 : 0 < s) (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s)
    (hna : S.NonArithmetic) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C : ℝ, Tendsto (G s μ) atTop (𝓝 C) := by
  haveI := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0 hsep hμ
  exact TailHarmonic.exists_tendsto_atTop_of_continuousOn
    (p := fun i => S.ratio i ^ s) (a := S.logRatio) (T := Real.log ρ⁻¹)
    (fun i => Real.rpow_pos_of_pos (S.ratio_pos i) s) hdim (fun i => S.logRatio_pos i) hna
    (B := A) (fun x _ => abs_G_le hs0 hA x) (continuous_G hs0 hA).continuousOn
    (fun w hw => g_recursion S hsep hμ hw)

/-- `thm:non-lattice-limit`, `eq:g-non-lattice-limit`.  In the non-arithmetic case the
normalised profile converges to `m⁻¹ ∫ z`, which is finite and strictly positive, where
`m = ∑ p_i a_i` is the renewal mean and `z = G - F * G` the renewal defect. -/
theorem nonLatticeLimit {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (_hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) :=
  nonLatticeLimit_of_tendsto S hs0 hsep hdim hμ (exists_tendsto_G S hs0 hsep hdim hna hμ)

end BrownianImages
