/-
Finite-support discrete renewal theory for the arithmetic Brownian tube equation.

This file starts from `System.TubeArithmetic h`, extracts positive integer
lattice steps, and develops the renewal-mass sequence used by the uniform
arithmetic theorem in `MinkowskiTubeArithmeticRenewal`.
-/
import BrownianImages.MinkowskiTubeArithmeticRenewal
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

namespace BrownianImages

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {iota : Type*} [Fintype iota] (S : BrownianImages.System iota)

/-- Every positive half-logarithmic step of an arithmetic system is a positive
natural multiple of the span. -/
theorem exists_pos_nat_halfLogRatio_eq_mul
    {h : ℝ} (hh : 0 < h) (harith : S.TubeArithmetic h) (i : iota) :
    ∃ k : ℕ, 0 < k ∧ S.halfLogRatio i = (k : ℝ) * h := by
  have hmem := S.halfLogRatio_mem_zmultiples_of_tubeArithmetic harith i
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hzeq : (z : ℝ) * h = S.halfLogRatio i := by
    simpa [zsmul_eq_mul] using hz
  have hzpos : 0 < z := by
    by_contra hz0
    have hzle : (z : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hz0)
    have : (z : ℝ) * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hzle hh.le
    linarith [S.halfLogRatio_pos i]
  have hzto : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hztnpos : 0 < z.toNat := by omega
  refine ⟨z.toNat, hztnpos, ?_⟩
  rw [← hzeq]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hzpos.le).symm

/-- The positive integer lag associated with an arithmetic tube step. -/
noncomputable def tubeLag {h : ℝ} (hh : 0 < h)
    (harith : S.TubeArithmetic h) (i : iota) : ℕ :=
  Classical.choose (S.exists_pos_nat_halfLogRatio_eq_mul hh harith i)

theorem tubeLag_pos {h : ℝ} (hh : 0 < h)
    (harith : S.TubeArithmetic h) (i : iota) :
    0 < S.tubeLag hh harith i :=
  (Classical.choose_spec (S.exists_pos_nat_halfLogRatio_eq_mul hh harith i)).1

theorem halfLogRatio_eq_tubeLag_mul {h : ℝ} (hh : 0 < h)
    (harith : S.TubeArithmetic h) (i : iota) :
    S.halfLogRatio i = (S.tubeLag hh harith i : ℝ) * h :=
  (Classical.choose_spec (S.exists_pos_nat_halfLogRatio_eq_mul hh harith i)).2

/-- The span in `TubeArithmetic h` is the maximal lattice span: the natural
integer lags have gcd one. -/
theorem setGcd_range_tubeLag_eq_one
    [Nonempty iota] {h : ℝ} (hh : 0 < h) (harith : S.TubeArithmetic h) :
    Nat.setGcd (Set.range (S.tubeLag hh harith)) = 1 := by
  let d : ℕ := Nat.setGcd (Set.range (S.tubeLag hh harith))
  have hdiv : ∀ i : iota, d ∣ S.tubeLag hh harith i := by
    intro i
    exact Nat.setGcd_dvd_of_mem ⟨i, rfl⟩
  have hsubset : Set.range S.halfLogRatio ⊆
      (AddSubgroup.zmultiples ((d : ℝ) * h) : Set ℝ) := by
    rintro x ⟨i, rfl⟩
    obtain ⟨q, hq⟩ := hdiv i
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(q : ℤ), ?_⟩
    rw [S.halfLogRatio_eq_tubeLag_mul hh harith i, hq]
    simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]
    ring
  have hle : AddSubgroup.closure (Set.range S.halfLogRatio) ≤
      AddSubgroup.zmultiples ((d : ℝ) * h) :=
    (AddSubgroup.closure_le _).2 hsubset
  have hhmem : h ∈ AddSubgroup.closure (Set.range S.halfLogRatio) := by
    rw [harith, AddSubgroup.mem_zmultiples_iff]
    exact ⟨1, by simp⟩
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (hle hhmem)
  have hzreal : (z : ℝ) * (d : ℝ) = 1 := by
    apply mul_right_cancel₀ hh.ne'
    simpa [zsmul_eq_mul, mul_assoc] using hz
  have hzint : z * (d : ℤ) = 1 := by exact_mod_cast hzreal
  have hdvdInt : (d : ℤ) ∣ 1 := ⟨z, by simpa [mul_comm] using hzint.symm⟩
  have hdvd : d ∣ 1 := by exact_mod_cast hdvdInt
  exact Nat.dvd_one.mp hdvd

end System

namespace DiscreteRenewal

/-- A finite, positive, aperiodic delay law on the natural numbers. -/
structure FiniteDelayLaw (iota : Type*) [Fintype iota] where
  lag : iota → ℕ
  lag_pos : ∀ i, 0 < lag i
  weight : iota → ℝ
  weight_pos : ∀ i, 0 < weight i
  sum_weight : ∑ i, weight i = 1
  lag_gcd : Nat.setGcd (Set.range lag) = 1

namespace FiniteDelayLaw

variable {iota : Type*} [Fintype iota] (F : FiniteDelayLaw iota)

/-- The discrete renewal masses, characterized by `u₀ = 1` and the usual
finite-delay renewal recurrence for positive indices. -/
noncomputable def renewalMass : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ i, if F.lag i ≤ n + 1 then
      F.weight i * renewalMass ((n + 1) - F.lag i) else 0
termination_by n => n
decreasing_by
  have := F.lag_pos i
  omega

@[simp]
theorem renewalMass_zero : F.renewalMass 0 = 1 := by
  rw [renewalMass]

theorem renewalMass_succ (n : ℕ) :
    F.renewalMass (n + 1) =
      ∑ i, if F.lag i ≤ n + 1 then
        F.weight i * F.renewalMass ((n + 1) - F.lag i) else 0 := by
  rw [renewalMass]

/-- Renewal masses are probabilities of hitting a lattice point, hence lie in
`[0,1]`.  The proof is the direct convex-recursion induction. -/
theorem renewalMass_mem_Icc (n : ℕ) : F.renewalMass n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [renewalMass_succ]
          constructor
          · exact Finset.sum_nonneg fun i _ ↦ by
              split
              · exact mul_nonneg (F.weight_pos i).le
                  (ih _ (by have := F.lag_pos i; omega)).1
              · exact le_rfl
          · calc
              ∑ i, (if F.lag i ≤ n + 1 then
                  F.weight i * F.renewalMass ((n + 1) - F.lag i) else 0) ≤
                  ∑ i, F.weight i * 1 := by
                apply Finset.sum_le_sum
                intro i _
                split
                · exact mul_le_mul_of_nonneg_left
                    (ih _ (by have := F.lag_pos i; omega)).2 (F.weight_pos i).le
                · simpa using (F.weight_pos i).le
              _ = 1 := by simpa using F.sum_weight

theorem renewalMass_nonneg (n : ℕ) : 0 ≤ F.renewalMass n :=
  (F.renewalMass_mem_Icc n).1

theorem renewalMass_le_one (n : ℕ) : F.renewalMass n ≤ 1 :=
  (F.renewalMass_mem_Icc n).2

/-- A convenient finite bound for all delays.  The sum, rather than the
maximum, makes the elementary proof independent of a choice of ordering on
the index type. -/
noncomputable def totalLag : ℕ := ∑ i, F.lag i

theorem lag_le_totalLag (i : iota) : F.lag i ≤ F.totalLag := by
  classical
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

theorem totalLag_pos [Nonempty iota] : 0 < F.totalLag := by
  classical
  let i : iota := Classical.choice inferInstance
  exact (F.lag_pos i).trans_le (F.lag_le_totalLag i)

/-- Above the largest delay, the defining recurrence is an honest convex
recurrence, with no truncated terms. -/
theorem renewalMass_eq_sum_of_totalLag_le [Nonempty iota] {n : ℕ}
    (hn : F.totalLag ≤ n) :
    F.renewalMass n = ∑ i, F.weight i * F.renewalMass (n - F.lag i) := by
  have hnpos : 0 < n := (F.totalLag_pos).trans_le hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  rw [renewalMass_succ]
  apply Finset.sum_congr rfl
  intro i _
  simp only [if_pos ((F.lag_le_totalLag i).trans hn)]

/-- If a bounded solution of the finite-delay equation approaches its limsup
along a cofinal sequence, then it also approaches the limsup one generating
delay earlier.  Positivity of every weight is the essential input. -/
theorem tendsto_limsup_along_sub_lag [Nonempty iota]
    {u : ℕ → ℝ} {r : ℕ → ℕ}
    (hub : IsBoundedUnder (· ≤ ·) atTop u)
    (hrec : ∀ {n : ℕ}, F.totalLag ≤ n →
      u n = ∑ k, F.weight k * u (n - F.lag k))
    (hrtop : Tendsto r atTop atTop)
    (hr : Tendsto (fun j ↦ u (r j)) atTop
      (𝓝 (limsup u atTop))) (i : iota) :
    Tendsto (fun j ↦ u (r j - F.lag i)) atTop
      (𝓝 (limsup u atTop)) := by
  let L : ℝ := limsup u atTop
  apply tendsto_order.2
  constructor
  · intro a ha
    let e : ℝ := L - a
    let p : ℝ := F.weight i
    let δ : ℝ := p * e / 4
    have he : 0 < e := sub_pos.mpr ha
    have hp : 0 < p := F.weight_pos i
    have hδ : 0 < δ := div_pos (mul_pos hp he) (by norm_num)
    have hpeak : ∀ᶠ j in atTop, L - δ < u (r j) := by
      have hnhds : Set.Ioi (L - δ) ∈ 𝓝 L := Ioi_mem_nhds (sub_lt_self L hδ)
      exact hr hnhds
    have huupper : ∀ᶠ n in atTop, u n < L + δ := by
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right L hδ) hub
    have hall : ∀ᶠ j in atTop, ∀ k : iota,
        u (r j - F.lag k) < L + δ := by
      rw [eventually_all]
      intro k
      exact ((tendsto_sub_atTop_nat (F.lag k)).comp hrtop) huupper
    have hlarge : ∀ᶠ j in atTop, F.totalLag ≤ r j :=
      hrtop (eventually_ge_atTop F.totalLag)
    filter_upwards [hpeak, hall, hlarge] with j hjpeak hjall hjlarge
    by_contra htarget
    have htarget' : u (r j - F.lag i) ≤ a := le_of_not_gt htarget
    have hnonneg : ∀ k ∈ (Finset.univ : Finset iota),
        0 ≤ F.weight k * (L + δ - u (r j - F.lag k)) := by
      intro k _
      exact mul_nonneg (F.weight_pos k).le (sub_nonneg.mpr (hjall k).le)
    have hselected :
        F.weight i * (L + δ - u (r j - F.lag i)) ≤
          ∑ k, F.weight k * (L + δ - u (r j - F.lag k)) :=
      Finset.single_le_sum hnonneg (Finset.mem_univ i)
    have hsum :
        (∑ k, F.weight k * (L + δ - u (r j - F.lag k))) =
          L + δ - u (r j) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, F.sum_weight, one_mul,
        ← hrec hjlarge]
    have hlower :
        p * (L + δ - a) ≤
          F.weight i * (L + δ - u (r j - F.lag i)) := by
      dsimp [p]
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_left htarget' (L + δ)) (F.weight_pos i).le
    have hdeficit : p * (L + δ - a) < 2 * δ := by
      calc
        p * (L + δ - a) ≤
            F.weight i * (L + δ - u (r j - F.lag i)) := hlower
        _ ≤ ∑ k, F.weight k * (L + δ - u (r j - F.lag k)) := hselected
        _ = L + δ - u (r j) := hsum
        _ < 2 * δ := by linarith
    have hleft : p * (L + δ - a) = p * e + p * δ := by
      dsimp [e]
      ring
    have hright : 2 * δ = p * e / 2 := by
      dsimp [δ]
      ring
    rw [hleft, hright] at hdeficit
    have hpe : 0 < p * e := mul_pos hp he
    have hpδ : 0 ≤ p * δ := mul_nonneg hp.le hδ.le
    linarith
  · intro b hb
    have huupper : ∀ᶠ n in atTop, u n < b :=
      eventually_lt_of_limsup_lt hb hub
    exact ((tendsto_sub_atTop_nat (F.lag i)).comp hrtop) huupper

/-- The preceding propagation can be iterated along every element of the
additive monoid generated by the delays. -/
theorem tendsto_limsup_along_sub_mem_closure [Nonempty iota]
    {u : ℕ → ℝ} {r : ℕ → ℕ}
    (hub : IsBoundedUnder (· ≤ ·) atTop u)
    (hrec : ∀ {n : ℕ}, F.totalLag ≤ n →
      u n = ∑ k, F.weight k * u (n - F.lag k))
    (hrtop : Tendsto r atTop atTop)
    (hr : Tendsto (fun j ↦ u (r j)) atTop
      (𝓝 (limsup u atTop))) {q : ℕ}
    (hq : q ∈ AddSubmonoid.closure (Set.range F.lag)) :
    Tendsto (fun j ↦ u (r j - q)) atTop
      (𝓝 (limsup u atTop)) := by
  induction hq using AddSubmonoid.closure_induction_right with
  | zero => simpa using hr
  | add_right x hx y hy ih =>
      obtain ⟨i, rfl⟩ := hy
      have hrtop' : Tendsto (fun j ↦ r j - x) atTop atTop :=
        (tendsto_sub_atTop_nat x).comp hrtop
      have ht := F.tendsto_limsup_along_sub_lag hub hrec hrtop' ih i
      simpa [Nat.sub_sub] using ht

/-- A lower bound on one complete delay window propagates forever through a
convex finite-delay recurrence. -/
theorem lower_bound_of_delay_block [Nonempty iota]
    {u : ℕ → ℝ} {b : ℕ} {a : ℝ}
    (hrec : ∀ {n : ℕ}, F.totalLag ≤ n →
      u n = ∑ k, F.weight k * u (n - F.lag k))
    (hblock : ∀ n, b ≤ n → n < b + F.totalLag → a ≤ u n) :
    ∀ n, b ≤ n → a ≤ u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hbn
      by_cases hnblock : n < b + F.totalLag
      · exact hblock n hbn hnblock
      · have hsum : F.totalLag ≤ n := by omega
        rw [hrec hsum]
        calc
          ∑ k, F.weight k * u (n - F.lag k) ≥
              ∑ k, F.weight k * a := by
            apply Finset.sum_le_sum
            intro k _
            apply mul_le_mul_of_nonneg_left _ (F.weight_pos k).le
            have hkpos := F.lag_pos k
            have hk := F.lag_le_totalLag k
            have hkn : F.lag k ≤ n := hk.trans hsum
            apply ih (n - F.lag k)
            · omega
            · omega
          _ = a := by
            rw [← Finset.sum_mul, F.sum_weight, one_mul]

/-- The renewal masses of a positive finite-support delay law of span one
converge.  This is the lattice renewal input needed by the tube theorem; no
spectral or Markov-chain result is imported. -/
theorem tendsto_renewalMass [Nonempty iota] :
    Tendsto F.renewalMass atTop
      (𝓝 (limsup F.renewalMass atTop)) := by
  let L : ℝ := limsup F.renewalMass atTop
  have hub : IsBoundedUnder (· ≤ ·) atTop F.renewalMass :=
    isBoundedUnder_of ⟨1, F.renewalMass_le_one⟩
  have hlb : IsBoundedUnder (· ≥ ·) atTop F.renewalMass :=
    isBoundedUnder_of ⟨0, F.renewalMass_nonneg⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop F.renewalMass :=
    hlb.isCoboundedUnder_le
  obtain ⟨r, hr, hrtop⟩ := exists_seq_tendsto_limsup hcob hub
  have hr' : Tendsto (fun j ↦ F.renewalMass (r j)) atTop (𝓝 L) := by
    simpa [L, Function.comp_def] using hr
  have hrec : ∀ {n : ℕ}, F.totalLag ≤ n →
      F.renewalMass n =
        ∑ k, F.weight k * F.renewalMass (n - F.lag k) := by
    intro n hn
    exact F.renewalMass_eq_sum_of_totalLag_le hn
  apply tendsto_order.2
  constructor
  · intro a ha
    let c : ℝ := (a + L) / 2
    have hac : a < c := by dsimp [c, L] at *; linarith
    have hcL : c < L := by dsimp [c, L] at *; linarith
    obtain ⟨Q, hQ⟩ := Nat.exists_mem_closure_of_ge (Set.range F.lag)
    have hmem {q : ℕ} (hq : Q ≤ q) :
        q ∈ AddSubmonoid.closure (Set.range F.lag) := by
      apply hQ q hq
      rw [F.lag_gcd]
      exact one_dvd q
    have hshift (q : ℕ) (hq : Q ≤ q) :
        Tendsto (fun j ↦ F.renewalMass (r j - q)) atTop (𝓝 L) := by
      exact F.tendsto_limsup_along_sub_mem_closure hub hrec hrtop hr'
        (hmem hq)
    have hall : ∀ᶠ j in atTop,
        ∀ q ∈ Finset.Icc Q (Q + F.totalLag),
          c < F.renewalMass (r j - q) := by
      rw [eventually_all_finset]
      intro q hq
      exact hshift q (Finset.mem_Icc.mp hq).1
        (Ioi_mem_nhds hcL)
    have hlarge : ∀ᶠ j in atTop, Q + F.totalLag ≤ r j :=
      hrtop (eventually_ge_atTop (Q + F.totalLag))
    obtain ⟨j, hjall, hjlarge⟩ := (hall.and hlarge).exists
    let b : ℕ := r j - (Q + F.totalLag)
    have hblock : ∀ n, b ≤ n → n < b + F.totalLag →
        c ≤ F.renewalMass n := by
      intro n hbn hn
      let q : ℕ := r j - n
      have hnle : n ≤ r j := by
        dsimp [b] at hbn hn ⊢
        omega
      have hqlo : Q ≤ q := by
        dsimp [q, b] at *
        omega
      have hqhi : q ≤ Q + F.totalLag := by
        dsimp [q, b] at *
        omega
      have hindex : r j - q = n := by
        dsimp [q]
        omega
      rw [← hindex]
      exact (hjall q (Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩)).le
    have hprop : ∀ n, b ≤ n → c ≤ F.renewalMass n :=
      F.lower_bound_of_delay_block hrec hblock
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hac.trans_le (hprop n hn)
  · intro d hd
    exact eventually_lt_of_limsup_lt hd hub

private theorem sum_range_ite_lag_le_sub
    (N lag : ℕ) (hlag : 0 < lag) (hle : lag ≤ N) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, if lag ≤ N - k then f k else 0) =
      ∑ k ∈ Finset.range (N - lag + 1), f k := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro k hk
    rfl

private theorem sum_range_ite_lag_convolution
    (N lag : ℕ) (hlag : 0 < lag) (hle : lag ≤ N)
    (w : ℝ) (u z : ℕ → ℝ) :
    (∑ k ∈ Finset.range N,
        if lag ≤ N - k then w * u (N - k - lag) * z k else 0) =
      w * (∑ k ∈ Finset.range (N - lag + 1),
        u (N - lag - k) * z k) := by
  calc
    _ = ∑ k ∈ Finset.range (N - lag + 1),
          w * u (N - k - lag) * z k :=
      sum_range_ite_lag_le_sub N lag hlag hle
        (fun k ↦ w * u (N - k - lag) * z k)
    _ = ∑ k ∈ Finset.range (N - lag + 1),
          w * (u (N - lag - k) * z k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Nat.sub_sub, Nat.add_comm]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- The exact finite renewal-series solution of a finite-delay equation. -/
theorem renewal_convolution_identity
    (x z : ℕ → ℝ)
    (hrec : ∀ n, x n =
      (∑ i, if F.lag i ≤ n then F.weight i * x (n - F.lag i) else 0) + z n) :
    ∀ n, x n = ∑ k ∈ Finset.range (n + 1),
      F.renewalMass (n - k) * z k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h N ih =>
      cases N with
      | zero =>
          rw [hrec]
          have hzero : (∑ i, if F.lag i ≤ 0 then
              F.weight i * x (0 - F.lag i) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [if_neg]
            exact Nat.not_le_of_lt (F.lag_pos i)
          rw [hzero, zero_add]
          simp
      | succ n =>
          let N : ℕ := n + 1
          rw [hrec]
          have hxexpand :
              (∑ i, if F.lag i ≤ N then
                  F.weight i * x (N - F.lag i) else 0) =
                ∑ i, if F.lag i ≤ N then
                  F.weight i *
                    (∑ k ∈ Finset.range (N - F.lag i + 1),
                      F.renewalMass (N - F.lag i - k) * z k) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs with hi
            · rw [ih (N - F.lag i)]
              have := F.lag_pos i
              omega
            · rfl
          rw [hxexpand]
          have hdouble :
              (∑ i, if F.lag i ≤ N then
                  F.weight i *
                    (∑ k ∈ Finset.range (N - F.lag i + 1),
                      F.renewalMass (N - F.lag i - k) * z k) else 0) =
                ∑ k ∈ Finset.range N,
                  F.renewalMass (N - k) * z k := by
            calc
              _ = ∑ i, ∑ k ∈ Finset.range N,
                    if F.lag i ≤ N - k then
                      F.weight i * F.renewalMass (N - k - F.lag i) * z k
                    else 0 := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases hi : F.lag i ≤ N
                · rw [if_pos hi]
                  exact (sum_range_ite_lag_convolution N (F.lag i)
                    (F.lag_pos i) hi (F.weight i) F.renewalMass z).symm
                · rw [if_neg hi]
                  symm
                  apply Finset.sum_eq_zero
                  intro k hk
                  rw [if_neg]
                  omega
              _ = ∑ k ∈ Finset.range N, ∑ i,
                    if F.lag i ≤ N - k then
                      F.weight i * F.renewalMass (N - k - F.lag i) * z k
                    else 0 := by
                rw [Finset.sum_comm]
              _ = _ := by
                apply Finset.sum_congr rfl
                intro k hk
                have hkN : k < N := Finset.mem_range.mp hk
                have hpos : 0 < N - k := by omega
                obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
                rw [hq, F.renewalMass_succ]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                simp only [Nat.succ_eq_add_one]
                split_ifs <;> ring
          rw [hdouble]
          have hlast :
              (∑ k ∈ Finset.range (N + 1),
                  F.renewalMass (N - k) * z k) =
                (∑ k ∈ Finset.range N,
                  F.renewalMass (N - k) * z k) + z N := by
            rw [show N + 1 = Nat.succ N by omega, Finset.sum_range_succ]
            rw [Nat.sub_self, F.renewalMass_zero, one_mul]
          exact hlast.symm

/-- Renewal masses extended by zero to negative integer indices. -/
noncomputable def intRenewalMass (n : ℤ) : ℝ :=
  if 0 ≤ n then F.renewalMass n.toNat else 0

theorem intRenewalMass_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    F.intRenewalMass n = F.renewalMass n.toNat := by
  simp [intRenewalMass, hn]

theorem intRenewalMass_of_neg {n : ℤ} (hn : n < 0) :
    F.intRenewalMass n = 0 := by
  simp [intRenewalMass, not_le.mpr hn]

theorem intRenewalMass_natCast (n : ℕ) :
    F.intRenewalMass (n : ℤ) = F.renewalMass n := by
  simp [intRenewalMass]

theorem intRenewalMass_natCast_sub {n k : ℕ} (hk : k ≤ n) :
    F.intRenewalMass ((n : ℤ) - (k : ℤ)) =
      F.renewalMass (n - k) := by
  have hnonneg : (0 : ℤ) ≤ (n : ℤ) - (k : ℤ) := by omega
  rw [F.intRenewalMass_of_nonneg hnonneg]
  congr 1
  omega

theorem abs_intRenewalMass_le_one (n : ℤ) :
    |F.intRenewalMass n| ≤ 1 := by
  by_cases hn : 0 ≤ n
  · rw [F.intRenewalMass_of_nonneg hn,
      abs_of_nonneg (F.renewalMass_nonneg n.toNat)]
    exact F.renewalMass_le_one _
  · rw [F.intRenewalMass_of_neg (lt_of_not_ge hn), abs_zero]
    norm_num

/-- Integer translates of the zero-extended renewal masses all have the same
limit.  The zero extension only affects finitely many indices. -/
theorem tendsto_intRenewalMass_shift [Nonempty iota] (k : ℤ) :
    Tendsto (fun n : ℕ ↦ F.intRenewalMass ((n : ℤ) - k)) atTop
      (𝓝 (limsup F.renewalMass atTop)) := by
  cases k with
  | ofNat q =>
      simp only [Int.ofNat_eq_natCast]
      have ht := F.tendsto_renewalMass.comp (tendsto_sub_atTop_nat q)
      apply ht.congr'
      filter_upwards [eventually_ge_atTop q] with n hn
      have hnonneg : (0 : ℤ) ≤ (n : ℤ) - (q : ℤ) := by omega
      simp only [Function.comp_apply]
      rw [F.intRenewalMass_of_nonneg hnonneg]
      congr 1
      omega
  | negSucc q =>
      have ht := F.tendsto_renewalMass.comp (tendsto_add_atTop_nat (q + 1))
      apply ht.congr'
      apply Eventually.of_forall
      intro n
      have hnonneg : (0 : ℤ) ≤ (n : ℤ) - Int.negSucc q := by omega
      simp only [Function.comp_apply]
      rw [F.intRenewalMass_of_nonneg hnonneg]
      congr 1

/-- For a forcing which vanishes on the negative half-line, the integer lattice
series with the zero-extended renewal masses is exactly its finite Cauchy sum. -/
theorem latticeSection_intRenewalMass_apply_eq_sum_range
    {h : ℝ} (hh : 0 < h) {z : ℝ → ℝ} (hz : Continuous z)
    (hz0 : ∀ v : ℝ, v ≤ 0 → z v = 0) (n : ℕ)
    (t : Set.Icc (0 : ℝ) h) :
    ArithmeticRenewal.latticeSection h z hz F.intRenewalMass n t =
      ∑ k ∈ Finset.range (n + 1),
        F.renewalMass (n - k) * z ((t : ℝ) + (k : ℝ) * h) := by
  have hout : ∀ k : ℤ, k ∉ Finset.Icc (0 : ℤ) (n : ℤ) →
      F.intRenewalMass ((n : ℤ) - k) •
          ArithmeticRenewal.forcingTranslate h z hz k = 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk' : k < 0 ∨ (n : ℤ) < k := by omega
    rcases hk' with hk | hk
    · have hforce : ArithmeticRenewal.forcingTranslate h z hz k = 0 := by
        ext t'
        simp only [ArithmeticRenewal.forcingTranslate_apply,
          ContinuousMap.zero_apply]
        apply hz0
        have hkreal : (k : ℝ) ≤ -1 := by
          exact_mod_cast (show k ≤ -1 by omega)
        nlinarith [t'.property.2]
      rw [hforce, smul_zero]
    · have hneg : (n : ℤ) - k < 0 := by omega
      rw [F.intRenewalMass_of_neg hneg, zero_smul]
  unfold ArithmeticRenewal.latticeSection
  rw [tsum_eq_sum hout]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ArithmeticRenewal.forcingTranslate_apply, smul_eq_mul]
  rw [Int.Icc_eq_finset_map]
  simp only [sub_zero, Int.toNat_natCast_add_one,
    Finset.sum_map, Function.Embedding.coe_trans, Function.comp_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    simp only [Finset.mem_range] at hk
    omega
  change F.intRenewalMass ((n : ℤ) - (k : ℤ)) *
      z ((t : ℝ) + (k : ℝ) * h) = _
  rw [F.intRenewalMass_natCast_sub hkn]

end FiniteDelayLaw

end DiscreteRenewal

namespace System

variable {iota : Type*} [Fintype iota] (S : BrownianImages.System iota)

/-- The finite aperiodic integer delay law induced by an arithmetic tube-renewal
system at its maximal span. -/
noncomputable def tubeDelayLaw [Nonempty iota] {s h : ℝ}
    (hdim : S.IsDimension s) (hh : 0 < h) (harith : S.TubeArithmetic h) :
    DiscreteRenewal.FiniteDelayLaw iota where
  lag := S.tubeLag hh harith
  lag_pos := S.tubeLag_pos hh harith
  weight := S.tubeWeight s
  weight_pos := S.tubeWeight_pos s
  sum_weight := S.sum_tubeWeight hdim
  lag_gcd := S.setGcd_range_tubeLag_eq_one hh harith

/-- On each arithmetic phase, the cutoff profile is the finite convolution of
the cutoff forcing with the renewal masses of the induced integer delay law. -/
theorem cutoffRescaledTubeProfile_phase_eq_renewal_sum
    [Nonempty iota] {s h : ℝ} (hdim : S.IsDimension s)
    (hh : 0 < h) (harith : S.TubeArithmetic h)
    {m : ℝ → ℝ} (t : Set.Icc (0 : ℝ) h) (n : ℕ) :
    cutoffRescaledTubeProfile m
        (2 * ((t : ℝ) + (n : ℝ) * h)) =
      ∑ k ∈ Finset.range (n + 1),
        (S.tubeDelayLaw hdim hh harith).renewalMass (n - k) *
          S.halfScaleCutoffTubeRenewalForcing s m
            ((t : ℝ) + (k : ℝ) * h) := by
  let F := S.tubeDelayLaw hdim hh harith
  let x : ℕ → ℝ := fun q ↦ cutoffRescaledTubeProfile m
    (2 * ((t : ℝ) + (q : ℝ) * h))
  let z : ℕ → ℝ := fun q ↦ S.halfScaleCutoffTubeRenewalForcing s m
    ((t : ℝ) + (q : ℝ) * h)
  have hlog (i : iota) :
      S.logRatio i = 2 * (S.tubeLag hh harith i : ℝ) * h := by
    have hi := S.halfLogRatio_eq_tubeLag_mul hh harith i
    simp only [halfLogRatio] at hi
    linarith
  have hrec : ∀ q, x q =
      (∑ i, if F.lag i ≤ q then F.weight i * x (q - F.lag i) else 0) + z q := by
    intro q
    have hbase : x q =
        (∑ i, S.tubeWeight s i * cutoffRescaledTubeProfile m
          (2 * ((t : ℝ) + (q : ℝ) * h) - S.logRatio i)) + z q := by
      dsimp [x, z, System.halfScaleCutoffTubeRenewalForcing]
      rw [System.cutoffTubeRenewalForcing]
      unfold System.renewalConv System.tubeWeight
      ring
    rw [hbase]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change S.tubeWeight s i * cutoffRescaledTubeProfile m
        (2 * ((t : ℝ) + (q : ℝ) * h) - S.logRatio i) =
      if S.tubeLag hh harith i ≤ q then
        S.tubeWeight s i * x (q - S.tubeLag hh harith i) else 0
    by_cases hi : S.tubeLag hh harith i ≤ q
    · rw [if_pos hi]
      congr 2
      rw [hlog i, Nat.cast_sub hi]
      ring
    · rw [if_neg hi]
      have harg :
          2 * ((t : ℝ) + (q : ℝ) * h) - S.logRatio i ≤ 0 := by
        rw [hlog i]
        have hilower : q + 1 ≤ S.tubeLag hh harith i := by omega
        have hilowerReal : (q : ℝ) + 1 ≤
            (S.tubeLag hh harith i : ℝ) := by exact_mod_cast hilower
        nlinarith [t.property.2]
      rw [cutoffRescaledTubeProfile, tubeRenewalCutoff_eq_zero_of_nonpos harg,
        zero_mul, mul_zero]
  change x n = _
  exact F.renewal_convolution_identity x z hrec n

/-- The preceding finite convolution is exactly the continuous-map lattice
section used by the uniform arithmetic renewal theorem. -/
theorem cutoffRescaledTubeProfile_phase_eq_latticeSection
    [Nonempty iota] {s h : ℝ} (hdim : S.IsDimension s)
    (hh : 0 < h) (harith : S.TubeArithmetic h)
    {m : ℝ → ℝ} (hm : Continuous m)
    (t : Set.Icc (0 : ℝ) h) (n : ℕ) :
    cutoffRescaledTubeProfile m
        (2 * ((t : ℝ) + (n : ℝ) * h)) =
      ArithmeticRenewal.latticeSection h
        (S.halfScaleCutoffTubeRenewalForcing s m)
        (S.continuous_halfScaleCutoffTubeRenewalForcing hm)
        (S.tubeDelayLaw hdim hh harith).intRenewalMass n t := by
  let F := S.tubeDelayLaw hdim hh harith
  calc
    cutoffRescaledTubeProfile m (2 * ((t : ℝ) + (n : ℝ) * h)) =
        ∑ k ∈ Finset.range (n + 1),
          F.renewalMass (n - k) *
            S.halfScaleCutoffTubeRenewalForcing s m
              ((t : ℝ) + (k : ℝ) * h) :=
      S.cutoffRescaledTubeProfile_phase_eq_renewal_sum hdim hh harith t n
    _ = ArithmeticRenewal.latticeSection h
        (S.halfScaleCutoffTubeRenewalForcing s m)
        (S.continuous_halfScaleCutoffTubeRenewalForcing hm)
        F.intRenewalMass n t := by
      symm
      exact F.latticeSection_intRenewalMass_apply_eq_sum_range hh
        (S.continuous_halfScaleCutoffTubeRenewalForcing hm)
        (fun v hv ↦ S.halfScaleCutoffTubeRenewalForcing_eq_zero_of_nonpos hv)
        n t

/-- The original profile agrees eventually, uniformly in the phase, with its
exact lattice renewal series.  The only threshold comes from passing the fixed
cutoff transition. -/
theorem exists_eventual_profile_eq_latticeSection
    [Nonempty iota] {s h : ℝ} (hdim : S.IsDimension s)
    (hh : 0 < h) (harith : S.TubeArithmetic h)
    {m : ℝ → ℝ} (hm : Continuous m) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ t : Set.Icc (0 : ℝ) h,
        m ((t : ℝ) + (n : ℝ) * h) =
          ArithmeticRenewal.latticeSection h
            (S.halfScaleCutoffTubeRenewalForcing s m)
            (S.continuous_halfScaleCutoffTubeRenewalForcing hm)
            (S.tubeDelayLaw hdim hh harith).intRenewalMass n t := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1 / (2 * h))
  refine ⟨N₀, ?_⟩
  intro n hn t
  have htwoh : 0 < 2 * h := mul_pos (by norm_num) hh
  have hcutN : 1 ≤ 2 * (N₀ : ℝ) * h := by
    calc
      1 = (1 / (2 * h)) * (2 * h) := by field_simp
      _ ≤ (N₀ : ℝ) * (2 * h) :=
        mul_le_mul_of_nonneg_right hN₀ htwoh.le
      _ = 2 * (N₀ : ℝ) * h := by ring
  have hnreal : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hy : 1 ≤ 2 * ((t : ℝ) + (n : ℝ) * h) := by
    nlinarith [t.property.1]
  calc
    m ((t : ℝ) + (n : ℝ) * h) =
        cutoffRescaledTubeProfile m
          (2 * ((t : ℝ) + (n : ℝ) * h)) := by
      rw [cutoffRescaledTubeProfile_eq_of_one_le hy]
      congr 1
      ring
    _ = _ :=
      S.cutoffRescaledTubeProfile_phase_eq_latticeSection
        hdim hh harith hm t n

/-- **Arithmetic tube-renewal theorem with no discrete hypotheses.**  The
integer delay law, its bounded renewal masses, their shifted limit, and the
exact lattice-series identity are all supplied internally. -/
theorem exists_periodic_limit_of_tubeArithmetic
    [Nonempty iota] {s h : ℝ} (hh : 0 < h) (harith : S.TubeArithmetic h)
    (hdim : S.IsDimension s) {m d : ℝ → ℝ}
    {A D γ c : ℝ} (hm : Continuous m)
    (hA : ∀ v : ℝ, 0 ≤ v → |m v| ≤ A)
    (hD : 0 ≤ D) (hγ : 0 < γ)
    (hrenew : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      m v = S.tubeRenewalConv s m v - d v)
    (hdefect : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      0 ≤ d v ∧ d v ≤ D * Real.exp (-γ * v))
    (hc : 0 < c) (hmc : ∀ v : ℝ, 0 ≤ v → c ≤ m v ∧ m v ≤ A) :
    ∃ P : ℝ → ℝ, Continuous P ∧ Function.Periodic P h ∧
      (∃ c₀ C₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ P t ∧ P t ≤ C₀) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t ∈ Set.Icc (0 : ℝ) h,
          |m (t + (n : ℝ) * h) - P t| ≤ ε := by
  let F := S.tubeDelayLaw hdim hh harith
  exact S.exists_periodic_limit_of_tubeArithmetic_of_discrete_renewal
    hh harith hdim (m := m) (d := d) hm hA hD hγ hrenew hdefect hc hmc
    (u := F.intRenewalMass) (B := 1)
    (ℓ := limsup F.renewalMass atTop) (by norm_num)
    F.abs_intRenewalMass_le_one F.tendsto_intRenewalMass_shift
    (fun _ ↦ S.exists_eventual_profile_eq_latticeSection hdim hh harith hm)

end System

/-- **Unconditional arithmetic-periodic convergence for the mean Brownian tube
profile.**  All lattice renewal inputs are discharged by the finite-delay law
constructed from `TubeArithmetic`. -/
theorem System.IsNatural.meanBrownianTubeProfile_periodic_limit_of_tubeArithmetic
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota] [Nonempty iota]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (S : System iota)
    {K : Set ℝ} {s h : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hdim : S.IsDimension s)
    (hh : 0 < h) (harith : S.TubeArithmetic h)
    (hm : Continuous
      (meanBrownianTubeProfile W P hmu.compactAttractor s))
    {c A D γ : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hγ : 0 < γ)
    (hbounds : ∀ v : ℝ, 0 ≤ v →
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s v ∧
      meanBrownianTubeProfile W P hmu.compactAttractor s v ≤ A)
    (hrenew : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      meanBrownianTubeProfile W P hmu.compactAttractor s v =
        S.tubeRenewalConv s
          (meanBrownianTubeProfile W P hmu.compactAttractor s) v -
          hmu.meanBrownianTubeDefectProfile S W P v)
    (hdefect : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      0 ≤ hmu.meanBrownianTubeDefectProfile S W P v ∧
      hmu.meanBrownianTubeDefectProfile S W P v ≤
        D * Real.exp (-γ * v)) :
    ∃ PK : ℝ → ℝ, Continuous PK ∧ Function.Periodic PK h ∧
      (∃ c₀ C₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ PK t ∧ PK t ≤ C₀) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t ∈ Set.Icc (0 : ℝ) h,
          |meanBrownianTubeProfile W P hmu.compactAttractor s
              (t + (n : ℝ) * h) - PK t| ≤ ε := by
  let m : ℝ → ℝ := meanBrownianTubeProfile W P hmu.compactAttractor s
  let d : ℝ → ℝ := hmu.meanBrownianTubeDefectProfile S W P
  have hAabs : ∀ v : ℝ, 0 ≤ v → |m v| ≤ A := by
    intro v hv
    rw [abs_of_nonneg (meanBrownianTubeProfile_nonneg W P
      hmu.compactAttractor s v)]
    exact (hbounds v hv).2
  exact S.exists_periodic_limit_of_tubeArithmetic
    hh harith hdim (m := m) (d := d) hm hAabs hD hγ
    (fun v hv ↦ hrenew v hv) (fun v hv ↦ hdefect v hv)
    hc (fun v hv ↦ hbounds v hv)

end

end BrownianImages
