/-
`sec:reconstruction`, `thm:neighbourhood-concentration` of
`BrownianImagesComplete.tex`: the deterministic delayed contraction argument.

The probabilistic estimates produce a nonnegative profile satisfying a square-root
recurrence with positive delays.  The squared cylinder weights sum to less than one.
After choosing a smaller exponential rate, the shifted squared weights still sum to
less than one.  Induction in blocks shorter than every delay then bounds the
exponentially weighted profile.

* `MinkowskiContraction.exists_shifted_contraction_exponent`: choose the smaller
  exponential rate.
* `MinkowskiContraction.exp_mul_sqrt_sum_le`: the weighted `L²` estimate used at one
  step of the recurrence.
* `MinkowskiContraction.exponential_decay_of_delayed_sqrt_recurrence`: exponential
  decay from the delayed recurrence and a bounded initial interval.
-/
import BrownianImages.Defs

namespace BrownianImages

open scoped BigOperators

namespace MinkowskiContraction

variable {ι : Type*} [Fintype ι]

/-- If the squared weights sum to less than one, then after choosing a sufficiently
small positive exponent the delay-shifted squared weights still sum to less than one.
The exponent can simultaneously be chosen below any prescribed positive error-decay
rate. -/
theorem exists_shifted_contraction_exponent (p beta : ι → ℝ) {η : ℝ} (hη : 0 < η)
    (hsq : ∑ i, (p i) ^ 2 < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < η ∧
      ∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i) < 1 := by
  let shifted : ℝ → ℝ := fun γ ↦ ∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i)
  have hcontinuous : Continuous shifted := by
    unfold shifted
    fun_prop
  have hzero : shifted 0 < 1 := by
    simpa [shifted] using hsq
  have hnhds : {x : ℝ | shifted x < 1} ∈ nhds (0 : ℝ) :=
    (isOpen_lt hcontinuous continuous_const).mem_nhds hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let γ : ℝ := min (ε / 2) (η / 2)
  have hγ : 0 < γ := lt_min (by linarith) (by linarith)
  have hγε : γ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hγη : γ < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨γ, hγ, hγη, ?_⟩
  exact hball (by simpa [Real.dist_eq, abs_of_nonneg hγ.le] using hγε)

/-- Multiplying a delayed `L²` combination by `exp (γ v)` inserts the factor
`exp (2 γ β_i)` into its squared weights.  If every exponentially weighted delayed
term is at most `M`, the whole combination is at most the shifted `L²` norm of the
weights times `M`. -/
theorem exp_mul_sqrt_sum_le (p beta x : ι → ℝ) {v γ M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ i, 0 ≤ x i)
    (hbound : ∀ i, Real.exp (γ * (v - beta i)) * x i ≤ M) :
    Real.exp (γ * v) * Real.sqrt (∑ i, (p i * x i) ^ 2) ≤
      Real.sqrt (∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i)) * M := by
  have hsum : 0 ≤ ∑ i, (p i * x i) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hshift : 0 ≤ ∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i) :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hleft : 0 ≤ Real.exp (γ * v) * Real.sqrt (∑ i, (p i * x i) ^ 2) :=
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hright :
      0 ≤ Real.sqrt (∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i)) * M :=
    mul_nonneg (Real.sqrt_nonneg _) hM
  apply (sq_le_sq₀ hleft hright).mp
  rw [mul_pow, Real.sq_sqrt hsum, mul_pow, Real.sq_sqrt hshift]
  have hexp_sq (y : ℝ) : Real.exp y ^ 2 = Real.exp (2 * y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp_sq]
  calc
    Real.exp (2 * (γ * v)) * ∑ i, (p i * x i) ^ 2 =
        ∑ i, Real.exp (2 * (γ * v)) * (p i * x i) ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i, ((p i) ^ 2 * Real.exp (2 * γ * beta i)) * M ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hweighted_nonneg : 0 ≤ Real.exp (γ * (v - beta i)) * x i :=
        mul_nonneg (Real.exp_pos _).le (hx i)
      have hsquare : (Real.exp (γ * (v - beta i)) * x i) ^ 2 ≤ M ^ 2 :=
        (sq_le_sq₀ hweighted_nonneg hM).mpr (hbound i)
      have hexp_split :
          Real.exp (2 * (γ * v)) =
            Real.exp (2 * γ * beta i) * Real.exp (2 * (γ * (v - beta i))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (2 * (γ * v)) * (p i * x i) ^ 2 =
            ((p i) ^ 2 * Real.exp (2 * γ * beta i)) *
              (Real.exp (γ * (v - beta i)) * x i) ^ 2 := by
                rw [hexp_split, mul_pow, mul_pow, hexp_sq]
                ring
        _ ≤ ((p i) ^ 2 * Real.exp (2 * γ * beta i)) * M ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare
            (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    _ = (∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i)) * M ^ 2 := by
      rw [Finset.sum_mul]

/-- A nonnegative profile satisfying a delayed square-root recurrence with exponentially
decaying error itself decays exponentially.

The constants `delta` and `b` are common lower and upper bounds for the positive
delays.  The recurrence is needed only after `b`, while `B` bounds the initial interval
`[0,b]`.  The conclusion uses any `gamma < eta` for which the delay-shifted squared
weights still form a strict contraction. -/
theorem exponential_decay_of_delayed_sqrt_recurrence [Nonempty ι]
    (p beta : ι → ℝ) (a : ℝ → ℝ)
    {delta b B E η γ : ℝ} (hp : ∀ i, 0 < p i) (hdelta : 0 < delta)
    (hbeta_lower : ∀ i, delta ≤ beta i) (hbeta_upper : ∀ i, beta i ≤ b)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hγ : 0 < γ) (hγη : γ < η)
    (hcontract : ∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i) < 1)
    (ha : ∀ v, 0 ≤ a v)
    (hbase : ∀ v, 0 ≤ v → v ≤ b → a v ≤ B)
    (hrec : ∀ v, b ≤ v →
      a v ≤ Real.sqrt (∑ i, (p i * a (v - beta i)) ^ 2) + E * Real.exp (-η * v)) :
    ∃ C ≥ 0, ∀ v ≥ 0, a v ≤ C * Real.exp (-γ * v) := by
  let shifted : ℝ := ∑ i, (p i) ^ 2 * Real.exp (2 * γ * beta i)
  let q : ℝ := Real.sqrt shifted
  have hshifted : 0 ≤ shifted := by
    unfold shifted
    exact Finset.sum_nonneg fun _ _ ↦
      mul_nonneg (pow_nonneg (hp _).le _) (Real.exp_pos _).le
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    unfold q
    have hlt : shifted < 1 := by simpa [shifted] using hcontract
    simpa using Real.sqrt_lt_sqrt hshifted hlt
  have honeq : 0 < 1 - q := sub_pos.mpr hq1
  let M : ℝ := max (Real.exp (γ * b) * B) (E / (1 - q))
  have hM0 : 0 ≤ M := by
    unfold M
    exact le_max_of_le_left (mul_nonneg (Real.exp_pos _).le hB)
  have hinitial : Real.exp (γ * b) * B ≤ M := le_max_left _ _
  have herror_fraction : E / (1 - q) ≤ M := le_max_right _ _
  have herror : E ≤ (1 - q) * M := by
    calc
      E = (1 - q) * (E / (1 - q)) := by
        field_simp
      _ ≤ (1 - q) * M :=
        mul_le_mul_of_nonneg_left herror_fraction honeq.le
  have hclose : q * M + E ≤ M := by
    nlinarith
  have hblocks : ∀ n : ℕ, ∀ v : ℝ, 0 ≤ v →
      v ≤ b + n * delta → Real.exp (γ * v) * a v ≤ M := by
    intro n
    induction n with
    | zero =>
        intro v hv0 hvb
        simp only [Nat.cast_zero, zero_mul, add_zero] at hvb
        calc
          Real.exp (γ * v) * a v ≤ Real.exp (γ * v) * B :=
            mul_le_mul_of_nonneg_left (hbase v hv0 hvb) (Real.exp_pos _).le
          _ ≤ Real.exp (γ * b) * B := by
            exact mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvb hγ.le)) hB
          _ ≤ M := hinitial
    | succ n ih =>
        intro v hv0 hvupper
        by_cases hold : v ≤ b + n * delta
        · exact ih v hv0 hold
        · have hndelta : 0 ≤ (n : ℝ) * delta :=
            mul_nonneg (Nat.cast_nonneg _) hdelta.le
          have hvb : b ≤ v := by linarith
          have hvupper' : v ≤ b + n * delta + delta := by
            norm_num [Nat.cast_add, Nat.cast_one] at hvupper ⊢
            linarith
          have hprev0 : ∀ i, 0 ≤ v - beta i := by
            intro i
            linarith [hbeta_upper i]
          have hprev_upper : ∀ i, v - beta i ≤ b + n * delta := by
            intro i
            linarith [hbeta_lower i]
          have hprev : ∀ i, Real.exp (γ * (v - beta i)) * a (v - beta i) ≤ M :=
            fun i ↦ ih (v - beta i) (hprev0 i) (hprev_upper i)
          have hsqrt :
              Real.exp (γ * v) * Real.sqrt (∑ i, (p i * a (v - beta i)) ^ 2) ≤
                q * M := by
            exact exp_mul_sqrt_sum_le p beta (fun i ↦ a (v - beta i)) hM0
              (fun i ↦ ha _) hprev
          have hexp_error :
              Real.exp (γ * v) * (E * Real.exp (-η * v)) ≤ E := by
            have hexponent : (γ - η) * v ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hγη.le) hv0
            calc
              Real.exp (γ * v) * (E * Real.exp (-η * v)) =
                  E * (Real.exp (γ * v) * Real.exp (-η * v)) := by ring
              _ = E * Real.exp (γ * v + (-η * v)) := by
                rw [Real.exp_add]
              _ = E * Real.exp ((γ - η) * v) := by
                congr 2
                ring
              _ ≤ E * 1 :=
                mul_le_mul_of_nonneg_left
                  ((Real.exp_le_one_iff).mpr hexponent) hE
              _ = E := mul_one E
          calc
            Real.exp (γ * v) * a v ≤
                Real.exp (γ * v) *
                  (Real.sqrt (∑ i, (p i * a (v - beta i)) ^ 2) +
                    E * Real.exp (-η * v)) :=
              mul_le_mul_of_nonneg_left (hrec v hvb) (Real.exp_pos _).le
            _ = Real.exp (γ * v) *
                  Real.sqrt (∑ i, (p i * a (v - beta i)) ^ 2) +
                Real.exp (γ * v) * (E * Real.exp (-η * v)) := by ring
            _ ≤ q * M + E := add_le_add hsqrt hexp_error
            _ ≤ M := hclose
  refine ⟨M, hM0, ?_⟩
  intro v hv0
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge ((v - b) / delta)
  have hvupper : v ≤ b + n * delta := by
    have hmul := (div_le_iff₀ hdelta).mp hn
    linarith
  have hweighted := hblocks n v hv0 hvupper
  calc
    a v = Real.exp (-γ * v) * (Real.exp (γ * v) * a v) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-γ * v) * M :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
    _ = M * Real.exp (-γ * v) := mul_comm _ _

/-- Combined form of the contraction step.  Positive weights with squared sum below
one, positive delays lying in `[delta,b]`, a bounded initial interval, and an
`exp (-η v)` recurrence error imply exponential decay for some rate
`0 < γ < η`. -/
theorem exists_exponential_decay_of_delayed_sqrt_recurrence [Nonempty ι]
    (p beta : ι → ℝ) (a : ℝ → ℝ)
    {delta b B E η : ℝ} (hp : ∀ i, 0 < p i) (hdelta : 0 < delta)
    (hbeta_lower : ∀ i, delta ≤ beta i) (hbeta_upper : ∀ i, beta i ≤ b)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hη : 0 < η) (hsq : ∑ i, (p i) ^ 2 < 1)
    (ha : ∀ v, 0 ≤ a v)
    (hbase : ∀ v, 0 ≤ v → v ≤ b → a v ≤ B)
    (hrec : ∀ v, b ≤ v →
      a v ≤ Real.sqrt (∑ i, (p i * a (v - beta i)) ^ 2) + E * Real.exp (-η * v)) :
    ∃ γ : ℝ, 0 < γ ∧ γ < η ∧
      ∃ C ≥ 0, ∀ v ≥ 0, a v ≤ C * Real.exp (-γ * v) := by
  obtain ⟨γ, hγ, hγη, hcontract⟩ :=
    exists_shifted_contraction_exponent p beta hη hsq
  obtain ⟨C, hC, hdecay⟩ := exponential_decay_of_delayed_sqrt_recurrence
    p beta a hp hdelta hbeta_lower hbeta_upper hB hE hγ hγη hcontract ha hbase hrec
  exact ⟨γ, hγ, hγη, C, hC, hdecay⟩

end MinkowskiContraction

end BrownianImages
