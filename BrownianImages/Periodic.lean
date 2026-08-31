/-
`sec:renewal`: the continuous periodic extension `G̃_A`.

The paper takes the continuous `p`-periodic extension of `G_A` from one period
`[p, 2p]`, which is legitimate exactly because the shift identity `eq:g-recursion` makes
the two endpoint values agree.  This module supplies that extension in general, by
lifting through `AddCircle p`, together with the elementary period arithmetic the
lattice case needs.

* `exists_period_representative`, `exists_nat_sub_mem_Ico`: every window of length `p`
  meets every residue class modulo `p`, in the two directions the proofs use.
* `shift_add_nsmul`: a shift identity above a threshold iterates upward.
* `exists_periodic_extension`: a function continuous on `[a, a+p]` with equal endpoint
  values extends to a continuous `p`-periodic function on the line.
* `exists_periodic_extension_of_shift`: the shape `sec:renewal` uses, where the shift
  identity supplies the endpoint condition and the extension agrees with the original
  function on the whole half line `[a, ∞)`.
-/
import BrownianImages.Defs

namespace BrownianImages

/-! ### Period arithmetic -/

/-- Every window of length `p` above `a` contains a point congruent to `a` modulo `p`. -/
theorem exists_period_representative {p a w : ℝ} (hp : 0 < p) (haw : a ≤ w + p) :
    ∃ n : ℕ, a + n * p ∈ Set.Icc w (w + p) := by
  by_cases h : w ≤ a
  · exact ⟨0, by simp only [Set.mem_Icc, Nat.cast_zero, zero_mul, add_zero]; exact ⟨h, haw⟩⟩
  · rw [not_le] at h
    have hx0 : 0 ≤ (w - a) / p := div_nonneg (by linarith) hp.le
    refine ⟨⌈(w - a) / p⌉₊, ?_⟩
    simp only [Set.mem_Icc]
    constructor
    · have h2 : w - a ≤ (⌈(w - a) / p⌉₊ : ℝ) * p :=
        (div_le_iff₀ hp).mp (Nat.le_ceil ((w - a) / p))
      linarith
    · have h1 : ((⌈(w - a) / p⌉₊ : ℕ) : ℝ) < (w - a) / p + 1 := Nat.ceil_lt_add_one hx0
      have h2 : ((⌈(w - a) / p⌉₊ : ℕ) : ℝ) * p < ((w - a) / p + 1) * p :=
        mul_lt_mul_of_pos_right h1 hp
      have h3 : ((w - a) / p + 1) * p = (w - a) + p := by field_simp
      rw [h3] at h2
      linarith

/-- Every point above `a` can be pulled back into `[a, a+p)` by a whole number of
periods. -/
theorem exists_nat_sub_mem_Ico {p a w : ℝ} (hp : 0 < p) (hw : a ≤ w) :
    ∃ n : ℕ, w - n * p ∈ Set.Ico a (a + p) := by
  have hx0 : 0 ≤ (w - a) / p := div_nonneg (by linarith) hp.le
  refine ⟨⌊(w - a) / p⌋₊, ?_⟩
  simp only [Set.mem_Ico]
  constructor
  · have h1 : ((⌊(w - a) / p⌋₊ : ℕ) : ℝ) ≤ (w - a) / p := Nat.floor_le hx0
    have h2 : ((⌊(w - a) / p⌋₊ : ℕ) : ℝ) * p ≤ w - a := by
      have := mul_le_mul_of_nonneg_right h1 hp.le
      rwa [div_mul_cancel₀ _ hp.ne'] at this
    linarith
  · have h1 : (w - a) / p < ((⌊(w - a) / p⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : w - a < (((⌊(w - a) / p⌋₊ : ℕ) : ℝ) + 1) * p := by
      have := mul_lt_mul_of_pos_right h1 hp
      rwa [div_mul_cancel₀ _ hp.ne'] at this
    nlinarith

/-- A shift identity above `c` iterates upward. -/
theorem shift_add_nsmul {p c : ℝ} (hp : 0 < p) {f : ℝ → ℝ}
    (hshift : ∀ w, c ≤ w → f w = f (w - p)) {w : ℝ} (hw : c - p ≤ w) :
    ∀ n : ℕ, f (w + n * p) = f w := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n : ℝ) * p := by positivity
      have hcast : w + ((n + 1 : ℕ) : ℝ) * p = (w + (n : ℝ) * p) + p := by push_cast; ring
      have hge : c ≤ (w + (n : ℝ) * p) + p := by linarith
      rw [hcast, hshift _ hge, add_sub_cancel_right]
      exact ih

/-! ### The extension -/

/-- A function continuous on a closed period and agreeing at its two ends extends to a
continuous periodic function on the line. -/
theorem exists_periodic_extension {p a : ℝ} (hp : 0 < p) {f : ℝ → ℝ}
    (hends : f a = f (a + p)) (hcont : ContinuousOn f (Set.Icc a (a + p))) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g p ∧
      ∀ w ∈ Set.Icc a (a + p), g w = f w := by
  haveI : Fact (0 < p) := ⟨hp⟩
  refine ⟨fun w => AddCircle.liftIco p a f (w : AddCircle p), ?_, ?_, ?_⟩
  · exact (AddCircle.liftIco_continuous hends hcont).comp (AddCircle.continuous_mk' (p := p))
  · intro w
    show AddCircle.liftIco p a f ((w + p : ℝ) : AddCircle p)
      = AddCircle.liftIco p a f ((w : ℝ) : AddCircle p)
    rw [AddCircle.coe_add_period p w]
  · intro w hw
    rcases lt_or_eq_of_le hw.2 with h | h
    · exact AddCircle.liftIco_coe_apply ⟨hw.1, h⟩
    · show AddCircle.liftIco p a f ((w : ℝ) : AddCircle p) = f w
      have hcoe : ((w : ℝ) : AddCircle p) = ((a : ℝ) : AddCircle p) := by
        rw [h, AddCircle.coe_add_period p a]
      rw [hcoe, AddCircle.liftIco_coe_apply (a := a) (Set.mem_Ico.mpr ⟨le_rfl, by linarith⟩),
        hends, ← h]

/-- The shape `sec:renewal` uses: a function satisfying the shift identity above `a + p`
extends to a continuous `p`-periodic function agreeing with it on the whole of
`[a, ∞)`.  This is `G̃_A`, the continuous `log 3`-periodic extension of `G_A`. -/
theorem exists_periodic_extension_of_shift {p a : ℝ} (hp : 0 < p) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici a))
    (hshift : ∀ w, a + p ≤ w → f w = f (w - p)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g p ∧ ∀ w, a ≤ w → g w = f w := by
  have hends : f a = f (a + p) := by
    have := hshift (a + p) le_rfl
    rw [this, add_sub_cancel_right]
  obtain ⟨g, hg, hgper, hgeq⟩ :=
    exists_periodic_extension hp hends (hcont.mono Set.Icc_subset_Ici_self)
  refine ⟨g, hg, hgper, ?_⟩
  intro w hw
  obtain ⟨n, hn⟩ := exists_nat_sub_mem_Ico (p := p) (a := a) hp hw
  have hgn : g (w - n * p) = g w := by
    have h := (hgper.nat_mul n) (w - n * p)
    rw [sub_add_cancel] at h
    exact h.symm
  have hfn : f (w - n * p + n * p) = f (w - n * p) :=
    shift_add_nsmul hp hshift (by linarith [hn.1]) n
  rw [sub_add_cancel] at hfn
  rw [← hgn, hgeq _ ⟨hn.1, le_of_lt hn.2⟩, hfn]

end BrownianImages
