/-
Riemann-sum bounds used in `thm:main-term-derivative`: for a `C¹` function `h` on
`[T, ∞)` with `h` and `h'` integrable, the sum `∑_{m≥1} T h(mT)` differs from `∫_T^∞ h`
by at most `T ∫_T^∞ |h'|`; for a non-negative antitone `h`, the sum lies between
`∫_T^∞ h` and `∫_T^∞ h + T h(T)`.  The index `m ≥ 1` is written `m + 1` over `m : ℕ`.

* `iUnion_cell_eq_Ioi`, `pairwise_disjoint_cell`: the cells `((m+1)T, (m+2)T]` partition
  `(T, ∞)`.
* `abs_mul_sub_integral_le`: the one-cell estimate.
* `abs_tsum_sub_integral_le`: the summed estimate, with the summability it needs.
* `tsum_le_integral_add`: the antitone bounds.
-/
import Mathlib

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

/-- The cell `((m+1)T, (m+2)T]`. -/
def cell (T : ℝ) (m : ℕ) : Set ℝ := Ioc (((m:ℝ) + 1) * T) (((m:ℝ) + 2) * T)

theorem measurableSet_cell (T : ℝ) (m : ℕ) : MeasurableSet (cell T m) := measurableSet_Ioc

theorem cell_eq (T : ℝ) (m : ℕ) :
    cell T m = Ioc (((m:ℝ) + 1) * T) (((m:ℝ) + 1) * T + T) := by
  unfold cell; congr 1; ring

/-- The cells partition `(T, ∞)`. -/
theorem iUnion_cell_eq_Ioi {T : ℝ} (hT : 0 < T) : (⋃ m : ℕ, cell T m) = Ioi T := by
  ext x
  simp only [cell, mem_iUnion, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨m, h1, h2⟩
    have : T ≤ ((m:ℝ) + 1) * T := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    linarith
  · intro hx
    have hy : 1 < x / T := by rwa [lt_div_iff₀ hT, one_mul]
    have hy0 : 0 ≤ x / T := by positivity
    have hk1 : 1 < ⌈x / T⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hy)
    have hk2 : 2 ≤ ⌈x / T⌉₊ := by omega
    refine ⟨⌈x / T⌉₊ - 2, ?_, ?_⟩
    · have h1 : ((⌈x / T⌉₊ : ℝ) - 1) < x / T := by
        have := Nat.ceil_lt_add_one hy0
        linarith
      have hcast : ((⌈x / T⌉₊ - 2 : ℕ) : ℝ) + 1 = (⌈x / T⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hk2]; push_cast; ring
      rw [hcast]
      calc ((⌈x / T⌉₊ : ℝ) - 1) * T < x / T * T := mul_lt_mul_of_pos_right h1 hT
        _ = x := div_mul_cancel₀ x hT.ne'
    · have h2 : x / T ≤ (⌈x / T⌉₊ : ℝ) := Nat.le_ceil _
      have hcast : ((⌈x / T⌉₊ - 2 : ℕ) : ℝ) + 2 = (⌈x / T⌉₊ : ℝ) := by
        rw [Nat.cast_sub hk2]; push_cast; ring
      rw [hcast]
      calc x = x / T * T := (div_mul_cancel₀ x hT.ne').symm
        _ ≤ (⌈x / T⌉₊ : ℝ) * T := mul_le_mul_of_nonneg_right h2 hT.le

theorem pairwise_disjoint_cell {T : ℝ} (hT : 0 < T) : Pairwise (Function.onFun Disjoint (cell T)) := by
  intro m m' hmm
  show Disjoint (cell T m) (cell T m')
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [cell, mem_Ioc] at hx hx'
  rcases lt_or_gt_of_ne hmm with h | h
  · have : (m:ℝ) + 1 ≤ m' := by exact_mod_cast h
    nlinarith
  · have : (m':ℝ) + 1 ≤ m := by exact_mod_cast h
    nlinarith

theorem cell_subset_Ioi {T : ℝ} (hT : 0 < T) (m : ℕ) : cell T m ⊆ Ioi T := by
  rw [← iUnion_cell_eq_Ioi hT]; exact subset_iUnion _ m

theorem Icc_cell_subset_Ici {T : ℝ} (hT : 0 < T) (m : ℕ) :
    Icc (((m:ℝ) + 1) * T) (((m:ℝ) + 1) * T + T) ⊆ Ici T := by
  intro x hx
  have : T ≤ ((m:ℝ) + 1) * T := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  exact le_trans this hx.1

theorem volume_cell (T : ℝ) (m : ℕ) : volume (cell T m) = ENNReal.ofReal T := by
  rw [cell_eq, Real.volume_Ioc]
  congr 1; ring

theorem volume_real_Ioc_add {a T : ℝ} (hT : 0 < T) :
    volume.real (Ioc a (a + T)) = T := by
  rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The constant `c` integrates to `T c` over a cell of length `T`. -/
theorem setIntegral_const_Ioc_add {a T : ℝ} (hT : 0 < T) (c : ℝ) :
    ∫ _ in Ioc a (a + T), c = T * c := by
  rw [setIntegral_const, volume_real_Ioc_add hT, smul_eq_mul]

theorem integrableOn_const_Ioc {a T : ℝ} (c : ℝ) :
    IntegrableOn (fun _ => c) (Ioc a (a + T)) := by
  refine integrableOn_const ?_
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

/-- The one-cell estimate: `|T h(a) - ∫_a^{a+T} h| ≤ T ∫_a^{a+T} |h'|`. -/
theorem abs_mul_sub_integral_le {h h' : ℝ → ℝ} {a T : ℝ} (hT : 0 < T)
    (hd : ∀ x ∈ Icc a (a + T), HasDerivAt h (h' x) x)
    (hint' : IntegrableOn h' (Ioc a (a + T))) :
    |T * h a - ∫ x in Ioc a (a + T), h x| ≤ T * ∫ x in Ioc a (a + T), |h' x| := by
  have haT : a ≤ a + T := by linarith
  have hcont : ContinuousOn h (Icc a (a + T)) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have hinth : IntegrableOn h (Ioc a (a + T)) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  set C := ∫ x in Ioc a (a + T), |h' x| with hC
  have hC0 : 0 ≤ C := integral_nonneg fun x => abs_nonneg _
  have habs : IntervalIntegrable (fun y => |h' y|) volume a (a + T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haT).2 hint'.abs
  have hpt : ∀ x ∈ Ioc a (a + T), |h x - h a| ≤ C := by
    intro x hx
    have hxa : a ≤ x := hx.1.le
    have hint'x : IntervalIntegrable h' volume a x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hxa).2
        (hint'.mono_set (Ioc_subset_Ioc le_rfl hx.2))
    have hftc : ∫ y in a..x, h' y = h x - h a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => hd y (Icc_subset_Icc le_rfl hx.2 (by rwa [uIcc_of_le hxa] at hy))) hint'x
    rw [← hftc]
    calc |∫ y in a..x, h' y| ≤ ∫ y in a..x, |h' y| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm (f := h') hxa
      _ ≤ ∫ y in a..a + T, |h' y| :=
          intervalIntegral.integral_mono_interval le_rfl hxa hx.2
            (Eventually.of_forall fun y => abs_nonneg _) habs
      _ = C := by rw [hC, intervalIntegral.integral_of_le haT]
  have hsplit : T * h a - ∫ x in Ioc a (a + T), h x
      = -∫ x in Ioc a (a + T), (h x - h a) := by
    rw [integral_sub hinth (integrableOn_const_Ioc (h a)), setIntegral_const_Ioc_add hT]
    ring
  rw [hsplit, abs_neg]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc a (a + T))
    (f := fun x => h x - h a) (C := C) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hpt x hx)
  rw [Real.norm_eq_abs, volume_real_Ioc_add hT] at this
  linarith

/-- The summed estimate: `|∑_{m≥1} T h(mT) - ∫_T^∞ h| ≤ T ∫_T^∞ |h'|`, with the
summability of the Riemann sum. -/
theorem abs_tsum_sub_integral_le {h h' : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hd : ∀ x ∈ Ici T, HasDerivAt h (h' x) x)
    (hint : IntegrableOn h (Ioi T)) (hint' : IntegrableOn h' (Ioi T)) :
    Summable (fun m : ℕ => T * h (((m:ℝ) + 1) * T)) ∧
    |∑' m : ℕ, T * h (((m:ℝ) + 1) * T) - ∫ x in Ioi T, h x|
      ≤ T * ∫ x in Ioi T, |h' x| := by
  have hU := iUnion_cell_eq_Ioi hT
  have hsumh : HasSum (fun m => ∫ x in cell T m, h x) (∫ x in Ioi T, h x) := by
    have := hasSum_integral_iUnion (μ := volume) (f := h) (measurableSet_cell T)
      (pairwise_disjoint_cell hT) (hU ▸ hint)
    rwa [hU] at this
  have hsumh' : HasSum (fun m => ∫ x in cell T m, |h' x|) (∫ x in Ioi T, |h' x|) := by
    have := hasSum_integral_iUnion (μ := volume) (f := fun x => |h' x|) (measurableSet_cell T)
      (pairwise_disjoint_cell hT) (hU ▸ hint'.abs)
    rwa [hU] at this
  have hcell : ∀ m : ℕ, |T * h (((m:ℝ) + 1) * T) - ∫ x in cell T m, h x|
      ≤ T * ∫ x in cell T m, |h' x| := by
    intro m
    rw [cell_eq]
    exact abs_mul_sub_integral_le hT (fun x hx => hd x (Icc_cell_subset_Ici hT m hx))
      (hint'.mono_set (by rw [← cell_eq]; exact cell_subset_Ioi hT m))
  set d : ℕ → ℝ := fun m => T * h (((m:ℝ) + 1) * T) - ∫ x in cell T m, h x with hd_def
  set e : ℕ → ℝ := fun m => T * ∫ x in cell T m, |h' x| with he_def
  have he : Summable e := hsumh'.summable.mul_left T
  have hdsum : Summable d :=
    Summable.of_norm_bounded he fun m => by rw [Real.norm_eq_abs]; exact hcell m
  have hTh : (fun m : ℕ => T * h (((m:ℝ) + 1) * T)) = fun m => d m + ∫ x in cell T m, h x := by
    funext m; simp [hd_def]
  have hsumTh : Summable fun m : ℕ => T * h (((m:ℝ) + 1) * T) := by
    rw [hTh]; exact hdsum.add hsumh.summable
  refine ⟨hsumTh, ?_⟩
  have h1 : ∑' m : ℕ, T * h (((m:ℝ) + 1) * T) - ∫ x in Ioi T, h x = ∑' m, d m := by
    rw [← hsumh.tsum_eq, ← hsumTh.tsum_sub hsumh.summable]
  rw [h1]
  calc |∑' m, d m| ≤ ∑' m, |d m| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdsum.norm
    _ ≤ ∑' m, e m := hdsum.abs.tsum_le_tsum (fun m => hcell m) he
    _ = T * ∫ x in Ioi T, |h' x| := by rw [he_def, tsum_mul_left, hsumh'.tsum_eq]

/-- The antitone bounds: for a non-negative antitone integrable `h` on `[T, ∞)`,
`∫_T^∞ h ≤ ∑_{m≥1} T h(mT) ≤ ∫_T^∞ h + T h(T)`. -/
theorem tsum_le_integral_add {h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hanti : AntitoneOn h (Ici T)) (hnn : ∀ x ∈ Ici T, 0 ≤ h x)
    (hint : IntegrableOn h (Ioi T)) :
    Summable (fun m : ℕ => T * h (((m:ℝ) + 1) * T)) ∧
    (∫ x in Ioi T, h x) ≤ ∑' m : ℕ, T * h (((m:ℝ) + 1) * T) ∧
    ∑' m : ℕ, T * h (((m:ℝ) + 1) * T) ≤ (∫ x in Ioi T, h x) + T * h T := by
  have hU := iUnion_cell_eq_Ioi hT
  have hsumh : HasSum (fun m => ∫ x in cell T m, h x) (∫ x in Ioi T, h x) := by
    have := hasSum_integral_iUnion (μ := volume) (f := h) (measurableSet_cell T)
      (pairwise_disjoint_cell hT) (hU ▸ hint)
    rwa [hU] at this
  have hmem : ∀ m : ℕ, ((m:ℝ) + 1) * T ∈ Ici T := fun m => by
    show T ≤ _; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hmem2 : ∀ m : ℕ, ((m:ℝ) + 2) * T ∈ Ici T := fun m => by
    show T ≤ _; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  -- the cell bounds
  have hupper : ∀ m : ℕ, ∫ x in cell T m, h x ≤ T * h (((m:ℝ) + 1) * T) := by
    intro m
    rw [cell_eq, ← setIntegral_const_Ioc_add hT]
    refine setIntegral_mono_on (by rw [← cell_eq]; exact hint.mono_set (cell_subset_Ioi hT m))
      (integrableOn_const_Ioc _) measurableSet_Ioc fun x hx => ?_
    exact hanti (hmem m) (le_trans (hmem m) hx.1.le) hx.1.le
  have hlower : ∀ m : ℕ, T * h (((m:ℝ) + 2) * T) ≤ ∫ x in cell T m, h x := by
    intro m
    rw [cell_eq, ← setIntegral_const_Ioc_add hT]
    refine setIntegral_mono_on (integrableOn_const_Ioc _)
      (by rw [← cell_eq]; exact hint.mono_set (cell_subset_Ioi hT m)) measurableSet_Ioc
      fun x hx => ?_
    have hx2 : x ≤ ((m:ℝ) + 2) * T := by linarith [hx.2]
    exact hanti (le_trans (hmem m) hx.1.le) (hmem2 m) hx2
  have hcast : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ) + 1) * T = ((m:ℝ) + 2) * T := fun m => by
    push_cast; ring
  -- summability of the shifted sequence, hence of the sequence
  have hshift : Summable fun m : ℕ => T * h ((((m + 1 : ℕ) : ℝ) + 1) * T) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hsumh.summable
    · rw [hcast]; exact mul_nonneg hT.le (hnn _ (hmem2 m))
    · rw [hcast]; exact hlower m
  have hsumTh : Summable fun m : ℕ => T * h (((m:ℝ) + 1) * T) :=
    (summable_nat_add_iff 1).1 hshift
  refine ⟨hsumTh, ?_, ?_⟩
  · rw [← hsumh.tsum_eq]
    exact hsumh.summable.tsum_le_tsum hupper hsumTh
  · rw [hsumTh.tsum_eq_zero_add, ← hsumh.tsum_eq]
    have h0 : T * h ((((0:ℕ):ℝ) + 1) * T) = T * h T := by simp
    rw [h0, add_comm]
    refine add_le_add_left ?_ _
    refine hshift.tsum_le_tsum (fun m => ?_) hsumh.summable
    rw [hcast]; exact hlower m

end

end BrownianImages
