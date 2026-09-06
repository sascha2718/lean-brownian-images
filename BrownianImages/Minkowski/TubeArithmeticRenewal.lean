/-
The arithmetic half of `thm:neighbourhood-renewal`.

The continuous renewal library used elsewhere in the project contains only the
non-arithmetic key renewal theorem.  This module isolates the genuinely discrete
input in the arithmetic case.  Assuming the renewal masses are bounded and obey
the shifted discrete renewal limit, Tannery's theorem in the Banach space of
continuous functions on one period gives uniform phase convergence.  The
exponentially decaying tube defect supplies the summable lattice envelope.
-/
import BrownianImages.Minkowski.TubeRenewalLimit
import BrownianImages.Periodic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace ArithmeticRenewal

/-- The translate of a forcing function by the `k`-th lattice point, restricted
to the closed fundamental interval. -/
def forcingTranslate (h : ℝ) (z : ℝ → ℝ) (hz : Continuous z) (k : ℤ) :
    C(Set.Icc (0 : ℝ) h, ℝ) :=
  ⟨fun t ↦ z ((t : ℝ) + (k : ℝ) * h),
    hz.comp (continuous_subtype_val.add continuous_const)⟩

/-- The `k`-th translate of the forcing, evaluated at `t ∈ [0, h]`, is the forcing at `t
+ kh`. -/
@[simp]
theorem forcingTranslate_apply (h : ℝ) (z : ℝ → ℝ) (hz : Continuous z)
    (k : ℤ) (t : Set.Icc (0 : ℝ) h) :
    forcingTranslate h z hz k t = z ((t : ℝ) + (k : ℝ) * h) := rfl

/-- The lattice renewal series on one fundamental interval. -/
def latticeSection (h : ℝ) (z : ℝ → ℝ) (hz : Continuous z)
    (u : ℤ → ℝ) (n : ℕ) : C(Set.Icc (0 : ℝ) h, ℝ) :=
  ∑' k : ℤ, u ((n : ℤ) - k) • forcingTranslate h z hz k

/-- The candidate arithmetic key-renewal limit on one fundamental interval. -/
def limitSection (h L : ℝ) (z : ℝ → ℝ) (hz : Continuous z) :
    C(Set.Icc (0 : ℝ) h, ℝ) :=
  ∑' k : ℤ, L • forcingTranslate h z hz k

/-- An arbitrary ambient representative of a continuous section.  Only its
restriction to the closed fundamental interval is used. -/
def ambientOfSection (h : ℝ) (q : C(Set.Icc (0 : ℝ) h, ℝ)) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc (0 : ℝ) h then q ⟨t, ht⟩ else 0

/-- The ambient extension of a section agrees with the section on `[0, h]`. -/
theorem ambientOfSection_eq {h : ℝ} (q : C(Set.Icc (0 : ℝ) h, ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) h) :
    ambientOfSection h q t = q ⟨t, ht⟩ := by
  simp [ambientOfSection, ht]

/-- The ambient extension of a section is continuous on `[0, h]`. -/
theorem continuousOn_ambientOfSection (h : ℝ)
    (q : C(Set.Icc (0 : ℝ) h, ℝ)) :
    ContinuousOn (ambientOfSection h q) (Set.Icc (0 : ℝ) h) := by
  rw [continuousOn_iff_continuous_restrict]
  convert q.continuous using 1
  funext t
  exact ambientOfSection_eq q t.property

/-- The translates of a forcing dominated by a summable sequence are summable in `C([0,
h])`. -/
theorem summable_smul_forcingTranslate
    {h L : ℝ} {z : ℝ → ℝ} (hz : Continuous z) {a : ℤ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (hza : ∀ (k : ℤ) (t : Set.Icc (0 : ℝ) h),
      |z ((t : ℝ) + (k : ℝ) * h)| ≤ a k) :
    Summable (fun k : ℤ ↦ L • forcingTranslate h z hz k) := by
  apply (ha.mul_left |L|).of_norm_bounded
  intro k
  rw [norm_smul, Real.norm_eq_abs]
  have hq : ‖forcingTranslate h z hz k‖ ≤ a k := by
    rw [ContinuousMap.norm_le _ (ha0 k)]
    intro t
    simpa [Real.norm_eq_abs] using hza k t
  exact mul_le_mul_of_nonneg_left hq (abs_nonneg L)

/-- The limiting section has matching endpoint values.  This is the lattice
reindexing `k ↦ k + 1`, and is the exact compatibility needed for the continuous
periodic extension. -/
theorem limitSection_zero_eq_end
    {h L : ℝ} (hh : 0 ≤ h) {z : ℝ → ℝ} (hz : Continuous z)
    {a : ℤ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (hza : ∀ (k : ℤ) (t : Set.Icc (0 : ℝ) h),
      |z ((t : ℝ) + (k : ℝ) * h)| ≤ a k) :
    limitSection h L z hz ⟨0, ⟨le_rfl, hh⟩⟩ =
      limitSection h L z hz ⟨h, ⟨hh, le_rfl⟩⟩ := by
  have hsum := summable_smul_forcingTranslate hz ha0 ha hza (L := L)
  rw [limitSection, ← ContinuousMap.tsum_apply hsum,
    ← ContinuousMap.tsum_apply hsum]
  simp only [ContinuousMap.smul_apply, forcingTranslate_apply, smul_eq_mul, zero_add]
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq
    (f := fun k : ℤ ↦ L * z ((k : ℝ) * h))]
  apply tsum_congr
  intro k
  congr 2
  simp only [Equiv.coe_addRight]
  push_cast
  ring

/-- Tannery's theorem, applied in the Banach space of continuous functions on a
closed fundamental interval.  This is the uniform part of the arithmetic key
renewal theorem.  Its only discrete input is the shifted renewal-mass limit. -/
theorem tendsto_latticeSection
    {h L B : ℝ} {z : ℝ → ℝ} (hz : Continuous z)
    {u a : ℤ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (hza : ∀ (k : ℤ) (t : Set.Icc (0 : ℝ) h),
      |z ((t : ℝ) + (k : ℝ) * h)| ≤ a k)
    (hB : 0 ≤ B) (huB : ∀ j, |u j| ≤ B)
    (hulim : ∀ k : ℤ,
      Tendsto (fun n : ℕ ↦ u ((n : ℤ) - k)) atTop (nhds L)) :
    Tendsto (latticeSection h z hz u) atTop
      (nhds (limitSection h L z hz)) := by
  have hbound : Summable (fun k : ℤ ↦ B * a k) := ha.mul_left B
  apply tendsto_tsum_of_dominated_convergence hbound
  · intro k
    exact (hulim k).smul_const (forcingTranslate h z hz k)
  · filter_upwards [] with n k
    rw [norm_smul, Real.norm_eq_abs]
    have hq : ‖forcingTranslate h z hz k‖ ≤ a k := by
      rw [ContinuousMap.norm_le _ (ha0 k)]
      intro t
      simpa [Real.norm_eq_abs] using hza k t
    exact mul_le_mul (huB _) hq (norm_nonneg _) hB

/-- Uniform convergence of continuous maps on a compact space gives pointwise
convergence. -/
theorem tendsto_apply_of_tendsto_continuousMap
    {X α : Type*} [TopologicalSpace X] [CompactSpace X]
    {l : Filter α} {f : α → C(X, ℝ)} {g : C(X, ℝ)}
    (hfg : Tendsto f l (nhds g)) (x : X) :
    Tendsto (fun n ↦ f n x) l (nhds (g x)) := by
  rw [Metric.tendsto_nhds] at hfg ⊢
  intro ε hε
  filter_upwards [hfg ε hε] with n hn
  calc
    dist (f n x) (g x) = ‖(f n - g) x‖ := by rw [dist_eq_norm]; rfl
    _ ≤ ‖f n - g‖ := ContinuousMap.norm_coe_le_norm _ _
    _ = dist (f n) g := by rw [dist_eq_norm]
    _ < ε := hn

/-! ### Summable lattice envelopes -/

/-- A function which vanishes on the negative half-line, is globally bounded,
and has a one-sided exponential tail has a summable envelope on the lattice
cells `t + k h`, uniformly for `t ∈ [0,h]`. -/
theorem exists_summable_lattice_envelope
    {h A C γ L : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hγ : 0 < γ) (hL : 0 ≤ L) {z : ℝ → ℝ}
    (hzero : ∀ x : ℝ, x ≤ 0 → z x = 0)
    (hbound : ∀ x : ℝ, |z x| ≤ A)
    (htail : ∀ x : ℝ, L ≤ x → |z x| ≤ C * Real.exp (-γ * x)) :
    ∃ a : ℤ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable a ∧
      ∀ (k : ℤ) (t : Set.Icc (0 : ℝ) h),
        |z ((t : ℝ) + (k : ℝ) * h)| ≤ a k := by
  let D : ℝ := (A + C) * Real.exp (γ * L)
  let a : ℤ → ℝ := fun k ↦
    if k < 0 then 0 else D * Real.exp (-γ * h * (k : ℝ))
  have hD : 0 ≤ D := mul_nonneg (add_nonneg hA hC) (Real.exp_pos _).le
  have ha0 : ∀ k, 0 ≤ a k := by
    intro k
    simp only [a]
    split
    · exact le_rfl
    · positivity
  have hasum : Summable a := by
    refine Summable.of_nat_of_neg ?_ ?_
    · have hgeo : Summable fun n : ℕ ↦
          D * Real.exp (-γ * h) ^ n := by
        exact Summable.mul_left D
          (summable_geometric_of_lt_one (Real.exp_pos _).le
            (Real.exp_lt_one_iff.mpr (by nlinarith)))
      refine hgeo.congr fun n ↦ ?_
      simp only [a]
      rw [if_neg (by omega)]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    · refine summable_of_ne_finset_zero (s := {0}) fun n hn ↦ ?_
      have hn0 : n ≠ 0 := by simpa using hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hneg : (-(n : ℤ)) < 0 := by omega
      change (if (-(n : ℤ)) < 0 then 0 else
        D * Real.exp (-γ * h * ((-(n : ℤ) : ℤ) : ℝ))) = 0
      rw [if_pos hneg]
  refine ⟨a, ha0, hasum, ?_⟩
  intro k t
  simp only [a]
  by_cases hk : k < 0
  · rw [if_pos hk]
    have hk1 : k + 1 ≤ 0 := by omega
    have hx0 : (t : ℝ) + (k : ℝ) * h ≤ 0 := by
      have hkc : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      calc
        (t : ℝ) + (k : ℝ) * h ≤ h + (k : ℝ) * h :=
          add_le_add t.property.2 le_rfl
        _ ≤ 0 := by nlinarith
    rw [hzero _ hx0, abs_zero]
  · rw [if_neg hk]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (not_lt.mp hk)
    have hkx : (k : ℝ) * h ≤ (t : ℝ) + (k : ℝ) * h := by
      linarith [t.property.1]
    by_cases hxL : L ≤ (t : ℝ) + (k : ℝ) * h
    · have hexp : Real.exp (-γ * ((t : ℝ) + (k : ℝ) * h)) ≤
          Real.exp (-γ * h * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hCD : C ≤ D := by
        calc
          C ≤ A + C := by linarith
          _ ≤ (A + C) * Real.exp (γ * L) :=
            le_mul_of_one_le_right (add_nonneg hA hC)
              (Real.one_le_exp (mul_nonneg hγ.le hL))
          _ = D := rfl
      exact (htail _ hxL).trans
        ((mul_le_mul_of_nonneg_left hexp hC).trans
          (mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le))
    · have hkL : (k : ℝ) * h < L :=
        lt_of_le_of_lt hkx (lt_of_not_ge hxL)
      have hexp1 : 1 ≤ Real.exp (γ * (L - h * (k : ℝ))) :=
        Real.one_le_exp (mul_nonneg hγ.le (by nlinarith))
      calc
        |z ((t : ℝ) + (k : ℝ) * h)| ≤ A := hbound _
        _ ≤ A + C := by linarith
        _ ≤ (A + C) * Real.exp (γ * (L - h * (k : ℝ))) :=
          le_mul_of_one_le_right (add_nonneg hA hC) hexp1
        _ = D * Real.exp (-γ * h * (k : ℝ)) := by
          simp only [D]
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- **Uniform arithmetic key-renewal assembly.**  The exact lattice renewal
series, a bounded renewal-mass sequence, its shifted discrete renewal limit, and
a summable cell envelope imply uniform convergence on one period.  The limit
extends continuously and periodically, and any uniform positive lower and upper
bounds on the original profile pass to that extension.

This theorem deliberately exposes the two discrete statements not present in the
vendored continuous renewal library: `hulim` is the discrete renewal theorem and
`hseries` is the lattice form of the iterated renewal equation. -/
theorem exists_periodic_limit_of_lattice_series
    {h L B c C : ℝ} (hh : 0 < h)
    {m z : ℝ → ℝ} (hz : Continuous z) {u a : ℤ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (hza : ∀ (k : ℤ) (t : Set.Icc (0 : ℝ) h),
      |z ((t : ℝ) + (k : ℝ) * h)| ≤ a k)
    (hB : 0 ≤ B) (huB : ∀ j, |u j| ≤ B)
    (hulim : ∀ k : ℤ,
      Tendsto (fun n : ℕ ↦ u ((n : ℤ) - k)) atTop (nhds L))
    (hseries : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ t : Set.Icc (0 : ℝ) h,
        m ((t : ℝ) + (n : ℝ) * h) = latticeSection h z hz u n t)
    (hc : 0 < c)
    (hmc : ∀ v : ℝ, 0 ≤ v → c ≤ m v ∧ m v ≤ C) :
    ∃ P : ℝ → ℝ, Continuous P ∧ Function.Periodic P h ∧
      (0 < c ∧ ∀ t : ℝ, c ≤ P t ∧ P t ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t ∈ Set.Icc (0 : ℝ) h,
          |m (t + (n : ℝ) * h) - P t| ≤ ε := by
  let q : C(Set.Icc (0 : ℝ) h, ℝ) := limitSection h L z hz
  let f : ℝ → ℝ := ambientOfSection h q
  have hlim : Tendsto (latticeSection h z hz u) atTop (nhds q) := by
    exact tendsto_latticeSection hz ha0 ha hza hB huB hulim
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) (0 + h)) := by
    simpa only [zero_add, f] using continuousOn_ambientOfSection h q
  have hfends : f 0 = f (0 + h) := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) h := ⟨le_rfl, hh.le⟩
    have hhmem : h ∈ Set.Icc (0 : ℝ) h := ⟨hh.le, le_rfl⟩
    rw [zero_add]
    change ambientOfSection h q 0 = ambientOfSection h q h
    rw [ambientOfSection_eq q h0, ambientOfSection_eq q hhmem]
    simpa only [q] using
      limitSection_zero_eq_end (L := L) hh.le hz ha0 ha hza
  obtain ⟨P, hPcont, hPper, hPeq⟩ :=
    exists_periodic_extension hh hfends hfcont
  refine ⟨P, hPcont, hPper, ⟨hc, ?_⟩, ?_⟩
  · intro w
    obtain ⟨t, ht, hwt⟩ := hPper.exists_mem_Ico₀ hh w
    have htIcc : t ∈ Set.Icc (0 : ℝ) h := ⟨ht.1, ht.2.le⟩
    have hqtend : Tendsto (fun n : ℕ ↦ latticeSection h z hz u n ⟨t, htIcc⟩)
        atTop (nhds (q ⟨t, htIcc⟩)) :=
      tendsto_apply_of_tendsto_continuousMap hlim ⟨t, htIcc⟩
    obtain ⟨N₀, hseries⟩ := hseries
    have hcq : c ≤ q ⟨t, htIcc⟩ := by
      apply ge_of_tendsto hqtend
      filter_upwards [eventually_ge_atTop N₀] with n hn
      rw [← hseries n hn ⟨t, htIcc⟩]
      exact (hmc _ (add_nonneg htIcc.1 (mul_nonneg (Nat.cast_nonneg _) hh.le))).1
    have hqC : q ⟨t, htIcc⟩ ≤ C := by
      apply le_of_tendsto hqtend
      filter_upwards [eventually_ge_atTop N₀] with n hn
      rw [← hseries n hn ⟨t, htIcc⟩]
      exact (hmc _ (add_nonneg htIcc.1 (mul_nonneg (Nat.cast_nonneg _) hh.le))).2
    have hPt : P t = q ⟨t, htIcc⟩ := by
      rw [hPeq t (by simpa only [zero_add] using htIcc)]
      change ambientOfSection h q t = q ⟨t, htIcc⟩
      exact ambientOfSection_eq q htIcc
    rw [hwt, hPt]
    exact ⟨hcq, hqC⟩
  · intro ε hε
    obtain ⟨N₀, hseries⟩ := hseries
    rw [Metric.tendsto_nhds] at hlim
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hlim ε hε)
    refine ⟨max N₀ N₁, fun n hn t ht ↦ ?_⟩
    have hn₀ : N₀ ≤ n := (le_max_left N₀ N₁).trans hn
    have hn₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans hn
    let ts : Set.Icc (0 : ℝ) h := ⟨t, ht⟩
    have hnorm : ‖latticeSection h z hz u n - q‖ < ε := by
      simpa only [dist_eq_norm] using hN₁ n hn₁
    have hPq : P t = q ts := by
      rw [hPeq t (by simpa only [zero_add] using ht)]
      change ambientOfSection h q t = q ts
      exact ambientOfSection_eq q ht
    rw [hseries n hn₀ ts, hPq]
    change |(latticeSection h z hz u n - q) ts| ≤ ε
    calc
      |(latticeSection h z hz u n - q) ts| =
          ‖(latticeSection h z hz u n - q) ts‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖latticeSection h z hz u n - q‖ :=
        ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ε := hnorm.le

end ArithmeticRenewal

namespace System

variable {iota : Type*} [Fintype iota] (S : System iota)

/-- Arithmeticity puts every half-logarithmic renewal step in the asserted
lattice.  Thus no extra support assumption is hidden in the discrete series
appearing below. -/
theorem halfLogRatio_mem_zmultiples_of_tubeArithmetic
    {h : ℝ} (harith : S.TubeArithmetic h) (i : iota) :
    S.halfLogRatio i ∈ AddSubgroup.zmultiples h := by
  rw [← harith]
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

/-- The cutoff tube forcing returned to the original half-logarithmic scale. -/
noncomputable def halfScaleCutoffTubeRenewalForcing
    (s : ℝ) (m : ℝ → ℝ) (v : ℝ) : ℝ :=
  S.cutoffTubeRenewalForcing s m (2 * v)

/-- The half-scale cutoff forcing is continuous when the mean profile is. -/
theorem continuous_halfScaleCutoffTubeRenewalForcing
    {s : ℝ} {m : ℝ → ℝ} (hm : Continuous m) :
    Continuous (S.halfScaleCutoffTubeRenewalForcing s m) := by
  exact (S.continuous_cutoffTubeRenewalForcing hm).comp
    (continuous_const.mul continuous_id)

/-- The half-scale cutoff forcing vanishes on the negative half-line. -/
theorem halfScaleCutoffTubeRenewalForcing_eq_zero_of_nonpos
    {s : ℝ} {m : ℝ → ℝ} {v : ℝ} (hv : v ≤ 0) :
    S.halfScaleCutoffTubeRenewalForcing s m v = 0 := by
  exact S.cutoffTubeRenewalForcing_eq_zero_of_nonpos (by linarith)

/-- The half-scale cutoff forcing is bounded by twice a bound on the mean profile. -/
theorem abs_halfScaleCutoffTubeRenewalForcing_le
    {s : ℝ} (hdim : S.IsDimension s) {m : ℝ → ℝ} {A : ℝ}
    (hA : ∀ v : ℝ, 0 ≤ v → |m v| ≤ A) (v : ℝ) :
    |S.halfScaleCutoffTubeRenewalForcing s m v| ≤ 2 * A := by
  exact S.abs_cutoffTubeRenewalForcing_le hdim hA (2 * v)

/-- Past the cutoff boundary layer, the half-scale forcing is the negative tube
defect and hence inherits its exponential bound without a change of exponent. -/
theorem abs_halfScaleCutoffTubeRenewalForcing_le_exp_of_tail
    [Nonempty iota] {s : ℝ} {m d : ℝ → ℝ} {C γ : ℝ}
    (hrenew : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      m v = S.tubeRenewalConv s m v - d v)
    (hdefect : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      0 ≤ d v ∧ d v ≤ C * Real.exp (-γ * v))
    {v : ℝ} (hv : S.tubeRenewalTailThreshold / 2 ≤ v) :
    |S.halfScaleCutoffTubeRenewalForcing s m v| ≤
      C * Real.exp (-γ * v) := by
  have hy : ∀ i : iota, 1 + S.logRatio i ≤ 2 * v := by
    intro i
    linarith [S.one_add_logRatio_le_tubeRenewalTailThreshold i]
  have hvsteps : ∀ i : iota, S.halfLogRatio i ≤ v := by
    intro i
    rw [halfLogRatio]
    linarith [hy i]
  rw [halfScaleCutoffTubeRenewalForcing,
    S.cutoffTubeRenewalForcing_eq_neg_of_tail hrenew hy,
    show 2 * v / 2 = v by ring, abs_neg,
    abs_of_nonneg (hdefect v hvsteps).1]
  exact (hdefect v hvsteps).2

/-- The cutoff forcing of the tube renewal equation has the uniform summable
lattice-cell envelope required by the arithmetic Tannery argument. -/
theorem exists_summable_envelope_halfScaleCutoffTubeRenewalForcing
    [Nonempty iota] {s h : ℝ} (hh : 0 < h) (hdim : S.IsDimension s)
    {m d : ℝ → ℝ} {A C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ)
    (hA : ∀ v : ℝ, 0 ≤ v → |m v| ≤ A)
    (hrenew : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      m v = S.tubeRenewalConv s m v - d v)
    (hdefect : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      0 ≤ d v ∧ d v ≤ C * Real.exp (-γ * v)) :
    ∃ a : ℤ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable a ∧
      ∀ (k : ℤ) (t : Set.Icc (0 : ℝ) h),
        |S.halfScaleCutoffTubeRenewalForcing s m
          ((t : ℝ) + (k : ℝ) * h)| ≤ a k := by
  have hA0 : 0 ≤ A := (abs_nonneg (m 0)).trans (hA 0 le_rfl)
  apply ArithmeticRenewal.exists_summable_lattice_envelope
    (A := 2 * A) (C := C) (γ := γ)
    (L := S.tubeRenewalTailThreshold / 2)
    (z := S.halfScaleCutoffTubeRenewalForcing s m)
    hh (mul_nonneg (by norm_num) hA0) hC hγ
    (div_nonneg S.tubeRenewalTailThreshold_nonneg (by norm_num))
  · intro v hv
    exact S.halfScaleCutoffTubeRenewalForcing_eq_zero_of_nonpos hv
  · intro v
    exact S.abs_halfScaleCutoffTubeRenewalForcing_le hdim hA v
  · intro v hv
    exact S.abs_halfScaleCutoffTubeRenewalForcing_le_exp_of_tail
      hrenew hdefect hv

/-- Paper-shaped arithmetic tube-renewal theorem.  All continuous analysis,
including uniformity in the phase, follows from the exponentially decaying tube
defect.  The hypotheses `hulim` and `hseries` are exactly the missing discrete
renewal theorem and the lattice renewal-series identity, respectively. -/
theorem exists_periodic_limit_of_tubeArithmetic_of_discrete_renewal
    [Nonempty iota] {s h : ℝ} (hh : 0 < h) (harith : S.TubeArithmetic h)
    (hdim : S.IsDimension s) {m d : ℝ → ℝ}
    {A D γ c B ℓ : ℝ} (hm : Continuous m)
    (hA : ∀ v : ℝ, 0 ≤ v → |m v| ≤ A)
    (hD : 0 ≤ D) (hγ : 0 < γ)
    (hrenew : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      m v = S.tubeRenewalConv s m v - d v)
    (hdefect : ∀ v : ℝ, (∀ i : iota, S.halfLogRatio i ≤ v) →
      0 ≤ d v ∧ d v ≤ D * Real.exp (-γ * v))
    (hc : 0 < c) (hmc : ∀ v : ℝ, 0 ≤ v → c ≤ m v ∧ m v ≤ A)
    {u : ℤ → ℝ} (hB : 0 ≤ B) (huB : ∀ j, |u j| ≤ B)
    (hulim : ∀ k : ℤ,
      Tendsto (fun n : ℕ ↦ u ((n : ℤ) - k)) atTop (nhds ℓ))
    (hseries : S.TubeArithmetic h →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ t : Set.Icc (0 : ℝ) h,
          m ((t : ℝ) + (n : ℝ) * h) =
            ArithmeticRenewal.latticeSection h
              (S.halfScaleCutoffTubeRenewalForcing s m)
              (S.continuous_halfScaleCutoffTubeRenewalForcing hm) u n t) :
    ∃ P : ℝ → ℝ, Continuous P ∧ Function.Periodic P h ∧
      (∃ c₀ C₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ P t ∧ P t ≤ C₀) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t ∈ Set.Icc (0 : ℝ) h,
          |m (t + (n : ℝ) * h) - P t| ≤ ε := by
  obtain ⟨a, ha0, ha, hza⟩ :=
    S.exists_summable_envelope_halfScaleCutoffTubeRenewalForcing
      hh hdim hD hγ hA hrenew hdefect
  obtain ⟨P, hPc, hPp, hPb, hPconv⟩ :=
    ArithmeticRenewal.exists_periodic_limit_of_lattice_series
      hh (S.continuous_halfScaleCutoffTubeRenewalForcing hm)
      ha0 ha hza hB huB hulim (hseries harith) hc hmc
  exact ⟨P, hPc, hPp, ⟨c, A, hPb⟩, hPconv⟩

end System

end

end BrownianImages
