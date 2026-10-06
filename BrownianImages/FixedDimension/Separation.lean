/-
`thm:fixed-dimension-separation`, the analytic part: the critical set `D_s` of `H̄_s` in
`(0, 1/2)` has no accumulation point in `(0, 1/2]`, the mean is strictly monotone on every
interval of `(0, 1/2)` free of critical points, in particular on some `(1/2 - ε_s, 1/2)`,
and every level set of `H̄_s` in `(0, 1/2]` has no accumulation point there and is countable.
The identity theorem for real analytic functions on `(0,1)` is the tool, with the
non-constancy of the mean from `thm:fixed-dimension-range`.  The finiteness of `D_s` for
`s ≤ 1/2` of `thm:critical-set-finite` follows from the positive derivative on `(0, p₀)`.

* `criticalSet`, `levelSet`: `D_s` and the level sets.
* `not_accPt_criticalSet`, `not_accPt_levelSet`, `levelSet_countable`.
* `strictMono_or_anti_of_ne_zero`, `exists_eps_strictMono`: strict monotonicity.
* `criticalSet_finite`: `thm:critical-set-finite`.
-/
import BrownianImages.FixedDimension.Range

namespace BrownianImages

open Filter Set Metric
open scoped Topology

noncomputable section

/-- The critical set `D_s`: the critical points of `H̄_s` in `(0, 1/2)`. -/
def criticalSet (s : ℝ) : Set ℝ := {p | p ∈ Ioo (0:ℝ) (1/2) ∧ deriv (fixedMean s) p = 0}

/-- The level set of `H̄_s` through `p₁`, in `(0, 1/2]`. -/
def levelSet (s p₁ : ℝ) : Set ℝ := {p | p ∈ Ioc (0:ℝ) (1/2) ∧ fixedMean s p = fixedMean s p₁}

/-- The mean is not constant on `(0,1)`: it tends to `0` at `0` and is positive at `1/2`. -/
theorem fixedMean_not_const {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ¬ ∀ p ∈ Ioo (0:ℝ) 1, fixedMean s p = fixedMean s (1/2) := by
  intro h
  have hc0 := fixedMean_pos hs hs1 (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
  have hlim := tendsto_fixedMean_zero hs hs1
  have hconst : Tendsto (fixedMean s) (𝓝[>] 0) (𝓝 (fixedMean s (1/2))) := by
    refine tendsto_const_nhds.congr' ?_
    have h1 : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p := eventually_mem_nhdsWithin
    have h2 : ∀ᶠ p in 𝓝[>] (0:ℝ), p < 1 :=
      (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0:ℝ)))).eventually
        (gt_mem_nhds one_pos)
    filter_upwards [h1, h2] with p hp1 hp2
    exact (h p ⟨hp1, hp2⟩).symm
  have := tendsto_nhds_unique hlim hconst
  linarith

theorem differentiableOn_fixedMean {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    DifferentiableOn ℝ (fixedMean s) (Ioo 0 1) :=
  fun _ hp => (analyticAt_fixedMean hs hs1 hp.1 hp.2).differentiableAt.differentiableWithinAt

/-- The derivative of the mean does not vanish identically on `(0,1)`. -/
theorem not_eqOn_deriv_fixedMean_zero {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ¬ EqOn (deriv (fixedMean s)) 0 (Ioo 0 1) := by
  intro h
  refine fixedMean_not_const hs hs1 fun p hp => ?_
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo (differentiableOn_fixedMean hs hs1)
    h hp ⟨by norm_num, by norm_num⟩

/-- The zeros of a real analytic function on `(0,1)` that is not identically zero do not
accumulate in `(0,1)`. -/
theorem not_accPt_zeros {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f (Ioo 0 1))
    (hne : ¬ EqOn f 0 (Ioo 0 1)) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    ¬ AccPt p (𝓟 {q | f q = 0}) := by
  intro hacc
  apply hne
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Ioo hp ?_
  rw [accPt_iff_frequently_nhdsNE] at hacc
  exact hacc.mono fun q hq => hq

/-- **`D_s` has no accumulation point in `(0, 1/2]`.** -/
theorem not_accPt_criticalSet {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {p : ℝ}
    (hp : p ∈ Ioc (0:ℝ) (1/2)) : ¬ AccPt p (𝓟 (criticalSet s)) := by
  intro hacc
  have hsub : criticalSet s ⊆ {q | deriv (fixedMean s) q = 0} := fun q hq => hq.2
  exact not_accPt_zeros (analyticOnNhd_deriv_fixedMean hs hs1)
    (not_eqOn_deriv_fixedMean_zero hs hs1) ⟨hp.1, by linarith [hp.2]⟩
    (hacc.mono (principal_mono.2 hsub))

/-- **Strict monotonicity on an interval free of critical points.** -/
theorem strictMono_or_anti_of_ne_zero {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {α β : ℝ}
    (hsub : Ioo α β ⊆ Ioo 0 (1/2)) (hne : ∀ q ∈ Ioo α β, deriv (fixedMean s) q ≠ 0) :
    StrictMonoOn (fixedMean s) (Ioo α β) ∨ StrictAntiOn (fixedMean s) (Ioo α β) := by
  have hsub' : Ioo α β ⊆ Ioo 0 1 := fun q hq => ⟨(hsub hq).1, by linarith [(hsub hq).2]⟩
  have hcont : ContinuousOn (deriv (fixedMean s)) (Ioo α β) := fun q hq =>
    ((analyticOnNhd_deriv_fixedMean hs hs1) q (hsub' hq)).continuousAt.continuousWithinAt
  have hcontf : ContinuousOn (fixedMean s) (Ioo α β) :=
    (continuousOn_fixedMean hs hs1).mono hsub'
  have hsign : (∀ q ∈ Ioo α β, 0 < deriv (fixedMean s) q) ∨
      (∀ q ∈ Ioo α β, deriv (fixedMean s) q < 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨q₁, hq₁, h₁⟩, ⟨q₂, hq₂, h₂⟩⟩ := hcon
    have h₁' : deriv (fixedMean s) q₁ < 0 := lt_of_le_of_ne h₁ (hne q₁ hq₁)
    have h₂' : 0 < deriv (fixedMean s) q₂ := lt_of_le_of_ne h₂ (hne q₂ hq₂).symm
    obtain ⟨q, hq, hq0⟩ := isPreconnected_Ioo.intermediate_value hq₁ hq₂ hcont ⟨h₁'.le, h₂'.le⟩
    exact hne q hq hq0
  rcases hsign with h | h
  · left
    exact strictMonoOn_of_deriv_pos (convex_Ioo α β) hcontf (by rw [interior_Ioo]; exact h)
  · right
    exact strictAntiOn_of_deriv_neg (convex_Ioo α β) hcontf (by rw [interior_Ioo]; exact h)

/-- **`ε_s`**: some interval `(1/2 - ε, 1/2)` contains no critical point, and the mean is
strictly monotone on it. -/
theorem exists_eps_strictMono {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ ε ∈ Ioo (0:ℝ) (1/2), (∀ q ∈ Ioo (1/2 - ε) (1/2), deriv (fixedMean s) q ≠ 0) ∧
      (StrictMonoOn (fixedMean s) (Ioo (1/2 - ε) (1/2)) ∨
        StrictAntiOn (fixedMean s) (Ioo (1/2 - ε) (1/2))) := by
  have hna := not_accPt_criticalSet hs hs1 (p := 1/2) ⟨by norm_num, le_rfl⟩
  rw [accPt_iff_nhds] at hna
  push Not at hna
  obtain ⟨U, hU, hUy⟩ := hna
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hmin1 : min δ (1/4) ≤ δ := min_le_left _ _
  have hmin2 : min δ (1/4) ≤ 1/4 := min_le_right _ _
  have hne : ∀ q ∈ Ioo (1/2 - min δ (1/4)) (1/2), deriv (fixedMean s) q ≠ 0 := by
    intro q hq hq0
    have hqU : q ∈ U := hball (by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hq.1, hq.2])
    have hqD : q ∈ criticalSet s := ⟨⟨by linarith [hq.1], hq.2⟩, hq0⟩
    have := hUy q ⟨hqU, hqD⟩
    linarith [hq.2]
  refine ⟨min δ (1/4), ⟨lt_min hδ (by norm_num), by linarith⟩, hne, ?_⟩
  exact strictMono_or_anti_of_ne_zero hs hs1
    (fun q hq => ⟨by linarith [hq.1], hq.2⟩) hne

/-- **The level sets have no accumulation point in `(0, 1/2]`.** -/
theorem not_accPt_levelSet {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (p₁ : ℝ) {p : ℝ}
    (hp : p ∈ Ioc (0:ℝ) (1/2)) :
    ¬ AccPt p (𝓟 (levelSet s p₁)) := by
  intro hacc
  have hf : AnalyticOnNhd ℝ (fun q => fixedMean s q - fixedMean s p₁) (Ioo 0 1) :=
    (analyticOnNhd_fixedMean hs hs1).sub analyticOnNhd_const
  have hne : ¬ EqOn (fun q => fixedMean s q - fixedMean s p₁) 0 (Ioo 0 1) := by
    intro h
    refine fixedMean_not_const hs hs1 fun q hq => ?_
    have h1 := h hq
    have h2 := h (show (1/2:ℝ) ∈ Ioo 0 1 by norm_num)
    simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
    rw [h1, h2]
  have hsub : levelSet s p₁ ⊆ {q | (fun q => fixedMean s q - fixedMean s p₁) q = 0} :=
    fun q hq => by simp [hq.2]
  exact not_accPt_zeros hf hne ⟨hp.1, by linarith [hp.2]⟩ (hacc.mono (principal_mono.2 hsub))

/-- **The level sets are countable.** -/
theorem levelSet_countable {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (p₁ : ℝ) :
    (levelSet s p₁).Countable := by
  have hfin : ∀ n : ℕ, (levelSet s p₁ ∩ Icc (1 / ((n:ℝ) + 2)) (1/2)).Finite := by
    intro n
    by_contra hinf
    obtain ⟨x, hxK, hacc⟩ :=
      Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc inter_subset_right
    have hx : x ∈ Ioc (0:ℝ) (1/2) := ⟨lt_of_lt_of_le (by positivity) hxK.1, hxK.2⟩
    exact not_accPt_levelSet hs hs1 p₁ hx (hacc.mono (principal_mono.2 inter_subset_left))
  have hcover : levelSet s p₁ ⊆ ⋃ n : ℕ, levelSet s p₁ ∩ Icc (1 / ((n:ℝ) + 2)) (1/2) := by
    intro p hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp.1.1
    refine mem_iUnion.2 ⟨n, hp, ?_, hp.1.2⟩
    calc 1 / ((n:ℝ) + 2) ≤ 1 / ((n:ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ p := hn.le
  exact (Set.countable_iUnion fun n => (hfin n).countable).mono hcover

/-- **`thm:critical-set-finite`**: `D_s` is finite for `s ≤ 1/2`. -/
theorem criticalSet_finite {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) : (criticalSet s).Finite := by
  obtain ⟨p₀, hp₀, hpos⟩ := exists_deriv_fixedMean_pos_small hs hs1
  have hs1' : s < 1 := by linarith
  have hsub : criticalSet s ⊆ Icc p₀ (1/2) := by
    intro p hp
    refine ⟨?_, hp.1.2.le⟩
    by_contra h
    push Not at h
    exact (hpos p ⟨hp.1.1, h⟩).ne' hp.2
  by_contra hinf
  obtain ⟨x, hxK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc hsub
  exact not_accPt_criticalSet hs hs1' ⟨lt_of_lt_of_le hp₀.1 hxK.1, hxK.2⟩ hacc

end

end BrownianImages
