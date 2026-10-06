/-
`thm:renewal-average` of `sec:two-contraction-formula`, the Cesàro mean of the expected
profile, which defines `H̄(c)` in `sec:introduction` before
`thm:two-contraction-distinction`.

The mean comes from the renewal equation directly, for lattice and non-lattice systems
at once: integrating
`G = z + ϑ * G` over `(-∞, T]` gives `∑ p_i ∫_{T-a_i}^T G → ∫ z`, and one more average
turns this into `T⁻¹ ∫₀ᵀ G → (∫ z)/m`.  Dominated convergence then carries the mean
through the smoothing formula `eq:h-definition`.

* `tendsto_avg_of_tendsto`: the Cesàro mean of a convergent function.
* `tendsto_avg_of_renewal`: the renewal average, for a bounded continuous function with
  an integrable renewal defect.
* `System.IsNatural.tendsto_avg_G`, `System.IsNatural.tendsto_avg_H`: the means of `G`
  and of `H_μ^s` for the natural measure of a system under the open set condition.
-/
import BrownianImages.KeyRenewalFourier
import BrownianImages.Schief
import BrownianImages.Kernel

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Cesàro mean of a locally integrable function that converges at infinity
converges to the same limit. -/
theorem tendsto_avg_of_tendsto {f : ℝ → E} {L : E}
    (hf : ∀ T, IntervalIntegrable f volume 0 T) (hlim : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ u in (0:ℝ)..T, f u) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨U, hU⟩ := (Metric.tendsto_atTop.1 hlim) (ε / 2) (by positivity)
  set U' := max U 0 with hU'
  have hU'0 : 0 ≤ U' := le_max_right _ _
  have hfL : ∀ T, IntervalIntegrable (fun u => f u - L) volume 0 T := fun T =>
    (hf T).sub intervalIntegrable_const
  set C := ‖∫ u in (0:ℝ)..U', (f u - L)‖ with hC
  refine ⟨max (U' + 1) (2 * C / ε + 1), fun T hT => ?_⟩
  have hT1 : U' + 1 ≤ T := le_of_max_le_left hT
  have hT2 : 2 * C / ε + 1 ≤ T := le_of_max_le_right hT
  have hTpos : 0 < T := by linarith
  have hrw : T⁻¹ • (∫ u in (0:ℝ)..T, f u) - L = T⁻¹ • ∫ u in (0:ℝ)..T, (f u - L) := by
    rw [intervalIntegral.integral_sub (hf T) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul,
      inv_mul_cancel₀ hTpos.ne', one_smul]
  have hsplit : ∫ u in (0:ℝ)..T, (f u - L)
      = (∫ u in (0:ℝ)..U', (f u - L)) + ∫ u in U'..T, (f u - L) :=
    (intervalIntegral.integral_add_adjacent_intervals (hfL U')
      (((hfL U').symm.trans (hfL T)))).symm
  have htail : ‖∫ u in U'..T, (f u - L)‖ ≤ ε / 2 * |T - U'| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have hx' : U < x := lt_of_le_of_lt (le_max_left _ _) (by
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact hx.1)
    have := hU x hx'.le
    rw [dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm, hrw, norm_smul, hsplit, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hTpos)]
  have hCε : C < ε / 2 * T := by
    have : 2 * C / ε < T := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  calc T⁻¹ * ‖(∫ u in (0:ℝ)..U', (f u - L)) + ∫ u in U'..T, (f u - L)‖
      ≤ T⁻¹ * (C + ε / 2 * |T - U'|) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl htail))
          (inv_pos.2 hTpos).le
    _ ≤ T⁻¹ * (C + ε / 2 * T) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (inv_pos.2 hTpos).le
        rw [abs_of_nonneg (by linarith)]
        nlinarith
    _ < T⁻¹ * (ε / 2 * T + ε / 2 * T) :=
        mul_lt_mul_of_pos_left (by linarith) (inv_pos.2 hTpos)
    _ = ε := by field_simp; ring

/-- **The renewal average.**  Let `g` be continuous and bounded, integrable on
`(-∞, 0]`, and let its renewal defect `z = g - ∑ p_i g(· - a_i)` be integrable, where the
weights `p_i ≥ 0` sum to one and the delays `a_i` are positive.  Then
`T⁻¹ ∫₀ᵀ g → (∫ z)/m` with `m = ∑ p_i a_i`.  Integrating the defect over `(-∞, T]` gives
`A(T) - ∑ p_i A(T - a_i) → ∫ z` for `A(T) = ∫_{-∞}^T g`, and averaging this once more
gives `m A(T) + O(1)`, since `A` is Lipschitz. -/
theorem tendsto_avg_of_renewal {ι : Type*} [Fintype ι] {g : ℝ → E} {B : ℝ}
    (hg : Continuous g) (hB : ∀ w, ‖g w‖ ≤ B) (hint : IntegrableOn g (Iic 0))
    (p a : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ha : ∀ i, 0 < a i)
    (hz : Integrable (fun w => g w - ∑ i, p i • g (w - a i))) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ u in (0:ℝ)..T, g u) atTop
      (𝓝 ((∑ i, p i * a i)⁻¹ • ∫ w, (g w - ∑ i, p i • g (w - a i)))) := by
  classical
  -- the renewal mean is positive
  have hm : 0 < ∑ i, p i * a i := by
    by_contra hle
    push Not at hle
    have hzero : ∀ i ∈ (Finset.univ : Finset ι), p i * a i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hp i) (ha i).le).1
        (le_antisymm hle (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (ha i).le))
    have : ∑ i, p i = 0 := Finset.sum_eq_zero fun i hi => by
      rcases mul_eq_zero.1 (hzero i hi) with h | h
      · exact h
      · exact absurd h (ha i).ne'
    rw [hsum] at this
    exact one_ne_zero this
  set m := ∑ i, p i * a i with hmdef
  set z : ℝ → E := fun w => g w - ∑ i, p i • g (w - a i) with hzdef
  -- integrability on every lower half-line
  have hIic : ∀ T : ℝ, IntegrableOn g (Iic T) := fun T =>
    (hint.union (hg.integrableOn_Icc (a := 0) (b := T))).mono_set fun w hw => by
      rcases le_or_gt w 0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.le, hw⟩
  set A : ℝ → E := fun T => ∫ w in Iic T, g w with hAdef
  have hAsub : ∀ t u, A u - A t = ∫ w in t..u, g w := fun t u =>
    intervalIntegral.integral_Iic_sub_Iic (hIic t) (hIic u)
  have hAlip : ∀ t u, ‖A u - A t‖ ≤ B * |u - t| := fun t u => by
    rw [hAsub]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => hB x
  have hAeq : A = fun u => A 0 + ∫ w in (0:ℝ)..u, g w := by
    funext u
    rw [← hAsub 0 u]
    abel
  have hAc : Continuous A := by
    rw [hAeq]
    exact continuous_const.add
      (intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0)
  -- translation of a lower half-line
  have htrans : ∀ (T c : ℝ), ∫ w in Iic T, g (w - c) = A (T - c) := by
    intro T c
    simp only [hAdef]
    rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
      ← integral_sub_right_eq_self (fun w => (Iic (T - c)).indicator g w) c]
    congr 1
    funext w
    simp only [Set.indicator_apply, Set.mem_Iic, sub_le_sub_iff_right]
  have htransInt : ∀ (T c : ℝ), IntegrableOn (fun w => g (w - c)) (Iic T) := by
    intro T c
    have h1 : Integrable (fun w => (Iic (T - c)).indicator g (w - c)) :=
      ((integrable_indicator_iff measurableSet_Iic).2 (hIic (T - c))).comp_sub_right c
    have h2 : (fun w => (Iic (T - c)).indicator g (w - c))
        = (Iic T).indicator (fun w => g (w - c)) := by
      funext w
      simp only [Set.indicator_apply, Set.mem_Iic, sub_le_sub_iff_right]
    rw [h2, integrable_indicator_iff measurableSet_Iic] at h1
    exact h1
  -- the integrated defect
  have hD : ∀ T, ∫ w in Iic T, z w = A T - ∑ i, p i • A (T - a i) := by
    intro T
    have hterm : ∀ i, IntegrableOn (fun w => p i • g (w - a i)) (Iic T) := fun i => by
      exact (htransInt T (a i)).smul (p i)
    have hsumInt : IntegrableOn (fun w => ∑ i, p i • g (w - a i)) (Iic T) :=
      integrable_finsetSum _ fun i _ => hterm i
    simp only [hzdef]
    rw [integral_sub (hIic T) hsumInt, integral_finsetSum _ fun i _ => hterm i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul, htrans]
  set D : ℝ → E := fun T => A T - ∑ i, p i • A (T - a i) with hDdef
  have hDlim : Tendsto D atTop (𝓝 (∫ w, z w)) := by
    have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := z)
      (s := fun T : ℝ => Iic T) (fun T => measurableSet_Iic)
      (fun t u htu => Iic_subset_Iic.2 htu) (by rw [iUnion_Iic]; exact hz.integrableOn)
    rw [iUnion_Iic, Measure.restrict_univ] at hlim
    exact hlim.congr hD
  have hDc : Continuous D :=
    hAc.sub (continuous_finsetSum _ fun i _ =>
      (hAc.comp (continuous_id.sub continuous_const)).const_smul (p i))
  -- the second average: `∫₀ᵀ D = m A(T) + R(T)` with `R` bounded
  set R : ℝ → E := fun T => ∑ i, p i • ((∫ u in (T - a i)..T, (A u - A T))
    - ∫ u in (-a i)..0, A u) with hRdef
  have hAint : ∀ a b, IntervalIntegrable A volume a b := fun a b => hAc.intervalIntegrable a b
  have hDint : ∀ T, ∫ u in (0:ℝ)..T, D u = m • A T + R T := by
    intro T
    have hshift : ∀ i, ∫ u in (0:ℝ)..T, A (u - a i) = ∫ u in (-a i)..(T - a i), A u := by
      intro i
      rw [intervalIntegral.integral_comp_sub_right A (a i), zero_sub]
    have hpiece : ∀ i, (∫ u in (0:ℝ)..T, A u) - ∫ u in (-a i)..(T - a i), A u
        = a i • A T + ((∫ u in (T - a i)..T, (A u - A T)) - ∫ u in (-a i)..0, A u) := by
      intro i
      have h1 : (∫ u in (-a i)..(T - a i), A u) + ∫ u in (T - a i)..T, A u
          = (∫ u in (-a i)..0, A u) + ∫ u in (0:ℝ)..T, A u := by
        rw [intervalIntegral.integral_add_adjacent_intervals (hAint _ _) (hAint _ _),
          intervalIntegral.integral_add_adjacent_intervals (hAint _ _) (hAint _ _)]
      have h2 : ∫ u in (T - a i)..T, (A u - A T)
          = (∫ u in (T - a i)..T, A u) - a i • A T := by
        rw [intervalIntegral.integral_sub (hAint _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, sub_sub_cancel]
      rw [h2]
      have h3 : ∫ u in (0:ℝ)..T, A u = (∫ u in (-a i)..(T - a i), A u)
          + (∫ u in (T - a i)..T, A u) - ∫ u in (-a i)..0, A u := by
        rw [h1]; abel
      rw [h3]
      abel
    have hsplit : ∫ u in (0:ℝ)..T, D u
        = ∑ i, p i • ((∫ u in (0:ℝ)..T, A u) - ∫ u in (-a i)..(T - a i), A u) := by
      have hterm : ∀ i, IntervalIntegrable (fun u => p i • A (u - a i)) volume 0 T :=
        fun i => (((hAc.comp (continuous_id.sub continuous_const)).const_smul
          (p i)).intervalIntegrable _ _)
      have hsumInt : IntervalIntegrable (fun u => ∑ i, p i • A (u - a i)) volume 0 T :=
        (continuous_finsetSum _ fun i _ =>
          (hAc.comp (continuous_id.sub continuous_const)).const_smul (p i)).intervalIntegrable
          _ _
      simp only [hDdef]
      rw [intervalIntegral.integral_sub (hAint _ _) hsumInt,
        intervalIntegral.integral_finsetSum fun i _ => hterm i]
      simp only [intervalIntegral.integral_smul, hshift, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hsum, one_smul]
    rw [hsplit]
    simp only [hpiece, smul_add, Finset.sum_add_distrib, smul_smul, hRdef, hmdef,
      Finset.sum_smul]
  -- `R` is bounded
  set R₀ := ∑ i, p i * (B * a i * a i + ‖∫ u in (-a i)..0, A u‖) with hR₀
  have hRbound : ∀ T, ‖R T‖ ≤ R₀ := by
    intro T
    simp only [hRdef, hR₀]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp i)]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ le_rfl)) (hp i)
    have hbd : ∀ u ∈ Ι (T - a i) T, ‖A u - A T‖ ≤ B * a i := by
      intro u hu
      rw [Set.uIoc_of_le (by linarith [ha i])] at hu
      rw [norm_sub_rev]
      refine (hAlip u T).trans ?_
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
      rw [abs_of_nonneg (by linarith [hu.2])]
      exact mul_le_mul_of_nonneg_left (by linarith [hu.1]) hB0
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans (le_of_eq ?_)
    rw [show T - (T - a i) = a i by ring, abs_of_pos (ha i)]
  -- assemble
  have hDavg := tendsto_avg_of_tendsto (fun T => hDc.intervalIntegrable 0 T) hDlim
  have hRavg : Tendsto (fun T : ℝ => T⁻¹ • R T) atTop (𝓝 0) := by
    have hR₀lim : Tendsto (fun T : ℝ => R₀ / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hR₀lim
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hT), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hRbound T) (inv_pos.2 hT).le
  have hAavg : Tendsto (fun T : ℝ => T⁻¹ • A T) atTop (𝓝 (m⁻¹ • ∫ w, z w)) := by
    have h := (hDavg.sub hRavg).const_smul m⁻¹
    rw [sub_zero] at h
    refine h.congr fun T => ?_
    have hc : m⁻¹ * T⁻¹ * m = T⁻¹ := by
      rw [mul_comm m⁻¹ T⁻¹, mul_assoc, inv_mul_cancel₀ hm.ne', mul_one]
    rw [hDint T, smul_add, add_sub_cancel_right, smul_smul, smul_smul, hc]
  have hA0 : Tendsto (fun T : ℝ => T⁻¹ • A 0) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa using this.smul_const (A 0)
  have := hAavg.sub hA0
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  rw [← smul_sub, hAsub]

namespace System

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

/-- The Cesàro mean of the normalised pair-distance profile `G` of a natural measure under
the open set condition is the renewal limit `(∫ z)/m`, in the lattice and in the
non-lattice case alike. -/
theorem IsNatural.tendsto_avg_G {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0:ℝ)..T, G s μ u) atTop
      (𝓝 ((S.renewalMean s)⁻¹ * ∫ w, S.renewalDefect s μ w)) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  have hsosc := hosc.strongOpenSetCondition S hμ.attractor
  have hint : IntegrableOn (G s μ) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic hs0 0).mono' measurable_G.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg w)]
    exact G_le_exp hs0.le le_rfl
  exact tendsto_avg_of_renewal (E := ℝ) (continuous_G hs0 hA)
    (fun w => by rw [Real.norm_eq_abs]; exact abs_G_le hs0 hA w) hint
    (fun i => S.ratio i ^ s) S.logRatio
    (fun i => (Real.rpow_pos_of_pos (S.ratio_pos i) s).le) hdim (S.logRatio_pos)
    (integrable_renewalDefect S hsosc hs0 hs1 hdim hμ)

/-- The averages of `G` along the substitution `w = 2t - log η` of `eq:h-definition`
have the same limit, for every `η`. -/
theorem IsNatural.tendsto_avg_G_comp {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (c : ℝ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, G s μ (2 * t - c)) atTop
      (𝓝 ((S.renewalMean s)⁻¹ * ∫ w, S.renewalDefect s μ w)) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  have hGc := continuous_G hs0 hA
  set L := (S.renewalMean s)⁻¹ * ∫ w, S.renewalDefect s μ w
  have hGavg := hμ.tendsto_avg_G S hs0 hs1 hosc hdim
  have hsub : ∀ T, ∫ t in (0:ℝ)..T, G s μ (2 * t - c)
      = 2⁻¹ * ((∫ u in (0:ℝ)..(2 * T - c), G s μ u) - ∫ u in (0:ℝ)..(-c), G s μ u) := by
    intro T
    rw [intervalIntegral.integral_comp_mul_sub (f := G s μ) two_ne_zero c, smul_eq_mul,
      mul_zero, zero_sub, intervalIntegral.integral_interval_sub_left
        (hGc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)]
  have hlin : Tendsto (fun T : ℝ => 2 * T - c) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-c) (tendsto_id.const_mul_atTop two_pos)
  have h1 := hGavg.comp hlin
  have h2 : Tendsto (fun T : ℝ => (2 * T - c) / (2 * T)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).sub
      ((tendsto_const_nhds (x := c)).div_atTop (tendsto_id.const_mul_atTop two_pos))
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [id]
    field_simp
  have h3 : Tendsto (fun T : ℝ => T⁻¹ * (2⁻¹ * ∫ u in (0:ℝ)..(-c), G s μ u)) atTop
      (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const (2⁻¹ * ∫ u in (0:ℝ)..(-c), G s μ u)
  have h := (h1.mul h2).sub h3
  rw [mul_one, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 c)] with T hT
  have hT0 : 0 < T := lt_of_le_of_lt (le_max_left _ _) hT
  have hTc : 2 * T - c ≠ 0 := by linarith [le_max_right 0 c]
  simp only [Function.comp]
  rw [hsub T]
  field_simp

/-- **`eq:mean-profile` of `thm:renewal-average`.**  For the natural measure of a system
under the open set condition, `T⁻¹ ∫₀ᵀ H_μ^s → (∫₀^∞ φ) (∫ z)/m`.  This is the existence
of `H̄(c)` before `thm:two-contraction-distinction`, and it holds for every such system. -/
theorem IsNatural.tendsto_avg_H {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, H s μ t) atTop
      (𝓝 ((∫ η in Ioi (0:ℝ), kern s η) *
        ((S.renewalMean s)⁻¹ * ∫ w, S.renewalDefect s μ w))) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  have hGc := continuous_G hs0 hA
  have hGb : ∀ w, |G s μ w| ≤ A := abs_G_le hs0 hA
  have hkint := kern_integrableOn (s := s) hs0 hs1
  have hkm : Measurable (kern s) := by unfold kern; fun_prop
  set L := (S.renewalMean s)⁻¹ * ∫ w, S.renewalDefect s μ w with hL
  -- Fubini
  have hswap : ∀ T, ∫ t in (0:ℝ)..T, H s μ t
      = ∫ η in Ioi (0:ℝ), kern s η * ∫ t in (0:ℝ)..T, G s μ (2 * t - Real.log η) := by
    intro T
    simp only [H]
    rw [intervalIntegral_integral_swap]
    · congr 1
      funext η
      rw [intervalIntegral.integral_const_mul]
    · have hmeas : Measurable (Function.uncurry fun (t η : ℝ) =>
          kern s η * G s μ (2 * t - Real.log η)) :=
        (hkm.comp measurable_snd).mul (measurable_G.comp
          ((measurable_const.mul measurable_fst).sub (Real.measurable_log.comp measurable_snd)))
      have hfin : volume (Ι (0:ℝ) T) ≠ ⊤ := by
        show volume (Set.Ioc _ _) ≠ ⊤
        exact measure_Ioc_lt_top.ne
      have hone : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ι (0:ℝ) T)) :=
        integrableOn_const hfin
      have hdom : Integrable (fun p : ℝ × ℝ => (1:ℝ) * (A * ‖kern s p.2‖))
          ((volume.restrict (Ι (0:ℝ) T)).prod (volume.restrict (Ioi (0:ℝ)))) :=
        Integrable.mul_prod hone (hkint.norm.const_mul A)
      refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, one_mul, norm_mul, Real.norm_eq_abs]
      rw [mul_comm A]
      exact mul_le_mul_of_nonneg_left (hGb _) (abs_nonneg _)
  -- the inner averages, in a form that is visibly measurable in `η`
  set B : ℝ → ℝ := fun u => ∫ u' in (0:ℝ)..u, G s μ u' with hB
  have hBc : Continuous B :=
    intervalIntegral.continuous_primitive (fun a b => hGc.intervalIntegrable a b) 0
  have hinner : ∀ T η, ∫ t in (0:ℝ)..T, G s μ (2 * t - Real.log η)
      = 2⁻¹ * (B (2 * T - Real.log η) - B (-Real.log η)) := by
    intro T η
    rw [intervalIntegral.integral_comp_mul_sub (f := G s μ) two_ne_zero (Real.log η),
      smul_eq_mul, mul_zero, zero_sub, intervalIntegral.integral_interval_sub_left
        (hGc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)]
  have hkey : Tendsto (fun T : ℝ => ∫ η in Ioi (0:ℝ),
      kern s η * (T⁻¹ * ∫ t in (0:ℝ)..T, G s μ (2 * t - Real.log η))) atTop
      (𝓝 (∫ η in Ioi (0:ℝ), kern s η * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun η => A * kern s η)
      (Eventually.of_forall fun T => ?_) ?_ (hkint.const_mul A) ?_
    · simp only [hinner]
      exact (hkm.mul (measurable_const.mul (measurable_const.mul
        ((hBc.measurable.comp (measurable_const.sub Real.measurable_log)).sub
          (hBc.measurable.comp Real.measurable_log.neg))))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with T hT
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
      have hk : (0:ℝ) ≤ kern s η := (kern_pos (s := s) hη).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, mul_comm A]
      refine mul_le_mul_of_nonneg_left ?_ hk
      have hI : |∫ t in (0:ℝ)..T, G s μ (2 * t - Real.log η)| ≤ A * |T - 0| := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by
          rw [Real.norm_eq_abs]; exact hGb _
      rw [sub_zero, abs_of_pos hT] at hI
      rw [abs_mul, abs_of_pos (inv_pos.2 hT)]
      calc T⁻¹ * |∫ t in (0:ℝ)..T, G s μ (2 * t - Real.log η)| ≤ T⁻¹ * (A * T) :=
            mul_le_mul_of_nonneg_left hI (inv_pos.2 hT).le
        _ = A := by field_simp
    · filter_upwards with η
      exact ((hμ.tendsto_avg_G_comp S hs0 hs1 hosc hdim (Real.log η))).const_mul (kern s η)
  have hval : ∫ η in Ioi (0:ℝ), kern s η * L = (∫ η in Ioi (0:ℝ), kern s η) * L :=
    integral_mul_const _ _
  rw [hval] at hkey
  refine hkey.congr fun T => ?_
  rw [hswap T, ← integral_const_mul]
  congr 1
  funext η
  ring

end System

end BrownianImages
