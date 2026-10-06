/-
`thm:fixed-dimension-range`: for every `s ∈ (0,1)`, `p ↦ H̄_s(p)` is continuous and strictly
positive on `(0,1)`, and `H̄_s(p) → 0` as `p ↓ 0`; consequently the family contains an
uncountable subfamily with pairwise distinct means.

Continuity is a consequence of `thm:fixed-dimension-analyticity`.  For the limit, the
leading-ones decomposition `eq:leading-ones` gives `M_p ≤ 2^s Σ(p)` once `a ≤ (1-b)/2`, the
main term is bounded through `Σ = (e^{sT} - 1) S(T)` and the Riemann-sum comparison, so `M_p`
stays bounded as `p ↓ 0`, while `pq/E(p) ≤ 1/log(1/p) → 0`.

* `fixedMean_pos`, `continuousAt_fixedMean`: positivity and continuity.
* `fixedMoment_le_of_small`: the uniform bound on the moment for small `p`.
* `tendsto_fixedMean_zero`: the limit.
* `exists_uncountable_injOn_fixedMean`: the uncountable subfamily.
-/
import BrownianImages.FixedDimension.Analyticity
import BrownianImages.FixedDimension.Monotone

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-! ### Continuity and positivity -/

theorem continuousAt_fixedMean {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousAt (fixedMean s) p :=
  (analyticAt_fixedMean hs hs1 hp0 hp1).continuousAt

theorem continuousOn_fixedMean {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ContinuousOn (fixedMean s) (Ioo 0 1) :=
  fun _ hp => (continuousAt_fixedMean hs hs1 hp.1 hp.2).continuousWithinAt

/-- `H̄_s(p) > 0`. -/
theorem fixedMean_pos {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < fixedMean s p := by
  have hC := fixedMean_const_pos hs1
  have hF : 0 < p * (1 - p) / entropy p :=
    div_pos (mul_pos hp0 (by linarith)) (entropy_pos hp0 hp1)
  have hM := one_le_fixedMoment hs hs1 hp0 hp1
  unfold fixedMean
  exact mul_pos (mul_pos hC hF) (by linarith)

/-! ### The moment near `p = 0` -/

/-- `s ∫_T^∞ f ≤ s/(1-s) + 1.59` for every `0 < s < 1`, from `f ≤ x^{-s}` on `(0,1]` and
`f ≤ (1 - e^{-1})^{-s} e^{-sx}` on `[1,∞)`. -/
theorem mul_integral_mainF_le' {s T : ℝ} (hs : 0 < s) (hs1 : s < 1) (hT : 0 < T) :
    s * ∫ x in Ioi T, mainF s x ≤ s / (1 - s) + 1.59 := by
  have hs2 : s ≤ 2 := by linarith
  have hC : (1 - Real.exp (-1)) ^ (-s) ≤ 1.59 := by
    have he := Real.exp_one_gt_d9
    have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h1 : Real.exp (-1) ≤ 0.3701 := by
      rw [hinv, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
    have hpos : 0 < 1 - Real.exp (-1) := by linarith
    have hle1 : 1 - Real.exp (-1) ≤ 1 := by linarith [Real.exp_pos (-1)]
    calc (1 - Real.exp (-1)) ^ (-s) ≤ (1 - Real.exp (-1)) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by linarith)
      _ = (1 - Real.exp (-1))⁻¹ := by rw [Real.rpow_neg_one]
      _ ≤ 1.59 := by rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  have hCpos : 0 < (1 - Real.exp (-1)) ^ (-s) := by
    apply Real.rpow_pos_of_pos
    have := Real.exp_lt_one_iff.2 (show (-1:ℝ) < 0 by norm_num); linarith
  have hsdiv : 0 ≤ s / (1 - s) := div_nonneg hs.le (by linarith)
  -- the tail integral from `max T 1`
  have htail : ∀ a : ℝ, 1 ≤ a → s * ∫ x in Ioi a, mainF s x ≤ 1.59 := by
    intro a ha
    have h1 : ∫ x in Ioi a, mainF s x
        ≤ ∫ x in Ioi a, (1 - Real.exp (-1)) ^ (-s) * Real.exp (-(s * x)) := by
      refine setIntegral_mono_on (integrableOn_mainF hs hs2 (by linarith)) ?_ measurableSet_Ioi
        fun x hx => mainF_le_exp hs.le one_pos (le_trans ha (le_of_lt hx))
      have := (exp_neg_integrableOn_Ioi a hs).const_mul ((1 - Real.exp (-1)) ^ (-s))
      exact this.congr (Eventually.of_forall fun x => by simp [neg_mul])
    have h2 : ∫ x in Ioi a, Real.exp (-(s * x)) ≤ ∫ x in Ioi (1:ℝ), Real.exp (-(s * x)) := by
      apply setIntegral_mono_set
      · have := exp_neg_integrableOn_Ioi (1:ℝ) hs
        exact this.congr (Eventually.of_forall fun x => by simp [neg_mul])
      · exact Eventually.of_forall fun x => (Real.exp_pos _).le
      · exact Eventually.of_forall (Ioi_subset_Ioi ha)
    rw [integral_const_mul] at h1
    rw [integral_exp_tail hs] at h2
    have h3 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc s * ∫ x in Ioi a, mainF s x
        ≤ s * ((1 - Real.exp (-1)) ^ (-s) * (Real.exp (-s) / s)) := by
          apply mul_le_mul_of_nonneg_left _ hs.le
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hCpos.le)
      _ = (1 - Real.exp (-1)) ^ (-s) * Real.exp (-s) := by field_simp
      _ ≤ 1.59 * 1 := mul_le_mul hC h3 (Real.exp_pos _).le (by norm_num)
      _ = 1.59 := by ring
  rcases le_or_gt 1 T with h1T | hT1
  · linarith [htail T h1T]
  · have hsplit : ∫ x in Ioi T, mainF s x
        = (∫ x in Ioc T 1, mainF s x) + ∫ x in Ioi (1:ℝ), mainF s x := by
      rw [← Ioc_union_Ioi_eq_Ioi hT1.le]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((integrableOn_mainF hs hs2 hT).mono_set Ioc_subset_Ioi_self)
        (integrableOn_mainF hs hs2 one_pos)
    have hpiece : ∫ x in Ioc T 1, mainF s x ≤ 1 / (1 - s) := by
      have hrp : ∫ x in Ioc T 1, x ^ (-s) = (1 - T ^ (-s + 1)) / (-s + 1) := by
        rw [← intervalIntegral.integral_of_le hT1.le, integral_rpow (Or.inr ⟨by linarith,
          fun h => by rw [uIcc_of_le hT1.le] at h; exact absurd h.1 (not_le.2 hT)⟩)]
        simp
      have hmono : ∫ x in Ioc T 1, mainF s x ≤ ∫ x in Ioc T 1, x ^ (-s) := by
        refine setIntegral_mono_on ((integrableOn_mainF hs hs2 hT).mono_set Ioc_subset_Ioi_self)
          ?_ measurableSet_Ioc fun x hx => mainF_le_rpow hs.le (hT.trans hx.1)
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
        exact continuousOn_id.rpow_const fun x hx => Or.inl (by linarith [hx.1] : x ≠ 0)
      rw [hrp] at hmono
      have hT' : 0 ≤ T ^ (-s + 1) := Real.rpow_nonneg hT.le _
      have hden : 0 < -s + 1 := by linarith
      calc ∫ x in Ioc T 1, mainF s x ≤ (1 - T ^ (-s + 1)) / (-s + 1) := hmono
        _ ≤ 1 / (-s + 1) := by
            apply div_le_div_of_nonneg_right _ hden.le; linarith
        _ = 1 / (1 - s) := by ring_nf
    have htail1 := htail 1 le_rfl
    have hs1' : s * (1 / (1 - s)) = s / (1 - s) := mul_one_div _ _
    rw [hsplit, mul_add]
    have := mul_le_mul_of_nonneg_left hpiece hs.le
    linarith

/-- `Λ_n ≤ ((1 - b^{n+1})/2)^{-s}` once `a ≤ (1 - b)/2`. -/
theorem leadingTerm_le_of_small {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ha : fixedA s p ≤ (1 - fixedB s p) / 2) (n : ℕ) :
    leadingTerm s p n ≤ ((1 - fixedB s p ^ (n + 1)) / 2) ^ (-s) := by
  have hb0 := fixedB_pos (s := s) hp1
  have hb1 := fixedB_lt_one hs hp0 hp1
  have hbn : fixedB s p ^ (n + 1) ≤ fixedB s p := by
    calc fixedB s p ^ (n + 1) ≤ fixedB s p ^ 1 :=
          pow_le_pow_of_le_one hb0.le hb1.le (by omega)
      _ = fixedB s p := pow_one _
  have hpos : 0 < (1 - fixedB s p ^ (n + 1)) / 2 := by
    have : fixedB s p ^ (n + 1) < 1 := pow_lt_one₀ hb0.le hb1 (Nat.succ_ne_zero n)
    linarith
  have hK : ∀ ω ω', |termKernel s p n ω ω'| ≤ ((1 - fixedB s p ^ (n + 1)) / 2) ^ (-s) := by
    intro ω ω'
    have hX := fixedCode_mem_Icc hs hp0 hp1 ω
    have hY := fixedCode_mem_Icc hs hp0 hp1 ω'
    have ha0 := fixedA_pos (s := s) hp0
    have hbase : (1 - fixedB s p ^ (n + 1)) / 2 ≤ 1 - fixedB s p ^ (n + 1) -
        fixedA s p * (fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω') := by
      have hbn0 : 0 ≤ fixedB s p ^ (n + 1) := pow_nonneg hb0.le _
      have h1 : fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω' ≤ 1 := by
        nlinarith [hX.2, hY.1]
      have h2 : fixedA s p * (fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω')
          ≤ fixedA s p := by nlinarith
      linarith
    have hge := (termKernel_mem hs hs1 hp0 hp1 n ω ω').1
    rw [abs_of_nonneg (by linarith)]
    unfold termKernel
    exact rpow_neg_antitone hpos hbase hs.le
  have := isProbabilityMeasure_twoBern_fixed hp0 hp1
  have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - p))
    (f := fun ω' => ∫ ω, termKernel s p n ω ω' ∂twoBern (1 - p))
    (Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs]; exact abs_inner_integral_le hp0 hp1 hK ω')
  rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- `M_p ≤ 2^s Σ(p)` once `a ≤ (1 - b)/2`. -/
theorem fixedMoment_le_mainTerm {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ha : fixedA s p ≤ (1 - fixedB s p) / 2) :
    fixedMoment s p ≤ 2 ^ s * mainTerm s p := by
  have h1 := hasSum_leadingTerm hs hs1 hp0 hp1
  have h2 := (summable_mainTerm_terms hs (by linarith) hp0 hp1).hasSum
  have h3 : HasSum (fun n : ℕ => 2 ^ s * (p * (1 - p) ^ n * (1 - fixedB s p ^ (n + 1)) ^ (-s)))
      (2 ^ s * mainTerm s p) := h2.mul_left _
  refine hasSum_le (fun n => ?_) h1 h3
  have hq : 0 ≤ p * (1 - p) ^ n := mul_nonneg hp0.le (pow_nonneg (by linarith) _)
  have hL := leadingTerm_le_of_small hs hs1 hp0 hp1 ha n
  have hb0 := fixedB_pos (s := s) hp1
  have hb1 := fixedB_lt_one hs hp0 hp1
  have hpos : 0 < 1 - fixedB s p ^ (n + 1) := by
    have : fixedB s p ^ (n + 1) < 1 := pow_lt_one₀ hb0.le hb1 (Nat.succ_ne_zero n)
    linarith
  have e : ((1 - fixedB s p ^ (n + 1)) / 2) ^ (-s) = 2 ^ s * (1 - fixedB s p ^ (n + 1)) ^ (-s) := by
    rw [Real.div_rpow hpos.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv, mul_comm]
  calc p * (1 - p) ^ n * leadingTerm s p n
      ≤ p * (1 - p) ^ n * (2 ^ s * (1 - fixedB s p ^ (n + 1)) ^ (-s)) :=
        mul_le_mul_of_nonneg_left (hL.trans e.le) hq
    _ = 2 ^ s * (p * (1 - p) ^ n * (1 - fixedB s p ^ (n + 1)) ^ (-s)) := by ring

/-- `Σ(p) ≤ (s/q) (∫_T^∞ f + T f(T))`. -/
theorem mainTerm_le {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    mainTerm s p ≤ (s / (1 - p)) *
      ((∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p)) := by
  have hT := fixedT_pos hs hp0 hp1
  obtain ⟨-, -, h⟩ := mainS_bounds hs (by linarith) hT
  have hq : (0:ℝ) < 1 - p := by linarith
  rw [mainTerm_eq hs hp0 hp1]
  unfold mainTermT
  have hexp : Real.exp (s * fixedT s p) - 1 ≤ s * fixedT s p * Real.exp (s * fixedT s p) := by
    have h0 := Real.add_one_le_exp (-(s * fixedT s p))
    have hpos := Real.exp_pos (s * fixedT s p)
    rw [Real.exp_neg] at h0
    have : (1 - s * fixedT s p) * Real.exp (s * fixedT s p) ≤ 1 := by
      calc (1 - s * fixedT s p) * Real.exp (s * fixedT s p)
          ≤ (Real.exp (s * fixedT s p))⁻¹ * Real.exp (s * fixedT s p) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos.le
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith
  have hS0 : 0 ≤ mainS s (fixedT s p) :=
    tsum_nonneg fun m => (mainF_pos (by positivity)).le
  calc (Real.exp (s * fixedT s p) - 1) * mainS s (fixedT s p)
      ≤ (s * fixedT s p * Real.exp (s * fixedT s p)) * mainS s (fixedT s p) :=
        mul_le_mul_of_nonneg_right hexp hS0
    _ = (s / (1 - p)) * (fixedT s p * mainS s (fixedT s p)) := by
        rw [exp_mul_fixedT hs hp1]; field_simp
    _ ≤ (s / (1 - p)) *
        ((∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p)) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- The uniform bound `2^s · 2 (s/(1-s) + 1.59 + s)` on the moment for small `p`. -/
def momentBound (s : ℝ) : ℝ := 2 ^ s * (2 * (s / (1 - s) + 1.59 + s))

/-- **The moment is bounded near `p = 0`**: for `p ≤ 1/2`, `T ≤ 1` and `a ≤ (1-b)/2`,
`M_p ≤ momentBound s`. -/
theorem fixedMoment_le_of_small {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp : p ≤ 1/2)
    (hT : fixedT s p ≤ 1) (ha : fixedA s p ≤ (1 - fixedB s p) / 2) :
    fixedMoment s p ≤ momentBound s := by
  have hp1 : p < 1 := by linarith
  have hTpos := fixedT_pos hs hp0 hp1
  have h1 := fixedMoment_le_mainTerm hs hs1 hp0 hp1 ha
  have h2 := mainTerm_le hs hs1 hp0 hp1
  have hJ : (∫ x in Ioi (fixedT s p), mainF s x) ≤ 1 / (1 - s) + 1.59 / s := by
    have h := mul_integral_mainF_le' hs hs1 hTpos
    have : (∫ x in Ioi (fixedT s p), mainF s x) ≤ (s / (1 - s) + 1.59) / s :=
      (le_div_iff₀' hs).2 h
    refine this.trans (le_of_eq ?_)
    field_simp
  have hJ0 : 0 ≤ ∫ x in Ioi (fixedT s p), mainF s x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => (mainF_pos (hTpos.trans hx)).le
  have hf : fixedT s p * mainF s (fixedT s p) ≤ 1 := by
    have := mainF_le_rpow hs.le hTpos
    calc fixedT s p * mainF s (fixedT s p) ≤ fixedT s p * fixedT s p ^ (-s) :=
          mul_le_mul_of_nonneg_left this hTpos.le
      _ = fixedT s p ^ (1 - s) := by
          rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add hTpos, Real.rpow_one]
      _ ≤ 1 := Real.rpow_le_one hTpos.le hT (by linarith)
  have hf0 : 0 ≤ fixedT s p * mainF s (fixedT s p) :=
    mul_nonneg hTpos.le (mainF_pos hTpos).le
  have hq : s / (1 - p) ≤ 2 * s := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hsum : (∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p)
      ≤ 1 / (1 - s) + 1.59 / s + 1 := by linarith
  have hsum0 : 0 ≤ (∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p) := by
    linarith
  have hmain : (s / (1 - p)) *
      ((∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p))
      ≤ 2 * (s / (1 - s) + 1.59 + s) := by
    calc (s / (1 - p)) *
        ((∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p))
        ≤ (2 * s) * (1 / (1 - s) + 1.59 / s + 1) :=
          mul_le_mul hq hsum hsum0 (by positivity)
      _ = 2 * (s / (1 - s) + 1.59 + s) := by field_simp
  unfold momentBound
  calc fixedMoment s p ≤ 2 ^ s * mainTerm s p := h1
    _ ≤ 2 ^ s * ((s / (1 - p)) *
        ((∫ x in Ioi (fixedT s p), mainF s x) + fixedT s p * mainF s (fixedT s p))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 ^ s * (2 * (s / (1 - s) + 1.59 + s)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

/-- The small-`p` conditions hold for all `p` near `0`. -/
theorem eventually_small {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p ∧ p ≤ 1/2 ∧ fixedT s p ≤ 1 ∧
      fixedA s p ≤ (1 - fixedB s p) / 2 := by
  have h0 : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p := eventually_mem_nhdsWithin
  have hsmall : ∀ᶠ p in 𝓝[>] (0:ℝ), p < min (1/2) (s / 2) :=
    (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0:ℝ)))).eventually
      (gt_mem_nhds (lt_min (by norm_num) (by positivity)))
  have hexp : (1:ℝ) < s⁻¹ := one_lt_inv_iff₀.2 ⟨hs, hs1⟩
  have hpow : ∀ᶠ p in 𝓝[>] (0:ℝ), p ^ (s⁻¹ - 1) < 1/4 := by
    have h := (Real.continuousAt_rpow_const 0 (s⁻¹ - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at h
    exact (tendsto_nhdsWithin_of_tendsto_nhds h).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [h0, hsmall, hpow] with p hp0 hps hpw
  have hp12 : p < 1/2 := lt_of_lt_of_le hps (min_le_left _ _)
  have hps2 : p < s / 2 := lt_of_lt_of_le hps (min_le_right _ _)
  have hp1 : p < 1 := by linarith
  have hT : fixedT s p ≤ 1 := by
    have h := mul_fixedT_le hs hp1
    have : p / (1 - p) ≤ 2 * p := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have : s * fixedT s p ≤ s := by linarith
    exact (mul_le_iff_le_one_right hs).1 this
  refine ⟨hp0, hp12.le, hT, ?_⟩
  have hTpos := fixedT_pos hs hp0 hp1
  have hTp := le_fixedT hs hs1.le hp0 hp1
  -- `1 - b ≥ T/(1+T) ≥ T/2 ≥ p/2`
  have hb : 1 - fixedB s p ≥ p / 2 := by
    rw [← exp_neg_fixedT hp1]
    have h1 := one_sub_exp_neg_ge hTpos.le
    have h2 : fixedT s p / 2 ≤ fixedT s p / (1 + fixedT s p) :=
      div_le_div_of_nonneg_left hTpos.le (by linarith) (by linarith)
    linarith
  -- `a = p^{1/s} = p · p^{1/s - 1} ≤ p/4`
  have ha : fixedA s p ≤ p / 4 := by
    unfold fixedA
    rw [show s⁻¹ = 1 + (s⁻¹ - 1) by ring, Real.rpow_add hp0, Real.rpow_one]
    nlinarith
  linarith

/-- `E(p) ≥ p log(1/p)`. -/
theorem entropy_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p * Real.log p⁻¹ ≤ entropy p := by
  unfold entropy
  have : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rw [Real.log_inv]
  nlinarith

/-- **`H̄_s(p) → 0` as `p ↓ 0`.** -/
theorem tendsto_fixedMean_zero {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Tendsto (fixedMean s) (𝓝[>] 0) (𝓝 0) := by
  set C := (2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) * momentBound s with hCdef
  have hlog : Tendsto (fun p : ℝ => (Real.log p⁻¹)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto Real.log (𝓝[>] (0:ℝ)) atBot :=
      Real.tendsto_log_nhdsNE_zero.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    have h2 : Tendsto (fun p : ℝ => Real.log p⁻¹) (𝓝[>] 0) atTop := by
      simp_rw [Real.log_inv]
      exact tendsto_neg_atBot_atTop.comp h1
    exact tendsto_inv_atTop_zero.comp h2
  have hbound : ∀ᶠ p in 𝓝[>] (0:ℝ),
      0 ≤ fixedMean s p ∧ fixedMean s p ≤ C * (Real.log p⁻¹)⁻¹ := by
    filter_upwards [eventually_small hs hs1] with p hp
    obtain ⟨hp0, hp, hT, ha⟩ := hp
    have hp1 : p < 1 := by linarith
    have hM := fixedMoment_le_of_small hs hs1 hp0 hp hT ha
    have hE := entropy_ge hp0 hp1
    have hlogpos : 0 < Real.log p⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hp0, hp1⟩)
    refine ⟨(fixedMean_pos hs hs1 hp0 hp1).le, ?_⟩
    have hF : p * (1 - p) / entropy p ≤ (Real.log p⁻¹)⁻¹ := by
      rw [div_le_iff₀ (entropy_pos hp0 hp1)]
      calc p * (1 - p) ≤ p := by nlinarith
        _ = (Real.log p⁻¹)⁻¹ * (p * Real.log p⁻¹) := by
            rw [mul_comm p, ← mul_assoc, inv_mul_cancel₀ hlogpos.ne', one_mul]
        _ ≤ (Real.log p⁻¹)⁻¹ * entropy p :=
            mul_le_mul_of_nonneg_left hE (inv_nonneg.2 hlogpos.le)
    have hC' : 0 < (2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) := fixedMean_const_pos hs1
    have hM0 : 0 ≤ fixedMoment s p := by linarith [one_le_fixedMoment hs hs1 hp0 hp1]
    unfold fixedMean
    calc (2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) * (p * (1 - p) / entropy p) * fixedMoment s p
        ≤ (2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) * (Real.log p⁻¹)⁻¹ * momentBound s :=
          mul_le_mul (mul_le_mul_of_nonneg_left hF hC'.le) hM hM0
            (mul_nonneg hC'.le (inv_nonneg.2 hlogpos.le))
      _ = C * (Real.log p⁻¹)⁻¹ := by rw [hCdef]; ring
  refine squeeze_zero' (hbound.mono fun p hp => hp.1) (hbound.mono fun p hp => hp.2) ?_
  have := hlog.const_mul C
  rwa [mul_zero] at this

/-! ### The uncountable subfamily -/

/-- Every value in `(0, H̄_s(1/2))` is attained on `(0, 1/2)`. -/
theorem exists_fixedMean_eq {s y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hy0 : 0 < y)
    (hy : y < fixedMean s (1/2)) : ∃ p ∈ Ioo (0:ℝ) (1/2), fixedMean s p = y := by
  have hev : ∀ᶠ p in 𝓝[>] (0:ℝ), fixedMean s p < y ∧ 0 < p ∧ p < 1/2 := by
    have h1 := (tendsto_fixedMean_zero hs hs1).eventually (gt_mem_nhds hy0)
    have h2 : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < p := eventually_mem_nhdsWithin
    have h3 : ∀ᶠ p in 𝓝[>] (0:ℝ), p < 1/2 :=
      (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0:ℝ)))).eventually
        (gt_mem_nhds (by norm_num))
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    exact ⟨hp1, hp2, hp3⟩
  obtain ⟨p₁, hp₁y, hp₁0, hp₁⟩ := hev.exists
  have hcont : ContinuousOn (fixedMean s) (Icc p₁ (1/2)) :=
    (continuousOn_fixedMean hs hs1).mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have himage := intermediate_value_Icc hp₁.le hcont
  obtain ⟨p, hp, hpy⟩ := himage ⟨hp₁y.le, hy.le⟩
  refine ⟨p, ⟨by linarith [hp.1], lt_of_le_of_ne hp.2 fun h => ?_⟩, hpy⟩
  rw [h] at hpy
  linarith

/-- **The uncountable subfamily**: a set `S ⊆ (0, 1/2)` that is not countable, on which
the mean is injective. -/
theorem exists_uncountable_injOn_fixedMean {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ S : Set ℝ, S ⊆ Ioo 0 (1/2) ∧ ¬ S.Countable ∧ S.InjOn (fixedMean s) := by
  set c := fixedMean s (1/2) with hc
  have hc0 : 0 < c := fixedMean_pos hs hs1 (by norm_num) (by norm_num)
  have hex : ∀ y : ℝ, y ∈ Ioo 0 c → ∃ p ∈ Ioo (0:ℝ) (1/2), fixedMean s p = y :=
    fun y hy => exists_fixedMean_eq hs hs1 hy.1 hy.2
  choose! g hg using hex
  refine ⟨g '' Ioo 0 c, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hg y hy).1
  · intro hS
    have himg : (fixedMean s '' (g '' Ioo 0 c)).Countable := hS.image _
    have heq : fixedMean s '' (g '' Ioo 0 c) = Ioo 0 c := by
      ext y
      constructor
      · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        rw [(hg y' hy').2]; exact hy'
      · intro hy
        exact ⟨g y, ⟨y, hy, rfl⟩, (hg y hy).2⟩
    rw [heq] at himg
    have hvol := himg.measure_zero volume
    rw [Real.volume_Ioo, sub_zero] at hvol
    exact absurd hvol (ENNReal.ofReal_pos.2 hc0).ne'
  · rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ h
    rw [(hg y₁ hy₁).2, (hg y₂ hy₂).2] at h
    rw [h]

end

end BrownianImages
