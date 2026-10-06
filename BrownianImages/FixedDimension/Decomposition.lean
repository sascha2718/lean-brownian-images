/-
`eq:leading-ones` in integral form, for the proof of `thm:remainder-derivative`: with `N`
the number of initial ones of the coding of `Y`, `Y = 1 - b^N + a b^N Y''`, so
`M_p(s) = ∑_{n≥0} p qⁿ g_n` with `g_n = 𝔼[(1 - b^{n+1} - a(X - b^{n+1} Y''))^{-s}]`; and the
level sum of the kernel `φ_n` at the real parameter `p` is the Bernoulli double integral of
`φ_n` at the coded points of the first `m` letters, which converges to `g_n`.

* `leadingTerm`, `leadingAux`: `g_n` and `h_n = 𝔼[(1 - b^{n+1}(1 - Y) - aX)^{-s}]`.
* `leadingAux_rec`, `hasSum_leadingTerm`: `h_n = q h_{n+1} + p g_n` and
  `M_p(s) = ∑ p qⁿ g_n`.
* `levelSum_kernel_ofReal`, `tendsto_integral_kernel_codeSeq`: the level sums at `p` and
  their limit `g_n`.
-/
import BrownianImages.FixedDimension.Kernel

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology ENNReal

noncomputable section

/-! ### The real decomposition -/

/-- `g_n = 𝔼[(1 - b^{n+1} - a(X - b^{n+1} Y))^{-s}]`. -/
def leadingTerm (s p : ℝ) (n : ℕ) : ℝ :=
  ∫ ω', ∫ ω, (1 - fixedB s p ^ (n + 1) -
    fixedA s p * (fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω')) ^ (-s)
    ∂twoBern (1 - p) ∂twoBern (1 - p)

/-- `h_n = 𝔼[(1 - b^{n+1}(1 - Y) - aX)^{-s}]`. -/
def leadingAux (s p : ℝ) (n : ℕ) : ℝ :=
  ∫ ω', ∫ ω, (1 - fixedB s p ^ (n + 1) * (1 - fixedCode s p ω') - fixedA s p * fixedCode s p ω) ^ (-s)
    ∂twoBern (1 - p) ∂twoBern (1 - p)

section Real

variable {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
include hs hs1 hp0 hp1

theorem gap_pos : 0 < 1 - fixedA s p - fixedB s p := by
  linarith [fixedA_add_fixedB_lt_one hs hs1 hp0 hp1]

/-- The base of `h_n` lies in `[1 - a - b, 1]` at coded points. -/
theorem leadingAux_base_mem (n : ℕ) (ω ω' : ℕ → Fin 2) :
    1 - fixedA s p - fixedB s p
      ≤ 1 - fixedB s p ^ (n + 1) * (1 - fixedCode s p ω') - fixedA s p * fixedCode s p ω ∧
    1 - fixedB s p ^ (n + 1) * (1 - fixedCode s p ω') - fixedA s p * fixedCode s p ω ≤ 1 := by
  have hX := fixedCode_mem_Icc hs hp0 hp1 ω
  have hY := fixedCode_mem_Icc hs hp0 hp1 ω'
  have ha := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have hb1 := fixedB_le_one hs hp0 hp1
  have hbn : fixedB s p ^ (n + 1) ≤ fixedB s p := by
    calc fixedB s p ^ (n + 1) ≤ fixedB s p ^ 1 := pow_le_pow_of_le_one hb0.le hb1 (by omega)
      _ = fixedB s p := pow_one _
  have hbn0 : 0 ≤ fixedB s p ^ (n + 1) := by positivity
  constructor
  · nlinarith [hX.2, hY.1, hY.2, mul_nonneg hbn0 (sub_nonneg.2 hY.2)]
  · nlinarith [hX.1, hY.1, hY.2, mul_nonneg hbn0 (sub_nonneg.2 hY.2)]

/-- The base of `g_n` lies in `[1 - a - b, 1]` at coded points. -/
theorem leadingTerm_base_mem (n : ℕ) (ω ω' : ℕ → Fin 2) :
    1 - fixedA s p - fixedB s p
      ≤ 1 - fixedB s p ^ (n + 1) -
          fixedA s p * (fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω') ∧
    1 - fixedB s p ^ (n + 1) -
        fixedA s p * (fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω') ≤ 1 := by
  have hX := fixedCode_mem_Icc hs hp0 hp1 ω
  have hY := fixedCode_mem_Icc hs hp0 hp1 ω'
  have ha := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have hb1 := fixedB_le_one hs hp0 hp1
  have hbn : fixedB s p ^ (n + 1) ≤ fixedB s p := by
    calc fixedB s p ^ (n + 1) ≤ fixedB s p ^ 1 := pow_le_pow_of_le_one hb0.le hb1 (by omega)
      _ = fixedB s p := pow_one _
  have hbn0 : 0 ≤ fixedB s p ^ (n + 1) := by positivity
  have ha1 := fixedA_le_one hs hp0 hp1
  have haY : fixedA s p * fixedCode s p ω' ≤ 1 := by nlinarith [hY.1, hY.2]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hX.2 ha.le, mul_nonneg ha.le (mul_nonneg hbn0 hY.1)]
  · nlinarith [mul_nonneg hbn0 (sub_nonneg.2 haY), mul_nonneg ha.le hX.1]

omit hs1 hp0 hp1 in
/-- A power `t^{-s}` of a base in `[g, 1]`, `g > 0`, lies in `[1, g^{-s}]`. -/
theorem rpow_neg_mem {g t : ℝ} (hg : 0 < g) (ht : g ≤ t) (ht1 : t ≤ 1) :
    1 ≤ t ^ (-s) ∧ t ^ (-s) ≤ g ^ (-s) := by
  constructor
  · calc (1:ℝ) = 1 ^ (-s) := (Real.one_rpow _).symm
      _ ≤ t ^ (-s) := rpow_neg_antitone (hg.trans_le ht) ht1 hs.le
  · exact rpow_neg_antitone hg ht hs.le

end Real

section Recursion

variable {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
include hs hs1 hp0 hp1

/-- The integrand of `h_n`. -/
def auxKernel (s p : ℝ) (n : ℕ) (ω ω' : ℕ → Fin 2) : ℝ :=
  (1 - fixedB s p ^ (n + 1) * (1 - fixedCode s p ω') - fixedA s p * fixedCode s p ω) ^ (-s)

/-- The integrand of `g_n`. -/
def termKernel (s p : ℝ) (n : ℕ) (ω ω' : ℕ → Fin 2) : ℝ :=
  (1 - fixedB s p ^ (n + 1) -
    fixedA s p * (fixedCode s p ω - fixedB s p ^ (n + 1) * fixedCode s p ω')) ^ (-s)

omit hs hs1 hp0 hp1 in
theorem measurable_auxKernel (n : ℕ) : Measurable (Function.uncurry (auxKernel s p n)) := by
  have h1 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) => fixedCode s p q.1 :=
    (measurable_fixedCode s p).comp measurable_fst
  have h2 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) => fixedCode s p q.2 :=
    (measurable_fixedCode s p).comp measurable_snd
  exact ((measurable_const.sub (measurable_const.mul (measurable_const.sub h2))).sub
    (measurable_const.mul h1)).pow_const _

omit hs hs1 hp0 hp1 in
theorem measurable_termKernel (n : ℕ) : Measurable (Function.uncurry (termKernel s p n)) := by
  have h1 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) => fixedCode s p q.1 :=
    (measurable_fixedCode s p).comp measurable_fst
  have h2 : Measurable fun q : (ℕ → Fin 2) × (ℕ → Fin 2) => fixedCode s p q.2 :=
    (measurable_fixedCode s p).comp measurable_snd
  exact ((measurable_const.sub measurable_const).sub
    (measurable_const.mul (h1.sub (measurable_const.mul h2)))).pow_const _

theorem auxKernel_mem (n : ℕ) (ω ω' : ℕ → Fin 2) :
    1 ≤ auxKernel s p n ω ω' ∧ auxKernel s p n ω ω' ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  obtain ⟨h1, h2⟩ := leadingAux_base_mem hs hs1 hp0 hp1 n ω ω'
  exact rpow_neg_mem hs (gap_pos hs hs1 hp0 hp1) h1 h2

theorem termKernel_mem (n : ℕ) (ω ω' : ℕ → Fin 2) :
    1 ≤ termKernel s p n ω ω' ∧ termKernel s p n ω ω' ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  obtain ⟨h1, h2⟩ := leadingTerm_base_mem hs hs1 hp0 hp1 n ω ω'
  exact rpow_neg_mem hs (gap_pos hs hs1 hp0 hp1) h1 h2

theorem abs_auxKernel_le (n : ℕ) (ω ω' : ℕ → Fin 2) :
    |auxKernel s p n ω ω'| ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  obtain ⟨h1, h2⟩ := auxKernel_mem hs hs1 hp0 hp1 n ω ω'
  rw [abs_of_nonneg (by linarith)]; exact h2

theorem abs_termKernel_le (n : ℕ) (ω ω' : ℕ → Fin 2) :
    |termKernel s p n ω ω'| ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  obtain ⟨h1, h2⟩ := termKernel_mem hs hs1 hp0 hp1 n ω ω'
  rw [abs_of_nonneg (by linarith)]; exact h2

omit hs hs1 in
/-- The inner integral of a bounded jointly measurable kernel is measurable in the outer
variable and bounded by the same constant. -/
theorem measurable_inner_integral {K : (ℕ → Fin 2) → (ℕ → Fin 2) → ℝ}
    (hK : Measurable (Function.uncurry K)) :
    Measurable fun ω' => ∫ ω, K ω ω' ∂twoBern (1 - p) := by
  have := isProbabilityMeasure_twoBern_fixed hp0 hp1
  exact (hK.stronglyMeasurable.integral_prod_left' (μ := twoBern (1 - p))).measurable

omit hs hs1 in
theorem abs_inner_integral_le {K : (ℕ → Fin 2) → (ℕ → Fin 2) → ℝ} {C : ℝ}
    (hC : ∀ ω ω', |K ω ω'| ≤ C) (ω' : ℕ → Fin 2) :
    |∫ ω, K ω ω' ∂twoBern (1 - p)| ≤ C := by
  have := isProbabilityMeasure_twoBern_fixed hp0 hp1
  have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - p)) (f := fun ω => K ω ω')
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω ω')
  simpa [Real.norm_eq_abs] using h

/-- `eq:leading-ones`: `h_n = q h_{n+1} + p g_n`, by splitting off the first letter of `Y`. -/
theorem leadingAux_rec (n : ℕ) :
    leadingAux s p n = (1 - p) * leadingAux s p (n + 1) + p * leadingTerm s p n := by
  have hprob : IsProbabilityMeasure (twoDigit (1 - p)) :=
    isProbabilityMeasure_twoDigit (by linarith) (by linarith)
  have hmeas := measurable_inner_integral hp0 hp1 (measurable_auxKernel (s := s) (p := p) n)
  have hbound := abs_inner_integral_le hp0 hp1 (abs_auxKernel_le hs hs1 hp0 hp1 n)
  have h := integral_infinitePi_cons (twoDigit (1 - p))
    (f := fun ω' => ∫ ω, auxKernel s p n ω ω' ∂twoBern (1 - p)) hmeas hbound
  unfold twoBern at h
  simp only [Fin.sum_univ_two] at h
  rw [twoDigit_toReal_zero (by linarith), twoDigit_toReal_one (by linarith)] at h
  show (∫ ω', ∫ ω, auxKernel s p n ω ω' ∂twoBern (1 - p) ∂twoBern (1 - p)) = _
  unfold twoBern
  rw [h]
  -- the two branches
  have h0 : ∀ ω', (∫ ω, auxKernel s p n ω (cons 0 ω') ∂Measure.infinitePi fun _ : ℕ => twoDigit (1 - p))
      = ∫ ω, termKernel s p n ω ω' ∂Measure.infinitePi fun _ : ℕ => twoDigit (1 - p) := by
    intro ω'
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    unfold auxKernel termKernel
    rw [fixedCode_cons_zero hs hp0 hp1]
    ring_nf
  have h1 : ∀ ω', (∫ ω, auxKernel s p n ω (cons 1 ω') ∂Measure.infinitePi fun _ : ℕ => twoDigit (1 - p))
      = ∫ ω, auxKernel s p (n + 1) ω ω' ∂Measure.infinitePi fun _ : ℕ => twoDigit (1 - p) := by
    intro ω'
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    unfold auxKernel
    rw [fixedCode_cons_one hs hp0 hp1]
    ring_nf
  simp_rw [h0, h1]
  unfold leadingAux leadingTerm twoBern auxKernel termKernel
  ring

omit hs hs1 hp0 hp1 in
theorem leadingAux_zero : leadingAux s p 0 = fixedMoment s p := by
  unfold leadingAux fixedMoment fixedKernel fixedCross
  simp only [zero_add, pow_one]
  congr 1; funext ω'; congr 1; funext ω
  ring_nf

theorem abs_leadingAux_le (n : ℕ) : |leadingAux s p n| ≤ (1 - fixedA s p - fixedB s p) ^ (-s) := by
  have := isProbabilityMeasure_twoBern_fixed hp0 hp1
  have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - p))
    (f := fun ω' => ∫ ω, auxKernel s p n ω ω' ∂twoBern (1 - p))
    (Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs]
      exact abs_inner_integral_le hp0 hp1 (abs_auxKernel_le hs hs1 hp0 hp1 n) ω')
  rw [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at h
  unfold auxKernel at h
  unfold leadingAux
  exact h

theorem leadingTerm_nonneg (n : ℕ) : 0 ≤ leadingTerm s p n := by
  have := isProbabilityMeasure_twoBern_fixed hp0 hp1
  unfold leadingTerm
  refine integral_nonneg fun ω' => integral_nonneg fun ω => ?_
  exact le_trans zero_le_one (termKernel_mem hs hs1 hp0 hp1 n ω ω').1

/-- The partial sums of `eq:leading-ones`. -/
theorem fixedMoment_eq_partial (N : ℕ) :
    fixedMoment s p = (∑ n ∈ Finset.range N, p * (1 - p) ^ n * leadingTerm s p n)
      + (1 - p) ^ N * leadingAux s p N := by
  induction N with
  | zero => simp [leadingAux_zero]
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, leadingAux_rec hs hs1 hp0 hp1 N]
    ring

/-- **`eq:leading-ones`.**  `M_p(s) = ∑_{n≥0} p qⁿ g_n`. -/
theorem hasSum_leadingTerm :
    HasSum (fun n => p * (1 - p) ^ n * leadingTerm s p n) (fixedMoment s p) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun n => by
    have := leadingTerm_nonneg hs hs1 hp0 hp1 n
    have : 0 ≤ (1 - p) ^ n := by positivity
    positivity]
  have hq : |1 - p| < 1 := by rw [abs_lt]; constructor <;> linarith
  have htail : Tendsto (fun N => (1 - p) ^ N * leadingAux s p N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => (1 - p) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
    have h2 : Tendsto (fun N => |(1 - p) ^ N| * (1 - fixedA s p - fixedB s p) ^ (-s)) atTop
        (𝓝 (|0| * (1 - fixedA s p - fixedB s p) ^ (-s))) :=
      ((continuous_abs.tendsto 0).comp h1).mul_const _
    rw [abs_zero, zero_mul] at h2
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun N => abs_nonneg _) (Eventually.of_forall fun N => ?_)
    show |(1 - p) ^ N * leadingAux s p N| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_leadingAux_le hs hs1 hp0 hp1 N) (abs_nonneg _)
  have : Tendsto (fun N => fixedMoment s p - (1 - p) ^ N * leadingAux s p N) atTop
      (𝓝 (fixedMoment s p - 0)) := tendsto_const_nhds.sub htail
  rw [sub_zero] at this
  refine this.congr fun N => ?_
  rw [fixedMoment_eq_partial hs hs1 hp0 hp1 N]
  ring

end Recursion

end

end BrownianImages
