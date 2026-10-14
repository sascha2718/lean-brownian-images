module

/-
The real-parameter expectation identity in `thm:level-sums`, for an arbitrary
continuous kernel with the stated coordinate Lipschitz bound. The open convex
domain need only contain the finite coded points: it contains `[0,1)`, and the
natural measure gives zero mass to the possibly missing endpoint `1`.
-/
public import BrownianImages.FixedDimension.Profiles

@[expose] public section

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- The constant second address approaches the endpoint `1`. -/
private theorem cpointSeq_one_address (a b : ℂ) (m : ℕ) :
    cpointSeq a b m (fun _ => 1) = 1 - b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    change b * cpointSeq a b m (fun _ => 1) + (1 - b) = 1 - b ^ (m + 1)
    rw [ih, pow_succ]
    ring

/-- A convex domain containing all finite coded points contains the real interval
`[0,1)`, even when the endpoint `1` lies on its boundary. -/
theorem ofReal_mem_domain_of_cpointSeq {s p : ℝ} (hs : 0 < s)
    (hp0 : 0 < p) (hp1 : p < 1) {D : Set ℂ} (hD : Convex ℝ D)
    (hpoints : ∀ m ω, cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m ω ∈ D)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : (x : ℂ) ∈ D := by
  have hzero : (0 : ℂ) ∈ D := by simpa using hpoints 0 (fun _ => 0)
  by_cases hx0 : x = 0
  · simpa [hx0] using hzero
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hlim : Tendsto (fun m : ℕ => 1 - fixedB s p ^ m) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (fixedB_pos (s := s) hp1).le
        (fixedB_lt_one hs hp0 hp1))
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds hx.2)).exists
  let y := 1 - fixedB s p ^ m
  have hypos : 0 < y := hxpos.trans hm
  have hy : (y : ℂ) ∈ D := by
    have h := hpoints m (fun _ => 1)
    rw [cpointSeq_one_address, cb_ofReal hp1.le] at h
    simpa only [y, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using h
  have hratio : x / y ≤ 1 := (div_le_one hypos).2 hm.le
  have h := hD hzero hy (sub_nonneg.mpr hratio) (div_nonneg hx.1 hypos.le)
    (by ring : 1 - x / y + x / y = 1)
  have heq : (1 - x / y) • (0 : ℂ) + (x / y) • (y : ℂ) = (x : ℂ) := by
    simp only [smul_zero, zero_add, Complex.real_smul, ← Complex.ofReal_mul,
      div_mul_cancel₀ x hypos.ne']
  rwa [heq] at h

/-- The natural code avoids the endpoint `1` almost surely. -/
theorem ae_fixedCode_lt_one {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᵐ ω ∂twoBern (1 - p), fixedCode s p ω < 1 := by
  obtain ⟨⟨K, μ⟩, hμ, _⟩ :=
    (fixedSystem s p hs hp0 hp1).exists_unique_isNatural (fixedSystem_isDimension hs hp0 hp1)
  have hosc := fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman _ hs.le hμ
  have hmap := map_fixedCode_twoBern hs hp0 hp1 hμ
  have hnull : (twoBern (1 - p)) {ω | fixedCode s p ω = 1} = 0 := by
    have heq := Measure.map_apply (μ := twoBern (1 - p))
      (measurable_fixedCode s p) (measurableSet_singleton (1 : ℝ))
    rw [hmap] at heq
    have hset : fixedCode s p ⁻¹' {(1 : ℝ)} = {ω | fixedCode s p ω = 1} := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    rw [hset] at heq
    exact heq.symm.trans (hA.measure_singleton hs 1)
  have hne : ∀ᵐ ω ∂twoBern (1 - p), fixedCode s p ω ≠ 1 := by
    simpa only [ae_iff, not_not, mem_ofPred_eq] using hnull
  filter_upwards [hne] with ω hω
  exact lt_of_le_of_ne (fixedCode_mem_Icc hs hp0 hp1 ω).2 hω

/-- `thm:level-sums`: at a real parameter the level sums of any continuous
coordinate-Lipschitz kernel converge to its expectation under two independent
natural codings. -/
theorem tendsto_levelSum_expectation {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp0 : 0 < p) (hp1 : p < 1) {D : Set ℂ} (hDopen : IsOpen D) (hD : Convex ℝ D)
    (hpoints : ∀ m ω, cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m ω ∈ D)
    {φ : ℂ → ℂ → ℂ → ℂ} {L : ℝ} (hL0 : 0 ≤ L)
    (hcont : ContinuousOn (fun q : ℂ × ℂ => φ p q.1 q.2) (D ×ˢ D))
    (hL : ∀ x ∈ D, ∀ y ∈ D, ∀ x' ∈ D, ∀ y' ∈ D,
      ‖φ p x' y' - φ p x y‖ ≤ L * (‖x' - x‖ + ‖y' - y‖)) :
    Tendsto (fun m => levelSum (ca s) (cb s) φ m (p : ℂ)) atTop
      (𝓝 (∫ ω', ∫ ω, φ p (fixedCode s p ω) (fixedCode s p ω')
        ∂twoBern (1 - p) ∂twoBern (1 - p))) := by
  let : IsProbabilityMeasure (twoBern (1 - p)) := isProbabilityMeasure_twoBern_fixed hp0 hp1
  let C := ‖φ p 0 0‖ + 2 * L
  let X (m : ℕ) (ω : ℕ → Fin 2) : ℂ :=
    ((codeSeq (fixedSystem s p hs hp0 hp1) ω m : ℝ) : ℂ)
  let G (m : ℕ) (ω ω' : ℕ → Fin 2) := φ p (X m ω) (X m ω')
  have hX : ∀ m ω, X m ω = cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m ω := by
    intro m ω
    rw [ca_ofReal hp0.le, cb_ofReal hp1.le, cpointSeq_ofReal hs hp0 hp1]
  have hXm : ∀ m ω, X m ω ∈ D := fun m ω => hX m ω ▸ hpoints m ω
  have hzero : (0 : ℂ) ∈ D := by simpa using hpoints 0 (fun _ => 0)
  have hXnorm : ∀ m ω, ‖X m ω‖ ≤ 1 := by
    intro m ω
    simpa only [X, Complex.norm_real, Real.norm_of_nonneg (codeSeq_mem_Icc _ ω m).1]
      using (codeSeq_mem_Icc (fixedSystem s p hs hp0 hp1) ω m).2
  have hG : ∀ m, Measurable (Function.uncurry (G m)) := by
    intro m
    have hXcont : Continuous (X m) := Complex.continuous_ofReal.comp (continuous_codeSeq _ m)
    exact (hcont.comp_continuous ((hXcont.comp continuous_fst).prodMk
      (hXcont.comp continuous_snd)) (fun q => ⟨hXm m q.1, hXm m q.2⟩)).measurable
  have hbound : ∀ m ω ω', ‖G m ω ω'‖ ≤ C := by
    intro m ω ω'
    have h := hL 0 hzero 0 hzero (X m ω) (hXm m ω) (X m ω') (hXm m ω')
    simp only [sub_zero] at h
    calc ‖G m ω ω'‖ ≤ ‖φ p (X m ω) (X m ω') - φ p 0 0‖ + ‖φ p 0 0‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ L * (‖X m ω‖ + ‖X m ω'‖) + ‖φ p 0 0‖ := by gcongr
      _ ≤ C := by dsimp [C]; nlinarith [hXnorm m ω, hXnorm m ω']
  have hfinite : ∀ m, levelSum (ca s) (cb s) φ m (p : ℂ) =
      ∫ ω', ∫ ω, G m ω ω' ∂twoBern (1 - p) ∂twoBern (1 - p) := by
    intro m
    rw [integral_integral_eq_sum_weight hp0.le hp1.le m (hG m) (hbound m) ?_]
    · unfold levelSum
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      simp only [weightSeq_ofReal, G, hX]
    · intro ω₁ ω₁' ω₂ ω₂' h₁ h₂
      simp only [G, hX, cpointSeq_congr _ _ m h₁, cpointSeq_congr _ _ m h₂]
  have hmem : ∀ᵐ ω ∂twoBern (1 - p), (fixedCode s p ω : ℂ) ∈ D := by
    filter_upwards [ae_fixedCode_lt_one hs hs1 hp0 hp1] with ω hω
    exact ofReal_mem_domain_of_cpointSeq hs hp0 hp1 hD hpoints
      ⟨(fixedCode_mem_Icc hs hp0 hp1 ω).1, hω⟩
  have hpt : ∀ ω ω', (fixedCode s p ω : ℂ) ∈ D → (fixedCode s p ω' : ℂ) ∈ D →
      Tendsto (fun m => G m ω ω') atTop
        (𝓝 (φ p (fixedCode s p ω) (fixedCode s p ω'))) := by
    intro ω ω' hω hω'
    have hlim : ∀ ω, Tendsto (fun m => X m ω) atTop (𝓝 (fixedCode s p ω : ℂ)) := by
      intro ω
      rw [fixedCode_eq hs hp0 hp1]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_codeSeq _ ω)
    exact ((hcont.continuousAt ((hDopen.prod hDopen).mem_nhds ⟨hω, hω'⟩)).tendsto).comp
      ((hlim ω).prodMk_nhds (hlim ω'))
  have hinner : ∀ᵐ ω' ∂twoBern (1 - p), Tendsto
      (fun m => ∫ ω, G m ω ω' ∂twoBern (1 - p)) atTop
      (𝓝 (∫ ω, φ p (fixedCode s p ω) (fixedCode s p ω') ∂twoBern (1 - p))) := by
    filter_upwards [hmem] with ω' hω'
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
      (integrable_const C) (fun m => Eventually.of_forall fun ω => hbound m ω ω') ?_
    · exact ((hG m).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards [hmem] with ω hω using hpt ω ω' hω hω'
  simp_rw [hfinite]
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
    (integrable_const C) (fun m => Eventually.of_forall fun ω' => ?_) hinner
  · exact ((hG m).stronglyMeasurable.integral_prod_left'
      (μ := twoBern (1 - p))).aestronglyMeasurable
  · have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - p))
      (f := fun ω => G m ω ω') (Eventually.of_forall fun ω => hbound m ω ω')
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end

end BrownianImages
