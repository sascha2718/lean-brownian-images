/-
`thm:profile-uniform-continuity` of `BrownianImagesComplete.tex`: the expected profile
`H_μ` is uniformly continuous on `ℝ`.

* `H_eq_Hlog`: the substitution `η = e^x` of `eq:h-definition`.
* `tendsto_integral_logKern_sub`: translation is continuous in `L¹(ℝ)` for the
  logarithmic kernel.
* `audit_profile_uniform_continuity`: the statement of `thm:profile-uniform-continuity`.
-/
import BrownianImages.Kernel
import BrownianImages.Profile

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {s A : ℝ} {μ : Measure ℝ}

/-! ### The substitution `η = e^x` -/

/-- The substitution `η = e^x` in `eq:h-definition`:
`H_μ(t) = ∫_ℝ e^x φ(e^x) G(2t - x) dx`. -/
theorem H_eq_Hlog (s : ℝ) (μ : Measure ℝ) (v : ℝ) : H s μ v = Hlog s μ v := by
  have himg : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
    rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.univ : Set ℝ) := Real.exp_injective.injOn
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun η : ℝ => kern s η * G s μ (2 * v - Real.log η))
  rw [himg] at hsub
  rw [H, hsub, Measure.restrict_univ, Hlog]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, Real.log_exp, logKern_eq]
  ring

/-! ### Continuity of translation in `L¹` for the logarithmic kernel -/

/-- Translation is continuous in `L¹(ℝ)` at the logarithmic kernel: this is dominated
convergence against the envelope `e^{-c|x|}` of `logKern_le_exp_neg_mul_abs`. -/
theorem tendsto_integral_logKern_sub (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun h : ℝ => ∫ x : ℝ, |logKern s (x + h) - logKern s x|) (𝓝 0) (𝓝 0) := by
  set c : ℝ := min s (1 - s) with hc
  have hc0 : 0 < c := lt_min hs0 (by linarith)
  have hbound : Integrable (fun x : ℝ => 2 * Real.exp c * Real.exp (-c * |x|)) :=
    (integrable_exp_neg_mul_abs hc0).const_mul _
  have hexpc : (1:ℝ) ≤ Real.exp c := Real.one_le_exp hc0.le
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (l := 𝓝 (0:ℝ))
    (F := fun (h : ℝ) (x : ℝ) => |logKern s (x + h) - logKern s x|)
    (f := fun _ : ℝ => (0:ℝ))
    (bound := fun x : ℝ => 2 * Real.exp c * Real.exp (-c * |x|))
    (Eventually.of_forall fun h => by
      exact (continuous_abs.comp
        ((continuous_logKern.comp (continuous_id.add continuous_const)).sub
          continuous_logKern)).aestronglyMeasurable)
    ?_ hbound ?_
  · simpa using hmain
  · have hsmall : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), |h| ≤ 1 := by
      have hmem : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), h ∈ Set.Icc (-1:ℝ) 1 :=
        Icc_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hmem] with h hh
      exact abs_le.mpr ⟨hh.1, hh.2⟩
    filter_upwards [hsmall] with h hh
    refine Eventually.of_forall fun x => ?_
    have hk1 : logKern s (x + h) ≤ Real.exp (-c * |x + h|) :=
      logKern_le_exp_neg_mul_abs hs0 hs1 _
    have hk2 : logKern s x ≤ Real.exp (-c * |x|) :=
      logKern_le_exp_neg_mul_abs hs0 hs1 _
    have htri : |x| ≤ |x + h| + 1 := by
      have habs : |x| ≤ |x + h| + |h| := by
        have := abs_add_le (x + h) (-h)
        simpa using this
      linarith [habs, hh]
    have hexp1 : Real.exp (-c * |x + h|) ≤ Real.exp c * Real.exp (-c * |x|) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hc0.le]
    have hexp2 : Real.exp (-c * |x|) ≤ Real.exp c * Real.exp (-c * |x|) := by
      nlinarith [Real.exp_pos (-c * |x|)]
    have hpos1 : 0 < logKern s (x + h) := logKern_pos _
    have hpos2 : 0 < logKern s x := logKern_pos _
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have hE : (0:ℝ) < Real.exp c * Real.exp (-c * |x|) :=
      mul_pos (Real.exp_pos c) (Real.exp_pos _)
    have hb1 := hk1.trans hexp1
    have hb2 := hk2.trans hexp2
    constructor <;> nlinarith [hpos1, hpos2, hE, hb1, hb2]
  · refine Eventually.of_forall fun x => ?_
    have hcont : Continuous fun h : ℝ => |logKern s (x + h) - logKern s x| :=
      continuous_abs.comp
        ((continuous_logKern.comp (continuous_const.add continuous_id)).sub continuous_const)
    simpa using hcont.tendsto 0

/-! ### The uniform-continuity estimate -/

/-- The estimate of the proof of `thm:profile-uniform-continuity`:
`|H_μ(a) - H_μ(b)| ≤ ‖G‖_∞ ‖k(· + 2(a-b)) - k‖_1`. -/
theorem abs_H_sub_le [IsProbabilityMeasure μ] (hs0 : 0 < s) (hs1 : s < 1)
    (hμ : IsFrostman s A μ) (a b : ℝ) :
    |H s μ a - H s μ b| ≤ A * ∫ x : ℝ, |logKern s (x + 2 * (a - b)) - logKern s x| := by
  set t : ℝ := 2 * (a - b) with ht
  have hkint : Integrable (logKern s) := logKern_integrable hs0 hs1
  have hkintt : Integrable (fun y : ℝ => logKern s (y + t)) := hkint.comp_add_right t
  have hGcont : Continuous (G s μ) := continuous_G hs0 hμ
  -- the two integrands
  have hmeas1 : AEStronglyMeasurable
      (fun y : ℝ => logKern s (y + t) * G s μ (2 * b - y)) volume :=
    ((continuous_logKern.comp (continuous_id.add continuous_const)).mul
      (hGcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable
      (fun y : ℝ => logKern s y * G s μ (2 * b - y)) volume :=
    (continuous_logKern.mul (hGcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hint1 : Integrable (fun y : ℝ => logKern s (y + t) * G s μ (2 * b - y)) := by
    refine Integrable.mono' (hkintt.const_mul A) hmeas1 (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logKern_pos _)]
    calc logKern s (y + t) * |G s μ (2 * b - y)|
        ≤ logKern s (y + t) * A :=
          mul_le_mul_of_nonneg_left (abs_G_le hs0 hμ _) (logKern_pos _).le
      _ = A * logKern s (y + t) := mul_comm _ _
  have hint2 : Integrable (fun y : ℝ => logKern s y * G s μ (2 * b - y)) := by
    refine Integrable.mono' (hkint.const_mul A) hmeas2 (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logKern_pos _)]
    calc logKern s y * |G s μ (2 * b - y)|
        ≤ logKern s y * A :=
          mul_le_mul_of_nonneg_left (abs_G_le hs0 hμ _) (logKern_pos _).le
      _ = A * logKern s y := mul_comm _ _
  -- the change of variables
  have hshift : (∫ y : ℝ, logKern s (y + t) * G s μ (2 * b - y)) = Hlog s μ a := by
    have hcongr : (∫ y : ℝ, logKern s (y + t) * G s μ (2 * b - y))
        = ∫ y : ℝ, logKern s (y + t) * G s μ (2 * a - (y + t)) := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      have harg : 2 * a - (y + t) = 2 * b - y := by rw [ht]; ring
      rw [harg]
    rw [hcongr, Hlog]
    exact integral_add_right_eq_self (fun x : ℝ => logKern s x * G s μ (2 * a - x)) t
  have hdiff : H s μ a - H s μ b
      = ∫ y : ℝ, (logKern s (y + t) - logKern s y) * G s μ (2 * b - y) := by
    rw [H_eq_Hlog, H_eq_Hlog, ← hshift, Hlog, ← integral_sub hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    ring
  -- the bound
  have hbint : Integrable
      (fun y : ℝ => A * |logKern s (y + t) - logKern s y|) :=
    ((hkintt.sub hkint).abs).const_mul A
  rw [hdiff, ← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le hbint (Eventually.of_forall fun y => ?_)) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    calc |logKern s (y + t) - logKern s y| * |G s μ (2 * b - y)|
        ≤ |logKern s (y + t) - logKern s y| * A :=
          mul_le_mul_of_nonneg_left (abs_G_le hs0 hμ _) (abs_nonneg _)
      _ = A * |logKern s (y + t) - logKern s y| := mul_comm _ _
  · rw [integral_const_mul]

/-! ### `thm:profile-uniform-continuity` -/

/-- `thm:profile-uniform-continuity`.  The expected profile is uniformly continuous. -/
theorem profile_uniformContinuous {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    UniformContinuous (H s μ) := by
  have hA : (1:ℝ) ≤ A := hμ.one_le_const
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have htend := tendsto_integral_logKern_sub hs0 hs1
  rw [Metric.tendsto_nhds] at htend
  obtain ⟨δ₀, hδ₀, hsmall⟩ :=
    Metric.eventually_nhds_iff.mp (htend (ε / A) (by positivity))
  refine ⟨δ₀ / 2, by positivity, ?_⟩
  intro a b hab
  have hdist : dist (2 * (a - b)) 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.dist_eq] at hab
    linarith [abs_nonneg (a - b)]
  have hI := hsmall hdist
  rw [Real.dist_eq, sub_zero] at hI
  have hle := abs_H_sub_le hs0 hs1 hμ a b
  have hIle : (∫ x : ℝ, |logKern s (x + 2 * (a - b)) - logKern s x|) < ε / A :=
    lt_of_le_of_lt (le_abs_self _) hI
  rw [Real.dist_eq]
  calc |H s μ a - H s μ b|
      ≤ A * ∫ x : ℝ, |logKern s (x + 2 * (a - b)) - logKern s x| := hle
    _ < A * (ε / A) := by exact mul_lt_mul_of_pos_left hIle hA0
    _ = ε := by field_simp

end BrownianImages
