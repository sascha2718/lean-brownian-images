/-
The general lattice branch of `thm:profile-asymptotics`.
The finite-delay renewal theorem already used for tube profiles applies to
`A + 1 - G(2v)`, whose renewal defect has the same sign as the tube defect.
Its uniform periodic limit gives a periodic limit for `G`; Gaussian smoothing
then gives the asserted limit for `H_μ^s`.
-/
import BrownianImages.NonLattice
import BrownianImages.Schief
import BrownianImages.Minkowski.TubeDiscreteRenewal
import BrownianImages.Minkowski.GenerationRatio

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

omit [Nonempty ι] in
/-- The lattice span in `thm:profile-asymptotics` becomes half that span for
the half-logarithmic renewal equation. -/
theorem tubeArithmetic_of_log_lattice {h : ℝ}
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h) :
    S.TubeArithmetic (h / 2) := by
  ext x
  constructor
  · intro hx
    have hx2 := S.two_mul_mem_logRatio_closure_of_mem_halfLogRatio_closure hx
    rw [hlat, AddSubgroup.mem_zmultiples_iff] at hx2
    obtain ⟨k, hk⟩ := hx2
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul] at hk ⊢
    linarith
  · intro hx
    rw [AddSubgroup.mem_zmultiples_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have hx2 : 2 * x ∈ AddSubgroup.closure (Set.range S.logRatio) := by
      rw [hlat, AddSubgroup.mem_zmultiples_iff]
      refine ⟨k, ?_⟩
      simp only [zsmul_eq_mul] at hk ⊢
      linarith
    simpa using S.half_mul_mem_halfLogRatio_closure_of_mem_logRatio_closure hx2

/-- The classical lower regularity estimate bounds the critical pair-distance
profile away from zero on the positive half-line. -/
theorem IsNatural.lower_bound_G {K : Set ℝ} {s : ℝ} (hs : 0 ≤ s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {w : ℝ} (hw : 0 ≤ w) :
    (S.minRatio / 2) ^ s ≤ G s μ w := by
  have := hμ.isProbabilityMeasure
  have hr := S.minRatio_pos
  have hδ0 : 0 < Real.exp (-w) := Real.exp_pos _
  have hδ1 : Real.exp (-w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hprod : ENNReal.ofReal ((S.minRatio * Real.exp (-w) / 2) ^ s) ≤
      (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ Real.exp (-w)} := by
    rw [phi_prod_eq]
    calc ENNReal.ofReal ((S.minRatio * Real.exp (-w) / 2) ^ s)
        = ∫⁻ _ : ℝ, ENNReal.ofReal ((S.minRatio * Real.exp (-w) / 2) ^ s) ∂μ := by simp
      _ ≤ ∫⁻ x, μ (Metric.closedBall x (Real.exp (-w))) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_iff.mpr hμ.support] with x hx
        exact hμ.le_measure_closedBall_of_mem S hs hx hδ0 hδ1
  have hphi : (S.minRatio * Real.exp (-w) / 2) ^ s ≤ Phi μ (Real.exp (-w)) := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hprod
  calc (S.minRatio / 2) ^ s
      = Real.exp (s * w) * (S.minRatio * Real.exp (-w) / 2) ^ s := by
        rw [show S.minRatio * Real.exp (-w) / 2 =
          (S.minRatio / 2) * Real.exp (-w) by ring,
          Real.mul_rpow (by positivity) hδ0.le, ← Real.exp_mul]
        rw [show -w * s = -(s * w) by ring, Real.exp_neg]
        field_simp
    _ ≤ G s μ w := mul_le_mul_of_nonneg_left hphi (Real.exp_pos _).le

/-- The lattice renewal limit for `G`, including continuity and positivity,
used in the proof of `thm:profile-asymptotics`. -/
theorem lattice_G_limit {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g h ∧
      (∀ w, 0 < g w) ∧ Tendsto (fun w ↦ G s μ w - g w) atTop (𝓝 0) := by
  classical
  have := hμ.isProbabilityMeasure
  have hr := S.minRatio_pos
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  obtain ⟨D, γ, hD, hγ, hdecay⟩ := exists_abs_renewalDefect_le_exp S
    (hosc.strongOpenSetCondition S hμ.attractor) hs0 hs1 hdim hμ
  let m : ℝ → ℝ := fun v ↦ A + 1 - G s μ (2 * v)
  let d : ℝ → ℝ := fun v ↦ S.renewalDefect s μ (2 * v)
  have hm : Continuous m := continuous_const.sub
    ((continuous_G hs0 hA).comp (continuous_const.mul continuous_id))
  have hmb : ∀ v : ℝ, 1 ≤ m v ∧ m v ≤ A + 1 := by
    intro v
    have hupper := (abs_le.mp (abs_G_le hs0 hA (2 * v))).2
    have hlower := G_nonneg (s := s) (μ := μ) (2 * v)
    dsimp [m]
    constructor <;> linarith
  have hren : ∀ v : ℝ, (∀ i, S.halfLogRatio i ≤ v) →
      m v = S.tubeRenewalConv s m v - d v := by
    intro v _
    dsimp [m, d, tubeRenewalConv, tubeWeight, renewalDefect, renewalConv]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hdim, one_mul]
    simp only [halfLogRatio]
    ring
  have hdefect : ∀ v : ℝ, (∀ i, S.halfLogRatio i ≤ v) →
      0 ≤ d v ∧ d v ≤ D * Real.exp (-(2 * γ) * v) := by
    intro v hv
    have hv0 : 0 ≤ v := (S.halfLogRatio_pos (Classical.arbitrary ι)).le.trans
      (hv (Classical.arbitrary ι))
    refine ⟨renewalDefect_nonneg S hμ _, ?_⟩
    have hb := hdecay (2 * v)
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * v)] at hb
    calc d v ≤ |S.renewalDefect s μ (2 * v)| := le_abs_self _
      _ ≤ D * Real.exp (-γ * (2 * v)) := hb
      _ = _ := by congr 2; ring
  obtain ⟨P, hPc, hPp, _, hPconv⟩ := S.exists_periodic_limit_of_tubeArithmetic
    (half_pos hh) (S.tubeArithmetic_of_log_lattice hlat) hdim hm
    (fun v _ ↦ by rw [abs_of_nonneg (by linarith [(hmb v).1] : 0 ≤ m v)]; exact (hmb v).2)
    hD.le (by positivity : 0 < 2 * γ) hren hdefect one_pos (fun v _ ↦ hmb v)
  have hlim := tendsto_sub_periodic_of_uniform_lattice (half_pos hh) hPp hPconv
  let g : ℝ → ℝ := fun w ↦ A + 1 - P (w / 2)
  have hg : Continuous g := continuous_const.sub (hPc.comp (continuous_id.div_const 2))
  have hgp : Function.Periodic g h := by
    intro w
    dsimp [g]
    rw [add_div, hPp]
  have hGlim : Tendsto (fun w ↦ G s μ w - g w) atTop (𝓝 0) := by
    have ht : Tendsto (fun w : ℝ ↦ w / 2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    convert (hlim.comp ht).neg using 1
    · funext w
      dsimp [m, g, Function.comp_def]
      ring_nf
    · simp
  refine ⟨g, hg, hgp, ?_, hGlim⟩
  intro w
  have ht : Tendsto (fun n : ℕ ↦ w + (n : ℝ) * h) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
  have hseq : Tendsto (fun n : ℕ ↦ G s μ (w + (n : ℝ) * h)) atTop (𝓝 (g w)) := by
    convert (hGlim.comp ht).add_const (g w) using 1
    · funext n
      rw [Function.comp_apply, hgp.nat_mul n w]
      ring
    · simp
  have hlow : (S.minRatio / 2) ^ s ≤ g w := by
    apply ge_of_tendsto hseq
    filter_upwards [ht.eventually_ge_atTop 0] with n hn
    exact hμ.lower_bound_G S hs0.le hn
  exact (Real.rpow_pos_of_pos (by positivity) s).trans_le hlow

end System

/-- Gaussian smoothing preserves a bounded error tending to zero.  This is the
last step of the lattice branch of `thm:profile-asymptotics`. -/
theorem smooth_profile_error_tendsto {s A p : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    {g : ℝ → ℝ} (hg : Continuous g) (hp : 0 < p) (hper : Function.Periodic g p)
    (hlim : Tendsto (fun w ↦ G s μ w - g w) atTop (𝓝 0)) :
    Tendsto (fun t ↦ H s μ t - smoothOp s g t) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_nonneg_bound_of_periodic hp.ne' hg hper
  have hGc := continuous_G hs0 hμ
  have hGbound : ∀ w, |G s μ w| ≤ A := abs_G_le hs0 hμ
  have hkey : Tendsto (fun t : ℝ ↦ ∫ η in Set.Ioi (0 : ℝ),
      kern s η * (G s μ (2 * t - Real.log η) - g (2 * t - Real.log η)))
      atTop (𝓝 (∫ _η in Set.Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun η ↦ (A + B) * kern s η)
      (Eventually.of_forall fun t ↦ ?_) (Eventually.of_forall fun t ↦ ?_)
      ((kern_integrableOn hs0 hs1).const_mul (A + B)) ?_
    · exact ((continuousOn_kern s).aestronglyMeasurable measurableSet_Ioi).mul
        (((hGc.sub hg).measurable.comp
          (measurable_const.sub Real.measurable_log)).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (kern_pos hη)]
      have hb : |G s μ (2 * t - Real.log η) - g (2 * t - Real.log η)| ≤ A + B :=
        (abs_sub _ _).trans (add_le_add (hGbound _) (hbound _))
      nlinarith [kern_pos (s := s) hη]
    · exact Eventually.of_forall fun η ↦ by
        have ht : Tendsto (fun t : ℝ ↦ 2 * t - Real.log η) atTop atTop := by
          simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-Real.log η)
            (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
        simpa using (hlim.comp ht).const_mul (kern s η)
  simp only [integral_zero] at hkey
  convert hkey using 1
  funext t
  rw [show H s μ t = smoothOp s (G s μ) t from rfl,
    ← smoothOp_sub hs0 hs1 hGc hg hGbound hbound]
  rfl

/-- `thm:profile-asymptotics`, the general lattice branch at its critical
dimension, with period half the span of the logarithmic contraction ratios. -/
theorem lattice_profile_asymptotics {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {s h : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s) (hh : 0 < h)
    (hlat : AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ P : ℝ → ℝ, Continuous P ∧ Function.Periodic P (h / 2) ∧
      (∀ t, 0 < P t) ∧ Tendsto (fun t ↦ H s μ t - P t) atTop (𝓝 0) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
  obtain ⟨g, hgc, hgp, hgpos, hglim⟩ := S.lattice_G_limit hs0 hs1 hosc hdim hh hlat hμ
  obtain ⟨B, _, hB⟩ := exists_nonneg_bound_of_periodic hh.ne' hgc hgp
  exact ⟨smoothOp s g, continuous_smoothOp hs0 hs1 hgc hB,
    smoothOp_periodic hgp, smoothOp_pos hs0 hs1 hgc hgpos hB,
    smooth_profile_error_tendsto hs0 hs1 hA hgc hh hgp hglim⟩

end

end BrownianImages
