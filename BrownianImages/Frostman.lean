/-
`sec:setup`: the pair-distance distribution of a Frostman measure.

The Frostman bound `eq:frostman` passes to `Φ` by Fubini, which is `eq:phi-frostman`
and the only place the Frostman constant is used before `sec:variance`.

* `phi_prod_eq`: the pair-distance mass as an integral of ball masses.
* `phi_le`: `eq:phi-frostman`, `Φ(δ) ≤ Aδ^s` for `0 < δ ≤ 1`.
* `phi_nonneg`, `phi_mono`: the elementary properties used throughout.
-/
import BrownianImages.Defs
import Mathlib.Probability.CDF

namespace BrownianImages

open MeasureTheory Filter
open scoped ENNReal Topology

variable {μ : Measure ℝ}

theorem phi_nonneg (δ : ℝ) : 0 ≤ Phi μ δ := ENNReal.toReal_nonneg

theorem phi_mono [SFinite μ] {δ δ' : ℝ} (h : δ ≤ δ') [IsFiniteMeasure μ] :
    Phi μ δ ≤ Phi μ δ' := by
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  exact fun p hp => le_trans hp h

/-- The section of the pair-distance set at `x` is the closed ball of radius `δ`. -/
theorem mk_preimage_phiSet (x δ : ℝ) :
    Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} = Metric.closedBall x δ := by
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_closedBall, Real.dist_eq,
    abs_sub_comm x y]

/-- The pair-distance mass is the average ball mass: the Fubini step of
`eq:phi-frostman`. -/
theorem phi_prod_eq [SFinite μ] (δ : ℝ) :
    (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      = ∫⁻ x, μ (Metric.closedBall x δ) ∂μ := by
  rw [Measure.prod_apply (measurableSet_phiSet δ)]
  simp only [mk_preimage_phiSet]

/-- A Frostman measure of positive exponent has no atoms.  This is what makes the
diagonal `μ × μ`-null in `thm:gaussian-reduction`: without it the identity there is
false, as `μ = δ₀` shows, since real division by zero puts the integrand at `0` on the
diagonal while the left-hand side is `1`. -/
theorem IsFrostman.measure_singleton {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ}
    (h : IsFrostman s A μ) (x : ℝ) : μ {x} = 0 := by
  have key : ∀ n : ℕ, μ {x} ≤ ENNReal.ofReal (A * (((n : ℝ) + 1) ^ s)⁻¹) := by
    intro n
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpos : (0:ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; linarith
    have hball := h.measure_closedBall_le x _ hpos hle
    rw [Real.inv_rpow (by positivity)] at hball
    exact le_trans (measure_mono
      (Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hpos.le))) hball
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ s)⁻¹) atTop (𝓝 0) :=
    h1.inv_tendsto_atTop
  have h3 : Tendsto (fun n : ℕ => A * (((n : ℝ) + 1) ^ s)⁻¹) atTop (𝓝 0) := by
    simpa using h2.const_mul A
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (A * (((n : ℝ) + 1) ^ s)⁻¹))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal h3
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall key)) (by simp)

/-- `Φ` is the distribution function of the pair-distance law: this is the
identification of `dΦ` in `eq:gaussian-reduction`. -/
theorem phi_eq_pairLaw [SFinite μ] (δ : ℝ) :
    Phi μ δ = (pairLaw μ (Set.Iic δ)).toReal := by
  rw [Phi, pairLaw, Measure.map_apply (by fun_prop) measurableSet_Iic]
  rfl

/-- `eq:phi-frostman`: the Frostman bound passes to the pair-distance distribution. -/
theorem phi_le [IsProbabilityMeasure μ] {s A : ℝ} (hμ : IsFrostman s A μ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Phi μ δ ≤ A * δ ^ s := by
  have hAδ : 0 ≤ A * δ ^ s := by
    have : (0:ℝ) < δ ^ s := Real.rpow_pos_of_pos hδ0 s
    nlinarith [hμ.one_le_const]
  refine ENNReal.toReal_le_of_le_ofReal hAδ ?_
  rw [phi_prod_eq]
  calc ∫⁻ x, μ (Metric.closedBall x δ) ∂μ
      ≤ ∫⁻ _, ENNReal.ofReal (A * δ ^ s) ∂μ :=
        lintegral_mono fun x => hμ.measure_closedBall_le x δ hδ0 hδ1
    _ = ENNReal.ofReal (A * δ ^ s) := by simp


/-! ### The two ball conventions -/

/-- `IsFrostman` gives the shape `eq:frostman` is written in: open balls sit inside
closed balls, and the centres are restricted. -/
theorem IsFrostman.isFrostmanOpen {s A : ℝ} (h : IsFrostman s A μ) :
    IsFrostmanOpen s A μ where
  one_le_const := h.one_le_const
  support := h.support
  measure_ball_le x _ ρ hρ0 hρ1 :=
    le_trans (measure_mono Metric.ball_subset_closedBall) (h.measure_closedBall_le x ρ hρ0 hρ1)

/-- The shape `eq:frostman` is written in gives `IsFrostman`, at the cost of the
constant `3^s A`, which is the change of constant the paper allows itself.  A closed
ball of radius `ρ ≤ 1/3` meeting `[0,1]` sits inside an open ball of radius `3ρ` centred
in `[0,1]`; larger radii are covered by the total mass. -/
theorem IsFrostmanOpen.isFrostman {s A : ℝ} (hs : 0 ≤ s) [IsProbabilityMeasure μ]
    (h : IsFrostmanOpen s A μ) : IsFrostman s (3 ^ s * A) μ where
  one_le_const := by
    have h3s : (1:ℝ) ≤ (3:ℝ) ^ s := by
      simpa using Real.rpow_le_rpow (by norm_num) (by norm_num : (1:ℝ) ≤ 3) hs
    nlinarith [h.one_le_const]
  support := h.support
  measure_closedBall_le := by
    intro x ρ hρ0 hρ1
    have hA := h.one_le_const
    have h3pos : (0:ℝ) < (3:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    by_cases hsmall : ρ ≤ 1/3
    · by_cases hmeet : (Metric.closedBall x ρ ∩ Set.Icc (0:ℝ) 1).Nonempty
      · obtain ⟨y, hy1, hy2⟩ := hmeet
        have hxy : dist x y ≤ ρ := by rw [dist_comm]; exact hy1
        have hsub : Metric.closedBall x ρ ⊆ Metric.ball y (3 * ρ) := by
          intro z hz
          have htri := dist_triangle z x y
          have hzx : dist z x ≤ ρ := hz
          simp only [Metric.mem_ball]
          linarith
        calc μ (Metric.closedBall x ρ) ≤ μ (Metric.ball y (3 * ρ)) := measure_mono hsub
          _ ≤ ENNReal.ofReal (A * (3 * ρ) ^ s) :=
              h.measure_ball_le y hy2 (3 * ρ) (by linarith) (by linarith)
          _ = ENNReal.ofReal (3 ^ s * A * ρ ^ s) := by
              rw [Real.mul_rpow (by norm_num) hρ0.le]; ring_nf
      · have hnull : Metric.closedBall x ρ ⊆ (Set.Icc (0:ℝ) 1)ᶜ := fun z hz hc =>
          hmeet ⟨z, hz, hc⟩
        rw [measure_mono_null hnull h.support]
        simp
    · rw [not_le] at hsmall
      refine le_trans prob_le_one ?_
      refine ENNReal.one_le_ofReal.mpr ?_
      have hmono : ((1:ℝ)/3) ^ s ≤ ρ ^ s := Real.rpow_le_rpow (by norm_num) hsmall.le hs
      have h13 : ((1:ℝ)/3) ^ s = ((3:ℝ) ^ s)⁻¹ := by
        rw [one_div, Real.inv_rpow (by norm_num)]
      rw [h13] at hmono
      have hcancel : (3:ℝ) ^ s * A * ((3:ℝ) ^ s)⁻¹ = A := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hmono
        (by positivity : (0:ℝ) ≤ (3:ℝ) ^ s * A)]


/-! ### The two ball conventions for `eq:ahlfors` -/

/-- The closed-ball form of `eq:ahlfors` gives the open-ball form the paper writes, at
the constant `2^s A`: an open ball contains the closed ball of half the radius. -/
theorem IsAhlforsClosed.isAhlfors {s A : ℝ} (hs : 0 ≤ s) (h : IsAhlforsClosed s A μ) :
    IsAhlfors s (2 ^ s * A) μ := by
  obtain ⟨hA, hball⟩ := h
  have h2s : (1:ℝ) ≤ (2:ℝ) ^ s := by
    simpa using Real.rpow_le_rpow (by norm_num) (by norm_num : (1:ℝ) ≤ 2) hs
  refine ⟨by nlinarith, ?_⟩
  intro x hx r hr0 hr1
  refine ⟨?_, ?_⟩
  · have hsub : Metric.closedBall x (r/2) ⊆ Metric.ball x r := fun z hz =>
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    have hhalf := (hball x hx (r/2) (by linarith) (by linarith)).1
    have heq : ((2:ℝ) ^ s * A)⁻¹ * r ^ s = A⁻¹ * (r/2) ^ s := by
      rw [Real.div_rpow hr0.le (by norm_num), mul_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact le_trans hhalf (measure_mono hsub)
  · refine le_trans (measure_mono Metric.ball_subset_closedBall)
      (le_trans (hball x hx r hr0 hr1).2 (ENNReal.ofReal_le_ofReal ?_))
    have hrs : (0:ℝ) ≤ r ^ s := (Real.rpow_pos_of_pos hr0 s).le
    have hApos : (0:ℝ) < A := by linarith
    calc A * r ^ s = 1 * (A * r ^ s) := by ring
      _ ≤ (2:ℝ) ^ s * (A * r ^ s) := by
          exact mul_le_mul_of_nonneg_right h2s (by positivity)
      _ = 2 ^ s * A * r ^ s := by ring


/-! ### The pair-distance law has no atoms -/

/-- The section of `{|x - y| = δ}` at `x` is contained in the pair `{x - δ, x + δ}`. -/
theorem mk_preimage_diffSet (x δ : ℝ) :
    Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => |p.1 - p.2|) ⁻¹' {δ}) ⊆ {x - δ, x + δ} := by
  intro y hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
  have hδ : 0 ≤ δ := hy ▸ abs_nonneg _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (abs_eq hδ).mp hy with h | h
  · left; linarith
  · right; linarith

/-- `sec:setup`: the pair-distance law has no atoms.  This is Fubini's theorem applied
to the section above, together with the atomlessness of `μ`; it is what makes `Φ`
continuous. -/
theorem pairLaw_measure_singleton [IsProbabilityMeasure μ] {s A : ℝ} (hs : 0 < s)
    (h : IsFrostman s A μ) (δ : ℝ) : pairLaw μ {δ} = 0 := by
  have hmeas : Measurable fun p : ℝ × ℝ => |p.1 - p.2| := by fun_prop
  have hpair : ∀ x : ℝ, μ ({x - δ, x + δ} : Set ℝ) = 0 := by
    intro x
    rw [Set.insert_eq]
    exact measure_union_null (h.measure_singleton hs _) (h.measure_singleton hs _)
  rw [pairLaw, Measure.map_apply hmeas (measurableSet_singleton δ),
    Measure.prod_apply (hmeas (measurableSet_singleton δ))]
  refine le_antisymm (le_of_le_of_eq (lintegral_mono fun x =>
    (measure_mono (mk_preimage_diffSet x δ)).trans_eq (hpair x)) ?_) (by simp)
  simp


/-! ### Continuity of `Φ` -/

/-- The distribution function of an atomless probability measure on `ℝ` is continuous.
Right continuity is built into the Stieltjes function; left continuity is exactly the
vanishing of the atom, through `StieltjesFunction.measure_singleton`. -/
theorem continuous_cdf_toReal {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hatom : ∀ x, ν {x} = 0) : Continuous fun x : ℝ => (ν (Set.Iic x)).toReal := by
  have hcdf : ∀ x : ℝ, (ν (Set.Iic x)).toReal = ProbabilityTheory.cdf ν x := fun x => by
    rw [ProbabilityTheory.cdf_eq_real]
    rfl
  simp_rw [hcdf]
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmono : Monotone (ProbabilityTheory.cdf ν) := ProbabilityTheory.monotone_cdf ν
  have hleft : Function.leftLim (ProbabilityTheory.cdf ν) x = ProbabilityTheory.cdf ν x := by
    have hs := (ProbabilityTheory.cdf ν).measure_singleton x
    rw [ProbabilityTheory.measure_cdf, hatom x] at hs
    have hle : Function.leftLim (ProbabilityTheory.cdf ν) x ≤ ProbabilityTheory.cdf ν x :=
      hmono.leftLim_le le_rfl
    have hzero := (ENNReal.ofReal_eq_zero).mp hs.symm
    linarith
  have hright : Function.rightLim (ProbabilityTheory.cdf ν) x = ProbabilityTheory.cdf ν x :=
    hmono.continuousWithinAt_Ioi_iff_rightLim_eq.mp
      (continuousWithinAt_Ioi_iff_Ici.mpr ((ProbabilityTheory.cdf ν).right_continuous x))
  exact hmono.continuousAt_iff_leftLim_eq_rightLim.mpr (hleft.trans hright.symm)

/-- `sec:setup`: `Φ` is continuous, since the pair-distance law has no atoms. -/
theorem continuous_phi [IsProbabilityMeasure μ] {s A : ℝ} (hs : 0 < s)
    (h : IsFrostman s A μ) : Continuous (Phi μ) := by
  haveI hprob : IsProbabilityMeasure (pairLaw μ) := by
    rw [pairLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hcont := continuous_cdf_toReal (ν := pairLaw μ) (pairLaw_measure_singleton hs h)
  have : Phi μ = fun δ : ℝ => (pairLaw μ (Set.Iic δ)).toReal := funext (phi_eq_pairLaw)
  rw [this]
  exact hcont

/-- `eq:g-definition`: the normalised profile is continuous.  This is what the key
renewal theorem asks of the kernel `z = G - F*G`. -/
theorem continuous_G [IsProbabilityMeasure μ] {s A : ℝ} (hs : 0 < s)
    (h : IsFrostman s A μ) : Continuous (G s μ) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((continuous_phi hs h).comp (Real.continuous_exp.comp continuous_neg))

end BrownianImages
