/-
`thm:non-lattice-limit` of `sec:renewal`: the renewal defect `z = G - F*G` of
`eq:g-non-lattice-limit`, the limit constant it computes, and the Choquet-Deny theorem
for the walk the recursion `eq:g-recursion` drives.

The vendored key renewal theorem does not apply to `F` (`not_nonlattice_renewalLaw`), so
what is proved here is everything on either side of the missing theorem.  Before it:
the paper's analysis of `z`, that it vanishes above `log ρ⁻¹`, that it is non-negative
because the off-diagonal blocks of the self-similar decomposition of `Φ` are, that it is
integrable, and that `∫ z > 0`.  After it: cutting the renewal equation at a threshold
above `log ρ⁻¹` gives `∫ z = ∑ p_i ∫_{T-a_i}^T G` exactly, so the limit of `G`, if it
exists, is forced to be `m⁻¹ ∫ z`.  `nonLatticeLimit_of_tendsto` is the endpoint's
conclusion, with the bare convergence of `G` as its one added hypothesis.

Beside that, and independent of the profile: the Choquet-Deny theorem for a finitely
supported step law with positive steps generating a dense group, in the shape a renewal
argument consumes it.  A bounded uniformly continuous harmonic function converges at
`+∞` to its supremum, hence is constant.  It does not close the endpoint on its own: the
recursion `eq:g-recursion` holds only on the tail `w > log ρ⁻¹`, so `G` is not harmonic
on the line, and passing to a harmonic limit of translates needs an equicontinuity for
`G` that is not available here.

* `sum_phi_le`, `renewalDefect_eq`, `renewalDefect_nonneg`, `renewalDefect_eq_zero`:
  the defect and its sign.
* `integrable_renewalDefect`, `integral_renewalDefect_pos`, `renewalConstant_pos`:
  `z ∈ L¹` and `m⁻¹ ∫ z ∈ (0, ∞)`.
* `integral_renewalDefect_eq`, `nonLatticeLimit_of_tendsto`: the identification of the
  constant, and the endpoint reduced to the convergence of `G`.
* `exists_net`, `iterate_le`, `propagate_le`, `tendsto_atTop_sSup`, `const_of_harmonic`,
  `const_of_g_recursion`: Choquet-Deny, and its reading for a system.
-/
import BrownianImages.Recursion
import BrownianImages.Profile
import BrownianImages.AhlforsRegular
import BrownianImages.Kernel

namespace BrownianImages

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace KeyRenewal

variable {ι : Type*} [Fintype ι]

/-- `Φ(δ) = 1` at every scale `δ ≥ 1`: a measure on `[0,1]` has all its pair distances
at most `1`. -/
theorem phi_eq_one_of_one_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Set.Icc (0:ℝ) 1)ᶜ = 0) {δ : ℝ} (hδ : 1 ≤ δ) : Phi μ δ = 1 := by
  have hIcc : μ (Set.Icc (0:ℝ) 1) = 1 := by
    have := measure_add_measure_compl (μ := μ) (s := Set.Icc (0:ℝ) 1) measurableSet_Icc
    rw [hsupp, add_zero, measure_univ] at this
    exact this
  have hsub : (Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1) ⊆ {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    simp only [Set.mem_setOf_eq, abs_le]
    constructor <;> linarith
  have hone : (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} = 1 := by
    refine le_antisymm (by simpa using prob_le_one) ?_
    calc (1 : ℝ≥0∞) = (μ.prod μ) ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) := by
          rw [Measure.prod_prod, hIcc, one_mul]
      _ ≤ _ := measure_mono hsub
  rw [Phi, hone, ENNReal.toReal_one]

/-- The full self-similar decomposition of `Φ` keeps the non-negative off-diagonal
blocks, so the diagonal sum of `eq:phi-recursion` is a lower bound at *every* scale, not
only below the separation gap.  This is the inequality the paper reads as `z ≥ 0`. -/
theorem sum_phi_le (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (δ : ℝ) :
    ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) ≤ Phi μ δ := by
  haveI := hμ.isProbabilityMeasure
  have hpre : ∀ (i : ι) (x : ℝ),
      S.map i ⁻¹' Metric.closedBall (S.map i x) δ = Metric.closedBall x (δ / S.ratio i) := by
    intro i x
    ext y
    simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, System.map]
    rw [show S.ratio i * y + S.shift i - (S.ratio i * x + S.shift i) = (y - x) * S.ratio i from
        by ring, abs_mul, abs_of_pos (S.ratio_pos i), le_div_iff₀ (S.ratio_pos i)]
  have hle : ∀ (i : ι) (x : ℝ),
      ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i))
        ≤ μ (Metric.closedBall (S.map i x) δ) := by
    intro i x
    calc ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i))
        = ENNReal.ofReal (S.ratio i ^ s) *
            μ (S.map i ⁻¹' Metric.closedBall (S.map i x) δ) := by rw [hpre]
      _ ≤ ∑ j, ENNReal.ofReal (S.ratio j ^ s) *
            μ (S.map j ⁻¹' Metric.closedBall (S.map i x) δ) :=
          Finset.single_le_sum
            (f := fun j => ENNReal.ofReal (S.ratio j ^ s) *
              μ (S.map j ⁻¹' Metric.closedBall (S.map i x) δ))
            (fun j _ => zero_le) (Finset.mem_univ i)
      _ = μ (Metric.closedBall (S.map i x) δ) :=
          (hμ.measure_eq_sum S measurableSet_closedBall).symm
  have hint : ∑ i, ENNReal.ofReal (S.ratio i ^ s) * (ENNReal.ofReal (S.ratio i ^ s) *
        ∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ)
      ≤ ∫⁻ x, μ (Metric.closedBall x δ) ∂μ := by
    rw [hμ.lintegral_eq_sum S (measurable_measure_closedBall μ δ)]
    refine Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl ?_
    rw [← lintegral_const_mul _ (measurable_measure_closedBall μ (δ / S.ratio i))]
    exact lintegral_mono fun x => hle i x
  have hfin : ∀ δ' : ℝ, (∫⁻ x, μ (Metric.closedBall x δ') ∂μ) ≠ ⊤ := by
    intro δ'
    rw [← phi_prod_eq]
    exact measure_ne_top _ _
  have hne : ∀ i : ι, ENNReal.ofReal (S.ratio i ^ s) * (ENNReal.ofReal (S.ratio i ^ s) *
      ∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ) ≠ ⊤ :=
    fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _))
  have hreal := ENNReal.toReal_mono (hfin δ) hint
  rw [ENNReal.toReal_sum (fun i _ => hne i)] at hreal
  have hphi : ∀ δ' : ℝ, Phi μ δ' = (∫⁻ x, μ (Metric.closedBall x δ') ∂μ).toReal := by
    intro δ'
    rw [Phi, phi_prod_eq]
  rw [← hphi δ] at hreal
  refine le_trans (le_of_eq ?_) hreal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le, ← hphi]
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_add (S.ratio_pos i), two_mul]

/-- The renewal defect `z = G - F*G` in terms of `Φ`: the bracket is exactly the
difference between `Φ` and the diagonal sum of `eq:phi-recursion`. -/
theorem renewalDefect_eq (S : System ι) {s : ℝ} {μ : Measure ℝ} (w : ℝ) :
    S.renewalDefect s μ w
      = Real.exp (s * w) * (Phi μ (Real.exp (-w))
          - ∑ i, S.ratio i ^ (2 * s) * Phi μ (Real.exp (-w) / S.ratio i)) := by
  rw [System.renewalDefect, System.renewalConv, G, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr := S.ratio_pos i
  have h1 : Real.exp (-(w - S.logRatio i)) = Real.exp (-w) / S.ratio i := by
    rw [show -(w - S.logRatio i) = -w + S.logRatio i from by ring, Real.exp_add,
      System.logRatio, Real.exp_log (inv_pos.mpr hr), div_eq_mul_inv]
  have h2 : Real.exp (s * (w - S.logRatio i)) = Real.exp (s * w) * S.ratio i ^ s := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_add, System.logRatio, Real.log_inv]
    congr 1
    ring
  have h3 : S.ratio i ^ (2 * s) = S.ratio i ^ s * S.ratio i ^ s := by
    rw [two_mul, Real.rpow_add hr]
  rw [G, h1, h2, h3]
  ring

/-- `z ≥ 0`: the off-diagonal blocks of the self-similar decomposition are
non-negative. -/
theorem renewalDefect_nonneg (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (w : ℝ) : 0 ≤ S.renewalDefect s μ w := by
  rw [renewalDefect_eq]
  exact mul_nonneg (Real.exp_pos _).le (by linarith [sum_phi_le S hμ (Real.exp (-w))])

/-- `z` vanishes above `log ρ⁻¹`: that is `eq:g-recursion`. -/
theorem renewalDefect_eq_zero (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {w : ℝ} (hw : Real.log ρ⁻¹ < w) : S.renewalDefect s μ w = 0 := by
  rw [System.renewalDefect, System.renewalConv, ← g_recursion S hsep hμ hw, sub_self]

/-- `z ≤ G`, since `F*G ≥ 0`. -/
theorem renewalDefect_le_G (S : System ι) {s : ℝ} {μ : Measure ℝ} (w : ℝ) :
    S.renewalDefect s μ w ≤ G s μ w := by
  rw [System.renewalDefect, sub_le_self_iff, System.renewalConv]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Real.rpow_pos_of_pos (S.ratio_pos i) s).le (G_nonneg _)

/-- `z(w) ≤ e^{sw}`, the trivial bound `Φ ≤ 1`. -/
theorem renewalDefect_le_exp (S : System ι) {s : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (w : ℝ) : S.renewalDefect s μ w ≤ Real.exp (s * w) :=
  (renewalDefect_le_G S w).trans (G_le_exp hs le_rfl)

/-- `z` is measurable: `G` is, and `F*G` is a finite sum of translates of `G`. -/
theorem measurable_renewalDefect (S : System ι) {s : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] : Measurable (S.renewalDefect s μ) := by
  refine measurable_G.sub (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul (measurable_G.comp (measurable_id.sub_const _))

/-- `z ∈ L¹(ℝ)`: it vanishes above `log ρ⁻¹` and is dominated by `e^{sw}` below it, so
the two-sided bound `e^{sL} e^{-s|w - L|}` covers the line. -/
theorem integrable_renewalDefect (S : System ι) {K : Set ℝ} {ρ s : ℝ} (hs : 0 < s)
    (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    Integrable (S.renewalDefect s μ) := by
  haveI := hμ.isProbabilityMeasure
  set L : ℝ := Real.log ρ⁻¹ with hL
  refine Integrable.mono'
    (g := fun w : ℝ => Real.exp (s * L) * Real.exp (-s * |w - L|))
    (((integrable_exp_neg_mul_abs hs).comp_sub_right L).const_mul _)
    (measurable_renewalDefect S).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (renewalDefect_nonneg S hμ w)]
  rcases le_or_gt w L with hw | hw
  · have habs : |w - L| = L - w := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs, ← Real.exp_add]
    refine (renewalDefect_le_exp S hs.le w).trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  · rw [renewalDefect_eq_zero S hsep hμ hw]
    positivity

/-- `z(w) = e^{sw}(1 - ∑ r_i^{2s}) > 0` for `w ≤ 0`: at those scales every `Φ` in the
defect is `1`, and `∑ r_i^{2s} < ∑ r_i^s = 1`. -/
theorem renewalDefect_pos_of_nonpos (S : System ι) [Nonempty ι] {K : Set ℝ} {s : ℝ}
    (hs : 0 < s) (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {w : ℝ} (hw : w ≤ 0) : 0 < S.renewalDefect s μ w := by
  haveI := hμ.isProbabilityMeasure
  have hsupp := hμ.support_Icc
  have hexp : (1:ℝ) ≤ Real.exp (-w) := Real.one_le_exp (by linarith)
  have hsum : ∑ i, S.ratio i ^ (2 * s) < 1 := by
    have hlt : ∀ i ∈ (Finset.univ : Finset ι),
        S.ratio i ^ (2 * s) < S.ratio i ^ s := by
      intro i _
      have h1 : S.ratio i ^ (2 * s) = S.ratio i ^ s * S.ratio i ^ s := by
        rw [two_mul, Real.rpow_add (S.ratio_pos i)]
      have h2 : S.ratio i ^ s < 1 :=
        Real.rpow_lt_one (S.ratio_pos i).le (S.ratio_lt_one i) hs
      have h3 : (0:ℝ) < S.ratio i ^ s := Real.rpow_pos_of_pos (S.ratio_pos i) s
      rw [h1]
      nlinarith
    calc ∑ i, S.ratio i ^ (2 * s) < ∑ i, S.ratio i ^ s :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hlt
      _ = 1 := hdim
  rw [renewalDefect_eq, phi_eq_one_of_one_le hsupp hexp]
  have hone : ∀ i : ι, Phi μ (Real.exp (-w) / S.ratio i) = 1 := by
    intro i
    refine phi_eq_one_of_one_le hsupp ?_
    rw [le_div_iff₀ (S.ratio_pos i)]
    nlinarith [S.ratio_lt_one i, S.ratio_pos i]
  simp only [hone, mul_one]
  have : (0:ℝ) < 1 - ∑ i, S.ratio i ^ (2 * s) := by linarith
  positivity

/-- `∫ z > 0`: the defect is non-negative, and strictly positive on the whole half line
`w ≤ 0`, which has infinite Lebesgue measure. -/
theorem integral_renewalDefect_pos (S : System ι) [Nonempty ι] {K : Set ℝ} {ρ s : ℝ}
    (hs : 0 < s) (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    0 < ∫ x : ℝ, S.renewalDefect s μ x := by
  refine (integral_pos_iff_support_of_nonneg (renewalDefect_nonneg S hμ)
    (integrable_renewalDefect S hs hsep hμ)).mpr ?_
  have hsub : Set.Iic (0:ℝ) ⊆ Function.support (S.renewalDefect s μ) := by
    intro w hw
    exact (renewalDefect_pos_of_nonpos S hs hdim hμ hw).ne'
  calc (0:ℝ≥0∞) < volume (Set.Iic (0:ℝ)) := by rw [Real.volume_Iic]; simp
    _ ≤ _ := measure_mono hsub

/-! ### The limit constant -/

/-- `G` is integrable below every threshold: `0 ≤ G ≤ e^{sw}`, and `e^{sw}` decays at
`-∞`. -/
theorem integrableOn_G_Iic {s : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (T : ℝ) : IntegrableOn (G s μ) (Set.Iic T) := by
  refine Integrable.mono'
    (g := fun w : ℝ => Real.exp (s * T) * Real.exp (-s * |w - T|))
    (((integrable_exp_neg_mul_abs hs).comp_sub_right T).const_mul _).integrableOn
    measurable_G.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun w hw => ?_)
  have hwT : w ≤ T := hw
  rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg w)]
  have habs : |w - T| = T - w := by rw [abs_of_nonpos (by linarith)]; ring
  rw [habs, ← Real.exp_add]
  refine (G_le_exp hs.le le_rfl).trans (Real.exp_le_exp.mpr ?_)
  nlinarith

/-- The mass `G` puts on a window of fixed length `b` at the top of the line tends to
`bC` when `G` converges to `C`.  This is the step that turns the exact identity
`∫ z = ∑ p_i ∫_{T - a_i}^T G` into `∫ z = mC`. -/
theorem tendsto_window_integral {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμF : IsFrostman s A μ) {C : ℝ}
    (hconv : Tendsto (G s μ) atTop (𝓝 C)) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ => ∫ w in Set.Ioc (T - b) T, G s μ w) atTop (𝓝 (b * C)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) b)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hchange : ∀ T : ℝ, ∫ w in Set.Ioc (T - b) T, G s μ w
      = ∫ v in Set.Ioc (0:ℝ) b, G s μ (v + (T - b)) := by
    intro T
    have hpre : (fun x : ℝ => x + (T - b)) ⁻¹' Set.Ioc (T - b) T = Set.Ioc (0:ℝ) b := by
      ext v
      simp only [Set.mem_preimage, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    have h := (measurePreserving_add_right (volume : Measure ℝ) (T - b)).setIntegral_preimage_emb
      (measurableEmbedding_addRight (T - b)) (G s μ) (Set.Ioc (T - b) T)
    rw [hpre] at h
    exact h.symm
  have hconst : b * C = ∫ _v in Set.Ioc (0:ℝ) b, C := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hb.le, smul_eq_mul]
    ring
  simp only [hchange]
  rw [hconst]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => A) ?_ ?_
    (integrable_const A) ?_
  · exact Eventually.of_forall fun T =>
      (measurable_G.comp (measurable_id.add_const _)).aestronglyMeasurable
  · refine Eventually.of_forall fun T => Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs]
    exact abs_G_le hs hμF _
  · refine Eventually.of_forall fun v => ?_
    have h1 : Tendsto (fun T : ℝ => T + (v - b)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    exact hconv.comp (h1.congr fun T => by ring)

/-- `∫ z = mC` whenever `G` converges to `C`: cutting the renewal equation at a
threshold `T` above `log ρ⁻¹`, where `z` already vanishes, leaves
`∫ z = ∑ p_i ∫_{T - a_i}^T G`, and each window contributes `a_i C` in the limit. -/
theorem integral_renewalDefect_eq (S : System ι) {K : Set ℝ} {ρ s : ℝ} (hs : 0 < s)
    (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {C : ℝ} (hconv : Tendsto (G s μ) atTop (𝓝 C)) :
    ∫ x : ℝ, S.renewalDefect s μ x = S.renewalMean s * C := by
  haveI := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs hsep hμ
  have hpre : ∀ (i : ι) (T : ℝ),
      (fun x : ℝ => x - S.logRatio i) ⁻¹' Set.Iic (T - S.logRatio i) = Set.Iic T := by
    intro i T
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  have hint2 : ∀ (i : ι) (T : ℝ),
      IntegrableOn (fun x => G s μ (x - S.logRatio i)) (Set.Iic T) := by
    intro i T
    have h := ((measurePreserving_sub_right (volume : Measure ℝ)
      (S.logRatio i)).integrableOn_comp_preimage
      (measurableEmbedding_subRight (S.logRatio i)) (f := G s μ)
      (s := Set.Iic (T - S.logRatio i))).mpr (integrableOn_G_Iic hs _)
    rw [hpre i T] at h
    exact h
  have htrans : ∀ (i : ι) (T : ℝ), (∫ x in Set.Iic T, G s μ (x - S.logRatio i))
      = ∫ y in Set.Iic (T - S.logRatio i), G s μ y := by
    intro i T
    have h := (measurePreserving_sub_right (volume : Measure ℝ)
      (S.logRatio i)).setIntegral_preimage_emb
      (measurableEmbedding_subRight (S.logRatio i)) (G s μ) (Set.Iic (T - S.logRatio i))
    rw [hpre i T] at h
    exact h
  have hkey : ∀ T : ℝ, Real.log ρ⁻¹ ≤ T → ∫ x : ℝ, S.renewalDefect s μ x
      = ∑ i, S.ratio i ^ s * ∫ w in Set.Ioc (T - S.logRatio i) T, G s μ w := by
    intro T hT
    have hz0 : ∀ x : ℝ, x ∉ Set.Iic T → S.renewalDefect s μ x = 0 := by
      intro x hx
      exact renewalDefect_eq_zero S hsep hμ (lt_of_le_of_lt hT (not_le.mp hx))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz0]
    have hsum : IntegrableOn
        (fun x => ∑ i, S.ratio i ^ s * G s μ (x - S.logRatio i)) (Set.Iic T) :=
      integrable_finsetSum _ fun i _ => (hint2 i T).const_mul _
    have hsplit : ∫ x in Set.Iic T, S.renewalDefect s μ x
        = (∫ x in Set.Iic T, G s μ x)
          - ∑ i, S.ratio i ^ s * ∫ x in Set.Iic T, G s μ (x - S.logRatio i) := by
      simp only [System.renewalDefect, System.renewalConv]
      rw [integral_sub (integrableOn_G_Iic (μ := μ) hs T) hsum,
        integral_finsetSum _ (fun i _ => (hint2 i T).const_mul _)]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => integral_const_mul _ _)
    have hwin : ∀ i : ι, (∫ x in Set.Iic T, G s μ x)
        - (∫ y in Set.Iic (T - S.logRatio i), G s μ y)
        = ∫ w in Set.Ioc (T - S.logRatio i) T, G s μ w := by
      intro i
      have hle : T - S.logRatio i ≤ T := by linarith [S.logRatio_pos i]
      have hdisj : Disjoint (Set.Iic (T - S.logRatio i)) (Set.Ioc (T - S.logRatio i) T) := by
        rw [Set.disjoint_left]
        rintro x hx ⟨hx1, -⟩
        exact absurd hx1 (not_lt.mpr hx)
      have hun := setIntegral_union hdisj measurableSet_Ioc
        (integrableOn_G_Iic (μ := μ) hs (T - S.logRatio i))
        ((integrableOn_G_Iic (μ := μ) hs T).mono_set Set.Ioc_subset_Iic_self)
      rw [Set.Iic_union_Ioc_eq_Iic hle] at hun
      rw [hun]
      ring
    have hG : (∫ x in Set.Iic T, G s μ x)
        = ∑ i, S.ratio i ^ s * ∫ x in Set.Iic T, G s μ x := by
      rw [← Finset.sum_mul, hdim, one_mul]
    rw [hsplit]
    simp only [htrans]
    rw [hG, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_sub, hwin i]
  have hlim : Tendsto (fun T : ℝ =>
      ∑ i, S.ratio i ^ s * ∫ w in Set.Ioc (T - S.logRatio i) T, G s μ w) atTop
      (𝓝 (∑ i, S.ratio i ^ s * (S.logRatio i * C))) :=
    tendsto_finsetSum _ fun i _ =>
      (tendsto_window_integral hs hA hconv (S.logRatio_pos i)).const_mul _
  have heq : Tendsto (fun _ : ℝ => ∫ x : ℝ, S.renewalDefect s μ x) atTop
      (𝓝 (∑ i, S.ratio i ^ s * (S.logRatio i * C))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (Real.log ρ⁻¹)] with T hT
    exact (hkey T hT).symm
  rw [tendsto_nhds_unique tendsto_const_nhds heq, System.renewalMean, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Choquet-Deny for a finitely supported step law -/

/-- The point `∑ k_i a_i` of the additive semigroup generated by the steps `a`, reached
in `∑ k_i` steps. -/
noncomputable def stepVal (a : ι → ℝ) (k : ι → ℕ) : ℝ := ∑ i, (k i : ℝ) * a i

variable {p a : ι → ℝ} {d : ℝ → ℝ}

/-- One step of the maximum principle: a non-negative function harmonic for the step law
`∑ p_i δ_{a_i}` loses at most a factor `q ≤ min_i p_i` along one step of the walk. -/
theorem step_le {q : ℝ} (hp : ∀ i, 0 ≤ p i) (hqle : ∀ i, q ≤ p i) (hd0 : ∀ x, 0 ≤ d x)
    (hharm : ∀ x, d x = ∑ i, p i * d (x - a i)) (x : ℝ) (i : ι) :
    q * d (x - a i) ≤ d x := by
  refine le_trans (mul_le_mul_of_nonneg_right (hqle i) (hd0 _)) ?_
  rw [hharm x]
  exact Finset.single_le_sum (f := fun j => p j * d (x - a j))
    (fun j _ => mul_nonneg (hp j) (hd0 _)) (Finset.mem_univ i)

/-- The maximum principle along a whole word: `n` steps of the walk cost at most a
factor `q^n`. -/
theorem iterate_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hp : ∀ i, 0 ≤ p i)
    (hqle : ∀ i, q ≤ p i) (hd0 : ∀ x, 0 ≤ d x)
    (hharm : ∀ x, d x = ∑ i, p i * d (x - a i)) :
    ∀ (n : ℕ) (k : ι → ℕ), (∑ i, k i) ≤ n → ∀ x : ℝ,
      q ^ n * d (x - stepVal a k) ≤ d x := by
  classical
  intro n
  induction n with
  | zero =>
      intro k hk x
      have hk0 : ∀ i, k i = 0 := fun i =>
        (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hk)) i (Finset.mem_univ i)
      have hv : stepVal a k = 0 := by simp [stepVal, hk0]
      rw [hv, pow_zero, one_mul, sub_zero]
  | succ n ih =>
      intro k hk x
      by_cases h0 : ∑ i, k i = 0
      · have hk0 : ∀ i, k i = 0 := fun i =>
          (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
        have hv : stepVal a k = 0 := by simp [stepVal, hk0]
        rw [hv, sub_zero]
        exact mul_le_of_le_one_left (hd0 x) (pow_le_one₀ hq0.le hq1)
      · obtain ⟨i₀, hi₀⟩ : ∃ i, k i ≠ 0 := by
          by_contra hc
          exact h0 (Finset.sum_eq_zero fun i _ => not_not.mp fun hne => hc ⟨i, hne⟩)
        set k' : ι → ℕ := Function.update k i₀ (k i₀ - 1) with hk'
        have hupd : ∀ i, i ≠ i₀ → k' i = k i := fun i hi => by
          simp [hk', Function.update_of_ne hi]
        have hupd₀ : k' i₀ = k i₀ - 1 := by simp [hk']
        have hsum' : ∑ i, k' i ≤ n := by
          have e1 : ∑ i, k i = k i₀ + ∑ i ∈ Finset.univ.erase i₀, k i :=
            (Finset.add_sum_erase _ k (Finset.mem_univ i₀)).symm
          have e2 : ∑ i, k' i = k' i₀ + ∑ i ∈ Finset.univ.erase i₀, k' i :=
            (Finset.add_sum_erase _ k' (Finset.mem_univ i₀)).symm
          have e3 : ∑ i ∈ Finset.univ.erase i₀, k' i = ∑ i ∈ Finset.univ.erase i₀, k i :=
            Finset.sum_congr rfl fun i hi => hupd i (Finset.ne_of_mem_erase hi)
          rw [e2, e3, hupd₀]
          omega
        have hV : stepVal a k = a i₀ + stepVal a k' := by
          have e1 : ∑ i, (k i : ℝ) * a i
              = (k i₀ : ℝ) * a i₀ + ∑ i ∈ Finset.univ.erase i₀, (k i : ℝ) * a i :=
            (Finset.add_sum_erase _ (fun i => (k i : ℝ) * a i) (Finset.mem_univ i₀)).symm
          have e2 : ∑ i, (k' i : ℝ) * a i
              = (k' i₀ : ℝ) * a i₀ + ∑ i ∈ Finset.univ.erase i₀, (k' i : ℝ) * a i :=
            (Finset.add_sum_erase _ (fun i => (k' i : ℝ) * a i) (Finset.mem_univ i₀)).symm
          have e3 : ∑ i ∈ Finset.univ.erase i₀, (k' i : ℝ) * a i
              = ∑ i ∈ Finset.univ.erase i₀, (k i : ℝ) * a i :=
            Finset.sum_congr rfl fun i hi => by rw [hupd i (Finset.ne_of_mem_erase hi)]
          have e4 : ((k' i₀ : ℕ) : ℝ) = (k i₀ : ℝ) - 1 := by
            rw [hupd₀, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi₀), Nat.cast_one]
          rw [stepVal, stepVal, e1, e2, e3, e4]
          ring
        have hrw : q ^ (n + 1) * d (x - stepVal a k)
            = q * (q ^ n * d ((x - a i₀) - stepVal a k')) := by
          rw [hV, sub_add_eq_sub_sub, pow_succ]
          ring
        rw [hrw]
        exact le_trans (mul_le_mul_of_nonneg_left (ih k' hsum' (x - a i₀)) hq0.le)
          (step_le hp hqle hd0 hharm x i₀)

/-- Density of the group generated by the steps makes the *semigroup* they generate
`δ`-dense in an interval of any prescribed length, with a uniform bound on the number of
steps used.  This is the arithmetic content of `System.NonArithmetic`: a small positive
group element is a difference `P - N` of two semigroup elements, and the `n+1` points
`jP + (n-j)N` form an arithmetic progression of step `P - N` and length `n(P-N)`. -/
theorem exists_net
    (hdense : Dense ((AddSubgroup.closure (Set.range a) : AddSubgroup ℝ) : Set ℝ))
    {δ R : ℝ} (hδ : 0 < δ) :
    ∃ (c : ℝ) (m : ℕ), ∀ y ∈ Set.Icc c (c + R),
      ∃ k : ι → ℕ, (∑ i, k i) ≤ m ∧ |y - stepVal a k| ≤ δ := by
  classical
  obtain ⟨x₀, hx₀mem, hx₀⟩ := hdense.exists_mem_open isOpen_Ioo
    (⟨δ / 2, by constructor <;> linarith⟩ : (Set.Ioo (0 : ℝ) δ).Nonempty)
  have hx0pos : 0 < x₀ := hx₀.1
  have hspan : x₀ ∈ Submodule.span ℤ (Set.range a) := by
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
    exact hx₀mem
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp hspan
  set kp : ι → ℕ := fun i => (cz i).toNat with hkp
  set km : ι → ℕ := fun i => (-cz i).toNat with hkm
  have hcast : ∀ i, (kp i : ℝ) - (km i : ℝ) = (cz i : ℝ) := by
    intro i
    have hz : ((kp i : ℤ) - (km i : ℤ)) = cz i := by simp only [hkp, hkm]; omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
  have hPN : stepVal a kp - stepVal a km = x₀ := by
    rw [stepVal, stepVal, ← Finset.sum_sub_distrib, ← hcz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_mul, hcast i, zsmul_eq_mul]
  set n : ℕ := ⌈R / x₀⌉₊ with hn
  have hnx : R ≤ (n : ℝ) * x₀ := by
    rw [← div_le_iff₀ hx0pos]
    exact Nat.le_ceil _
  refine ⟨(n : ℝ) * stepVal a km, n * (∑ i, kp i) + n * (∑ i, km i), ?_⟩
  rintro y ⟨hy1, hy2⟩
  set t : ℝ := (y - (n : ℝ) * stepVal a km) / x₀ with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hx0pos.le
  have htn : t ≤ (n : ℝ) := by
    rw [ht, div_le_iff₀ hx0pos]
    linarith
  set j : ℕ := ⌊t⌋₊ with hj
  have hjt : (j : ℝ) ≤ t := Nat.floor_le ht0
  have htj : t < (j : ℝ) + 1 := Nat.lt_floor_add_one t
  have hjn : j ≤ n := by simpa using Nat.floor_mono htn
  refine ⟨fun i => j * kp i + (n - j) * km i, ?_, ?_⟩
  · calc ∑ i, (j * kp i + (n - j) * km i)
        = j * (∑ i, kp i) + (n - j) * (∑ i, km i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ n * (∑ i, kp i) + n * (∑ i, km i) := by
          gcongr
          omega
  · have hnj : (((n - j : ℕ)) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjn
    have hV : stepVal a (fun i => j * kp i + (n - j) * km i)
        = (j : ℝ) * x₀ + (n : ℝ) * stepVal a km := by
      have hterm : ∀ i : ι, ((j * kp i + (n - j) * km i : ℕ) : ℝ) * a i
          = (j : ℝ) * ((kp i : ℝ) * a i) + ((n : ℝ) - (j : ℝ)) * ((km i : ℝ) * a i) := by
        intro i
        push_cast [hnj]
        ring
      rw [stepVal, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← stepVal, ← stepVal, ← hPN]
      ring
    have htx : t * x₀ = y - (n : ℝ) * stepVal a km := by
      rw [ht]
      field_simp
    have hdiff : y - ((j : ℝ) * x₀ + (n : ℝ) * stepVal a km) = (t - (j : ℝ)) * x₀ := by
      rw [sub_mul, htx]
      ring
    rw [hV, hdiff, abs_of_nonneg (mul_nonneg (by linarith) hx0pos.le)]
    nlinarith [hx₀.2]

/-- Upward propagation: harmonicity expresses a value through values strictly below it,
so a bound on one window of length at least `max_i a_i` spreads to the whole half line
above that window. -/
theorem propagate_le [Nonempty ι] (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (ha : ∀ i, 0 < a i) (hharm : ∀ x, d x = ∑ i, p i * d (x - a i))
    {u η R : ℝ} (hRa : ∀ i, a i ≤ R) (hbase : ∀ y ∈ Set.Icc u (u + R), d y ≤ η) :
    ∀ z, u ≤ z → d z ≤ η := by
  classical
  obtain ⟨i₁, -, hmin⟩ := Finset.exists_min_image Finset.univ a
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have he : 0 < a i₁ := ha i₁
  have key : ∀ n : ℕ, ∀ y ∈ Set.Icc u (u + R + (n : ℝ) * a i₁), d y ≤ η := by
    intro n
    induction n with
    | zero => intro y hy; exact hbase y ⟨hy.1, by simpa using hy.2⟩
    | succ n ih =>
        rintro y ⟨hy1, hy2⟩
        have hcast : ((n : ℝ) + 1) * a i₁ = (n : ℝ) * a i₁ + a i₁ := by ring
        rw [Nat.cast_succ, hcast] at hy2
        rcases le_or_gt y (u + R + (n : ℝ) * a i₁) with hle | hgt
        · exact ih y ⟨hy1, hle⟩
        · have hn0 : (0 : ℝ) ≤ (n : ℝ) * a i₁ :=
            mul_nonneg (Nat.cast_nonneg n) he.le
          rw [hharm y]
          calc ∑ i, p i * d (y - a i) ≤ ∑ i, p i * η := by
                refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp i)
                refine ih (y - a i) ⟨?_, ?_⟩
                · have := hRa i
                  linarith
                · have := hmin i (Finset.mem_univ i)
                  linarith
            _ = η := by rw [← Finset.sum_mul, hpsum, one_mul]
  intro z hz
  obtain ⟨N, hN⟩ := exists_nat_ge ((z - u - R) / a i₁)
  refine key N z ⟨hz, ?_⟩
  rw [div_le_iff₀ he] at hN
  linarith

/-- **Choquet-Deny**, in the form the renewal analysis needs.  A bounded, uniformly
continuous function harmonic for a finitely supported step law with positive steps whose
generated group is dense converges at `+∞` to its supremum: the maximum principle pushes
the supremum down the semigroup generated by the steps, that semigroup is dense in a
window of length `max_i a_i` far below any near-maximiser, and harmonicity carries the
bound back up the line. -/
theorem tendsto_atTop_sSup [Nonempty ι] {h : ℝ → ℝ} (hp : ∀ i, 0 < p i)
    (hpsum : ∑ i, p i = 1) (ha : ∀ i, 0 < a i)
    (hdense : Dense ((AddSubgroup.closure (Set.range a) : AddSubgroup ℝ) : Set ℝ))
    (hbdd : BddAbove (Set.range h))
    (huc : ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| ≤ δ → |h x - h y| ≤ ε)
    (hharm : ∀ x, h x = ∑ i, p i * h (x - a i)) :
    Tendsto h atTop (𝓝 (sSup (Set.range h))) := by
  classical
  set M := sSup (Set.range h) with hM
  have hMle : ∀ x, h x ≤ M := fun x => le_csSup hbdd ⟨x, rfl⟩
  set d : ℝ → ℝ := fun x => M - h x with hd
  have hd0 : ∀ x, 0 ≤ d x := fun x => sub_nonneg.mpr (hMle x)
  have hdharm : ∀ x, d x = ∑ i, p i * d (x - a i) := by
    intro x
    have hrw : ∑ i, p i * d (x - a i) = (∑ i, p i) * M - ∑ i, p i * h (x - a i) := by
      simp only [hd, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hrw, hpsum, one_mul, ← hharm x]
  obtain ⟨i₀, -, hqmin⟩ := Finset.exists_min_image Finset.univ p
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hq0 : 0 < p i₀ := hp i₀
  have hqle : ∀ i, p i₀ ≤ p i := fun i => hqmin i (Finset.mem_univ i)
  have hq1 : p i₀ ≤ 1 := by
    calc p i₀ ≤ ∑ i, p i :=
          Finset.single_le_sum (fun i _ => (hp i).le) (Finset.mem_univ i₀)
      _ = 1 := hpsum
  obtain ⟨i₂, -, hamax⟩ := Finset.exists_max_image Finset.univ a
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hRa : ∀ i, a i ≤ a i₂ := fun i => hamax i (Finset.mem_univ i)
  have core : ∀ η > 0, ∃ u : ℝ, ∀ z, u ≤ z → d z ≤ η := by
    intro η hη
    obtain ⟨δ, hδ0, hδ⟩ := huc (η / 2) (by linarith)
    obtain ⟨c, m, hnet⟩ := exists_net (a := a) hdense hδ0 (R := a i₂)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, d x₀ ≤ (η / 2) * p i₀ ^ m := by
      have hpos : 0 < (η / 2) * p i₀ ^ m := by positivity
      obtain ⟨y, hy, hylt⟩ := exists_lt_of_lt_csSup (Set.range_nonempty h)
        (show M - (η / 2) * p i₀ ^ m < M by linarith)
      obtain ⟨x₀, rfl⟩ := hy
      exact ⟨x₀, by simp only [hd]; linarith⟩
    refine ⟨x₀ - c - a i₂, ?_⟩
    refine propagate_le (fun i => (hp i).le) hpsum ha hdharm hRa ?_
    rintro y ⟨hy1, hy2⟩
    obtain ⟨k, hk, hkd⟩ := hnet (x₀ - y) ⟨by linarith, by linarith⟩
    have h1 : p i₀ ^ m * d (x₀ - stepVal a k) ≤ d x₀ :=
      iterate_le hq0 hq1 (fun i => (hp i).le) hqle hd0 hdharm m k hk x₀
    have hqm : 0 < p i₀ ^ m := pow_pos hq0 m
    have h2 : d (x₀ - stepVal a k) ≤ η / 2 := by
      refine le_of_mul_le_mul_left ?_ hqm
      calc p i₀ ^ m * d (x₀ - stepVal a k) ≤ d x₀ := h1
        _ ≤ (η / 2) * p i₀ ^ m := hx₀
        _ = p i₀ ^ m * (η / 2) := by ring
    have h3 : |h (x₀ - stepVal a k) - h y| ≤ η / 2 := by
      refine hδ _ _ ?_
      rw [show x₀ - stepVal a k - y = (x₀ - y) - stepVal a k from by ring]
      exact hkd
    have h4 : d y - d (x₀ - stepVal a k) = h (x₀ - stepVal a k) - h y := by
      simp only [hd]; ring
    have h5 := (abs_le.mp h3).2
    linarith
  have hdtend : Tendsto d atTop (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨u, hu⟩ := core (ε / 2) (by linarith)
    refine ⟨u, fun z hz => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 z)]
    have := hu z hz
    linarith
  have hfin : Tendsto (fun x => M - d x) atTop (𝓝 (M - 0)) :=
    tendsto_const_nhds.sub hdtend
  have hfun : (fun x => M - d x) = h := by funext x; simp [hd]
  rw [hfun, sub_zero] at hfin
  exact hfin

/-- **Choquet-Deny**: a bounded, uniformly continuous harmonic function of a finitely
supported non-arithmetic step law is constant. -/
theorem const_of_harmonic [Nonempty ι] {h : ℝ → ℝ} (hp : ∀ i, 0 < p i)
    (hpsum : ∑ i, p i = 1) (ha : ∀ i, 0 < a i)
    (hdense : Dense ((AddSubgroup.closure (Set.range a) : AddSubgroup ℝ) : Set ℝ))
    (hbddA : BddAbove (Set.range h)) (hbddB : BddBelow (Set.range h))
    (huc : ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| ≤ δ → |h x - h y| ≤ ε)
    (hharm : ∀ x, h x = ∑ i, p i * h (x - a i)) :
    ∀ x y : ℝ, h x = h y := by
  have h1 := tendsto_atTop_sSup hp hpsum ha hdense hbddA huc hharm
  have hbdd' : BddAbove (Set.range fun x => -h x) := by
    obtain ⟨b, hb⟩ := hbddB
    refine ⟨-b, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact neg_le_neg (hb ⟨x, rfl⟩)
  have huc' : ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| ≤ δ → |(-h x) - (-h y)| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := huc ε hε
    refine ⟨δ, hδ0, fun x y hxy => ?_⟩
    rw [show -h x - -h y = -(h x - h y) from by ring, abs_neg]
    exact hδ x y hxy
  have hharm' : ∀ x, (fun x => -h x) x = ∑ i, p i * (fun x => -h x) (x - a i) := by
    intro x
    simp only [mul_neg, Finset.sum_neg_distrib, ← hharm x]
  have h2 := tendsto_atTop_sSup hp hpsum ha hdense hbdd' huc' hharm'
  have h3 : Tendsto h atTop (𝓝 (-(sSup (Set.range fun x => -h x)))) := by
    have := h2.neg
    simpa using this
  have h4 : sSup (Set.range h) = -(sSup (Set.range fun x => -h x)) := tendsto_nhds_unique h1 h3
  have hval : ∀ x : ℝ, h x = sSup (Set.range h) := by
    intro x
    have hx1 : h x ≤ sSup (Set.range h) := le_csSup hbddA ⟨x, rfl⟩
    have hx2 : -h x ≤ sSup (Set.range fun x => -h x) := le_csSup hbdd' ⟨x, rfl⟩
    have hx3 : -(sSup (Set.range fun x => -h x)) ≤ h x := by linarith
    rw [← h4] at hx3
    linarith
  intro x y
  rw [hval x, hval y]

end KeyRenewal

/-- `thm:non-lattice-limit`, the first half of `eq:g-non-lattice-limit`: the limit
constant `C = m⁻¹ ∫ z` is strictly positive.  The renewal mean is positive because the
log-ratios are, and `∫ z > 0` because the off-diagonal blocks of the self-similar
decomposition of `Φ` are non-negative and the diagonal ones do not exhaust the mass. -/
theorem renewalConstant_pos {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x :=
  mul_pos (inv_pos.mpr (S.renewalMean_pos s))
    (KeyRenewal.integral_renewalDefect_pos S hs0 hsep hdim hμ)

/-- Choquet-Deny in the language of the paper: a bounded, uniformly continuous function
satisfying the recursion `eq:g-recursion` on the *whole* line is constant, as soon as the
system is non-arithmetic.  `eq:g-recursion` holds for `G` only on the tail
`w > log ρ⁻¹`, which is why this does not by itself close `thm:non-lattice-limit`. -/
theorem const_of_g_recursion {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {s : ℝ}
    (hdim : S.IsDimension s) (hna : S.NonArithmetic) {g : ℝ → ℝ}
    (hbddA : BddAbove (Set.range g)) (hbddB : BddBelow (Set.range g))
    (huc : ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| ≤ δ → |g x - g y| ≤ ε)
    (hrec : ∀ w, g w = ∑ i, S.ratio i ^ s * g (w - S.logRatio i)) :
    ∀ x y : ℝ, g x = g y :=
  KeyRenewal.const_of_harmonic (fun i => Real.rpow_pos_of_pos (S.ratio_pos i) s) hdim
    (fun i => S.logRatio_pos i) hna hbddA hbddB huc hrec

/-- `thm:non-lattice-limit`, `eq:g-non-lattice-limit`, reduced to the bare convergence of
`G`.  Everything the statement asserts beyond the existence of the limit is proved here:
the limit is the constant `m⁻¹ ∫ z` the paper names, and that constant is finite and
strictly positive.  The missing input is the key renewal theorem itself, which is what
supplies the hypothesis `hconv`. -/
theorem nonLatticeLimit_of_tendsto {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    (hconv : ∃ C : ℝ, Tendsto (G s μ) atTop (𝓝 C)) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) := by
  obtain ⟨C, hC⟩ := hconv
  have hval : (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x = C := by
    rw [KeyRenewal.integral_renewalDefect_eq S hs0 hsep hdim hμ hC,
      inv_mul_cancel_left₀ (S.renewalMean_pos s).ne']
  exact ⟨renewalConstant_pos S hs0 hsep hdim hμ, by rw [hval]; exact hC⟩

end BrownianImages


