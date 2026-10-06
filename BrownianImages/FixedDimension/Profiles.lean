/-
`thm:fixed-dimension-profiles`, the mean and the non-lattice limit: for the natural measure
`μ_p` of the system `x ↦ ax`, `x ↦ bx + 1 - b` with `a = p^{1/s}`, `b = q^{1/s}`, the Cesàro
means of the expected profile `H_{μ_p}^s` converge to `eq:fixed-dimension-mean`,
`H̄_s(p) = 2^{1-s} Γ(1-s) pq M_p(s)/E(p)`, and in the non-lattice case the profile itself
converges.  The proof is that of `thm:two-contraction-formula`: the renewal mean is
`m = E(p)/s`, the cross term is `Φ_× = 2pq ℙ(Z_p ≤ δ)`, and the forcing transform at
`ξ = 0` is `2pq M_p(s)/s`.

* `fixedSystem_stronglySeparated`, `fixedSystem_openSetCondition`: the geometry.
* `fixedSystem_crossPhi`: `Φ_× = 2pq ℙ(Z_p ≤ δ)`.
* `fixedSystem_renewalMean`: `m = E(p)/s`.
* `fixedSystem_integral_renewalDefect`: `∫ z = 2pq M_p(s)/s`.
* `fixedSystem_tendsto_avg_H`: `eq:fixed-dimension-mean`.
* `fixedSystem_tendsto_H_nonLattice`: the non-lattice limit.
-/
import BrownianImages.FixedDimension.Natural
import BrownianImages.FixedDimension.RealLevelSums
import BrownianImages.TwoContraction.Formula

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

/-! ### The geometry of the system -/

/-- The fixed-dimension system is strongly separated with gap `1 - a - b` on every subset of
`[0,1]`: the first-level hulls are `[0, a]` and `[1 - b, 1]`. -/
theorem fixedSystem_stronglySeparated {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {K : Set ℝ} (hK : K ⊆ Icc 0 1) :
    (fixedSystem s p hs hp0 hp1).StronglySeparated K (crossGap s p) := by
  refine ⟨crossGap_pos hs hs1 hp0 hp1, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hx0, hx1⟩ := hK hx
  obtain ⟨hy0, hy1⟩ := hK hy
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have ha1 := fixedA_le_one hs hp0 hp1
  have hb1 := fixedB_le_one hs hp0 hp1
  unfold crossGap
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [fixedSystem_map_zero, fixedSystem_map_one, le_abs]; right; nlinarith
  · rw [fixedSystem_map_one, fixedSystem_map_zero, le_abs]; left; nlinarith

/-- The open set condition for the fixed-dimension system, from strong separation. -/
theorem fixedSystem_openSetCondition {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {K : Set ℝ} (hK : (fixedSystem s p hs hp0 hp1).IsAttractor K) :
    (fixedSystem s p hs hp0 hp1).OpenSetCondition :=
  ((fixedSystem_stronglySeparated hs hs1 hp0 hp1 hK.2.2.1).strongOpenSetCondition _
    hK).openSetCondition _

/-- **`Φ_× = 2pq ℙ(Z_p ≤ δ)`**: the cross term of the fixed-dimension system, conditioned on
distinct first digits. -/
theorem fixedSystem_crossPhi {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ}
    {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) (δ : ℝ) :
    (fixedSystem s p hs hp0 hp1).crossPhi s μ δ
      = 2 * (p * (1 - p)) *
          ((μ.prod μ) {q : ℝ × ℝ | fixedCross s p q.1 q.2 ≤ δ}).toReal := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  have hm0 : Measurable ((fixedSystem s p hs hp0 hp1).map 0) :=
    (Hutchinson.continuous_systemMap _ 0).measurable
  have hm1 : Measurable ((fixedSystem s p hs hp0 hp1).map 1) :=
    (Hutchinson.continuous_systemMap _ 1).measurable
  have hset : MeasurableSet {q : ℝ × ℝ | |q.1 - q.2| ≤ δ} := measurableSet_phiSet δ
  have h01 : ((μ.map ((fixedSystem s p hs hp0 hp1).map 0)).prod
      (μ.map ((fixedSystem s p hs hp0 hp1).map 1))) {q : ℝ × ℝ | |q.1 - q.2| ≤ δ}
      = (μ.prod μ) {q : ℝ × ℝ | fixedCross s p q.1 q.2 ≤ δ} := by
    rw [Measure.map_prod_map μ μ hm0 hm1, Measure.map_apply (hm0.prodMap hm1) hset]
    refine measure_congr (hbox.mono fun q hq => ?_)
    simp only [Set.mem_preimage, Prod.map_fst, Prod.map_snd, Set.mem_ofPred_eq,
      fixedSystem_map_zero, fixedSystem_map_one]
    have hZ := (fixedCross_mem hs hp0 hp1 hq.1 hq.2).1
    have hg : 0 ≤ 1 - fixedA s p - fixedB s p := by
      have := crossGap_pos hs hs1 hp0 hp1
      unfold crossGap at this
      linarith
    unfold fixedCross at hZ
    have hrw : |fixedA s p * q.1 - (fixedB s p * q.2 + (1 - fixedB s p))|
        = fixedCross s p q.1 q.2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      unfold fixedCross; ring
    exact propext (by rw [hrw])
  have h10 : ((μ.map ((fixedSystem s p hs hp0 hp1).map 1)).prod
      (μ.map ((fixedSystem s p hs hp0 hp1).map 0))) {q : ℝ × ℝ | |q.1 - q.2| ≤ δ}
      = (μ.prod μ) {q : ℝ × ℝ | fixedCross s p q.1 q.2 ≤ δ} := by
    rw [Measure.map_prod_map μ μ hm1 hm0, Measure.map_apply (hm1.prodMap hm0) hset]
    conv_lhs => rw [← Measure.prod_swap, Measure.map_apply measurable_swap
        ((hm1.prodMap hm0) hset)]
    refine measure_congr (hbox.mono fun q hq => ?_)
    simp only [Set.mem_preimage, Prod.map_fst, Prod.map_snd, Set.mem_ofPred_eq,
      Prod.fst_swap, Prod.snd_swap, fixedSystem_map_zero, fixedSystem_map_one]
    have hZ := (fixedCross_mem hs hp0 hp1 hq.1 hq.2).1
    have hg : 0 ≤ 1 - fixedA s p - fixedB s p := by
      have := crossGap_pos hs hs1 hp0 hp1
      unfold crossGap at this
      linarith
    unfold fixedCross at hZ
    have hrw : |fixedB s p * q.2 + (1 - fixedB s p) - fixedA s p * q.1|
        = fixedCross s p q.1 q.2 := by
      rw [abs_of_nonneg (by linarith)]
      unfold fixedCross; ring
    exact propext (by rw [hrw])
  classical
  unfold System.crossPhi
  simp only [Fin.sum_univ_two, Fin.isValue]
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) = False from by decide,
    show ((1 : Fin 2) = 0) = False from by decide, ite_false, zero_add, add_zero, h01, h10]
  rw [fixedSystem_ratio_zero, fixedSystem_ratio_one, fixedA_rpow hs hp0, fixedB_rpow hs hp1]
  ring

/-- **The renewal mean is `m = E(p)/s`**: `p log(1/a) + q log(1/b)` with `a = p^{1/s}`,
`b = q^{1/s}`. -/
theorem fixedSystem_renewalMean {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    (fixedSystem s p hs hp0 hp1).renewalMean s = entropy p / s := by
  simp only [System.renewalMean, System.logRatio, Fin.sum_univ_two, fixedSystem_ratio_zero,
    fixedSystem_ratio_one, fixedA_rpow hs hp0, fixedB_rpow hs hp1]
  unfold fixedA fixedB entropy
  rw [Real.log_inv, Real.log_inv, Real.log_rpow hp0, Real.log_rpow (by linarith)]
  field_simp
  ring

/-! ### The moment against the natural measure -/

/-- `M_p(s)` as an integral over `μ ⊗ μ`. -/
def fixedMomentProd (s p : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, fixedCross s p q.1 q.2 ^ (-s) ∂(μ.prod μ)

/-- For the natural measure, `fixedMomentProd` is `M_p(s)`. -/
theorem fixedMomentProd_eq {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    fixedMomentProd s p μ = fixedMoment s p := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  rw [fixedMoment_eq_natural hs hp0 hp1 hμ]
  unfold fixedMomentProd
  refine integral_prod_symm _ ?_
  refine Integrable.of_bound ((continuous_fixedCross s p).measurable.pow_const _).aestronglyMeasurable
    (crossGap s p ^ (-s)) (hbox.mono fun q hq => ?_)
  have hZ := fixedCross_mem hs hp0 hp1 hq.1 hq.2
  have hg := crossGap_pos hs hs1 hp0 hp1
  have hZp : 0 < fixedCross s p q.1 q.2 := lt_of_lt_of_le hg hZ.1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hZp.le _)]
  exact rpow_neg_antitone hg hZ.1 hs.le

/-- **`∫ z = 2pq M_p(s)/s`**, the forcing transform `eq:fixed-dimension-forcing` at `ξ = 0`,
by Tonelli. -/
theorem fixedSystem_integral_renewalDefect {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    ∫ w, (fixedSystem s p hs hp0 hp1).renewalDefect s μ w
      = 2 * (p * (1 - p)) * fixedMomentProd s p μ / s := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  set ν := μ.prod μ with hν
  set Z : ℝ × ℝ → ℝ := fun q => fixedCross s p q.1 q.2 with hZ
  have hZc : Continuous Z := continuous_fixedCross s p
  have hbpos : 0 < crossGap s p := crossGap_pos hs hs1 hp0 hp1
  have hZpos : ∀ᵐ q ∂ν, crossGap s p ≤ Z q ∧ Z q ≤ 1 :=
    hbox.mono fun q hq => fixedCross_mem hs hp0 hp1 hq.1 hq.2
  -- the defect through the cross term
  have hz : ∀ w, (fixedSystem s p hs hp0 hp1).renewalDefect s μ w
      = 2 * (p * (1 - p)) * (Real.exp (s * w) * (ν {q | Z q ≤ Real.exp (-w)}).toReal) := by
    intro w
    rw [renewalDefect_eq_crossPhi _ hμ, fixedSystem_crossPhi hs hs1 hp0 hp1 hμ]
    ring
  -- the key identity, by Tonelli
  set f : ℝ → ℝ := fun w => Real.exp (s * w) * (ν {q | Z q ≤ Real.exp (-w)}).toReal with hf
  have hfnn : ∀ w, 0 ≤ f w := fun w => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  set A : Set (ℝ × (ℝ × ℝ)) := {q | Z q.2 ≤ Real.exp (-q.1)} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le (hZc.comp continuous_snd)
      (Real.continuous_exp.comp continuous_fst.neg)).measurableSet
  set F : ℝ × (ℝ × ℝ) → ℝ≥0∞ := A.indicator fun q => ENNReal.ofReal (Real.exp (s * q.1))
    with hF
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_fst))).indicator hAm
  have hleft : ∫⁻ w, ENNReal.ofReal (f w) = ∫⁻ w, ∫⁻ q, F (w, q) ∂ν := by
    refine lintegral_congr fun w => ?_
    have hsec : ∀ q, F (w, q) = {q | Z q ≤ Real.exp (-w)}.indicator
        (fun _ => ENNReal.ofReal (Real.exp (s * w))) q := by
      intro q
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [hsec]
    rw [lintegral_indicator_const ((isClosed_le hZc continuous_const).measurableSet),
      hf, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hright : ∫⁻ q, ∫⁻ w, F (w, q) ∂volume ∂ν
      = ∫⁻ q, ENNReal.ofReal (Z q ^ (-s) / s) ∂ν := by
    refine lintegral_congr_ae (hZpos.mono fun q hq => ?_)
    have hZq : 0 < Z q := lt_of_lt_of_le hbpos hq.1
    have hsec : ∀ w, F (w, q) = (Iic (-Real.log (Z q))).indicator
        (fun w => ENNReal.ofReal (Real.exp (s * w))) w := by
      intro w
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      congr 1
      exact propext (by rw [le_neg, ← Real.log_le_iff_le_exp hZq, le_neg])
    simp only [hsec]
    rw [lintegral_indicator measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hs _)
        (Eventually.of_forall fun w => (Real.exp_pos _).le),
      integral_exp_mul_Iic hs, Real.rpow_def_of_pos hZq]
    congr 2
    ring_nf
  have hswap : ∫⁻ w, ∫⁻ q, F (w, q) ∂ν = ∫⁻ q, ∫⁻ w, F (w, q) ∂volume ∂ν :=
    lintegral_lintegral_swap hFm.aemeasurable
  -- integrability and the passage back to Bochner integrals
  have hMint : Integrable (fun q => Z q ^ (-s) / s) ν := by
    refine Integrable.of_bound ((hZc.measurable.pow_const _).div_const _).aestronglyMeasurable
      (crossGap s p ^ (-s) / s) (hZpos.mono fun q hq => ?_)
    have hZq : 0 < Z q := lt_of_lt_of_le hbpos hq.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hZq.le _) hs.le)]
    exact div_le_div_of_nonneg_right (rpow_neg_antitone hbpos hq.1 hs.le) hs.le
  have hkey : ∫ w, f w = fixedMomentProd s p μ / s := by
    have hlin : ∫⁻ w, ENNReal.ofReal (f w) = ENNReal.ofReal (fixedMomentProd s p μ / s) := by
      rw [hleft, hswap, hright, fixedMomentProd, ← integral_div,
        ofReal_integral_eq_lintegral_ofReal hMint
          (hZpos.mono fun q hq => div_nonneg (Real.rpow_nonneg
            (lt_of_lt_of_le hbpos hq.1).le _) hs.le)]
    have hfm : AEStronglyMeasurable f volume := by
      refine ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
        ?_).aestronglyMeasurable
      have hmono : Antitone fun w : ℝ => (ν {q | Z q ≤ Real.exp (-w)}).toReal := by
        intro w w' hww'
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun q hq => ?_)
        exact le_trans hq (Real.exp_le_exp.2 (by linarith))
      exact hmono.measurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfnn) hfm, hlin,
      ENNReal.toReal_ofReal]
    have hM : 0 ≤ fixedMomentProd s p μ := integral_nonneg_of_ae (hZpos.mono fun q hq =>
      Real.rpow_nonneg (lt_of_lt_of_le hbpos hq.1).le _)
    exact div_nonneg hM hs.le
  simp only [hz]
  rw [integral_const_mul, hkey]
  ring

/-! ### `eq:fixed-dimension-mean` and the non-lattice limit -/

/-- **`eq:fixed-dimension-mean`.**  For the natural measure of the fixed-dimension system,
the Cesàro means of `H_{μ_p}^s` converge to `H̄_s(p) = 2^{1-s} Γ(1-s) pq M_p(s)/E(p)`, in the
lattice and the non-lattice case alike. -/
theorem fixedSystem_tendsto_avg_H {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, H s μ t) atTop (𝓝 (fixedMean s p)) := by
  have h := hμ.tendsto_avg_H _ hs hs1 (fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor)
    (fixedSystem_isDimension hs hp0 hp1)
  convert h using 2
  rw [integral_kern_eq_Gamma hs1, fixedSystem_integral_renewalDefect hs hs1 hp0 hp1 hμ,
    fixedSystem_renewalMean hs hp0 hp1, fixedMomentProd_eq hs hs1 hp0 hp1 hμ]
  unfold fixedMean
  have hE := entropy_pos hp0 hp1
  rw [show (2:ℝ) ^ (1 - s) = 2 * 2 ^ (-s) by
    rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add (by norm_num), Real.rpow_one]]
  field_simp

/-- **The non-lattice limit** of `thm:fixed-dimension-profiles`: if the system is
non-lattice, `H_{μ_p}^s(t) → H̄_s(p)`. -/
theorem fixedSystem_tendsto_H_nonLattice {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
    (hna : (fixedSystem s p hs hp0 hp1).NonArithmetic) :
    Tendsto (H s μ) atTop (𝓝 (fixedMean s p)) := by
  have := hμ.isProbabilityMeasure
  have hosc := fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman _ hs.le hμ
  obtain ⟨hCpos, hC⟩ := non_lattice_limit _ hs hs1
    (hosc.strongOpenSetCondition _ hμ.attractor) (fixedSystem_isDimension hs hp0 hp1) hna hμ
  have h := (profile_asymptotics_nonLattice hs hs1 hA hCpos hC).2
  convert h using 2
  rw [integral_kern_eq_Gamma hs1, fixedSystem_integral_renewalDefect hs hs1 hp0 hp1 hμ,
    fixedSystem_renewalMean hs hp0 hp1, fixedMomentProd_eq hs hs1 hp0 hp1 hμ]
  unfold fixedMean
  have hE := entropy_pos hp0 hp1
  rw [show (2:ℝ) ^ (1 - s) = 2 * 2 ^ (-s) by
    rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add (by norm_num), Real.rpow_one]]
  field_simp

end

end BrownianImages
