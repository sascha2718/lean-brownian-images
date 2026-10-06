/-
`sec:two-contraction-formula`, the limiting profiles: the mean of the expected profile
of the family `x ↦ x/2`, `x ↦ cx + 1 - c`, through the cross-distance
`Z_c = 1 - c + cY - X/2` between a point `cY + 1 - c` of the right piece and a point
`X/2` of the left one.

* `crossDist`, `crossMoment`: `Z_c` and its moment `M_c(α) = 𝔼 Z_c^{-α}` at real `α`.
* `pairSystem_crossPhi`: `Φ_×(δ) = 2pq ℙ(Z_c ≤ δ)`, conditioning on distinct first
  digits, as in the proof of `thm:two-contraction-formula`.
* `pairSystem_integral_renewalDefect`: `∫ z = 2pq M_c(s)/s`, the forcing transform
  `eq:two-contraction-forcing-transform` at `ξ = 0`, by Tonelli.
* `integral_kern_eq_Gamma`: `∫₀^∞ φ = 2^{-s} Γ(1-s)`, the multiplier
  `eq:gamma-multiplier` at `k = 0`.
* `twoContractionMean`, `pairSystem_tendsto_avg_H`: `eq:two-contraction-mean`, the mean
  of `H_{μ_c}^s` in closed form, in the lattice and the non-lattice case alike.
* `pairSystem_tendsto_H_nonLattice`: `eq:two-contraction-constant`, the limit of
  `H_{μ_c}^s` itself in the non-lattice case.
-/
import BrownianImages.TwoContraction.Cesaro
import BrownianImages.Multiplier
import BrownianImages.Asymptotics

namespace BrownianImages

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

/-- The cross-distance `Z_c = 1 - c + cY - X/2` of `sec:two-contraction-formula`, at
`X = x` and `Y = y`: the distance from the point `x/2` of the left piece to the point
`cy + 1 - c` of the right one. -/
def crossDist (c x y : ℝ) : ℝ := 1 - c + c * y - x / 2

/-- The moment `M_c(α) = 𝔼 Z_c^{-α}` of `sec:two-contraction-formula` at real `α`, for
independent `X, Y` with law `μ`. -/
def crossMoment (c : ℝ) (μ : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, crossDist c p.1 p.2 ^ (-z) ∂(μ.prod μ)

/-- The first ratio of the two-map system is `1/2`. -/
@[simp] theorem pairSystem_ratio_zero {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    (pairSystem c hc0 hc).ratio 0 = 1/2 := rfl

/-- The second ratio of the two-map system is `c`. -/
@[simp] theorem pairSystem_ratio_one {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    (pairSystem c hc0 hc).ratio 1 = c := rfl

/-- On the unit square the cross-distance lies in `[1/2 - c, 1]`. -/
theorem crossDist_mem {c x y : ℝ} (hc0 : 0 ≤ c) (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1) : 1/2 - c ≤ crossDist c x y ∧ crossDist c x y ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  unfold crossDist
  constructor <;> nlinarith

/-- The cross-distance is continuous. -/
theorem continuous_crossDist (c : ℝ) :
    Continuous fun p : ℝ × ℝ => crossDist c p.1 p.2 := by
  unfold crossDist; fun_prop

/-- A measure on `[0,1]` makes its square carry the unit square. -/
theorem ae_prod_mem_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : μ (Icc (0:ℝ) 1)ᶜ = 0) :
    ∀ᵐ p ∂(μ.prod μ), p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ Icc (0:ℝ) 1 := by
  have hx : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1 := by
    rw [ae_iff]
    exact h
  exact (Measure.quasiMeasurePreserving_fst.ae hx).and
    (Measure.quasiMeasurePreserving_snd.ae hx)

/-- **`Φ_× = 2pq ℙ(Z_c ≤ δ)`**: the cross term of the two-map system, conditioned on
distinct first digits.  Both orders of the two digits give the distance `Z_c`, since
the right piece lies to the right of the left one. -/
theorem pairSystem_crossPhi {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : (pairSystem c hc0 hc).IsNatural K s μ) (δ : ℝ) :
    (pairSystem c hc0 hc).crossPhi s μ δ
      = 2 * ((1/2 : ℝ) ^ s * c ^ s) *
          ((μ.prod μ) {p : ℝ × ℝ | crossDist c p.1 p.2 ≤ δ}).toReal := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  have hm0 : Measurable ((pairSystem c hc0 hc).map 0) :=
    (Hutchinson.continuous_systemMap _ 0).measurable
  have hm1 : Measurable ((pairSystem c hc0 hc).map 1) :=
    (Hutchinson.continuous_systemMap _ 1).measurable
  have hset : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := measurableSet_phiSet δ
  -- the `(0,1)` term
  have h01 : ((μ.map ((pairSystem c hc0 hc).map 0)).prod
      (μ.map ((pairSystem c hc0 hc).map 1))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      = (μ.prod μ) {p : ℝ × ℝ | crossDist c p.1 p.2 ≤ δ} := by
    rw [Measure.map_prod_map μ μ hm0 hm1, Measure.map_apply (hm0.prodMap hm1) hset]
    refine measure_congr (hbox.mono fun p hp => ?_)
    simp only [Set.mem_preimage, Prod.map_fst, Prod.map_snd, Set.mem_ofPred_eq,
      pairSystem_map_zero, pairSystem_map_one]
    have hZ := (crossDist_mem hc0.le hp.1 hp.2).1
    unfold crossDist at hZ
    have hrw : |1/2 * p.1 - (c * p.2 + (1 - c))| = crossDist c p.1 p.2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      unfold crossDist; ring
    exact propext (by rw [hrw])
  -- the `(1,0)` term
  have h10 : ((μ.map ((pairSystem c hc0 hc).map 1)).prod
      (μ.map ((pairSystem c hc0 hc).map 0))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      = (μ.prod μ) {p : ℝ × ℝ | crossDist c p.1 p.2 ≤ δ} := by
    rw [Measure.map_prod_map μ μ hm1 hm0, Measure.map_apply (hm1.prodMap hm0) hset]
    conv_lhs => rw [← Measure.prod_swap, Measure.map_apply measurable_swap
        ((hm1.prodMap hm0) hset)]
    refine measure_congr (hbox.mono fun p hp => ?_)
    simp only [Set.mem_preimage, Prod.map_fst, Prod.map_snd, Set.mem_ofPred_eq,
      Prod.fst_swap, Prod.snd_swap, pairSystem_map_zero, pairSystem_map_one]
    have hZ := (crossDist_mem hc0.le hp.1 hp.2).1
    unfold crossDist at hZ
    have hrw : |c * p.2 + (1 - c) - 1/2 * p.1| = crossDist c p.1 p.2 := by
      rw [abs_of_nonneg (by linarith)]
      unfold crossDist; ring
    exact propext (by rw [hrw])
  classical
  unfold System.crossPhi
  simp only [Fin.sum_univ_two, Fin.isValue]
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) = False from by decide,
    show ((1 : Fin 2) = 0) = False from by decide, ite_false, zero_add, add_zero, h01, h10]
  rw [pairSystem_ratio_zero, pairSystem_ratio_one]
  ring

/-- The open set condition for the two-map system, from strong separation. -/
theorem pairSystem_openSetCondition {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ}
    (hK : (pairSystem c hc0 hc).IsAttractor K) : (pairSystem c hc0 hc).OpenSetCondition :=
  ((pairSystem_stronglySeparated hc0 hc hK.2.2.1).strongOpenSetCondition _ hK).openSetCondition _

/-- The renewal mean of the two-map system is `m = 2^{-s} log 2 + c^s log(1/c)`. -/
theorem pairSystem_renewalMean {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (s : ℝ) :
    (pairSystem c hc0 hc).renewalMean s
      = (1/2 : ℝ) ^ s * Real.log 2 + c ^ s * Real.log c⁻¹ := by
  simp only [System.renewalMean, System.logRatio, Fin.sum_univ_two, pairSystem_ratio_zero,
    pairSystem_ratio_one]
  norm_num

/-- `eq:two-contraction-forcing-transform` at `ξ = 0`: `∫ z = 2pq M_c(s)/s`.  By Tonelli,
`∫ e^{sw} ℙ(Z_c ≤ e^{-w}) dw = 𝔼 ∫_{-∞}^{-log Z_c} e^{sw} dw = 𝔼 Z_c^{-s}/s`. -/
theorem pairSystem_integral_renewalDefect {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ}
    {s : ℝ} (hs0 : 0 < s) {μ : Measure ℝ} (hμ : (pairSystem c hc0 hc).IsNatural K s μ) :
    ∫ w, (pairSystem c hc0 hc).renewalDefect s μ w
      = 2 * ((1/2 : ℝ) ^ s * c ^ s) * crossMoment c μ s / s := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  set ν := μ.prod μ with hν
  set Z : ℝ × ℝ → ℝ := fun p => crossDist c p.1 p.2 with hZ
  have hZc : Continuous Z := continuous_crossDist c
  have hZpos : ∀ᵐ p ∂ν, 1/2 - c ≤ Z p ∧ Z p ≤ 1 :=
    hbox.mono fun p hp => crossDist_mem hc0.le hp.1 hp.2
  have hbpos : (0:ℝ) < 1/2 - c := by linarith
  -- the defect through the cross term
  have hz : ∀ w, (pairSystem c hc0 hc).renewalDefect s μ w
      = 2 * ((1/2 : ℝ) ^ s * c ^ s) *
          (Real.exp (s * w) * (ν {p | Z p ≤ Real.exp (-w)}).toReal) := by
    intro w
    rw [renewalDefect_eq_crossPhi _ hμ, pairSystem_crossPhi hc0 hc hμ]
    ring
  -- the key identity, by Tonelli
  set f : ℝ → ℝ := fun w => Real.exp (s * w) * (ν {p | Z p ≤ Real.exp (-w)}).toReal with hf
  have hfnn : ∀ w, 0 ≤ f w := fun w => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  set A : Set (ℝ × (ℝ × ℝ)) := {q | Z q.2 ≤ Real.exp (-q.1)} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le (hZc.comp continuous_snd) (Real.continuous_exp.comp continuous_fst.neg)).measurableSet
  set F : ℝ × (ℝ × ℝ) → ℝ≥0∞ := A.indicator fun q => ENNReal.ofReal (Real.exp (s * q.1))
    with hF
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_fst))).indicator hAm
  have hleft : ∫⁻ w, ENNReal.ofReal (f w) = ∫⁻ w, ∫⁻ p, F (w, p) ∂ν := by
    refine lintegral_congr fun w => ?_
    have hsec : ∀ p, F (w, p) = {p | Z p ≤ Real.exp (-w)}.indicator
        (fun _ => ENNReal.ofReal (Real.exp (s * w))) p := by
      intro p
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [hsec]
    rw [lintegral_indicator_const ((isClosed_le hZc continuous_const).measurableSet),
      hf, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hright : ∫⁻ p, ∫⁻ w, F (w, p) ∂volume ∂ν
      = ∫⁻ p, ENNReal.ofReal (Z p ^ (-s) / s) ∂ν := by
    refine lintegral_congr_ae (hZpos.mono fun p hp => ?_)
    have hZp : 0 < Z p := lt_of_lt_of_le hbpos hp.1
    have hsec : ∀ w, F (w, p) = (Iic (-Real.log (Z p))).indicator
        (fun w => ENNReal.ofReal (Real.exp (s * w))) w := by
      intro w
      simp only [hF, hA, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
      congr 1
      exact propext (by rw [le_neg, ← Real.log_le_iff_le_exp hZp, le_neg])
    simp only [hsec]
    rw [lintegral_indicator measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hs0 _)
        (Eventually.of_forall fun w => (Real.exp_pos _).le),
      integral_exp_mul_Iic hs0, Real.rpow_def_of_pos hZp]
    congr 2
    ring_nf
  have hswap : ∫⁻ w, ∫⁻ p, F (w, p) ∂ν = ∫⁻ p, ∫⁻ w, F (w, p) ∂volume ∂ν :=
    lintegral_lintegral_swap hFm.aemeasurable
  -- integrability and the passage back to Bochner integrals
  have hMint : Integrable (fun p => Z p ^ (-s) / s) ν := by
    refine Integrable.of_bound ((hZc.measurable.pow_const _).div_const _).aestronglyMeasurable
      ((1/2 - c) ^ (-s) / s) (hZpos.mono fun p hp => ?_)
    have hZp : 0 < Z p := lt_of_lt_of_le hbpos hp.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hZp.le _) hs0.le)]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hbpos hp.1 (by linarith))
      hs0.le
  have hkey : ∫ w, f w = crossMoment c μ s / s := by
    have hlin : ∫⁻ w, ENNReal.ofReal (f w) = ENNReal.ofReal (crossMoment c μ s / s) := by
      rw [hleft, hswap, hright, crossMoment, ← integral_div,
        ofReal_integral_eq_lintegral_ofReal hMint
          (hZpos.mono fun p hp => div_nonneg (Real.rpow_nonneg
            (lt_of_lt_of_le hbpos hp.1).le _) hs0.le)]
    have hfm : AEStronglyMeasurable f volume := by
      refine ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul ?_).aestronglyMeasurable
      have hmono : Antitone fun w : ℝ => (ν {p | Z p ≤ Real.exp (-w)}).toReal := by
        intro w w' hww'
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun p hp => ?_)
        exact le_trans hp (Real.exp_le_exp.2 (by linarith))
      exact hmono.measurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfnn) hfm, hlin,
      ENNReal.toReal_ofReal]
    have hM : 0 ≤ crossMoment c μ s := integral_nonneg_of_ae (hZpos.mono fun p hp =>
      Real.rpow_nonneg (lt_of_lt_of_le hbpos hp.1).le _)
    exact div_nonneg hM hs0.le
  simp only [hz]
  rw [integral_const_mul, hkey]
  ring

/-- `∫₀^∞ φ = 2^{-s} Γ(1-s)`: the multiplier `eq:gamma-multiplier` at `k = 0`. -/
theorem integral_kern_eq_Gamma {s : ℝ} (hs1 : s < 1) :
    ∫ η in Ioi (0:ℝ), kern s η = (2:ℝ) ^ (-s) * Real.Gamma (1 - s) := by
  have h := multInt_eq_gammaMult hs1 1 0
  simp only [multInt, gammaMult, freq, Int.cast_zero, mul_zero, zero_div, neg_zero,
    Complex.cpow_zero, mul_one, add_zero] at h
  have h1 : (((∫ η in Ioi (0:ℝ), kern s η) : ℝ) : ℂ) = ∫ η in Ioi (0:ℝ), (kern s η : ℂ) :=
    integral_ofReal.symm
  rw [← h1] at h
  have h2 : (2:ℂ) ^ (-(s:ℂ)) * Complex.Gamma (1 - (s:ℂ))
      = (((2:ℝ) ^ (-s) * Real.Gamma (1 - s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (by norm_num), ← Complex.Gamma_ofReal]
    push_cast
    ring_nf
  exact_mod_cast h.trans h2

/-- `eq:two-contraction-mean`: the closed form `2pq 2^{-s} Γ(1-s) M_c(s)/(sm)` of the mean
`H̄(c)`, with `p = 2^{-s}`, `q = c^s` and `m = p log 2 + q log(1/c)`. -/
def twoContractionMean (c s : ℝ) (μ : Measure ℝ) : ℝ :=
  2 * ((1/2 : ℝ) ^ s * c ^ s) * ((2:ℝ) ^ (-s) * Real.Gamma (1 - s)) * crossMoment c μ s /
    (s * ((1/2 : ℝ) ^ s * Real.log 2 + c ^ s * Real.log c⁻¹))

/-- **`eq:two-contraction-mean`.**  For the natural measure of the two-map system at its
dimension, the Cesàro means of `H_{μ_c}^s` converge to `twoContractionMean c s μ`, in the
lattice and the non-lattice case alike. -/
theorem pairSystem_tendsto_avg_H {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hdim : (pairSystem c hc0 hc).IsDimension s)
    {μ : Measure ℝ} (hμ : (pairSystem c hc0 hc).IsNatural K s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, H s μ t) atTop
      (𝓝 (twoContractionMean c s μ)) := by
  have h := hμ.tendsto_avg_H _ hs0 hs1 (pairSystem_openSetCondition hc0 hc hμ.attractor) hdim
  convert h using 2
  rw [integral_kern_eq_Gamma hs1, pairSystem_integral_renewalDefect hc0 hc hs0 hμ,
    pairSystem_renewalMean, twoContractionMean]
  field_simp

/-- **`eq:two-contraction-constant`.**  In the non-lattice case the expected profile of
the natural measure itself converges, to the closed form `twoContractionMean c s μ`:
`thm:non-lattice-limit` gives `G → (∫ z)/m`, and dominated convergence in
`eq:h-definition` multiplies by `∫ φ = 2^{-s} Γ(1-s)`. -/
theorem pairSystem_tendsto_H_nonLattice {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ}
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hdim : (pairSystem c hc0 hc).IsDimension s)
    {μ : Measure ℝ} (hμ : (pairSystem c hc0 hc).IsNatural K s μ)
    (hna : (pairSystem c hc0 hc).NonArithmetic) :
    Tendsto (H s μ) atTop (𝓝 (twoContractionMean c s μ)) := by
  have := hμ.isProbabilityMeasure
  have hosc := pairSystem_openSetCondition hc0 hc hμ.attractor
  obtain ⟨A, hA⟩ := hosc.exists_isFrostman _ hs0.le hμ
  obtain ⟨hCpos, hC⟩ := non_lattice_limit _ hs0 hs1
    (hosc.strongOpenSetCondition _ hμ.attractor) hdim hna hμ
  have h := (profile_asymptotics_nonLattice hs0 hs1 hA hCpos hC).2
  convert h using 2
  rw [twoContractionMean, integral_kern_eq_Gamma hs1,
    pairSystem_integral_renewalDefect hc0 hc hs0 hμ, pairSystem_renewalMean]
  field_simp

end

end BrownianImages
