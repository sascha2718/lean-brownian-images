/-
`thm:homogeneous-nonconstancy` for every `0 < λ < 1/2`.

The proof follows the first-difference argument in the paper.  It identifies the source
of the homogeneous renewal equation with a weighted tail of the logarithmic cross-law,
periodises that source, and shows that a constant eventual profile would force the
cross-law, and hence the signed difference law near zero, to have an `O(δ)` interval
bound.  Constancy also makes `Φ(δ)` live on the `δ^s` scale; since `s < 1`, the two bounds
are incompatible.
-/
import BrownianImages.PairDifference
import BrownianImages.AhlforsRegular
import BrownianImages.Smoothing
import BrownianImages.Profile

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

namespace HomogeneousNonconstancy

open PairDifference

variable {K : Set ℝ} {μ : Measure ℝ}

/-- The block `{u : λu + c ∈ T}`, the set of differences a pair of maps of the
homogeneous system with shifts differing by `c` sends to `T`. -/
def homBlockSet (lam c : ℝ) (T : Set ℝ) : Set ℝ :=
  (fun u : ℝ => lam * u + c) ⁻¹' T

/-- A block of a measurable set is measurable. -/
theorem measurableSet_homBlockSet (lam c : ℝ) {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet (homBlockSet lam c T) :=
  (measurable_const.mul measurable_id |>.add measurable_const) hT

/-- Both maps of the homogeneous system contract by `λ`. -/
theorem homogeneous_ratio {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) (i : Fin 2) :
    (homogeneousSystem lam hlam0 hlam).ratio i = lam := rfl

/-- The first map of the homogeneous system has shift `0`. -/
theorem homogeneous_shift_zero {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    (homogeneousSystem lam hlam0 hlam).shift 0 = 0 := by
  simp [homogeneousSystem]

/-- The second map of the homogeneous system has shift `1 - λ`. -/
theorem homogeneous_shift_one {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    (homogeneousSystem lam hlam0 hlam).shift 1 = 1 - lam := by
  simp [homogeneousSystem]

/-- The weight `λ^s` of each map at the similarity dimension is `1/2`. -/
theorem ofReal_homogeneous_weight {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    ENNReal.ofReal (lam ^ homogeneousDim lam) = 2⁻¹ := by
  rw [rpow_homogeneousDim hlam0 hlam, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- One map applied to the first coordinate: Hutchinson's identity in the second
coordinate splits the section integral into the two blocks of `T`. -/
theorem lintegral_homogeneous_map_decomp {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    {T : Set ℝ} (hT : MeasurableSet T) (i : Fin 2) :
    ∫⁻ x, μ {y : ℝ | (homogeneousSystem lam hlam0 hlam).map i x - y ∈ T} ∂μ
      = 2⁻¹ * pairDiff μ (homBlockSet lam
          ((homogeneousSystem lam hlam0 hlam).shift i) T)
        + 2⁻¹ * pairDiff μ (homBlockSet lam
          ((homogeneousSystem lam hlam0 hlam).shift i - (1 - lam)) T) := by
  haveI := hA.isProbabilityMeasure
  have hstep : ∀ x : ℝ, μ {y : ℝ | (homogeneousSystem lam hlam0 hlam).map i x - y ∈ T}
      = 2⁻¹ * μ {y : ℝ | x - y ∈ homBlockSet lam
          ((homogeneousSystem lam hlam0 hlam).shift i) T}
        + 2⁻¹ * μ {y : ℝ | x - y ∈ homBlockSet lam
          ((homogeneousSystem lam hlam0 hlam).shift i - (1 - lam)) T} := by
    intro x
    have hmeas : MeasurableSet {y : ℝ |
        (homogeneousSystem lam hlam0 hlam).map i x - y ∈ T} :=
      (measurable_const.sub measurable_id) hT
    have hj : ∀ j : Fin 2, (homogeneousSystem lam hlam0 hlam).map j ⁻¹'
          {y : ℝ | (homogeneousSystem lam hlam0 hlam).map i x - y ∈ T}
        = {y : ℝ | x - y ∈ homBlockSet lam
          ((homogeneousSystem lam hlam0 hlam).shift i -
            (homogeneousSystem lam hlam0 hlam).shift j) T} := by
      intro j
      ext y
      have hval : (homogeneousSystem lam hlam0 hlam).map i x -
          (homogeneousSystem lam hlam0 hlam).map j y = lam * (x - y) +
            ((homogeneousSystem lam hlam0 hlam).shift i -
              (homogeneousSystem lam hlam0 hlam).shift j) := by
        simp only [System.map]
        change lam * x + _ - (lam * y + _) = _
        ring
      simp only [Set.mem_preimage, Set.mem_setOf_eq, homBlockSet, hval]
    rw [hA.measure_eq_sum (homogeneousSystem lam hlam0 hlam) hmeas,
      Fin.sum_univ_two, hj 0, hj 1]
    rw [homogeneous_ratio hlam0 hlam 0, homogeneous_ratio hlam0 hlam 1,
      ofReal_homogeneous_weight hlam0 hlam]
    simp only [homogeneous_shift_zero, homogeneous_shift_one, sub_zero]
  have hm : ∀ c : ℝ, Measurable fun x : ℝ => μ {y : ℝ | x - y ∈ homBlockSet lam c T} :=
    fun c => measurable_section (measurableSet_homBlockSet lam c hT) μ
  rw [lintegral_congr hstep,
    lintegral_add_left ((hm _).const_mul _),
    lintegral_const_mul _ (hm _), lintegral_const_mul _ (hm _),
    ← pairDiff_eq_lintegral μ (measurableSet_homBlockSet _ _ hT),
    ← pairDiff_eq_lintegral μ (measurableSet_homBlockSet _ _ hT)]

/-- The four-block decomposition of the difference mass under the homogeneous system,
the engine of `thm:homogeneous-nonconstancy`. -/
theorem pairDiff_homogeneous_decomp {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    {T : Set ℝ} (hT : MeasurableSet T) :
    pairDiff μ T = 4⁻¹ *
      (pairDiff μ (homBlockSet lam 0 T)
        + pairDiff μ (homBlockSet lam (-(1 - lam)) T)
        + pairDiff μ (homBlockSet lam (1 - lam) T)
        + pairDiff μ (homBlockSet lam 0 T)) := by
  haveI := hA.isProbabilityMeasure
  have h4 : (4:ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  rw [pairDiff_eq_lintegral μ hT,
    hA.lintegral_eq_sum (homogeneousSystem lam hlam0 hlam) (measurable_section hT μ),
    Fin.sum_univ_two, lintegral_homogeneous_map_decomp hlam0 hlam hA hT 0,
    lintegral_homogeneous_map_decomp hlam0 hlam hA hT 1]
  rw [homogeneous_ratio hlam0 hlam 0, homogeneous_ratio hlam0 hlam 1,
    ofReal_homogeneous_weight hlam0 hlam]
  simp only [homogeneous_shift_zero, homogeneous_shift_one, zero_sub, sub_self]
  rw [h4]
  ring

/-- The cross term of `thm:renewal-recursion` for the homogeneous system: the
pair-distance distribution of two points in different first-level pieces. -/
noncomputable def crossCDF (lam : ℝ) (μ : Measure ℝ) (δ : ℝ) : ℝ :=
  (pairDiff μ (homBlockSet lam (1 - lam) (Set.Icc (-δ) δ))).toReal

/-- `thm:renewal-recursion` for the homogeneous system as a first-difference recursion:
`Φ(δ) = ½ Φ(δ/λ) + ½ Φ_cross(δ)`. -/
theorem phi_first_difference_recursion {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (δ : ℝ) :
    Phi μ δ = 1/2 * Phi μ (δ / lam) + 1/2 * crossCDF lam μ δ := by
  haveI := hA.isProbabilityMeasure
  have hdiag : homBlockSet lam 0 (Set.Icc (-δ) δ) = Set.Icc (-(δ / lam)) (δ / lam) := by
    ext u
    simp only [homBlockSet, Set.mem_preimage, Set.mem_Icc, add_zero]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor
    · rw [← neg_div]
      rw [div_le_iff₀ hlam0]
      nlinarith
    · rw [le_div_iff₀ hlam0]
      nlinarith
    · rw [← neg_div] at hlo
      rw [div_le_iff₀ hlam0] at hlo
      nlinarith
    · rw [le_div_iff₀ hlam0] at hhi
      nlinarith
  have hcross : pairDiff μ (homBlockSet lam (-(1 - lam)) (Set.Icc (-δ) δ))
      = pairDiff μ (homBlockSet lam (1 - lam) (Set.Icc (-δ) δ)) := by
    rw [pairDiff_neg μ (measurableSet_homBlockSet _ _ measurableSet_Icc)]
    congr 1
    ext u
    simp only [Set.mem_preimage, homBlockSet, Set.mem_Icc]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  have hdecomp := pairDiff_homogeneous_decomp hlam0 hlam hA
    (measurableSet_Icc (a := -δ) (b := δ))
  rw [hdiag, hcross] at hdecomp
  have hreal := congrArg ENNReal.toReal hdecomp
  have hfin : ∀ T : Set ℝ, pairDiff μ T ≠ ⊤ := pairDiff_ne_top
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hreal
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩) (hfin _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) (hfin _),
    ENNReal.toReal_add (hfin _) (hfin _)] at hreal
  rw [phi_eq_pairDiff, phi_eq_pairDiff, crossCDF]
  linarith

/-- The logarithmic cross-law: the law of `-log(1 - λ + λ(X - Y))` under `μ × μ`, under
which the cross term becomes a tail mass. -/
noncomputable def crossLogLaw (lam : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => -Real.log (1 - lam + lam * (p.1 - p.2))) (μ.prod μ)

/-- The logarithmic cross map is measurable. -/
theorem measurable_crossLogMap (lam : ℝ) :
    Measurable (fun p : ℝ × ℝ => -Real.log (1 - lam + lam * (p.1 - p.2))) := by
  fun_prop

/-- The logarithmic cross-law of a probability measure is a probability measure. -/
instance crossLogLaw.isProbabilityMeasure (lam : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (crossLogLaw lam μ) := by
  unfold crossLogLaw
  exact Measure.isProbabilityMeasure_map (measurable_crossLogMap lam).aemeasurable

/-- The cross term at `δ = e^{-w}` is the tail mass of `[w, ∞)` under the logarithmic
cross-law. -/
theorem crossCDF_eq_crossLogLaw_Ici {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (w : ℝ) :
    crossCDF lam μ (Real.exp (-w)) = (crossLogLaw lam μ (Set.Ici w)).toReal := by
  haveI := hA.isProbabilityMeasure
  rw [crossLogLaw, Measure.map_apply (measurable_crossLogMap lam) measurableSet_Ici]
  unfold crossCDF pairDiff
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hsquare : ∀ᵐ p ∂μ.prod μ, p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    rw [ae_iff]
    exact prod_compl_square hA.support_Icc
  filter_upwards [hsquare] with p hp
  let z : ℝ := 1 - lam + lam * (p.1 - p.2)
  have hz0 : 0 < z := by
    dsimp [z]
    nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  apply propext
  simp only [homBlockSet, Set.mem_preimage, Set.mem_Icc]
  change (-Real.exp (-w) ≤ lam * (p.1 - p.2) + (1 - lam) ∧
      lam * (p.1 - p.2) + (1 - lam) ≤ Real.exp (-w)) ↔
        w ≤ -Real.log (1 - lam + lam * (p.1 - p.2))
  have hzexpr : lam * (p.1 - p.2) + (1 - lam) = z := by
    dsimp [z]
    ring
  rw [hzexpr]
  change (-Real.exp (-w) ≤ z ∧ z ≤ Real.exp (-w)) ↔ w ≤ -Real.log z
  constructor
  · rintro ⟨-, hze⟩
    have hlog := Real.log_le_log hz0 hze
    rw [Real.log_exp] at hlog
    linarith
  · intro hlog
    have hlog' : Real.log z ≤ -w := by linarith
    have hze := Real.exp_le_exp.mpr hlog'
    rw [Real.exp_log hz0] at hze
    exact ⟨by linarith [Real.exp_pos (-w), hz0], hze⟩

/-- The source of the homogeneous renewal equation: the one-step defect `G(w) - G(w -
log(1/λ))` of the shift identity. -/
noncomputable def homSource (lam : ℝ) (μ : Measure ℝ) (w : ℝ) : ℝ :=
  G (homogeneousDim lam) μ w -
    G (homogeneousDim lam) μ (w - Real.log lam⁻¹)

/-- The source is a weighted tail of the logarithmic cross-law: `½ e^{sw}` times the
mass of `[w, ∞)`. -/
theorem homSource_eq {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (w : ℝ) :
    homSource lam μ w = 1/2 * Real.exp (homogeneousDim lam * w) *
      (crossLogLaw lam μ (Set.Ici w)).toReal := by
  let s := homogeneousDim lam
  let p := Real.log lam⁻¹
  have hδ : Real.exp (-(w - p)) = Real.exp (-w) / lam := by
    rw [show -(w - p) = -w + p by ring, Real.exp_add]
    dsimp [p]
    rw [Real.exp_log (inv_pos.mpr hlam0),
      div_eq_mul_inv]
  have he : Real.exp (s * (w - p)) = Real.exp (s * w) * (1/2) := by
    have hrpow : lam ^ s = 1/2 := rpow_homogeneousDim hlam0 hlam
    rw [show s * (w - p) = s * w - s * p by ring, Real.exp_sub]
    have hep : Real.exp (s * p) = (lam ^ s)⁻¹ := by
      dsimp [p]
      rw [Real.rpow_def_of_pos hlam0, Real.log_inv]
      rw [show s * -Real.log lam = -(Real.log lam * s) by ring, Real.exp_neg]
    rw [hep, hrpow]
    ring
  have hrec := phi_first_difference_recursion hlam0 hlam hA (Real.exp (-w))
  rw [crossCDF_eq_crossLogLaw_Ici hlam0 hlam hA w] at hrec
  unfold homSource G
  change Real.exp (s * w) * Phi μ (Real.exp (-w)) -
      Real.exp (s * (w - p)) * Phi μ (Real.exp (-(w - p))) = _
  rw [hδ, he, hrec]
  ring

/-- `eq:g-definition`: the normalised profile vanishes at `-∞`, since `Φ ≤ 1` and
`e^{sw} → 0`. -/
theorem tendsto_G_atBot_zero {s : ℝ} (hs : 0 < s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] : Tendsto (G s μ) atBot (𝓝 0) := by
  have hexp : Tendsto (fun w : ℝ => Real.exp (s * w)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot hs tendsto_id)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
    (fun w => G_nonneg w) (fun w => G_le_exp hs.le le_rfl)

/-- The sources telescope: the sum of the one-step defects along `n` shifts is `G(w) -
G(w - n log(1/λ))`. -/
theorem sum_range_homSource (lam : ℝ) (μ : Measure ℝ) (w : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, homSource lam μ (w - i * Real.log lam⁻¹) =
      G (homogeneousDim lam) μ w -
        G (homogeneousDim lam) μ (w - n * Real.log lam⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [homSource]
      have harg : w - (n : ℝ) * Real.log lam⁻¹ - Real.log lam⁻¹ =
          w - (n + 1 : ℕ) * Real.log lam⁻¹ := by
        push_cast
        ring
      rw [harg]
      ring

/-- The profile is the sum of its sources along the shifts, by telescoping and
`tendsto_G_atBot_zero`. -/
theorem hasSum_homSource {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (w : ℝ) :
    HasSum (fun n : ℕ => homSource lam μ (w - n * Real.log lam⁻¹))
      (G (homogeneousDim lam) μ w) := by
  haveI := hA.isProbabilityMeasure
  have hp := log_inv_pos hlam0 hlam
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · rw [show (fun n : ℕ => ∑ i ∈ Finset.range n,
        homSource lam μ (w - i * Real.log lam⁻¹)) =
        (fun n : ℕ => G (homogeneousDim lam) μ w -
          G (homogeneousDim lam) μ (w - n * Real.log lam⁻¹)) by
      funext n
      exact sum_range_homSource lam μ w n]
    have harg : Tendsto (fun n : ℕ => w - n * Real.log lam⁻¹) atTop atBot := by
      rw [tendsto_atBot]
      intro b
      have hev := (tendsto_natCast_atTop_atTop.const_mul_atTop hp)
        (eventually_ge_atTop (w - b))
      filter_upwards [hev] with n hn
      change w - b ≤ Real.log lam⁻¹ * (n : ℝ) at hn
      nlinarith
    simpa using tendsto_const_nhds.sub
      ((tendsto_G_atBot_zero (homogeneousDim_pos hlam0 hlam)).comp harg)
  · intro n
    rw [homSource_eq hlam0 hlam hA]
    positivity

/-- A tail of the logarithmic cross-law splits at any later point. -/
theorem crossLogLaw_Ici_eq_add_Ico (lam : ℝ) (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b) :
    crossLogLaw lam μ (Set.Ici a) = crossLogLaw lam μ (Set.Ico a b) +
      crossLogLaw lam μ (Set.Ici b) := by
  have hd : Disjoint (Set.Ico a b) (Set.Ici b) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hy) hx.2
  rw [← measure_union hd measurableSet_Ici,
    Set.Ico_union_Ici_eq_Ici hab]

/-- The source at `a` minus the discounted source at `b` is the weighted mass of `[a,
b)` under the logarithmic cross-law. -/
theorem homSource_interval {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    {a b : ℝ} (hab : a ≤ b) :
    homSource lam μ a - Real.exp (-(homogeneousDim lam * (b - a))) * homSource lam μ b =
      1/2 * Real.exp (homogeneousDim lam * a) *
        (crossLogLaw lam μ (Set.Ico a b)).toReal := by
  haveI := hA.isProbabilityMeasure
  have hfin (T : Set ℝ) : crossLogLaw lam μ T ≠ ⊤ := measure_ne_top _ _
  have htail := crossLogLaw_Ici_eq_add_Ico lam μ hab
  have htailReal := congrArg ENNReal.toReal htail
  rw [ENNReal.toReal_add (hfin _) (hfin _)] at htailReal
  rw [homSource_eq hlam0 hlam hA, homSource_eq hlam0 hlam hA]
  rw [show Real.exp (-(homogeneousDim lam * (b - a))) *
      (1 / 2 * Real.exp (homogeneousDim lam * b) *
        (crossLogLaw lam μ (Set.Ici b)).toReal) =
      1 / 2 * Real.exp (homogeneousDim lam * a) *
        (crossLogLaw lam μ (Set.Ici b)).toReal by
    calc
      _ = 1 / 2 * (Real.exp (-(homogeneousDim lam * (b - a))) *
          Real.exp (homogeneousDim lam * b)) *
          (crossLogLaw lam μ (Set.Ici b)).toReal := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring_nf]
  rw [htailReal]
  ring

/-- If the profile is eventually constant, the logarithmic cross-law gives every
interval `[a, b)` in `[0, ∞)` mass `O(b - a)`. -/
theorem crossLogLaw_Ico_le_of_eventually_constant {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    {w₀ C : ℝ}
    (hconst : ∀ w, w₀ ≤ w → G (homogeneousDim lam) μ w = C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (crossLogLaw lam μ (Set.Ico a b)).toReal ≤ 2 * C * homogeneousDim lam * (b - a) := by
  haveI := hA.isProbabilityMeasure
  let s := homogeneousDim lam
  let p := Real.log lam⁻¹
  have hs0 : 0 < s := homogeneousDim_pos hlam0 hlam
  have hp : 0 < p := log_inv_pos hlam0 hlam
  obtain ⟨m, hm⟩ := exists_nat_gt ((w₀ - a) / p)
  have ham : w₀ ≤ a + m * p := by
    have := (div_lt_iff₀ hp).1 hm
    linarith
  have hbm : w₀ ≤ b + m * p := by linarith
  let e : ℝ := Real.exp (-(s * (b - a)))
  have hsa : HasSum (fun n : ℕ => homSource lam μ (a + m * p - n * p)) C := by
    have h := hasSum_homSource hlam0 hlam hA (a + m * p)
    change HasSum (fun n : ℕ => homSource lam μ (a + m * p - n * p))
      (G s μ (a + m * p)) at h
    rwa [hconst _ ham] at h
  have hsb : HasSum (fun n : ℕ => homSource lam μ (b + m * p - n * p)) C := by
    have h := hasSum_homSource hlam0 hlam hA (b + m * p)
    change HasSum (fun n : ℕ => homSource lam μ (b + m * p - n * p))
      (G s μ (b + m * p)) at h
    rwa [hconst _ hbm] at h
  have hd : HasSum (fun n : ℕ => homSource lam μ (a + m * p - n * p) -
      e * homSource lam μ (b + m * p - n * p)) (C - e * C) :=
    hsa.sub (hsb.mul_left e)
  have hnonneg : ∀ n : ℕ, 0 ≤ homSource lam μ (a + m * p - n * p) -
      e * homSource lam μ (b + m * p - n * p) := by
    intro n
    have hi := homSource_interval hlam0 hlam hA
      (a := a + m * p - n * p) (b := b + m * p - n * p) (by linarith)
    change homSource lam μ (a + m * p - n * p) -
      Real.exp (-(s * ((b + m * p - n * p) - (a + m * p - n * p)))) *
        homSource lam μ (b + m * p - n * p) = _ at hi
    have heq : (b + m * p - n * p) - (a + m * p - n * p) = b - a := by ring
    rw [heq] at hi
    change _ - e * _ = _ at hi
    rw [hi]
    positivity
  have hle := hd.summable.le_tsum m (fun j _ => hnonneg j)
  rw [hd.tsum_eq] at hle
  have hindexa : a + (m : ℝ) * p - (m : ℝ) * p = a := by ring
  have hindexb : b + (m : ℝ) * p - (m : ℝ) * p = b := by ring
  rw [hindexa, hindexb, homSource_interval hlam0 hlam hA hab.le] at hle
  change 1/2 * Real.exp (s * a) * (crossLogLaw lam μ (Set.Ico a b)).toReal ≤
    C - Real.exp (-(s * (b - a))) * C at hle
  have hepos : 0 < Real.exp (s * a) := Real.exp_pos _
  have hmass : (crossLogLaw lam μ (Set.Ico a b)).toReal ≤
      (C - Real.exp (-(s * (b - a))) * C) / ((1/2) * Real.exp (s * a)) := by
    rw [le_div_iff₀ (by positivity : 0 < (1:ℝ)/2 * Real.exp (s * a))]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle
  have hexpLower : 1 ≤ Real.exp (s * a) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hs0.le ha)
  have hone : 1 - Real.exp (-(s * (b - a))) ≤ s * (b - a) := by
    linarith [Real.one_sub_le_exp_neg (s * (b - a))]
  have hC0 : 0 < C := by
    rw [← hconst w₀ le_rfl]
    exact G_pos _
  calc
    (crossLogLaw lam μ (Set.Ico a b)).toReal
        ≤ (C - Real.exp (-(s * (b - a))) * C) /
          ((1/2) * Real.exp (s * a)) := hmass
    _ = 2 * C * (1 - Real.exp (-(s * (b - a)))) / Real.exp (s * a) := by
      field_simp
    _ ≤ 2 * C * (s * (b - a)) / Real.exp (s * a) := by
      gcongr
    _ ≤ 2 * C * (s * (b - a)) := by
      rw [div_le_iff₀ hepos]
      have hnon : 0 ≤ 2 * C * (s * (b - a)) := by positivity
      nlinarith
    _ = 2 * C * s * (b - a) := by ring

/-- An atomless measure gives its difference law no atoms. -/
theorem pairDiff_singleton_zero [IsProbabilityMeasure μ]
    (hatom : ∀ x : ℝ, μ {x} = 0) (d : ℝ) : pairDiff μ {d} = 0 := by
  rw [pairDiff_eq_lintegral μ (measurableSet_singleton d)]
  rw [← lintegral_zero]
  apply lintegral_congr
  intro x
  have hset : {y : ℝ | x - y ∈ ({d} : Set ℝ)} = {x - d} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [hset, hatom]

/-- For an atomless `μ` the logarithmic cross-law has no atoms. -/
theorem crossLogLaw_singleton_zero {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (hatom : ∀ x : ℝ, μ {x} = 0) (t : ℝ) : crossLogLaw lam μ {t} = 0 := by
  haveI := hA.isProbabilityMeasure
  rw [crossLogLaw, Measure.map_apply (measurable_crossLogMap lam) (measurableSet_singleton t)]
  let d : ℝ := (Real.exp (-t) - (1 - lam)) / lam
  have hsquare : ∀ᵐ p ∂μ.prod μ, p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    rw [ae_iff]
    exact prod_compl_square hA.support_Icc
  calc
    (μ.prod μ) ((fun p : ℝ × ℝ => -Real.log (1 - lam + lam * (p.1 - p.2))) ⁻¹' {t})
        = (μ.prod μ) {p : ℝ × ℝ | p.1 - p.2 ∈ ({d} : Set ℝ)} := by
          apply measure_congr
          filter_upwards [hsquare] with p hp
          apply propext
          let z : ℝ := 1 - lam + lam * (p.1 - p.2)
          have hz0 : 0 < z := by
            dsimp [z]
            nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
          change -Real.log z = t ↔ p.1 - p.2 = d
          constructor
          · intro h
            have hzlog : Real.log z = -t := by linarith
            have hzexp := congrArg Real.exp hzlog
            rw [Real.exp_log hz0] at hzexp
            dsimp [d]
            rw [eq_div_iff hlam0.ne']
            dsimp [z] at hzexp
            linarith
          · intro h
            dsimp [d] at h
            rw [eq_div_iff hlam0.ne'] at h
            have hz : z = Real.exp (-t) := by
              dsimp [z]
              linarith
            rw [hz, Real.log_exp]
            ring
    _ = pairDiff μ {d} := rfl
    _ = 0 := pairDiff_singleton_zero hatom d

/-- For `δ` below the first-level gap, `Φ(δ)` is the mass of the interval `[-log(1 - λ +
λδ), -log(1 - λ - λδ)]` under the logarithmic cross-law. -/
theorem phi_eq_crossLogLaw_interval {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (hlower : 0 < 1 - lam - lam * δ) :
    Phi μ δ = (crossLogLaw lam μ
      (Set.Icc (-Real.log (1 - lam + lam * δ))
        (-Real.log (1 - lam - lam * δ)))).toReal := by
  haveI := hA.isProbabilityMeasure
  rw [Phi, crossLogLaw, Measure.map_apply (measurable_crossLogMap lam) measurableSet_Icc]
  apply congrArg ENNReal.toReal
  have hsquare : ∀ᵐ p ∂μ.prod μ, p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    rw [ae_iff]
    exact prod_compl_square hA.support_Icc
  apply measure_congr
  filter_upwards [hsquare] with p hp
  apply propext
  let z : ℝ := 1 - lam + lam * (p.1 - p.2)
  have hz0 : 0 < z := by
    dsimp [z]
    nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hupper : 0 < 1 - lam + lam * δ := by nlinarith
  change |p.1 - p.2| ≤ δ ↔
    -Real.log (1 - lam + lam * δ) ≤ -Real.log z ∧
      -Real.log z ≤ -Real.log (1 - lam - lam * δ)
  rw [abs_le]
  constructor
  · rintro ⟨hdlo, hdhi⟩
    have hzlo : 1 - lam - lam * δ ≤ z := by
      dsimp [z]
      nlinarith
    have hzhi : z ≤ 1 - lam + lam * δ := by
      dsimp [z]
      nlinarith
    have hlo := Real.log_le_log hlower hzlo
    have hhi := Real.log_le_log hz0 hzhi
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    have hloglo : Real.log z ≤ Real.log (1 - lam + lam * δ) := by linarith
    have hloghi : Real.log (1 - lam - lam * δ) ≤ Real.log z := by linarith
    have hzhi := Real.exp_le_exp.mpr hloglo
    have hzlo := Real.exp_le_exp.mpr hloghi
    rw [Real.exp_log hz0, Real.exp_log hupper] at hzhi
    rw [Real.exp_log hlower, Real.exp_log hz0] at hzlo
    dsimp [z] at hzlo hzhi
    constructor <;> nlinarith

/-- An eventually constant profile forces `Φ(δ) ≤ Mδ` for small `δ`, through
`phi_eq_crossLogLaw_interval` and `crossLogLaw_Ico_le_of_eventually_constant`. -/
theorem phi_linear_bound_of_eventually_constant {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (hatom : ∀ x : ℝ, μ {x} = 0)
    {w₀ C : ℝ} (hconst : ∀ w, w₀ ≤ w → G (homogeneousDim lam) μ w = C) :
    ∃ M > 0, ∀ δ : ℝ, 0 < δ → δ < min 1 ((1 - 2 * lam) / (2 * lam)) →
      Phi μ δ ≤ M * δ := by
  haveI := hA.isProbabilityMeasure
  let s := homogeneousDim lam
  have hs0 : 0 < s := homogeneousDim_pos hlam0 hlam
  have hC0 : 0 < C := by
    rw [← hconst w₀ le_rfl]
    exact G_pos _
  have hgap : 0 < 1 - 2 * lam := by linarith
  refine ⟨8 * C * s * lam / (1 - 2 * lam), by positivity, ?_⟩
  intro δ hδ0 hδsmall
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδsmall (min_le_left _ _))
  have hδgap : δ < (1 - 2 * lam) / (2 * lam) :=
    lt_of_lt_of_le hδsmall (min_le_right _ _)
  have hmul : 2 * lam * δ < 1 - 2 * lam :=
    by
      have := (lt_div_iff₀ (by positivity : 0 < 2 * lam)).1 hδgap
      nlinarith
  let a : ℝ := -Real.log (1 - lam + lam * δ)
  let b : ℝ := -Real.log (1 - lam - lam * δ)
  have hlower : 0 < 1 - lam - lam * δ := by nlinarith
  have hupper : 0 < 1 - lam + lam * δ := by nlinarith
  have hupperOne : 1 - lam + lam * δ ≤ 1 := by nlinarith
  have ha : 0 ≤ a := by
    dsimp [a]
    have := Real.log_nonpos hupper.le hupperOne
    linarith
  have hab : a < b := by
    dsimp [a, b]
    have harg : 1 - lam - lam * δ < 1 - lam + lam * δ := by nlinarith
    have := Real.strictMonoOn_log hlower hupper harg
    linarith
  have hphi := phi_eq_crossLogLaw_interval hlam0 hlam hA hδ0 hδ1 hlower
  have hatb := crossLogLaw_singleton_zero hlam0 hlam hA hatom b
  have hmeasure : crossLogLaw lam μ (Set.Icc a b) = crossLogLaw lam μ (Set.Ico a b) := by
    have hset : Set.Icc a b = Set.Ico a b ∪ {b} := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ico, Set.mem_singleton_iff]
      constructor
      · intro hx
        rcases lt_or_eq_of_le hx.2 with h | h
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr h
      · rintro (h | rfl)
        · exact ⟨h.1, h.2.le⟩
        · exact ⟨hab.le, le_rfl⟩
    rw [hset, measure_union (by
      rw [Set.disjoint_left]
      intro x hx hxb
      simp only [Set.mem_singleton_iff] at hxb
      exact (ne_of_lt hx.2) hxb) (measurableSet_singleton b), hatb, add_zero]
  have hτ := crossLogLaw_Ico_le_of_eventually_constant hlam0 hlam hA hconst ha hab
  have hlength : b - a ≤ 4 * lam * δ / (1 - 2 * lam) := by
    dsimp [a, b]
    have hlogeq : -Real.log (1 - lam - lam * δ) - -Real.log (1 - lam + lam * δ) =
        Real.log ((1 - lam + lam * δ) / (1 - lam - lam * δ)) := by
      rw [Real.log_div hupper.ne' hlower.ne']
      ring
    rw [hlogeq]
    calc
      Real.log ((1 - lam + lam * δ) / (1 - lam - lam * δ))
          ≤ (1 - lam + lam * δ) / (1 - lam - lam * δ) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hupper hlower)
      _ = 2 * lam * δ / (1 - lam - lam * δ) := by field_simp; ring
      _ ≤ 2 * lam * δ / ((1 - 2 * lam) / 2) := by
        gcongr
        nlinarith
      _ = 4 * lam * δ / (1 - 2 * lam) := by field_simp; ring
  rw [hphi, hmeasure]
  calc
    (crossLogLaw lam μ (Set.Ico a b)).toReal ≤ 2 * C * s * (b - a) := hτ
    _ ≤ 2 * C * s * (4 * lam * δ / (1 - 2 * lam)) := by gcongr
    _ = (8 * C * s * lam / (1 - 2 * lam)) * δ := by ring

/-- `thm:homogeneous-nonconstancy`, the core: the profile of the homogeneous natural
measure is not eventually constant, since constancy would put `Φ(δ)` both on the `δ`
scale and on the `δ^s` scale with `s < 1`. -/
theorem homogeneous_G_not_eventually_constant {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ) :
    ¬ ∃ w₀ C : ℝ, ∀ w, w₀ ≤ w → G (homogeneousDim lam) μ w = C := by
  haveI := hA.isProbabilityMeasure
  let s := homogeneousDim lam
  have hs0 : 0 < s := homogeneousDim_pos hlam0 hlam
  have hs1 : s < 1 := homogeneousDim_lt_one hlam0 hlam
  obtain ⟨A, hFrost⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0
    (homogeneousSystem_stronglySeparated hlam0 hlam hA.attractor.2.2.1) hA
  intro h
  obtain ⟨w₀, C, hconst⟩ := h
  have hC0 : 0 < C := by
    rw [← hconst w₀ le_rfl]
    exact G_pos _
  obtain ⟨M, hM0, hM⟩ := phi_linear_bound_of_eventually_constant hlam0 hlam hA
    (fun x => hFrost.measure_singleton hs0 x) hconst
  have hsmall : ∀ᶠ v : ℝ in atTop,
      Real.exp (-v) < min 1 ((1 - 2 * lam) / (2 * lam)) := by
    have hbound : 0 < min 1 ((1 - 2 * lam) / (2 * lam)) := by
      exact lt_min one_pos (div_pos (by linarith) (by positivity))
    have ht : Tendsto (fun v : ℝ => Real.exp (-v)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    exact ht.eventually (Iio_mem_nhds hbound)
  have hupper : ∀ᶠ v : ℝ in atTop,
      C ≤ M * Real.exp ((s - 1) * v) := by
    filter_upwards [eventually_ge_atTop w₀, hsmall] with v hv hδsmall
    have hphi := hM (Real.exp (-v)) (Real.exp_pos _) hδsmall
    have hG := hconst v hv
    change Real.exp (s * v) * Phi μ (Real.exp (-v)) = C at hG
    calc
      C = Real.exp (s * v) * Phi μ (Real.exp (-v)) := hG.symm
      _ ≤ Real.exp (s * v) * (M * Real.exp (-v)) := by gcongr
      _ = M * Real.exp ((s - 1) * v) := by
        calc
          _ = M * (Real.exp (s * v) * Real.exp (-v)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
  have hzero : Tendsto (fun v : ℝ => M * Real.exp ((s - 1) * v)) atTop (𝓝 0) := by
    have hneg : s - 1 < 0 := by linarith
    have ht : Tendsto (fun v : ℝ => (s - 1) * v) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg hneg).2 tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp ht).const_mul M
  have hlt : ∀ᶠ v : ℝ in atTop, M * Real.exp ((s - 1) * v) < C :=
    hzero.eventually (Iio_mem_nhds hC0)
  obtain ⟨v, hv, hv'⟩ := (hupper.and hlt).exists
  exact (not_lt_of_ge hv) hv'

/-- `eq:g-recursion` for the homogeneous system: above `log(1/(1 - 2λ))` the profile
satisfies the shift identity `G(w) = G(w - log(1/λ))`. -/
theorem homogeneous_g_period {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ) :
    ∀ w, Real.log (1 - 2 * lam)⁻¹ < w →
      G (homogeneousDim lam) μ w =
        G (homogeneousDim lam) μ (w - Real.log lam⁻¹) := by
  have hsep := homogeneousSystem_stronglySeparated hlam0 hlam hA.attractor.2.2.1
  intro w hw
  have h := g_recursion (homogeneousSystem lam hlam0 hlam) hsep hA (w := w) hw
  rw [Fin.sum_univ_two] at h
  have hlr : ∀ i : Fin 2, (homogeneousSystem lam hlam0 hlam).logRatio i =
      Real.log lam⁻¹ := by
    intro i
    rfl
  rw [hlr 0, hlr 1, homogeneous_ratio hlam0 hlam 0,
    homogeneous_ratio hlam0 hlam 1, rpow_homogeneousDim hlam0 hlam] at h
  linarith

/-- `thm:homogeneous-nonconstancy`: on every tail the profile of the homogeneous natural
measure takes two distinct values.  The endpoint `audit_cantor_nonconstant`. -/
theorem homogeneous_G_nonconstant_on_tail {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (w₀ : ℝ) :
    ∃ x, w₀ ≤ x ∧ ∃ y, w₀ ≤ y ∧
      G (homogeneousDim lam) μ x ≠ G (homogeneousDim lam) μ y := by
  by_contra h
  push Not at h
  apply homogeneous_G_not_eventually_constant hlam0 hlam hA
  exact ⟨w₀, G (homogeneousDim lam) μ w₀, fun w hw => h w hw w₀ le_rfl⟩

end HomogeneousNonconstancy

/-- The point `w_A = log(1/(1-2λ)) + log(1/λ)` from which the paper fixes the
periodic extension of the homogeneous profile. -/
noncomputable def homogeneousStart (lam : ℝ) : ℝ :=
  Real.log (1 - 2 * lam)⁻¹ + Real.log lam⁻¹

/-- `thm:homogeneous-nonconstancy` together with the periodic extension used after it.
For every `0 < λ < 1/2`, the tail of `G_A` extends to a continuous, positive,
non-constant function of period `log(1/λ)`. -/
theorem exists_homogeneous_periodic_profile {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {K : Set ℝ} {μ : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
      (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μ w) ∧
      (∀ x, 0 < g x) ∧ ∃ x y, g x ≠ g y := by
  haveI := hA.isProbabilityMeasure
  have hs0 := homogeneousDim_pos hlam0 hlam
  have hp := log_inv_pos hlam0 hlam
  obtain ⟨A, hFrost⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0
    (homogeneousSystem_stronglySeparated hlam0 hlam hA.attractor.2.2.1) hA
  have hshift : ∀ w, homogeneousStart lam + Real.log lam⁻¹ ≤ w →
      G (homogeneousDim lam) μ w =
        G (homogeneousDim lam) μ (w - Real.log lam⁻¹) := by
    intro w hw
    apply HomogeneousNonconstancy.homogeneous_g_period hlam0 hlam hA w
    unfold homogeneousStart at hw
    linarith
  obtain ⟨g, hgcont, hgper, hgeq⟩ :=
    exists_periodic_extension_of_shift (p := Real.log lam⁻¹)
      (a := homogeneousStart lam) hp
      (continuous_G hs0 hFrost).continuousOn hshift
  refine ⟨g, hgcont, hgper, hgeq, fun x => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt ((homogeneousStart lam - x) / Real.log lam⁻¹)
    have hnx : homogeneousStart lam ≤ x + n * Real.log lam⁻¹ := by
      have := (div_lt_iff₀ hp).1 hn
      linarith
    have hshiftg : g (x + n * Real.log lam⁻¹) = g x := hgper.nat_mul n x
    rw [← hshiftg, hgeq _ hnx]
    exact G_pos _
  · obtain ⟨x, hx, y, hy, hne⟩ :=
      HomogeneousNonconstancy.homogeneous_G_nonconstant_on_tail hlam0 hlam hA
        (homogeneousStart lam)
    exact ⟨x, y, by rw [hgeq _ hx, hgeq _ hy]; exact hne⟩

end BrownianImages
