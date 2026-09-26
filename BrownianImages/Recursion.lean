/-
`thm:renewal-recursion` of `sec:renewal`: the self-similar recursion of the pair-distance
profile, `eq:phi-recursion` and `eq:g-recursion`, with the cross term `Φ_×` of pairs
with different first-level addresses.

The computation runs on the Fubini form `Φ(δ) = (∫⁻ x, μ(B̄(x,δ)) ∂μ).toReal` of
`phi_prod_eq`, never on `μ × μ` directly: Mathlib's `Measure.prod_sum` is stated for
`Measure.sum` over a countable index, not for the `Finset` sums that
`IsNatural.selfSimilar` produces.  Writing Hutchinson's identity in both coordinates
turns `μ × μ` into the double sum `∑_{i,j} p_i p_j (μ_i × μ_j)`; the diagonal blocks
rescale to `Φ(δ/r_i)`, and the off-diagonal blocks are `Φ_×`.

* `measurable_measure_closedBall`: `x ↦ μ(B̄(x,δ))` is measurable.
* `System.IsNatural.measure_eq_sum`, `.lintegral_eq_sum`: Hutchinson's identity on a set
  and on a lower integral.
* `System.crossPhi`: `Φ_×(δ) = ∑_{i ≠ j} p_i p_j (μ_i × μ_j){|x - y| ≤ δ}`.
* `System.IsNatural.prod_eq_double_sum`, `.prod_map_diag`: the double-sum decomposition
  of `μ × μ` and the rescaling of a diagonal block.
* `phi_recursion_cross`, `g_recursion_cross`: `eq:phi-recursion` and `eq:g-recursion`
  at every scale, with the cross term.
* `crossPhi_nonneg`, `crossPhi_eq_zero_of_stronglySeparated`: the cross term is
  non-negative, and vanishes below the gap of a strongly separated system.
* `phi_recursion`, `g_recursion`: the two recursions below the separation gap, which
  the homogeneous analysis of `sec:renewal` uses.
-/
import BrownianImages.SelfSimilar
import BrownianImages.Frostman

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

/-- The ball-mass function is measurable: it is the section function of the
pair-distance set. -/
theorem measurable_measure_closedBall (μ : Measure ℝ) [SFinite μ] (δ : ℝ) :
    Measurable fun x : ℝ => μ (Metric.closedBall x δ) := by
  have h : Measurable fun x : ℝ => μ (Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}) :=
    measurable_measure_prodMk_left (measurableSet_phiSet δ)
  simpa only [mk_preimage_phiSet] using h

variable {ι : Type*} [Fintype ι]

/-- Hutchinson's identity read on a measurable set. -/
theorem System.IsNatural.measure_eq_sum (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {A : Set ℝ} (hA : MeasurableSet A) :
    μ A = ∑ j, ENNReal.ofReal (S.ratio j ^ s) * μ (S.map j ⁻¹' A) := by
  conv_lhs => rw [hμ.selfSimilar]
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (S.measurable_map j) hA]

/-- Hutchinson's identity read on a lower integral. -/
theorem System.IsNatural.lintegral_eq_sum (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * ∫⁻ x, f (S.map i x) ∂μ := by
  conv_lhs => rw [hμ.selfSimilar]
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_smul_measure, lintegral_map hf (S.measurable_map i), smul_eq_mul]

/-- Below the separation gap only the diagonal block survives: a ball of radius `δ < ρ`
centred in the piece `S_i K` meets no other piece, and pulling it back through `S_i`
rescales the radius by `r_i`. -/
theorem System.StronglySeparated.measure_closedBall_map (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {δ : ℝ} (hδ : δ < ρ) (i : ι) {x : ℝ} (hx : x ∈ K) :
    μ (Metric.closedBall (S.map i x) δ)
      = ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i)) := by
  have hr := S.ratio_pos i
  rw [hμ.measure_eq_sum S measurableSet_closedBall, Finset.sum_eq_single i]
  · congr 2
    ext y
    simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, System.map]
    rw [show S.ratio i * y + S.shift i - (S.ratio i * x + S.shift i) = (y - x) * S.ratio i from
        by ring, abs_mul, abs_of_pos hr, le_div_iff₀ hr]
  · intro j _ hji
    have hsub : S.map j ⁻¹' Metric.closedBall (S.map i x) δ ⊆ Kᶜ := by
      intro y hy hyK
      have h1 : |S.map j y - S.map i x| ≤ δ := by
        simpa only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] using hy
      have h2 : ρ ≤ |S.map i x - S.map j y| := hsep.2 i j (Ne.symm hji) x hx y hyK
      rw [abs_sub_comm] at h1
      linarith
    rw [measure_mono_null hsub hμ.support, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Below the separation gap an off-diagonal block carries no mass: a ball of radius
`δ < ρ` centred in the piece `S_i K` meets no other piece. -/
theorem System.StronglySeparated.measure_preimage_closedBall_eq_zero (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {δ : ℝ} (hδ : δ < ρ) {i j : ι} (hij : i ≠ j) {x : ℝ}
    (hx : x ∈ K) : μ (S.map j ⁻¹' Metric.closedBall (S.map i x) δ) = 0 := by
  refine measure_mono_null ?_ hμ.support
  intro y hy hyK
  have h1 : |S.map j y - S.map i x| ≤ δ := by
    simpa only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] using hy
  have h2 : ρ ≤ |S.map i x - S.map j y| := hsep.2 i j hij x hx y hyK
  rw [abs_sub_comm] at h1
  linarith

/-- The pull-back of a ball centred in a piece through the same piece is a ball of the
rescaled radius. -/
theorem System.preimage_closedBall_map_self (S : System ι) (i : ι) (x δ : ℝ) :
    S.map i ⁻¹' Metric.closedBall (S.map i x) δ = Metric.closedBall x (δ / S.ratio i) := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, System.map]
  rw [show S.ratio i * y + S.shift i - (S.ratio i * x + S.shift i) = (y - x) * S.ratio i from
      by ring, abs_mul, abs_of_pos (S.ratio_pos i), le_div_iff₀ (S.ratio_pos i)]

/-! ### The cross term -/

open scoped Classical in
/-- `sec:renewal`: the cross term
`Φ_×(δ) = ∑_{i ≠ j} p_i p_j (μ_i × μ_j){(x,y) : |x - y| ≤ δ}` of pairs with different
first-level addresses, where `μ_i = (S_i)_* μ` and `p_i = r_i^s`. -/
noncomputable def System.crossPhi (S : System ι) (s : ℝ) (μ : Measure ℝ) (δ : ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else
    S.ratio i ^ s * S.ratio j ^ s *
      (((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal

/-- The cross term is non-negative. -/
theorem System.crossPhi_nonneg (S : System ι) (s : ℝ) (μ : Measure ℝ) (δ : ℝ) :
    0 ≤ S.crossPhi s μ δ := by
  classical
  unfold System.crossPhi
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (S.ratio_pos i).le s)
      (Real.rpow_nonneg (S.ratio_pos j).le s)) ENNReal.toReal_nonneg

/-- The mass of an off-diagonal block in Fubini form. -/
theorem System.IsNatural.prod_map_apply_eq (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (i j : ι) (δ : ℝ) :
    ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      = ∫⁻ x, (μ.map (S.map j)) (Metric.closedBall (S.map i x) δ) ∂μ := by
  have := hμ.isProbabilityMeasure
  rw [Measure.prod_apply (measurableSet_phiSet δ)]
  simp only [mk_preimage_phiSet]
  exact lintegral_map (measurable_measure_closedBall _ δ) (S.measurable_map i)

/-- A diagonal block rescales: `(μ_i × μ_i){|x - y| ≤ δ} = (μ × μ){|x - y| ≤ δ/r_i}`. -/
theorem System.IsNatural.prod_map_diag (S : System ι) {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) (i : ι) (δ : ℝ) :
    ((μ.map (S.map i)).prod (μ.map (S.map i))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      = (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ / S.ratio i} := by
  have := hμ.isProbabilityMeasure
  rw [hμ.prod_map_apply_eq S i i δ, phi_prod_eq]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply (S.measurable_map i) measurableSet_closedBall,
    S.preimage_closedBall_map_self]

/-- Hutchinson's identity in both coordinates: `μ × μ = ∑_{i,j} p_i p_j (μ_i × μ_j)`,
read on the pair-distance set. -/
theorem System.IsNatural.prod_eq_double_sum (S : System ι) {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (δ : ℝ) :
    (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}
      = ∑ i, ∑ j, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio j ^ s) *
          ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
  have := hμ.isProbabilityMeasure
  rw [phi_prod_eq, hμ.lintegral_eq_sum S (measurable_measure_closedBall μ δ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmeas : ∀ j : ι, Measurable fun x =>
      (μ.map (S.map j)) (Metric.closedBall (S.map i x) δ) := fun j =>
    (measurable_measure_closedBall (μ.map (S.map j)) δ).comp (S.measurable_map i)
  have hpt : ∀ x, μ (Metric.closedBall (S.map i x) δ)
      = ∑ j, ENNReal.ofReal (S.ratio j ^ s) *
          (μ.map (S.map j)) (Metric.closedBall (S.map i x) δ) := by
    intro x
    rw [hμ.measure_eq_sum S measurableSet_closedBall]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Measure.map_apply (S.measurable_map j) measurableSet_closedBall]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun j _ => (hmeas j).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_const_mul _ (hmeas j), hμ.prod_map_apply_eq S i j δ, mul_assoc]

/-- **`thm:renewal-recursion`, `eq:phi-recursion`.**  At every scale,
`Φ(δ) = ∑ r_i^{2s} Φ(δ/r_i) + Φ_×(δ)`: the diagonal blocks of the self-similar
decomposition rescale, and the other blocks form the cross term. -/
theorem phi_recursion_cross {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (δ : ℝ) :
    Phi μ δ = ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) + S.crossPhi s μ δ := by
  classical
  have := hμ.isProbabilityMeasure
  have hne : ∀ i j : ι, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio j ^ s) *
      ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≠ ⊤ :=
    fun i j => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hterm : ∀ i j : ι,
      (ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio j ^ s) *
        ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal
      = (if i = j then S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) else 0) +
        (if i = j then 0 else S.ratio i ^ s * S.ratio j ^ s *
          (((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal) := by
    intro i j
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le,
      ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos j) s).le]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, add_zero, hμ.prod_map_diag S i δ, Phi, two_mul,
        Real.rpow_add (S.ratio_pos i)]
    · rw [if_neg hij, if_neg hij, zero_add]
  rw [Phi, hμ.prod_eq_double_sum S δ, ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr
    fun j _ => hne i j]
  simp_rw [ENNReal.toReal_sum fun j _ => hne _ j, hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- **`thm:renewal-recursion`, `eq:g-recursion`.**  At every `w`,
`G(w) = ∑ p_i G(w - a_i) + e^{sw} Φ_×(e^{-w})`. -/
theorem g_recursion_cross {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (w : ℝ) :
    G s μ w = ∑ i, S.ratio i ^ s * G s μ (w - S.logRatio i)
      + Real.exp (s * w) * S.crossPhi s μ (Real.exp (-w)) := by
  rw [G, phi_recursion_cross S hμ (Real.exp (-w)), mul_add, Finset.mul_sum]
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

/-- **`thm:renewal-recursion`, the separated case.**  If the first-level pieces have
mutual distance at least `ρ`, the cross term vanishes for `0 < δ < ρ`. -/
theorem crossPhi_eq_zero_of_stronglySeparated {ι : Type*} [Fintype ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ}
    (hμ : S.IsNatural K s μ) {δ : ℝ} (hδ : δ < ρ) : S.crossPhi s μ δ = 0 := by
  classical
  have := hμ.isProbabilityMeasure
  unfold System.crossPhi
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · rfl
  have hK : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]; exact hμ.support
  have hzero : ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} = 0 := by
    rw [hμ.prod_map_apply_eq S i j δ]
    have hae : (fun x => (μ.map (S.map j)) (Metric.closedBall (S.map i x) δ))
        =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hK] with x hx
      rw [Measure.map_apply (S.measurable_map j) measurableSet_closedBall]
      exact hsep.measure_preimage_closedBall_eq_zero S hμ hδ hij hx
    rw [lintegral_congr_ae hae, lintegral_zero]
  rw [hzero, ENNReal.toReal_zero, mul_zero]

/-- `thm:renewal-recursion`, `eq:phi-recursion`.  Below the separation gap the
pair-distance distribution satisfies the self-similar recursion. -/
theorem phi_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < ρ) :
    Phi μ δ = ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) := by
  have := hμ.isProbabilityMeasure
  have _hδ0 := hδ0  -- the positivity of `δ` is not needed below
  have hphi : ∀ δ' : ℝ, Phi μ δ' = (∫⁻ x, μ (Metric.closedBall x δ') ∂μ).toReal := by
    intro δ'; rw [Phi, phi_prod_eq]
  have hfin : ∀ δ' : ℝ, (∫⁻ x, μ (Metric.closedBall x δ') ∂μ) ≠ ⊤ := by
    intro δ'
    rw [← phi_prod_eq]
    exact measure_ne_top _ _
  have hK : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]; exact hμ.support
  have hkey : (∫⁻ x, μ (Metric.closedBall x δ) ∂μ)
      = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
          ∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ := by
    rw [hμ.lintegral_eq_sum S (measurable_measure_closedBall μ δ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hae : ∀ᵐ x ∂μ, μ (Metric.closedBall (S.map i x) δ)
        = ENNReal.ofReal (S.ratio i ^ s) * μ (Metric.closedBall x (δ / S.ratio i)) := by
      filter_upwards [hK] with x hx
      exact hsep.measure_closedBall_map S hμ hδ i hx
    rw [lintegral_congr_ae hae,
      lintegral_const_mul _ (measurable_measure_closedBall μ (δ / S.ratio i)), mul_assoc]
  have hne : ∀ i : ι, ENNReal.ofReal (S.ratio i ^ s) * ENNReal.ofReal (S.ratio i ^ s) *
      (∫⁻ x, μ (Metric.closedBall x (δ / S.ratio i)) ∂μ) ≠ ⊤ :=
    fun i => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hfin _)
  rw [hphi δ, hkey, ENNReal.toReal_sum (fun i _ => hne i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hphi (δ / S.ratio i), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le]
  congr 1
  rw [← Real.rpow_add (S.ratio_pos i), two_mul]

/-- `thm:renewal-recursion`, `eq:g-recursion`.  The recursion in the normalised
profile. -/
theorem g_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {w : ℝ} (hw : Real.log ρ⁻¹ < w) :
    G s μ w = ∑ i, S.ratio i ^ s * G s μ (w - S.logRatio i) := by
  have hρ : 0 < ρ := hsep.1
  have hδ0 : 0 < Real.exp (-w) := Real.exp_pos _
  have hδ : Real.exp (-w) < ρ := by
    rw [Real.log_inv] at hw
    calc Real.exp (-w) < Real.exp (Real.log ρ) := Real.exp_lt_exp.mpr (by linarith)
      _ = ρ := Real.exp_log hρ
  rw [G, phi_recursion S hsep hμ hδ0 hδ, Finset.mul_sum]
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

end BrownianImages
