/-
`sec:renewal`: the theory of strongly separated self-similar systems on `[0,1]` and
their natural `s`-dimensional measures.

The objects themselves, `System` with `IsAttractor`, `StronglySeparated`,
`IsDimension`, `IsNatural`, `logRatio` and `NonArithmetic`, together with
`homogeneousSystem`, `homogeneousDim`, `pairSystem` and `pairRatio`, live in
`Defs.lean`, where `Challenge.lean` can copy them.  This module carries what the
proofs need beyond the definitions:

* `measurable_map`, `StronglySeparated.mono`, the `IsNatural` extractors and
  `logRatio_pos`.
* `log_two_pos`, `log_inv_pos`, `homogeneousDim_pos`, `homogeneousDim_lt_one`,
  `rpow_homogeneousDim`: the similarity dimension `log 2 / log(1/λ)` of the homogeneous
  system and its elementary bounds.
* `homogeneousSystem_isDimension`, `homogeneousSystem_stronglySeparated`,
  `pairSystem_isDimension`, `pairSystem_stronglySeparated`: the similarity dimensions
  and separation gaps of the two systems of the application.
* `pairRatio_rpow`, `pairRatio_pos`, `pairRatio_lt_half`: the ratio `c` of
  `eq:c-definition` solves `c^s = 1 - 2^{-s}` and lies in `(0, 1/2)`.
* `pairSystem_nonArithmetic_iff`: `eq:non-lattice` is exactly non-arithmeticity of
  the paired system.
* `renewalConv`, `renewalDefect`, `renewalMean`: the renewal data `ϑ * G`, `z = G - ϑ * G`
  and `m = ∑ p_i a_i` of `thm:non-lattice-limit`.
-/
import BrownianImages.Periodic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace BrownianImages

/-- `log 2 > 0`, the positivity every dimension computation of `sec:renewal` starts from. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

open MeasureTheory

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- Every map of a system is measurable, being affine. -/
theorem measurable_map (i : ι) : Measurable (S.map i) := by
  unfold map; fun_prop

/-- Separation on a larger set restricts. -/
theorem StronglySeparated.mono {K K' : Set ℝ} {ρ : ℝ} (h : K' ⊆ K)
    (hs : S.StronglySeparated K ρ) : S.StronglySeparated K' ρ :=
  ⟨hs.1, fun i j hij x hx y hy => hs.2 i j hij x (h hx) y (h hy)⟩

/-- The natural measure is a probability measure; `IsNatural` already carries this, and
this is the extractor that lets a consumer avoid a separate instance binder. -/
theorem IsNatural.isProbabilityMeasure {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (h : S.IsNatural K s μ) : IsProbabilityMeasure μ := h.isProbability

/-- The natural measure sits on `[0,1]`, as every statement of the paper assumes. -/
theorem IsNatural.support_Icc {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (h : S.IsNatural K s μ) : μ (Set.Icc (0:ℝ) 1)ᶜ = 0 :=
  measure_mono_null (Set.compl_subset_compl.mpr h.attractor.2.2.1) h.support

/-- The log-ratios `a_i = log(1/r_i)` are positive. -/
theorem logRatio_pos (i : ι) : 0 < S.logRatio i := by
  rw [logRatio, Real.log_inv, neg_pos]
  exact Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)

/-- The renewal convolution `ϑ * g` of `thm:non-lattice-limit`, where
`ϑ = ∑ p_i δ_{a_i}`: `(ϑ * g)(w) = ∑ p_i g(w - a_i)`. -/
noncomputable def renewalConv (s : ℝ) (g : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∑ i, S.ratio i ^ s * g (w - S.logRatio i)

/-- The renewal defect `z = G - ϑ * G` of `thm:non-lattice-limit`, whose integral gives
the limit constant `eq:g-non-lattice-limit`. -/
noncomputable def renewalDefect (s : ℝ) (μ : Measure ℝ) (w : ℝ) : ℝ :=
  G s μ w - S.renewalConv s (G s μ) w

/-- The renewal measure `ϑ = ∑ p_i δ_{a_i}` of `thm:non-lattice-limit`, whose atoms are
the log-ratios and whose weights are `p_i = r_i^s`.  This is the measure the key renewal
theorem is applied to. -/
noncomputable def renewalLaw (s : ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac (S.logRatio i)

/-- The renewal law evaluated on a set: the weighted sum of the Dirac masses at the
log-ratios. -/
theorem renewalLaw_apply (s : ℝ) (A : Set ℝ) :
    S.renewalLaw s A = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * (Measure.dirac (S.logRatio i)) A := by
  simp [renewalLaw]

/-- The weights sum to one exactly when `s` is the similarity dimension. -/
theorem sum_ofReal_ratio_rpow {s : ℝ} (hdim : S.IsDimension s) :
    ∑ i, ENNReal.ofReal (S.ratio i ^ s) = 1 := by
  have hnn : ∀ i ∈ Finset.univ, (0:ℝ) ≤ S.ratio i ^ s := fun i _ =>
    (Real.rpow_pos_of_pos (S.ratio_pos i) s).le
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, hdim, ENNReal.ofReal_one]

/-- `ϑ` is a probability measure exactly when the weights are the `s`-powers of the
ratios and `s` is the similarity dimension. -/
theorem isProbabilityMeasure_renewalLaw {s : ℝ} (hdim : S.IsDimension s) :
    IsProbabilityMeasure (S.renewalLaw s) := by
  constructor
  rw [renewalLaw_apply S s Set.univ]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, mul_one]
  exact S.sum_ofReal_ratio_rpow hdim

/-- The renewal mean `m = ∑ p_i a_i` of `thm:non-lattice-limit`. -/
noncomputable def renewalMean (s : ℝ) : ℝ := ∑ i, S.ratio i ^ s * S.logRatio i

/-- The renewal mean is the first moment of `ϑ`: this is the `∫ x ∂μ` the key renewal
theorem divides by. -/
theorem integral_id_renewalLaw (s : ℝ) :
    ∫ x, x ∂(S.renewalLaw s) = S.renewalMean s := by
  have hint : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun x : ℝ => x)
      (ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac (S.logRatio i)) := by
    intro i _
    refine (integrable_smul_measure ?_ (by simp)).mpr (integrable_dirac (by simp))
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (S.ratio_pos i) s
  rw [renewalMean, renewalLaw, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le]

/-- The renewal mean `m = ∑ p_i a_i` is positive. -/
theorem renewalMean_pos (s : ℝ) [Nonempty ι] :
    0 < S.renewalMean s := by
  refine Finset.sum_pos' (fun i _ => ?_) ?_
  · exact mul_nonneg (Real.rpow_pos_of_pos (S.ratio_pos i) s).le (S.logRatio_pos i).le
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨i, Finset.mem_univ i, ?_⟩
  have : (0:ℝ) < S.ratio i ^ s := Real.rpow_pos_of_pos (S.ratio_pos i) s
  have := S.logRatio_pos i
  positivity

end System

/-! ### The systems of the application -/

/-! ### The homogeneous system -/

theorem log_inv_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    0 < Real.log lam⁻¹ := by
  rw [Real.log_pos_iff (inv_nonneg.mpr hlam0.le), one_lt_inv₀ hlam0]
  linarith

/-- The homogeneous dimension `log 2 / log(1/λ)` is positive. -/
theorem homogeneousDim_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    0 < homogeneousDim lam :=
  div_pos log_two_pos (log_inv_pos hlam0 hlam)

/-- The homogeneous dimension is below `1`, since `λ < 1/2`. -/
theorem homogeneousDim_lt_one {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    homogeneousDim lam < 1 := by
  have hlog := log_inv_pos hlam0 hlam
  rw [homogeneousDim, div_lt_one hlog]
  have h2inv : (2 : ℝ) < lam⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hlam0]
    nlinarith
  exact Real.strictMonoOn_log (by norm_num) (inv_pos.mpr hlam0) h2inv

/-- The identity `λ^s = 1/2` for `s = log 2 / log (1/λ)`. -/
theorem rpow_homogeneousDim {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    lam ^ homogeneousDim lam = 1/2 := by
  have hlog := log_inv_pos hlam0 hlam
  have hloglam : Real.log lam = -Real.log lam⁻¹ := by
    rw [Real.log_inv]
    ring
  rw [homogeneousDim, Real.rpow_def_of_pos hlam0, hloglam]
  rw [show (-Real.log lam⁻¹) * (Real.log 2 / Real.log lam⁻¹) = -Real.log 2 by
    rw [div_eq_mul_inv]
    calc
      -Real.log lam⁻¹ * (Real.log 2 * (Real.log lam⁻¹)⁻¹)
          = -Real.log 2 * (Real.log lam⁻¹ * (Real.log lam⁻¹)⁻¹) := by ring
      _ = -Real.log 2 := by rw [mul_inv_cancel₀ hlog.ne', mul_one]]
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- `sec:renewal`: `log 2 / log(1/λ)` is the similarity dimension of the homogeneous
system. -/
theorem homogeneousSystem_isDimension {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    (homogeneousSystem lam hlam0 hlam).IsDimension (homogeneousDim lam) := by
  simp only [System.IsDimension, homogeneousSystem, Fin.sum_univ_two,
    rpow_homogeneousDim hlam0 hlam]
  norm_num

/-- The first map of the homogeneous system is `x ↦ λx`. -/
theorem homogeneousSystem_map_zero {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (x : ℝ) : (homogeneousSystem lam hlam0 hlam).map 0 x = lam * x := by
  simp [System.map, homogeneousSystem]

/-- The second map of the homogeneous system is `x ↦ λx + 1 - λ`. -/
theorem homogeneousSystem_map_one {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (x : ℝ) : (homogeneousSystem lam hlam0 hlam).map 1 x = lam * x + (1 - lam) := by
  simp [System.map, homogeneousSystem]

/-- The homogeneous system is strongly separated, with first-level gap `1 - 2λ`. -/
theorem homogeneousSystem_stronglySeparated {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {K : Set ℝ} (hK : K ⊆ Set.Icc 0 1) :
    (homogeneousSystem lam hlam0 hlam).StronglySeparated K (1 - 2 * lam) := by
  refine ⟨by linarith, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hx0, hx1⟩ := hK hx
  obtain ⟨hy0, hy1⟩ := hK hy
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [homogeneousSystem_map_zero, homogeneousSystem_map_one, le_abs]
    right
    nlinarith
  · rw [homogeneousSystem_map_one, homogeneousSystem_map_zero, le_abs]
    left
    nlinarith

/-- `(1/2)^s = 2^{-s}`. -/
theorem half_rpow (s : ℝ) : ((1:ℝ)/2) ^ s = (2:ℝ) ^ (-s) := by
  rw [one_div, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]

/-! ### The paired system -/

theorem one_sub_two_rpow_pos {s : ℝ} (hs : 0 < s) : 0 < 1 - (2:ℝ) ^ (-s) := by
  have h : (2:ℝ) ^ (-s) < 2 ^ (0:ℝ) :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by linarith)
  simpa using h

/-- `eq:c-definition`: the ratio `c` is positive. -/
theorem pairRatio_pos {s : ℝ} (hs : 0 < s) : 0 < pairRatio s :=
  Real.rpow_pos_of_pos (one_sub_two_rpow_pos hs) _

/-- `eq:c-definition`: `c^s = 1 - 2^{-s}`. -/
theorem pairRatio_rpow {s : ℝ} (hs : 0 < s) : (pairRatio s) ^ s = 1 - (2:ℝ) ^ (-s) := by
  rw [pairRatio, ← Real.rpow_mul (one_sub_two_rpow_pos hs).le, inv_mul_cancel₀ hs.ne',
    Real.rpow_one]

/-- `c < 1/2`, the disjointness of the first-level hulls noted in `sec:renewal`: `s < 1`
gives `1 - 2^{-s} < 2^{-s}`. -/
theorem pairRatio_lt_half {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : pairRatio s < 1/2 := by
  have hhalf : (1:ℝ)/2 < (2:ℝ) ^ (-s) := by
    have h : (2:ℝ) ^ (-(1:ℝ)) < (2:ℝ) ^ (-s) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at h
  have hlt : (pairRatio s) ^ s < ((1:ℝ)/2) ^ s := by
    rw [pairRatio_rpow hs0, half_rpow]; linarith
  exact (Real.rpow_lt_rpow_iff (pairRatio_pos hs0).le (by norm_num) hs0).mp hlt

/-- The paired system has similarity dimension `s`: `2^{-s} + c^s = 1`. -/
theorem pairSystem_isDimension {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (pairSystem (pairRatio s) (pairRatio_pos hs0)
      (pairRatio_lt_half hs0 hs1)).IsDimension s := by
  simp only [System.IsDimension, pairSystem, Fin.sum_univ_two]
  norm_num
  rw [half_rpow, pairRatio_rpow hs0]
  ring

/-- The first map of the paired system is `x ↦ x/2`. -/
theorem pairSystem_map_zero {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (x : ℝ) :
    (pairSystem c hc0 hc).map 0 x = 1/2 * x := by
  simp [System.map, pairSystem]

/-- The second map of the paired system is `x ↦ cx + 1 - c`. -/
theorem pairSystem_map_one {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (x : ℝ) :
    (pairSystem c hc0 hc).map 1 x = c * x + (1 - c) := by
  simp [System.map, pairSystem]

/-- The log-ratios of the paired system are `log(1/c)` and `log 2`. -/
theorem pairSystem_range_logRatio {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    Set.range (pairSystem c hc0 hc).logRatio = {Real.log c⁻¹, Real.log 2} := by
  have h0 : (pairSystem c hc0 hc).logRatio 0 = Real.log 2 := by
    simp [System.logRatio, pairSystem]
  have h1 : (pairSystem c hc0 hc).logRatio 1 = Real.log c⁻¹ := by
    simp [System.logRatio, pairSystem]
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, h0, h1, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h.symm

/-- `eq:non-lattice` is exactly non-arithmeticity of the paired system: the additive
group generated by `log 2` and `log(1/c)` is dense precisely when their ratio is
irrational. -/
theorem pairSystem_nonArithmetic_iff {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (pairSystem (pairRatio s) (pairRatio_pos hs0)
        (pairRatio_lt_half hs0 hs1)).NonArithmetic
      ↔ Irrational (Real.log (pairRatio s)⁻¹ / Real.log 2) := by
  rw [System.NonArithmetic,
    pairSystem_range_logRatio (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)]
  exact dense_addSubgroupClosure_pair_iff

/-- The paired system is strongly separated with gap `1/2 - c` on every subset of
`[0,1]`: the first-level hulls are `[0,1/2]` and `[1-c,1]`. -/
theorem pairSystem_stronglySeparated {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ}
    (hK : K ⊆ Set.Icc 0 1) : (pairSystem c hc0 hc).StronglySeparated K (1/2 - c) := by
  refine ⟨by linarith, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hx0, hx1⟩ := hK hx
  obtain ⟨hy0, hy1⟩ := hK hy
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pairSystem_map_zero, pairSystem_map_one, le_abs]; right; nlinarith
  · rw [pairSystem_map_one, pairSystem_map_zero, le_abs]; left; nlinarith

end BrownianImages
