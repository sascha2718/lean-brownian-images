/-
`sec:renewal`: the theory of strongly separated self-similar IFSs on `[0,1]` and
their natural `s`-dimensional measures.

The objects themselves, `System` with `IsAttractor`, `StronglySeparated`,
`IsDimension`, `IsNatural`, `logRatio` and `NonArithmetic`, together with
`homogeneousSystem`, `homogeneousDim`, `pairSystem` and `pairRatio`, live in
`Defs.lean`, where `Challenge.lean` can copy them.  This module carries what the
proofs need beyond the definitions:

* `abs_sub_of_affine`, `image_Icc_of_affine`, `image_Ioo_of_affine`,
  `image_ball_of_affine`, `preimage_closedBall_of_affine`: the elementary geometry of an
  affine map of the line with non-zero slope, shared by every composition of similarities.
* `measurable_map`, the `IsNatural` extractors and `logRatio_pos`.
* `abs_sign`, `map_sub`, `abs_map_sub`, `map_injective`, `inv`: the orientation of a
  similarity, its signed slope `ε_i r_i`, and its inverse.
* `left`, `map_image_unitInterval`: the left endpoint `ℓ_i = min(S_i(0), S_i(1))` of the
  first-level interval `S_i([0,1]) = [ℓ_i, ℓ_i + r_i]`.
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

/-! ### Affine maps of the line -/

section Affine

variable {f : ℝ → ℝ} {a : ℝ}

/-- An affine map of slope `a` scales distances by `|a|`. -/
theorem abs_sub_of_affine (hf : ∀ x y, f x - f y = a * (x - y)) (x y : ℝ) :
    |f x - f y| = |a| * |x - y| := by
  rw [hf, abs_mul]

/-- An affine map of non-zero slope is injective. -/
theorem injective_of_affine (hf : ∀ x y, f x - f y = a * (x - y)) (ha : a ≠ 0) :
    Function.Injective f := by
  intro x y hxy
  have h := hf x y
  rw [hxy, sub_self] at h
  rcases mul_eq_zero.mp h.symm with h0 | h0
  · exact absurd h0 ha
  · exact sub_eq_zero.mp h0

/-- The image of a closed interval under an affine map of non-zero slope. -/
theorem image_Icc_of_affine (hf : ∀ x y, f x - f y = a * (x - y)) (ha : a ≠ 0) {c d : ℝ}
    (hcd : c ≤ d) : f '' Set.Icc c d = Set.Icc (min (f c) (f d)) (max (f c) (f d)) := by
  have hfc : ∀ x, f x = a * (x - c) + f c := fun x => by linarith [hf x c]
  have hdc : f d - f c = a * (d - c) := hf d c
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hle : f d ≤ f c := by nlinarith
    rw [min_eq_right hle, max_eq_left hle]
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [hfc x]
      constructor <;> nlinarith
    · rintro ⟨hy0, hy1⟩
      refine ⟨c + (y - f c) / a, ⟨?_, ?_⟩, ?_⟩
      · have : 0 ≤ (y - f c) / a := div_nonneg_of_nonpos (by linarith) ha.le
        linarith
      · have : (y - f c) / a ≤ d - c := by
          rw [div_le_iff_of_neg ha]
          linarith
        linarith
      · rw [hfc]
        field_simp
        ring
  · have hle : f c ≤ f d := by nlinarith
    rw [min_eq_left hle, max_eq_right hle]
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [hfc x]
      constructor <;> nlinarith
    · rintro ⟨hy0, hy1⟩
      refine ⟨c + (y - f c) / a, ⟨?_, ?_⟩, ?_⟩
      · have : 0 ≤ (y - f c) / a := div_nonneg (by linarith) ha.le
        linarith
      · have : (y - f c) / a ≤ d - c := by
          rw [div_le_iff₀ ha]
          linarith
        linarith
      · rw [hfc]
        field_simp
        ring

/-- The image of an open interval under an affine map of non-zero slope. -/
theorem image_Ioo_of_affine (hf : ∀ x y, f x - f y = a * (x - y)) (ha : a ≠ 0) {c d : ℝ}
    (hcd : c ≤ d) : f '' Set.Ioo c d = Set.Ioo (min (f c) (f d)) (max (f c) (f d)) := by
  have hfc : ∀ x, f x = a * (x - c) + f c := fun x => by linarith [hf x c]
  have hdc : f d - f c = a * (d - c) := hf d c
  rcases hcd.lt_or_eq with hcd | rfl
  swap
  · simp
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hle : f d ≤ f c := by nlinarith
    rw [min_eq_right hle, max_eq_left hle]
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [hfc x]
      constructor <;> nlinarith
    · rintro ⟨hy0, hy1⟩
      refine ⟨c + (y - f c) / a, ⟨?_, ?_⟩, ?_⟩
      · have : 0 < (y - f c) / a := div_pos_of_neg_of_neg (by linarith) ha
        linarith
      · have : (y - f c) / a < d - c := by
          rw [div_lt_iff_of_neg ha]
          linarith
        linarith
      · rw [hfc]
        field_simp
        ring
  · have hle : f c ≤ f d := by nlinarith
    rw [min_eq_left hle, max_eq_right hle]
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [hfc x]
      constructor <;> nlinarith
    · rintro ⟨hy0, hy1⟩
      refine ⟨c + (y - f c) / a, ⟨?_, ?_⟩, ?_⟩
      · have : 0 < (y - f c) / a := div_pos (by linarith) ha
        linarith
      · have : (y - f c) / a < d - c := by
          rw [div_lt_iff₀ ha]
          linarith
        linarith
      · rw [hfc]
        field_simp
        ring

/-- The image of an open ball under an affine map of non-zero slope. -/
theorem image_ball_of_affine (hf : ∀ x y, f x - f y = a * (x - y)) (ha : a ≠ 0) (x ε : ℝ) :
    f '' Metric.ball x ε = Metric.ball (f x) (|a| * ε) := by
  rcases le_or_gt ε 0 with hε | hε
  · rw [Metric.ball_eq_empty.mpr hε, Set.image_empty, Metric.ball_eq_empty.mpr]
    exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg a) hε
  rw [Real.ball_eq_Ioo, Real.ball_eq_Ioo, image_Ioo_of_affine hf ha (by linarith)]
  have h1 := hf x (x - ε)
  have h2 := hf (x + ε) x
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · rw [abs_of_neg ha', min_eq_right (by nlinarith), max_eq_left (by nlinarith)]
    congr 1 <;> linarith
  · rw [abs_of_pos ha', min_eq_left (by nlinarith), max_eq_right (by nlinarith)]
    congr 1 <;> linarith

/-- The preimage of a closed ball centred at `f x` under an affine map of slope `a ≠ 0`
is the closed ball of radius `δ/|a|` at `x`. -/
theorem preimage_closedBall_of_affine (hf : ∀ x y, f x - f y = a * (x - y)) (ha : a ≠ 0)
    (x δ : ℝ) : f ⁻¹' Metric.closedBall (f x) δ = Metric.closedBall x (δ / |a|) := by
  have ha' : 0 < |a| := abs_pos.mpr ha
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, abs_sub_of_affine hf,
    le_div_iff₀ ha', mul_comm]

variable {σ ρ : ℝ}

/-- For an affine map of slope `σρ` with `σ = ±1` and `ρ > 0`, the smaller endpoint image
`min(f(0), f(1))` in closed form. -/
theorem min_eq_of_affine (hf : ∀ x y, f x - f y = σ * ρ * (x - y)) (hσ : σ = 1 ∨ σ = -1)
    (hρ : 0 < ρ) : min (f 0) (f 1) = f 0 + (σ - 1) / 2 * ρ := by
  have h := hf 1 0
  rcases hσ with rfl | rfl
  · rw [min_eq_left (by nlinarith)]
    ring
  · rw [min_eq_right (by nlinarith)]
    linarith

/-- The larger endpoint image `max(f(0), f(1))` in closed form. -/
theorem max_eq_of_affine (hf : ∀ x y, f x - f y = σ * ρ * (x - y)) (hσ : σ = 1 ∨ σ = -1)
    (hρ : 0 < ρ) : max (f 0) (f 1) = f 0 + (σ - 1) / 2 * ρ + ρ := by
  have h := hf 1 0
  rcases hσ with rfl | rfl
  · rw [max_eq_right (by nlinarith)]
    linarith
  · rw [max_eq_left (by nlinarith)]
    ring

/-- The image of `[0,1]` under an affine map of slope `σρ`, `σ = ±1`, `ρ > 0`, is the
interval of length `ρ` starting at `min(f(0), f(1))`. -/
theorem image_unitInterval_of_affine (hf : ∀ x y, f x - f y = σ * ρ * (x - y))
    (hσ : σ = 1 ∨ σ = -1) (hρ : 0 < ρ) :
    f '' Set.Icc (0:ℝ) 1 = Set.Icc (f 0 + (σ - 1) / 2 * ρ) (f 0 + (σ - 1) / 2 * ρ + ρ) := by
  have hne : σ * ρ ≠ 0 := mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hρ.ne'
  rw [image_Icc_of_affine hf hne zero_le_one, min_eq_of_affine hf hσ hρ,
    max_eq_of_affine hf hσ hρ]

/-- An affine map of slope `σρ` is the orientation-preserving similarity of ratio `ρ` onto
its interval, preceded by the reflection `x ↦ 1 - x` when `σ = -1`:
`f(x) = ℓ + ρ ((1 - σ)/2 + σ x)` with `ℓ = f(0) + (σ - 1) ρ / 2`. -/
theorem eq_left_add_of_affine (hf : ∀ x y, f x - f y = σ * ρ * (x - y)) (x : ℝ) :
    f x = (f 0 + (σ - 1) / 2 * ρ) + ρ * ((1 - σ) / 2 + σ * x) := by
  linear_combination hf x 0

end Affine

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- Every map of a system is measurable, being affine. -/
theorem measurable_map (i : ι) : Measurable (S.map i) := by
  unfold map; fun_prop

/-! ### Orientation -/

/-- The orientation of a similarity has modulus one. -/
theorem abs_sign (i : ι) : |S.sign i| = 1 := by
  rcases S.sign_eq i with h | h <;> simp [h]

/-- The orientation of a similarity is non-zero. -/
theorem sign_ne_zero (i : ι) : S.sign i ≠ 0 := by
  rcases S.sign_eq i with h | h <;> simp [h]

/-- The orientation squares to one. -/
theorem sign_mul_self (i : ι) : S.sign i * S.sign i = 1 := by
  rcases S.sign_eq i with h | h <;> simp [h]

/-- The signed ratio `ε_i r_i` has modulus `r_i`. -/
theorem abs_sign_mul_ratio (i : ι) : |S.sign i * S.ratio i| = S.ratio i := by
  rw [abs_mul, abs_sign, one_mul, abs_of_pos (S.ratio_pos i)]

/-- The signed ratio is non-zero. -/
theorem sign_mul_ratio_ne_zero (i : ι) : S.sign i * S.ratio i ≠ 0 :=
  mul_ne_zero (S.sign_ne_zero i) (S.ratio_pos i).ne'

/-- `S_i` is affine with slope the signed ratio `ε_i r_i`. -/
theorem map_sub (i : ι) (x y : ℝ) :
    S.map i x - S.map i y = S.sign i * S.ratio i * (x - y) := by
  simp only [map]; ring

/-- `S_i` scales distances by `r_i`, whatever its orientation. -/
theorem abs_map_sub (i : ι) (x y : ℝ) : |S.map i x - S.map i y| = S.ratio i * |x - y| := by
  rw [abs_sub_of_affine (S.map_sub i), abs_sign_mul_ratio]

/-- `S_i` scales distances by `r_i`. -/
theorem dist_map_map (i : ι) (x y : ℝ) :
    dist (S.map i x) (S.map i y) = S.ratio i * dist x y := by
  rw [Real.dist_eq, Real.dist_eq, abs_map_sub]

/-- Each similarity is injective. -/
theorem map_injective (i : ι) : Function.Injective (S.map i) :=
  injective_of_affine (S.map_sub i) (S.sign_mul_ratio_ne_zero i)

/-- The inverse similarity `S_i⁻¹(y) = ε_i (y - b_i) / r_i`. -/
noncomputable def inv (i : ι) (y : ℝ) : ℝ := S.sign i * (y - S.shift i) / S.ratio i

/-- `S_i ∘ S_i⁻¹ = id`. -/
theorem map_inv (i : ι) (y : ℝ) : S.map i (S.inv i y) = y := by
  have hr := (S.ratio_pos i).ne'
  rcases S.sign_eq i with h | h <;> simp only [map, inv, h] <;> field_simp <;> ring

/-- `S_i⁻¹ ∘ S_i = id`. -/
theorem inv_map (i : ι) (x : ℝ) : S.inv i (S.map i x) = x := by
  have hr := (S.ratio_pos i).ne'
  rcases S.sign_eq i with h | h <;> simp only [map, inv, h] <;> field_simp <;> ring

/-- The inverse similarity is continuous. -/
theorem continuous_inv (i : ι) : Continuous (S.inv i) := by
  unfold inv; fun_prop

/-- The image of a set under `S_i` is its preimage under `S_i⁻¹`. -/
theorem image_eq_preimage_inv (i : ι) (A : Set ℝ) : S.map i '' A = S.inv i ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, inv_map]
    exact hx
  · intro hy
    exact ⟨S.inv i y, hy, S.map_inv i y⟩

/-- The preimage of a closed ball centred in `S_i(x)` under `S_i` is the closed ball of
radius `δ/r_i` at `x`. -/
theorem preimage_closedBall_map (i : ι) (x δ : ℝ) :
    S.map i ⁻¹' Metric.closedBall (S.map i x) δ = Metric.closedBall x (δ / S.ratio i) := by
  rw [preimage_closedBall_of_affine (S.map_sub i) (S.sign_mul_ratio_ne_zero i),
    abs_sign_mul_ratio]

/-! ### The first-level intervals -/

/-- The left endpoint `ℓ_i = min(S_i(0), S_i(1))` of the first-level interval
`S_i([0,1])`, in the closed form `b_i + (ε_i - 1) r_i / 2`. -/
noncomputable def left (i : ι) : ℝ := S.shift i + (S.sign i - 1) / 2 * S.ratio i

/-- The left endpoint is the smaller of the two endpoint images. -/
theorem left_eq_min (i : ι) : S.left i = min (S.map i 0) (S.map i 1) := by
  have hr := S.ratio_pos i
  rcases S.sign_eq i with h | h
  · simp only [left, map, h]
    rw [min_eq_left (by linarith)]
    ring
  · simp only [left, map, h]
    rw [min_eq_right (by linarith)]
    ring

/-- The right endpoint `ℓ_i + r_i` is the larger of the two endpoint images. -/
theorem max_map_eq (i : ι) : max (S.map i 0) (S.map i 1) = S.left i + S.ratio i := by
  rw [left_eq_min]
  have h := max_sub_min_eq_abs (S.map i 0) (S.map i 1)
  have h' : |S.map i 0 - S.map i 1| = S.ratio i := by
    rw [abs_map_sub]; norm_num
  have h'' : |S.map i 1 - S.map i 0| = S.ratio i := by
    rw [abs_map_sub]; norm_num
  simp only [h''] at h
  linarith

/-- `S_i(x) = ℓ_i + r_i ((1 - ε_i)/2 + ε_i x)`: the similarity is the orientation-preserving
similarity of ratio `r_i` onto its interval, preceded by the reflection `x ↦ 1 - x` when
`ε_i = -1`. -/
theorem map_eq_left_add (i : ι) (x : ℝ) :
    S.map i x = S.left i + S.ratio i * ((1 - S.sign i) / 2 + S.sign i * x) := by
  simp only [map, left]; ring

/-- The left endpoint is non-negative. -/
theorem left_nonneg (i : ι) : 0 ≤ S.left i := by
  rw [left_eq_min]
  exact le_min (S.mapsTo i ⟨le_rfl, zero_le_one⟩).1 (S.mapsTo i ⟨zero_le_one, le_rfl⟩).1

/-- The first-level interval ends at or before `1`. -/
theorem left_add_ratio_le_one (i : ι) : S.left i + S.ratio i ≤ 1 := by
  rw [← max_map_eq]
  exact max_le (S.mapsTo i ⟨le_rfl, zero_le_one⟩).2 (S.mapsTo i ⟨zero_le_one, le_rfl⟩).2

/-- The image of a closed interval under a similarity. -/
theorem map_image_Icc (i : ι) {c d : ℝ} (hcd : c ≤ d) :
    S.map i '' Set.Icc c d = Set.Icc (min (S.map i c) (S.map i d)) (max (S.map i c) (S.map i d)) :=
  image_Icc_of_affine (S.map_sub i) (S.sign_mul_ratio_ne_zero i) hcd

/-- The first-level interval `S_i([0,1]) = [ℓ_i, ℓ_i + r_i]`. -/
theorem map_image_unitInterval (i : ι) :
    S.map i '' Set.Icc (0:ℝ) 1 = Set.Icc (S.left i) (S.left i + S.ratio i) := by
  rw [map_image_Icc S i zero_le_one, ← left_eq_min, max_map_eq]

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
