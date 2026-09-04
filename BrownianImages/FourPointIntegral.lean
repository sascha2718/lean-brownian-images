/-
`sec:variance` of `BrownianImagesComplete.tex`: the dyadic summation of
`thm:four-point-integral` and the variance bound `thm:variance` that follows from it.

The four dyadic sums in the proof of `thm:four-point-integral` are the content here.  They factor: the master sum is a product of
two one-dimensional sums, because
`min {1, λ/(β+η), λ²/(βη)} ≤ min {1, λ/β} · min {1, λ/η}`, and each one-dimensional sum
is a geometric series split at the dyadic scale nearest `λ`.

* `min_mul_min_le`: the factorisation of the elementary return bound of `thm:endpoint-block-mass`.
* `tsum_dyadic_lt_one`, `tsum_dyadic_eq_one`, `tsum_dyadic_gt_one`: the three regimes of
  the one-dimensional dyadic sum, the middle one carrying the
  logarithm.
* `tsum_master_le`: the double dyadic sum, summed against `eq:variance-scale`.
* `measurePreserving_perm4`: `μ⁴` is invariant under permuting the four times, which is
  what lets the mass bound of `thm:endpoint-block-mass`, stated for ordered quadruples,
  be applied to every labelled arrangement.
* `four_point_integral_of_block`: `thm:four-point-integral`, `eq:four-point-integral`,
  on the dyadic block bound of `thm:endpoint-block-mass`.
* `variance_of_block`, `thm_variance_of_block`: `thm:variance`, on that
  bound and on the expansion of the variance over `μ⁴`.
-/
import BrownianImages.Frostman
import BrownianImages.FourPoint
import Mathlib.Probability.Moments.Variance

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace FourPointIntegral

/-! ### Elementary rearrangements of dyadic powers -/

/-- A dyadic power raised to a real exponent is a power of the dyadic power. -/
theorem half_pow_rpow (θ : ℝ) (j : ℕ) : (((1:ℝ)/2) ^ j) ^ θ = ((((1:ℝ)/2)) ^ θ) ^ j := by
  rw [← Real.rpow_natCast ((1:ℝ)/2) j, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- Positivity of the dyadic powers, used throughout. -/
theorem half_pow_pos (j : ℕ) : (0:ℝ) < ((1:ℝ)/2) ^ j := by positivity

/-- The real power `(1/2)^θ` lies in `(0,1)` for `0 < θ`. -/
theorem half_rpow_lt_one {θ : ℝ} (hθ : 0 < θ) : ((1:ℝ)/2) ^ θ < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hθ

/-- The real power `(1/2)^θ` is positive. -/
theorem half_rpow_pos (θ : ℝ) : (0:ℝ) < ((1:ℝ)/2) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ

/-! ### Geometric sums -/

/-- A partial geometric sum with ratio in `[0,1)` is bounded by the full one. -/
theorem geom_range_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) (K : ℕ) :
    ∑ i ∈ Finset.range K, u ^ i ≤ (1 - u)⁻¹ := by
  have hsum := summable_geometric_of_lt_one h0 h1
  have := hsum.sum_le_tsum (Finset.range K) (fun i _ => pow_nonneg h0 i)
  rwa [tsum_geometric_of_lt_one h0 h1] at this

/-- A partial geometric sum with ratio above `1`, bounded by its last term. -/
theorem geom_range_gt_le {w : ℝ} (h1 : 1 < w) (K : ℕ) :
    ∑ i ∈ Finset.range K, w ^ i ≤ w ^ K / (w - 1) := by
  rw [geom_sum_eq (by linarith) K]
  have hw : (0:ℝ) < w - 1 := by linarith
  rw [div_le_div_iff_of_pos_right hw]
  linarith [one_le_pow₀ h1.le (n := K)]

/-- The bridge from a bound on every partial sum to a bound on the `ℝ≥0∞`-valued sum. -/
theorem tsum_ofReal_le {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) {B : ℝ}
    (h : ∀ M : ℕ, ∑ j ∈ Finset.range M, f j ≤ B) :
    ∑' j : ℕ, ENNReal.ofReal (f j) ≤ ENNReal.ofReal B := by
  rw [ENNReal.tsum_eq_iSup_sum' Finset.range Finset.exists_nat_subset_range]
  refine iSup_le fun M => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hf j)]
  exact ENNReal.ofReal_le_ofReal (h M)

/-! ### The dyadic scale nearest `λ` -/

/-- The least dyadic scale below `λ` is within a factor two of it. -/
theorem exists_dyadic_index {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∃ N : ℕ, ((1:ℝ)/2) ^ N ≤ lam ∧ lam ≤ 2 * ((1:ℝ)/2) ^ N := by
  classical
  have hex : ∃ n : ℕ, ((1:ℝ)/2) ^ n ≤ lam := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 (by norm_num : (1:ℝ)/2 < 1)
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]
    norm_num
    linarith
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := not_le.mp (Nat.find_min hex (m := k) (by omega))
    rw [hk]
    have hpow : (2:ℝ) * ((1:ℝ)/2) ^ (k + 1) = ((1:ℝ)/2) ^ k := by ring
    rw [hpow]
    exact hmin.le

/-! ### The one-dimensional dyadic sums -/

/-- The partial sums of `∑ β^θ min(1, λ/β)` over `β ∈ 𝒟`, split at a dyadic scale `N`
below `λ`: on `β ≤ λ` the elementary bound is `β^θ`, and on `β > λ` it is `λ β^{θ-1}`. -/
theorem sum_range_split {θ lam : ℝ} (hθ : 0 < θ) (hlam0 : 0 < lam) {N : ℕ}
    (hN : ((1:ℝ)/2) ^ N ≤ lam) (M : ℕ) :
    ∑ j ∈ Finset.range M, (((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j)
      ≤ lam * ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ (θ - 1)) ^ j
          + lam ^ θ * (1 - ((1:ℝ)/2) ^ θ)⁻¹ := by
  classical
  have hu0 : (0:ℝ) < ((1:ℝ)/2) ^ θ := half_rpow_pos θ
  have hu1 : ((1:ℝ)/2) ^ θ < 1 := half_rpow_lt_one hθ
  have hterm : ∀ j : ℕ, (((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j)
      ≤ if j < N then lam * (((1:ℝ)/2) ^ (θ - 1)) ^ j else (((1:ℝ)/2) ^ θ) ^ j := by
    intro j
    have hβ : (0:ℝ) < ((1:ℝ)/2) ^ j := half_pow_pos j
    have hβθ : (0:ℝ) < (((1:ℝ)/2) ^ j) ^ θ := Real.rpow_pos_of_pos hβ θ
    by_cases hj : j < N
    · rw [if_pos hj]
      have h1 : (((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j)
          ≤ (((1:ℝ)/2) ^ j) ^ θ * (lam / ((1:ℝ)/2) ^ j) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hβθ.le
      have h2 : (((1:ℝ)/2) ^ j) ^ θ * (lam / ((1:ℝ)/2) ^ j)
          = lam * (((1:ℝ)/2) ^ (θ - 1)) ^ j := by
        rw [← half_pow_rpow, Real.rpow_sub hβ, Real.rpow_one]
        field_simp
      linarith [h2 ▸ h1]
    · rw [if_neg hj, ← half_pow_rpow]
      have h1 : (((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j)
          ≤ (((1:ℝ)/2) ^ j) ^ θ * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hβθ.le
      linarith
  have hstep :
      ∑ j ∈ Finset.range M, (((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j)
        ≤ (∑ j ∈ (Finset.range M).filter (fun j => j < N),
              lam * (((1:ℝ)/2) ^ (θ - 1)) ^ j)
          + ∑ j ∈ (Finset.range M).filter (fun j => ¬ j < N), (((1:ℝ)/2) ^ θ) ^ j := by
    rw [← Finset.sum_ite]
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have hhead : (∑ j ∈ (Finset.range M).filter (fun j => j < N),
        lam * (((1:ℝ)/2) ^ (θ - 1)) ^ j)
      ≤ lam * ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ (θ - 1)) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact hx.2
  have htail : (∑ j ∈ (Finset.range M).filter (fun j => ¬ j < N), (((1:ℝ)/2) ^ θ) ^ j)
      ≤ lam ^ θ * (1 - ((1:ℝ)/2) ^ θ)⁻¹ := by
    have hsub : (∑ j ∈ (Finset.range M).filter (fun j => ¬ j < N), (((1:ℝ)/2) ^ θ) ^ j)
        ≤ ∑ j ∈ Finset.Ico N M, (((1:ℝ)/2) ^ θ) ^ j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢
      omega
    have hIco : ∑ j ∈ Finset.Ico N M, (((1:ℝ)/2) ^ θ) ^ j
        = (((1:ℝ)/2) ^ θ) ^ N * ∑ i ∈ Finset.range (M - N), (((1:ℝ)/2) ^ θ) ^ i := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [pow_add])
    have hpowN : (((1:ℝ)/2) ^ θ) ^ N ≤ lam ^ θ := by
      rw [← half_pow_rpow]
      exact Real.rpow_le_rpow (half_pow_pos N).le hN hθ.le
    have hgeom : ∑ i ∈ Finset.range (M - N), (((1:ℝ)/2) ^ θ) ^ i
        ≤ (1 - ((1:ℝ)/2) ^ θ)⁻¹ := geom_range_le hu0.le hu1 _
    calc (∑ j ∈ (Finset.range M).filter (fun j => ¬ j < N), (((1:ℝ)/2) ^ θ) ^ j)
        ≤ (((1:ℝ)/2) ^ θ) ^ N * ∑ i ∈ Finset.range (M - N), (((1:ℝ)/2) ^ θ) ^ i := by
          rw [← hIco]; exact hsub
      _ ≤ lam ^ θ * (1 - ((1:ℝ)/2) ^ θ)⁻¹ := by
          refine mul_le_mul hpowN hgeom (Finset.sum_nonneg fun i _ => by positivity)
            (Real.rpow_nonneg hlam0.le θ)
  linarith

/-- `λ · λ^{θ-1} = λ^θ`. -/
theorem mul_rpow_sub_one {lam θ : ℝ} (h : 0 < lam) : lam * lam ^ (θ - 1) = lam ^ θ := by
  have h1 : lam ^ (1:ℝ) * lam ^ (θ - 1) = lam ^ θ := by
    rw [← Real.rpow_add h]
    congr 1
    ring
  rwa [Real.rpow_one] at h1

/-- The one-dimensional dyadic sum, the subcritical regime: for `0 < θ < 1` the dyadic sum
`∑ β^θ min(1, λ/β)` is `O(λ^θ)`. -/
theorem tsum_dyadic_lt_one {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ D > 0, ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∑' j : ℕ, ENNReal.ofReal ((((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j))
        ≤ ENNReal.ofReal (D * lam ^ θ) := by
  have hu0 : (0:ℝ) < ((1:ℝ)/2) ^ θ := half_rpow_pos θ
  have hu1 : ((1:ℝ)/2) ^ θ < 1 := half_rpow_lt_one hθ0
  have hw1 : 1 < ((1:ℝ)/2) ^ (θ - 1) :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).2 (Or.inr ⟨by norm_num, by linarith⟩)
  refine ⟨(1 - ((1:ℝ)/2) ^ θ)⁻¹ + ((1:ℝ)/2) ^ (θ - 1) / (((1:ℝ)/2) ^ (θ - 1) - 1), by positivity,
    ?_⟩
  intro lam h0 h1
  refine tsum_ofReal_le (fun j => by positivity) (fun M => ?_)
  obtain ⟨N, hN1, hN2⟩ := exists_dyadic_index h0 h1
  have hsplit := sum_range_split hθ0 h0 hN1 M
  have hwN : (((1:ℝ)/2) ^ (θ - 1)) ^ N ≤ lam ^ (θ - 1) * ((1:ℝ)/2) ^ (θ - 1) := by
    rw [← half_pow_rpow]
    have hle : ((((1:ℝ)/2)) ^ N) ^ (θ - 1) ≤ (lam / 2) ^ (θ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have heq : (lam / 2) ^ (θ - 1) = lam ^ (θ - 1) * ((1:ℝ)/2) ^ (θ - 1) := by
      rw [show lam / 2 = lam * ((1:ℝ)/2) by ring, Real.mul_rpow h0.le (by norm_num)]
    linarith [heq ▸ hle]
  have hgeomN : ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ (θ - 1)) ^ j
      ≤ (((1:ℝ)/2) ^ (θ - 1)) ^ N / (((1:ℝ)/2) ^ (θ - 1) - 1) := geom_range_gt_le hw1 N
  have hden : (0:ℝ) < ((1:ℝ)/2) ^ (θ - 1) - 1 := by linarith
  have hhead : lam * ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ (θ - 1)) ^ j
      ≤ lam ^ θ * (((1:ℝ)/2) ^ (θ - 1) / (((1:ℝ)/2) ^ (θ - 1) - 1)) := by
    have h2 : lam * ((((1:ℝ)/2) ^ (θ - 1)) ^ N / (((1:ℝ)/2) ^ (θ - 1) - 1))
        ≤ lam * ((lam ^ (θ - 1) * ((1:ℝ)/2) ^ (θ - 1)) / (((1:ℝ)/2) ^ (θ - 1) - 1)) := by
      gcongr
    have h3 : lam * ((lam ^ (θ - 1) * ((1:ℝ)/2) ^ (θ - 1)) / (((1:ℝ)/2) ^ (θ - 1) - 1))
        = lam ^ θ * (((1:ℝ)/2) ^ (θ - 1) / (((1:ℝ)/2) ^ (θ - 1) - 1)) := by
      rw [← mul_rpow_sub_one (lam := lam) (θ := θ) h0]
      field_simp
    have h4 : lam * ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ (θ - 1)) ^ j
        ≤ lam * ((((1:ℝ)/2) ^ (θ - 1)) ^ N / (((1:ℝ)/2) ^ (θ - 1) - 1)) := by
      gcongr
    linarith [h3 ▸ h2]
  nlinarith [hsplit, hhead, Real.rpow_nonneg h0.le θ]

/-- The one-dimensional dyadic sum, the critical regime: at `θ = 1` the dyadic sum carries the
logarithm, `O(λ(1 + log(1/λ)))`. -/
theorem tsum_dyadic_eq_one :
    ∃ D > 0, ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∑' j : ℕ, ENNReal.ofReal ((((1:ℝ)/2) ^ j) ^ (1:ℝ) * min 1 (lam / ((1:ℝ)/2) ^ j))
        ≤ ENNReal.ofReal (D * (lam * (1 + Real.log lam⁻¹))) := by
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 + (Real.log 2)⁻¹, by positivity, ?_⟩
  intro lam h0 h1
  refine tsum_ofReal_le (fun j => by positivity) (fun M => ?_)
  obtain ⟨N, hN1, hN2⟩ := exists_dyadic_index h0 h1
  have hsplit := sum_range_split (θ := 1) one_pos h0 hN1 M
  have hlogpos : 0 ≤ Real.log lam⁻¹ := by
    rw [Real.log_inv]
    have := Real.log_nonpos h0.le h1
    linarith
  have hNlog : (N : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log lam⁻¹ := by
    have hlt : Real.log lam ≤ Real.log (2 * ((1:ℝ)/2) ^ N) := Real.log_le_log h0 hN2
    have hval : Real.log (2 * ((1:ℝ)/2) ^ N) = Real.log 2 - N * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        show ((1:ℝ)/2) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
      ring
    rw [hval] at hlt
    rw [Real.log_inv]
    linarith
  have hNle : (N : ℝ) - 1 ≤ Real.log lam⁻¹ / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith
  have hsum1 : ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ ((1:ℝ) - 1)) ^ j = (N : ℝ) := by
    simp
  rw [hsum1] at hsplit
  have htail : lam ^ (1:ℝ) * (1 - ((1:ℝ)/2) ^ (1:ℝ))⁻¹ = 2 * lam := by
    rw [Real.rpow_one, Real.rpow_one]
    norm_num
    ring
  rw [htail] at hsplit
  have hhead : lam * (N : ℝ) ≤ lam * (1 + Real.log lam⁻¹ / Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) h0.le
  have hinv : (0:ℝ) < (Real.log 2)⁻¹ := by positivity
  have hfinal : lam * (1 + Real.log lam⁻¹ / Real.log 2) + 2 * lam
      ≤ (3 + (Real.log 2)⁻¹) * (lam * (1 + Real.log lam⁻¹)) := by
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (mul_nonneg h0.le hlogpos) hinv.le, mul_nonneg h0.le hlogpos,
      mul_nonneg h0.le hinv.le]
  linarith

/-- The one-dimensional dyadic sum, the supercritical regime: for `θ > 1` the dyadic sum is
`O(λ)`. -/
theorem tsum_dyadic_gt_one {θ : ℝ} (hθ1 : 1 < θ) :
    ∃ D > 0, ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∑' j : ℕ, ENNReal.ofReal ((((1:ℝ)/2) ^ j) ^ θ * min 1 (lam / ((1:ℝ)/2) ^ j))
        ≤ ENNReal.ofReal (D * lam) := by
  have hθ0 : (0:ℝ) < θ := by linarith
  have hu0 : (0:ℝ) < ((1:ℝ)/2) ^ θ := half_rpow_pos θ
  have hu1 : ((1:ℝ)/2) ^ θ < 1 := half_rpow_lt_one hθ0
  have hw0 : (0:ℝ) < ((1:ℝ)/2) ^ (θ - 1) := half_rpow_pos _
  have hw1 : ((1:ℝ)/2) ^ (θ - 1) < 1 := half_rpow_lt_one (by linarith)
  refine ⟨(1 - ((1:ℝ)/2) ^ θ)⁻¹ + (1 - ((1:ℝ)/2) ^ (θ - 1))⁻¹, by positivity, ?_⟩
  intro lam h0 h1
  refine tsum_ofReal_le (fun j => by positivity) (fun M => ?_)
  obtain ⟨N, hN1, hN2⟩ := exists_dyadic_index h0 h1
  have hsplit := sum_range_split hθ0 h0 hN1 M
  have hgeom : ∑ j ∈ Finset.range N, (((1:ℝ)/2) ^ (θ - 1)) ^ j
      ≤ (1 - ((1:ℝ)/2) ^ (θ - 1))⁻¹ := geom_range_le hw0.le hw1 N
  have hpow : lam ^ θ ≤ lam := by
    have := Real.rpow_le_rpow_of_exponent_ge h0 h1 hθ1.le
    rwa [Real.rpow_one] at this
  have hinv : (0:ℝ) < (1 - ((1:ℝ)/2) ^ θ)⁻¹ := by positivity
  nlinarith [hsplit, hgeom, hpow, h0.le]

/-! ### The master sum -/

/-- The elementary return bound of `thm:endpoint-block-mass` factors over the two scales:
`min {1, λ/(β+η), λ²/(βη)} ≤ min {1, λ/β} · min {1, λ/η}`.  This is what makes
the double dyadic sum a product of two one-dimensional sums. -/
theorem min_mul_min_le {β η lam : ℝ} (hβ : 0 < β) (hη : 0 < η) (hlam : 0 < lam) :
    min 1 (min (lam / (β + η)) (lam ^ 2 / (β * η))) ≤ min 1 (lam / β) * min 1 (lam / η) := by
  rcases le_or_gt β lam with hb | hb <;> rcases le_or_gt η lam with he | he
  · have h1 : min 1 (lam / β) = 1 := min_eq_left ((one_le_div hβ).2 hb)
    have h2 : min 1 (lam / η) = 1 := min_eq_left ((one_le_div hη).2 he)
    rw [h1, h2, mul_one]
    exact min_le_left _ _
  · have h1 : min 1 (lam / β) = 1 := min_eq_left ((one_le_div hβ).2 hb)
    have h2 : min 1 (lam / η) = lam / η := min_eq_right ((div_le_one hη).2 he.le)
    rw [h1, h2, one_mul]
    refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
    gcongr
    linarith
  · have h1 : min 1 (lam / β) = lam / β := min_eq_right ((div_le_one hβ).2 hb.le)
    have h2 : min 1 (lam / η) = 1 := min_eq_left ((one_le_div hη).2 he)
    rw [h1, h2, mul_one]
    refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
    gcongr
    linarith
  · have h1 : min 1 (lam / β) = lam / β := min_eq_right ((div_le_one hβ).2 hb.le)
    have h2 : min 1 (lam / η) = lam / η := min_eq_right ((div_le_one hη).2 he.le)
    rw [h1, h2]
    refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) ?_)
    rw [div_mul_div_comm]
    apply le_of_eq
    ring

/-- A product of dyadic sums, as an `ℝ≥0∞`-valued sum over `ℕ × ℕ`. -/
theorem tsum_prod_factor (a b : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∑' y : ℕ × ℕ, ENNReal.ofReal (a y.1 * b y.2)
      = (∑' j : ℕ, ENNReal.ofReal (a j)) * ∑' l : ℕ, ENNReal.ofReal (b l) := by
  rw [ENNReal.tsum_prod' (f := fun y : ℕ × ℕ => ENNReal.ofReal (a y.1 * b y.2))]
  simp_rw [ENNReal.ofReal_mul (ha _), ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

/-- `(r²)^c = r^{2c}`. -/
theorem sq_rpow {r : ℝ} (hr : 0 < r) (c : ℝ) : (r ^ 2) ^ c = r ^ (2 * c) := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
  norm_num

/-- The double dyadic sum of `thm:four-point-integral`, bounded
by the variance scale `eq:variance-scale`.  The three regimes of `V_s` are the three
regimes of the `η`-sum: `2s < 1`, `2s = 1` and `2s > 1`. -/
theorem tsum_master_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ D > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∑' y : ℕ × ℕ,
          ENNReal.ofReal (min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ y.1 + ((1:ℝ)/2) ^ y.2))
              (r ^ 4 / (((1:ℝ)/2) ^ y.1 * ((1:ℝ)/2) ^ y.2))))
            * ENNReal.ofReal ((((1:ℝ)/2) ^ y.1) ^ s * (((1:ℝ)/2) ^ y.2) ^ (2 * s))
        ≤ ENNReal.ofReal (D * varScale s r) := by
  obtain ⟨D₁, hD₁0, hD₁⟩ := tsum_dyadic_lt_one hs0 hs1
  have key : ∀ (r : ℝ), 0 < r → r ≤ 1 →
      ∑' y : ℕ × ℕ,
          ENNReal.ofReal (min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ y.1 + ((1:ℝ)/2) ^ y.2))
              (r ^ 4 / (((1:ℝ)/2) ^ y.1 * ((1:ℝ)/2) ^ y.2))))
            * ENNReal.ofReal ((((1:ℝ)/2) ^ y.1) ^ s * (((1:ℝ)/2) ^ y.2) ^ (2 * s))
        ≤ (∑' j : ℕ, ENNReal.ofReal ((((1:ℝ)/2) ^ j) ^ s * min 1 (r ^ 2 / ((1:ℝ)/2) ^ j)))
            * ∑' l : ℕ, ENNReal.ofReal ((((1:ℝ)/2) ^ l) ^ (2 * s)
                * min 1 (r ^ 2 / ((1:ℝ)/2) ^ l)) := by
    intro r hr0 hr1
    rw [← tsum_prod_factor _ _ (fun j => by positivity)]
    refine ENNReal.tsum_le_tsum (fun y => ?_)
    have hβ : (0:ℝ) < ((1:ℝ)/2) ^ y.1 := half_pow_pos _
    have hη : (0:ℝ) < ((1:ℝ)/2) ^ y.2 := half_pow_pos _
    have hlam : (0:ℝ) < r ^ 2 := by positivity
    have hmin : (0:ℝ) ≤ min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ y.1 + ((1:ℝ)/2) ^ y.2))
        (r ^ 4 / (((1:ℝ)/2) ^ y.1 * ((1:ℝ)/2) ^ y.2))) := by
      refine le_min zero_le_one (le_min (by positivity) (by positivity))
    rw [← ENNReal.ofReal_mul hmin]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfac := min_mul_min_le hβ hη hlam
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
    nlinarith [hfac, Real.rpow_nonneg hβ.le s, Real.rpow_nonneg hη.le (2 * s),
      mul_nonneg (Real.rpow_nonneg hβ.le s) (Real.rpow_nonneg hη.le (2 * s)),
      le_min (zero_le_one (α := ℝ)) (le_min (div_nonneg hlam.le (by positivity))
        (div_nonneg (by positivity) (by positivity) : (0:ℝ) ≤ (r ^ 2) ^ 2 / (((1:ℝ)/2) ^ y.1 * ((1:ℝ)/2) ^ y.2)))]
  rcases lt_trichotomy s 2⁻¹ with hcase | hcase | hcase
  · obtain ⟨D₂, hD₂0, hD₂⟩ := tsum_dyadic_lt_one (by linarith : (0:ℝ) < 2 * s)
      (by linarith : 2 * s < 1)
    refine ⟨D₁ * D₂, by positivity, fun r hr0 hr1 => ?_⟩
    have hlam0 : (0:ℝ) < r ^ 2 := by positivity
    have hlam1 : r ^ 2 ≤ 1 := by nlinarith
    refine le_trans (key r hr0 hr1) ?_
    refine le_trans (mul_le_mul' (hD₁ _ hlam0 hlam1) (hD₂ _ hlam0 hlam1)) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [varScale, if_pos hcase, sq_rpow hr0, sq_rpow hr0,
      show D₁ * (r ^ (2 * s)) * (D₂ * r ^ (2 * (2 * s))) = D₁ * D₂ * (r ^ (2 * s) * r ^ (2 * (2 * s))) by ring,
      ← Real.rpow_add hr0]
    apply le_of_eq
    ring_nf
  · subst hcase
    obtain ⟨D₂, hD₂0, hD₂⟩ := tsum_dyadic_eq_one
    refine ⟨2 * (D₁ * D₂), by positivity, fun r hr0 hr1 => ?_⟩
    have hlam0 : (0:ℝ) < r ^ 2 := by positivity
    have hlam1 : r ^ 2 ≤ 1 := by nlinarith
    have hlogr : 0 ≤ Real.log r⁻¹ := by
      rw [Real.log_inv]
      linarith [Real.log_nonpos hr0.le hr1]
    refine le_trans (key r hr0 hr1) ?_
    have hrw : ∀ l : ℕ, (((1:ℝ)/2) ^ l) ^ (2 * (2:ℝ)⁻¹) = (((1:ℝ)/2) ^ l) ^ (1:ℝ) := by
      intro l
      norm_num
    simp_rw [hrw]
    refine le_trans (mul_le_mul' (hD₁ _ hlam0 hlam1) (hD₂ _ hlam0 hlam1)) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlog : Real.log (r ^ 2)⁻¹ = 2 * Real.log r⁻¹ := by
      rw [Real.log_inv, Real.log_pow, Real.log_inv]
      ring
    have hhalf : (r ^ 2) ^ (2:ℝ)⁻¹ = r := by
      rw [sq_rpow hr0]
      norm_num
    rw [varScale, if_neg (by norm_num), if_pos rfl, hlog, hhalf]
    have hr3 : r ^ (3:ℝ) = r * r ^ 2 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hr3]
    nlinarith [mul_nonneg (mul_nonneg hD₁0.le hD₂0.le) (mul_nonneg hr0.le hlam0.le),
      mul_nonneg (mul_nonneg (mul_nonneg hD₁0.le hD₂0.le) (mul_nonneg hr0.le hlam0.le)) hlogr]
  · obtain ⟨D₂, hD₂0, hD₂⟩ := tsum_dyadic_gt_one (by linarith : (1:ℝ) < 2 * s)
    refine ⟨D₁ * D₂, by positivity, fun r hr0 hr1 => ?_⟩
    have hlam0 : (0:ℝ) < r ^ 2 := by positivity
    have hlam1 : r ^ 2 ≤ 1 := by nlinarith
    refine le_trans (key r hr0 hr1) ?_
    refine le_trans (mul_le_mul' (hD₁ _ hlam0 hlam1) (hD₂ _ hlam0 hlam1)) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [varScale, if_neg (by linarith), if_neg (by linarith), sq_rpow hr0]
    have hsplit : r ^ (2 * s) * r ^ 2 = r ^ (2 * s + 2) := by
      rw [show (r:ℝ) ^ 2 = r ^ ((2:ℕ):ℝ) by rw [Real.rpow_natCast], Real.rpow_natCast,
        ← Real.rpow_natCast r 2, ← Real.rpow_add hr0]
      norm_num
    refine le_of_eq ?_
    calc D₁ * r ^ (2 * s) * (D₂ * r ^ 2) = D₁ * D₂ * (r ^ (2 * s) * r ^ 2) := by ring
      _ = D₁ * D₂ * r ^ (2 * s + 2) := by rw [hsplit]

/-! ### Permuting the four times -/

/-- The four times of a labelled quadruple, read as a function on `Fin 4`. -/
def coord (p : ℝ × ℝ × ℝ × ℝ) : Fin 4 → ℝ := ![p.1, p.2.1, p.2.2.1, p.2.2.2]

/-- Reading the four times is measurable. -/
theorem measurable_coord : Measurable coord :=
  measurable_pi_lambda _ (fun i => by
    fin_cases i
    exacts [measurable_fst, measurable_fst.comp measurable_snd,
      measurable_fst.comp (measurable_snd.comp measurable_snd),
      measurable_snd.comp (measurable_snd.comp measurable_snd)])

/-- The quadruple of times as a measurable equivalence with `Fin 4 → ℝ`. -/
def toPiE : (ℝ × ℝ × ℝ × ℝ) ≃ᵐ (Fin 4 → ℝ) where
  toFun := coord
  invFun := fun x => (x 0, x 1, x 2, x 3)
  left_inv := fun p => rfl
  right_inv := fun x => by funext i; fin_cases i <;> rfl
  measurable_toFun := measurable_coord
  measurable_invFun := by
    show Measurable fun x : Fin 4 → ℝ => (x 0, x 1, x 2, x 3)
    fun_prop

/-- Permuting the four times of a labelled quadruple. -/
def perm4 (σ : Equiv.Perm (Fin 4)) (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (coord p (σ 0), coord p (σ 1), coord p (σ 2), coord p (σ 3))

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The preimage of a box under the coordinate reading is a box. -/
theorem coord_preimage_pi (s : Fin 4 → Set ℝ) :
    coord ⁻¹' (Set.pi Set.univ s) = (s 0) ×ˢ (s 1) ×ˢ (s 2) ×ˢ (s 3) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, coord]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> assumption

/-- `μ⁴` on `ℝ⁴` is the four-fold product measure on `Fin 4 → ℝ`. -/
theorem measurePreserving_coord :
    MeasurePreserving coord (μ.prod (μ.prod (μ.prod μ))) (Measure.pi fun _ : Fin 4 => μ) := by
  refine ⟨measurable_coord, ?_⟩
  refine (Measure.pi_eq ?_).symm
  intro s hs
  rw [Measure.map_apply measurable_coord (MeasurableSet.univ_pi hs), coord_preimage_pi,
    Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_four]
  ring

/-- A product of identical factors is invariant under permuting the indices. -/
theorem measurePreserving_comp_perm (σ : Equiv.Perm (Fin 4)) :
    MeasurePreserving (fun x : Fin 4 → ℝ => x ∘ σ)
      (Measure.pi fun _ : Fin 4 => μ) (Measure.pi fun _ : Fin 4 => μ) := by
  have hmeas : Measurable (fun x : Fin 4 → ℝ => x ∘ σ) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq ?_).symm
  intro s hs
  have hpre : (fun x : Fin 4 → ℝ => x ∘ σ) ⁻¹' (Set.pi Set.univ s)
      = Set.pi Set.univ (fun i => s (σ.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h i
      have := h (σ.symm i)
      rwa [Equiv.apply_symm_apply] at this
    · intro h i
      have := h (σ i)
      rwa [Equiv.symm_apply_apply] at this
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  exact Fintype.prod_equiv σ.symm _ _ (fun i => rfl)

/-- `μ⁴` is invariant under permuting the four times.  This is what carries the mass
bound of `thm:endpoint-block-mass`, stated for ordered quadruples, to every labelled
arrangement of the four endpoints. -/
theorem measurePreserving_perm4 (σ : Equiv.Perm (Fin 4)) :
    MeasurePreserving (perm4 σ)
      (μ.prod (μ.prod (μ.prod μ))) (μ.prod (μ.prod (μ.prod μ))) :=
  (measurePreserving_coord.symm toPiE).comp
    ((measurePreserving_comp_perm σ).comp measurePreserving_coord)

/-! ### The dyadic blocks and the exceptional sets -/

/-- `E_{β,η}` of `thm:endpoint-block-mass` at the dyadic values `β = 2^{-j}`,
`η = 2^{-l}`: the ordered quadruples with `β/2 < b ≤ β` and `η/2 < h ≤ η`. -/
def blockSet (j l : ℕ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
    ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
    ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
    (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}

/-- The dyadic block is measurable. -/
theorem measurableSet_blockSet (j l : ℕ) : MeasurableSet (blockSet j l) := by
  have h1 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h2 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.2.1 < p.2.2.1} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h3 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.2.2.1 < p.2.2.2} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h4 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h5 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h6 : MeasurableSet
      {p : ℝ × ℝ × ℝ × ℝ | ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1)} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h7 : MeasurableSet
      {p : ℝ × ℝ × ℝ × ℝ | (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))

/-- The quadruples whose four times all lie in `[0,1]`, where `μ` sits. -/
def unitSet : Set (ℝ × ℝ × ℝ × ℝ) := {p | ∀ i : Fin 4, coord p i ∈ Set.Icc (0:ℝ) 1}

/-- The quadruples at which one of the four crossing ties holds. -/
def tieSet : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 = p.2.2.1} ∪ {p | p.1 = p.2.2.2} ∪ {p | p.2.1 = p.2.2.1} ∪ {p | p.2.1 = p.2.2.2}

/-- A null set of times gives a null set of quadruples, in each of the four slots. -/
theorem coord_mem_null {Z : Set ℝ} (hZ0 : μ Z = 0) (i : Fin 4) :
    (μ.prod (μ.prod (μ.prod μ))) {p : ℝ × ℝ × ℝ × ℝ | coord p i ∈ Z} = 0 := by
  fin_cases i
  · show (μ.prod (μ.prod (μ.prod μ))) {p : ℝ × ℝ × ℝ × ℝ | p.1 ∈ Z} = 0
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.1 ∈ Z} = Z ×ˢ (Set.univ : Set (ℝ × ℝ × ℝ)) := by
      ext p; simp
    rw [hset, Measure.prod_prod, hZ0, zero_mul]
  · show (μ.prod (μ.prod (μ.prod μ))) {p : ℝ × ℝ × ℝ × ℝ | p.2.1 ∈ Z} = 0
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.2.1 ∈ Z}
        = (Set.univ : Set ℝ) ×ˢ (Z ×ˢ (Set.univ : Set (ℝ × ℝ))) := by
      ext p; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hZ0, zero_mul, mul_zero]
  · show (μ.prod (μ.prod (μ.prod μ))) {p : ℝ × ℝ × ℝ × ℝ | p.2.2.1 ∈ Z} = 0
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.2.2.1 ∈ Z}
        = (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ (Z ×ˢ (Set.univ : Set ℝ))) := by
      ext p; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hZ0, zero_mul, mul_zero,
      mul_zero]
  · show (μ.prod (μ.prod (μ.prod μ))) {p : ℝ × ℝ × ℝ × ℝ | p.2.2.2 ∈ Z} = 0
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.2.2.2 ∈ Z}
        = (Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ ((Set.univ : Set ℝ) ×ˢ Z)) := by
      ext p; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hZ0, mul_zero, mul_zero,
      mul_zero]

/-- Off `[0,1]` there is no mass: the complement of `unitSet` is `μ⁴`-null.  This is the
support condition carried by `IsFrostman`. -/
theorem measure_unitSet_compl {s A : ℝ} (hμ : IsFrostman s A μ) :
    (μ.prod (μ.prod (μ.prod μ))) (unitSetᶜ) = 0 := by
  have hsub : (unitSetᶜ : Set (ℝ × ℝ × ℝ × ℝ))
      ⊆ ⋃ i : Fin 4, {p : ℝ × ℝ × ℝ × ℝ | coord p i ∈ (Set.Icc (0:ℝ) 1)ᶜ} := by
    intro p hp
    simp only [unitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hp
    obtain ⟨i, hi⟩ := hp
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null (fun i => ?_)
  exact coord_mem_null hμ.support i

/-- The four crossing ties are `μ⁴`-null, because a Frostman measure of positive
dimension has no atoms. -/
theorem measure_tieSet {s A : ℝ} (hs : 0 < s) (hμ : IsFrostman s A μ) :
    (μ.prod (μ.prod (μ.prod μ))) tieSet = 0 := by
  have hdiag : (μ.prod (μ.prod (μ.prod μ))) {p : ℝ × ℝ × ℝ × ℝ | p.1 = p.2.1} = 0 := by
    have hmeas : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | p.1 = p.2.1} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    rw [Measure.prod_apply hmeas]
    have hsec : ∀ x : ℝ, (μ.prod (μ.prod μ)) {a : ℝ × ℝ × ℝ | x = a.1} = 0 := by
      intro x
      have hset : {a : ℝ × ℝ × ℝ | x = a.1} = ({x} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
        ext q; simp [eq_comm]
      rw [hset, Measure.prod_prod, hμ.measure_singleton hs x, zero_mul]
    simp only [Set.preimage_setOf_eq]
    rw [lintegral_congr hsec]
    simp
  have htrans : ∀ σ : Equiv.Perm (Fin 4),
      (μ.prod (μ.prod (μ.prod μ)))
        ((perm4 σ) ⁻¹' {p : ℝ × ℝ × ℝ × ℝ | p.1 = p.2.1}) = 0 := by
    intro σ
    rw [(measurePreserving_perm4 σ).measure_preimage
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).nullMeasurableSet, hdiag]
  refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
  · exact htrans (Equiv.ofBijective ![0, 2, 1, 3] (by decide))
  · exact htrans (Equiv.ofBijective ![0, 3, 1, 2] (by decide))
  · exact htrans (Equiv.ofBijective ![1, 2, 0, 3] (by decide))
  · exact htrans (Equiv.ofBijective ![1, 3, 0, 2] (by decide))

/-! ### Sorting the four endpoints -/

/-- Positive overlap says the two closed time intervals cross. -/
theorem overlap_lt {t u t' u' : ℝ} (h : 0 < overlap t u t' u') :
    max (min t u) (min t' u') < min (max t u) (max t' u') := by
  rw [overlap, lt_max_iff] at h
  rcases h with h | h
  · exact absurd h (lt_irrefl 0)
  · linarith

/-- Four reals with `a < b`, `c < d`, `a < d`, `c < b` and no tie between `a, c` or
between `b, d` sort in one of four ways.  The two middle ones are the crossing pairing,
the two outer ones the nested pairing of `sec:variance`. -/
theorem sorted_cases {a b c d : ℝ} (hab : a < b) (hcd : c < d) (had : a < d) (hcb : c < b)
    (hac : a ≠ c) (hbd : b ≠ d) :
    (a < c ∧ c < b ∧ b < d) ∨ (a < c ∧ c < d ∧ d < b) ∨ (c < a ∧ a < b ∧ b < d) ∨
      (c < a ∧ a < d ∧ d < b) := by
  rcases lt_or_gt_of_ne hac with h1 | h1 <;> rcases lt_or_gt_of_ne hbd with h2 | h2
  · exact Or.inl ⟨h1, hcb, h2⟩
  · exact Or.inr (Or.inl ⟨h1, hcd, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, hab, h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, had, h2⟩))

/-- Every scale in `(0,1]` sits in exactly one dyadic bracket `(2^{-j-1}, 2^{-j}]`. -/
theorem exists_dyadic_bracket {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∃ j : ℕ, ((1:ℝ)/2) ^ j / 2 < t ∧ t ≤ ((1:ℝ)/2) ^ j := by
  classical
  have hex : ∃ n : ℕ, ((1:ℝ)/2) ^ (n + 1) < t := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 (by norm_num : (1:ℝ)/2 < 1)
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
  refine ⟨Nat.find hex, ?_, ?_⟩
  · have := Nat.find_spec hex
    have hrw : ((1:ℝ)/2) ^ (Nat.find hex + 1) = ((1:ℝ)/2) ^ Nat.find hex / 2 := by ring
    linarith [hrw ▸ this]
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h]
      simpa using h1
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin := not_lt.mp (Nat.find_min hex (m := k) (by omega))
      rw [hk]
      exact hmin

/-- A sorted quadruple of times in `[0,1]` lies in one of the dyadic blocks. -/
theorem mem_block_of_sorted {x₁ x₂ x₃ x₄ : ℝ} (h0 : 0 ≤ x₁) (h12 : x₁ < x₂) (h23 : x₂ < x₃)
    (h34 : x₃ < x₄) (h1 : x₄ ≤ 1) : ∃ j l : ℕ, (x₁, x₂, x₃, x₄) ∈ blockSet j l := by
  obtain ⟨j, hj1, hj2⟩ := exists_dyadic_bracket (by linarith : (0:ℝ) < x₃ - x₂) (by linarith)
  obtain ⟨l, hl1, hl2⟩ :=
    exists_dyadic_bracket (by linarith : (0:ℝ) < (x₂ - x₁) + (x₄ - x₃)) (by linarith)
  exact ⟨j, l, h12, h23, h34, hj1, hj2, hl1, hl2⟩

/-- A permutation realises one of the two overlapping pairings of `sec:variance`: the
two increments carried by a labelled quadruple are those of the crossing pairing
`[x₁,x₃], [x₂,x₄]` or of the nested pairing `[x₁,x₄], [x₂,x₃]` of the permuted quadruple.
This is a relabelling, so it is a property of the permutation alone. -/
def IsPairing {α : Type*} (F : ℝ → ℝ → ℝ → ℝ → α) (σ : Equiv.Perm (Fin 4)) : Prop :=
  (∀ q : ℝ × ℝ × ℝ × ℝ, F q.1 q.2.1 q.2.2.1 q.2.2.2
      = F (perm4 σ q).1 (perm4 σ q).2.2.1 (perm4 σ q).2.1 (perm4 σ q).2.2.2) ∨
  (∀ q : ℝ × ℝ × ℝ × ℝ, F q.1 q.2.1 q.2.2.1 q.2.2.2
      = F (perm4 σ q).1 (perm4 σ q).2.2.2 (perm4 σ q).2.1 (perm4 σ q).2.2.1)

/-- The leaf of the sorting case analysis: a permutation carrying the labelled quadruple
to a sorted one in `[0,1]`, together with the pairing it realises.  The pairing identity
is a relabelling, so it holds at every quadruple, not only at `p`. -/
theorem exists_of_sorted {α : Type*} {F : ℝ → ℝ → ℝ → ℝ → α} {p : ℝ × ℝ × ℝ × ℝ}
    (σ : Equiv.Perm (Fin 4)) {x₁ x₂ x₃ x₄ : ℝ} (hp : perm4 σ p = (x₁, x₂, x₃, x₄))
    (h0 : 0 ≤ x₁) (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄) (h1 : x₄ ≤ 1)
    (hF : (∀ q : ℝ × ℝ × ℝ × ℝ, F q.1 q.2.1 q.2.2.1 q.2.2.2
            = F (perm4 σ q).1 (perm4 σ q).2.2.1 (perm4 σ q).2.1 (perm4 σ q).2.2.2) ∨
      (∀ q : ℝ × ℝ × ℝ × ℝ, F q.1 q.2.1 q.2.2.1 q.2.2.2
            = F (perm4 σ q).1 (perm4 σ q).2.2.2 (perm4 σ q).2.1 (perm4 σ q).2.2.1)) :
    ∃ τ : Equiv.Perm (Fin 4),
      IsPairing F τ ∧
      ∃ j l : ℕ, perm4 τ p ∈ blockSet j l := by
  obtain ⟨j, l, hjl⟩ := mem_block_of_sorted h0 h12 h23 h34 h1
  exact ⟨σ, hF, j, l, by rw [hp]; exact hjl⟩

/-- The covering step of `thm:four-point-integral`: off the four crossing ties and off
the null set where a time leaves `[0,1]`, a labelled quadruple with overlapping intervals
is a permutation of a sorted quadruple in a dyadic block, and the two increments it
carries are the crossing or the nested pairing of that sorted quadruple.  `F` stands for
any quantity that sees the two time pairs unordered. -/
theorem cover_mem {α : Type*} (F : ℝ → ℝ → ℝ → ℝ → α)
    (hswapL : ∀ t u t' u' : ℝ, F t u t' u' = F u t t' u')
    (hswapR : ∀ t u t' u' : ℝ, F t u t' u' = F t u u' t')
    (hswapP : ∀ t u t' u' : ℝ, F t u t' u' = F t' u' t u)
    {p : ℝ × ℝ × ℝ × ℝ} (hov : 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hu : p ∈ unitSet) (ht : p ∉ tieSet) :
    ∃ σ : Equiv.Perm (Fin 4),
      IsPairing F σ ∧
      ∃ j l : ℕ, perm4 σ p ∈ blockSet j l := by
  have hz0 : (0:ℝ) ≤ p.1 := (hu 0).1
  have hz1 : (0:ℝ) ≤ p.2.1 := (hu 1).1
  have hz2 : (0:ℝ) ≤ p.2.2.1 := (hu 2).1
  have hz3 : (0:ℝ) ≤ p.2.2.2 := (hu 3).1
  have ho0 : p.1 ≤ 1 := (hu 0).2
  have ho1 : p.2.1 ≤ 1 := (hu 1).2
  have ho2 : p.2.2.1 ≤ 1 := (hu 2).2
  have ho3 : p.2.2.2 ≤ 1 := (hu 3).2
  simp only [tieSet, Set.mem_union, Set.mem_setOf_eq, not_or] at ht
  obtain ⟨⟨⟨hne13, hne14⟩, hne23⟩, hne24⟩ := ht
  have hlt := overlap_lt hov
  have hA : min p.1 p.2.1 < max p.1 p.2.1 :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlt (min_le_left _ _))
  have hB : min p.2.2.1 p.2.2.2 < max p.2.2.1 p.2.2.2 :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlt (min_le_right _ _))
  have hC : min p.1 p.2.1 < max p.2.2.1 p.2.2.2 :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlt (min_le_right _ _))
  have hD : min p.2.2.1 p.2.2.2 < max p.1 p.2.1 :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlt (min_le_left _ _))
  rcases le_total p.1 p.2.1 with h12 | h12 <;> rcases le_total p.2.2.1 p.2.2.2 with h34 | h34
  · rw [min_eq_left h12, max_eq_right h12] at hA
    rw [min_eq_left h34, max_eq_right h34] at hB
    rw [min_eq_left h12, max_eq_right h34] at hC
    rw [min_eq_left h34, max_eq_right h12] at hD
    rcases sorted_cases hA hB hC hD hne13 hne24 with ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩ |
      ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![0, 2, 1, 3] (by decide))
        (x₁ := p.1) (x₂ := p.2.2.1) (x₃ := p.2.1) (x₄ := p.2.2.2) rfl hz0 o1 o2 o3 ho3
        (Or.inl (fun _ => rfl))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![0, 2, 3, 1] (by decide))
        (x₁ := p.1) (x₂ := p.2.2.1) (x₃ := p.2.2.2) (x₄ := p.2.1) rfl hz0 o1 o2 o3 ho1
        (Or.inr (fun _ => rfl))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![2, 0, 1, 3] (by decide))
        (x₁ := p.2.2.1) (x₂ := p.1) (x₃ := p.2.1) (x₄ := p.2.2.2) rfl hz2 o1 o2 o3 ho3
        (Or.inr (fun _ => hswapP _ _ _ _))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![2, 0, 3, 1] (by decide))
        (x₁ := p.2.2.1) (x₂ := p.1) (x₃ := p.2.2.2) (x₄ := p.2.1) rfl hz2 o1 o2 o3 ho1
        (Or.inl (fun _ => hswapP _ _ _ _))
  · rw [min_eq_left h12, max_eq_right h12] at hA
    rw [min_eq_right h34, max_eq_left h34] at hB
    rw [min_eq_left h12, max_eq_left h34] at hC
    rw [min_eq_right h34, max_eq_right h12] at hD
    rcases sorted_cases hA hB hC hD hne14 hne23 with ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩ |
      ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![0, 3, 1, 2] (by decide))
        (x₁ := p.1) (x₂ := p.2.2.2) (x₃ := p.2.1) (x₄ := p.2.2.1) rfl hz0 o1 o2 o3 ho2
        (Or.inl (fun _ => hswapR _ _ _ _))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![0, 3, 2, 1] (by decide))
        (x₁ := p.1) (x₂ := p.2.2.2) (x₃ := p.2.2.1) (x₄ := p.2.1) rfl hz0 o1 o2 o3 ho1
        (Or.inr (fun _ => hswapR _ _ _ _))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![3, 0, 1, 2] (by decide))
        (x₁ := p.2.2.2) (x₂ := p.1) (x₃ := p.2.1) (x₄ := p.2.2.1) rfl hz3 o1 o2 o3 ho2
        (Or.inr (fun _ => (hswapP _ _ _ _).trans (hswapL _ _ _ _)))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![3, 0, 2, 1] (by decide))
        (x₁ := p.2.2.2) (x₂ := p.1) (x₃ := p.2.2.1) (x₄ := p.2.1) rfl hz3 o1 o2 o3 ho1
        (Or.inl (fun _ => (hswapP _ _ _ _).trans (hswapL _ _ _ _)))
  · rw [min_eq_right h12, max_eq_left h12] at hA
    rw [min_eq_left h34, max_eq_right h34] at hB
    rw [min_eq_right h12, max_eq_right h34] at hC
    rw [min_eq_left h34, max_eq_left h12] at hD
    rcases sorted_cases hA hB hC hD hne23 hne14 with ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩ |
      ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![1, 2, 0, 3] (by decide))
        (x₁ := p.2.1) (x₂ := p.2.2.1) (x₃ := p.1) (x₄ := p.2.2.2) rfl hz1 o1 o2 o3 ho3
        (Or.inl (fun _ => hswapL _ _ _ _))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![1, 2, 3, 0] (by decide))
        (x₁ := p.2.1) (x₂ := p.2.2.1) (x₃ := p.2.2.2) (x₄ := p.1) rfl hz1 o1 o2 o3 ho0
        (Or.inr (fun _ => hswapL _ _ _ _))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![2, 1, 0, 3] (by decide))
        (x₁ := p.2.2.1) (x₂ := p.2.1) (x₃ := p.1) (x₄ := p.2.2.2) rfl hz2 o1 o2 o3 ho3
        (Or.inr (fun _ => (hswapP _ _ _ _).trans (hswapR _ _ _ _)))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![2, 1, 3, 0] (by decide))
        (x₁ := p.2.2.1) (x₂ := p.2.1) (x₃ := p.2.2.2) (x₄ := p.1) rfl hz2 o1 o2 o3 ho0
        (Or.inl (fun _ => (hswapP _ _ _ _).trans (hswapR _ _ _ _)))
  · rw [min_eq_right h12, max_eq_left h12] at hA
    rw [min_eq_right h34, max_eq_left h34] at hB
    rw [min_eq_right h12, max_eq_left h34] at hC
    rw [min_eq_right h34, max_eq_left h12] at hD
    rcases sorted_cases hA hB hC hD hne24 hne13 with ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩ |
      ⟨o1, o2, o3⟩ | ⟨o1, o2, o3⟩
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![1, 3, 0, 2] (by decide))
        (x₁ := p.2.1) (x₂ := p.2.2.2) (x₃ := p.1) (x₄ := p.2.2.1) rfl hz1 o1 o2 o3 ho2
        (Or.inl (fun _ => (hswapL _ _ _ _).trans (hswapR _ _ _ _)))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![1, 3, 2, 0] (by decide))
        (x₁ := p.2.1) (x₂ := p.2.2.2) (x₃ := p.2.2.1) (x₄ := p.1) rfl hz1 o1 o2 o3 ho0
        (Or.inr (fun _ => (hswapL _ _ _ _).trans (hswapR _ _ _ _)))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![3, 1, 0, 2] (by decide))
        (x₁ := p.2.2.2) (x₂ := p.2.1) (x₃ := p.1) (x₄ := p.2.2.1) rfl hz3 o1 o2 o3 ho2
        (Or.inr (fun _ => ((hswapP _ _ _ _).trans (hswapL _ _ _ _)).trans (hswapR _ _ _ _)))
    · exact exists_of_sorted (F := F) (Equiv.ofBijective ![3, 1, 2, 0] (by decide))
        (x₁ := p.2.2.2) (x₂ := p.2.1) (x₃ := p.2.2.1) (x₄ := p.1) rfl hz3 o1 o2 o3 ho0
        (Or.inl (fun _ => ((hswapP _ _ _ _).trans (hswapL _ _ _ _)).trans (hswapR _ _ _ _)))

/-! ### The cover, integrated -/

/-- The set of quadruples with all four times in `[0,1]` is measurable. -/
theorem measurableSet_unitSet : MeasurableSet unitSet := by
  have h : unitSet = ⋂ i : Fin 4, (fun p : ℝ × ℝ × ℝ × ℝ => coord p i) ⁻¹' (Set.Icc (0:ℝ) 1) := by
    rw [unitSet, Set.setOf_forall]
    rfl
  rw [h]
  exact MeasurableSet.iInter (fun i =>
    ((measurable_pi_apply i).comp measurable_coord) measurableSet_Icc)

open scoped Classical in
/-- The piece of the cover attached to a permutation and a dyadic pair: the quadruples
in `[0,1]⁴` that the permutation carries into the block, and empty unless the
permutation realises one of the two overlapping pairings. -/
noncomputable def piece {α : Type*} (F : ℝ → ℝ → ℝ → ℝ → α)
    (x : Equiv.Perm (Fin 4) × ℕ × ℕ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  if IsPairing F x.1 then (perm4 x.1) ⁻¹' (blockSet x.2.1 x.2.2) ∩ unitSet else ∅

/-- Permuting the four times is measurable. -/
theorem measurable_perm4 (σ : Equiv.Perm (Fin 4)) : Measurable (perm4 σ) :=
  (((measurable_pi_apply (σ 0)).comp measurable_coord).prodMk
    (((measurable_pi_apply (σ 1)).comp measurable_coord).prodMk
      (((measurable_pi_apply (σ 2)).comp measurable_coord).prodMk
        ((measurable_pi_apply (σ 3)).comp measurable_coord))))

/-- Each piece is measurable. -/
theorem measurableSet_piece {α : Type*} (F : ℝ → ℝ → ℝ → ℝ → α)
    (x : Equiv.Perm (Fin 4) × ℕ × ℕ) : MeasurableSet (piece F x) := by
  classical
  rw [piece]
  split_ifs
  · exact (measurable_perm4 x.1 (measurableSet_blockSet x.2.1 x.2.2)).inter measurableSet_unitSet
  · exact MeasurableSet.empty

/-- Each piece sits inside the permuted block. -/
theorem piece_subset {α : Type*} (F : ℝ → ℝ → ℝ → ℝ → α) (x : Equiv.Perm (Fin 4) × ℕ × ℕ) :
    piece F x ⊆ (perm4 x.1) ⁻¹' (blockSet x.2.1 x.2.2) := by
  classical
  rw [piece]
  split_ifs
  · exact Set.inter_subset_left
  · exact Set.empty_subset _

omit [IsProbabilityMeasure μ] in
/-- A countable cover by measurable pieces, off a null set, with the integrand bounded on
each piece, bounds the integral by the sum of the products. -/
theorem lintegral_le_tsum {ι : Type*} [Countable ι] (f : ℝ × ℝ × ℝ × ℝ → ℝ≥0∞)
    (E : Set (ℝ × ℝ × ℝ × ℝ)) (S : ι → Set (ℝ × ℝ × ℝ × ℝ)) (N : Set (ℝ × ℝ × ℝ × ℝ))
    (c : ι → ℝ≥0∞) (hcover : E ⊆ (⋃ i, S i) ∪ N)
    (hN : (μ.prod (μ.prod (μ.prod μ))) N = 0) (hmeas : ∀ i, MeasurableSet (S i))
    (hf : ∀ i, ∀ p ∈ S i, f p ≤ c i) :
    ∫⁻ p in E, f p ∂(μ.prod (μ.prod (μ.prod μ)))
      ≤ ∑' i, c i * (μ.prod (μ.prod (μ.prod μ))) (S i) := by
  calc ∫⁻ p in E, f p ∂(μ.prod (μ.prod (μ.prod μ)))
      ≤ ∫⁻ p in (⋃ i, S i) ∪ N, f p ∂(μ.prod (μ.prod (μ.prod μ))) :=
        lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
    _ ≤ ∫⁻ p in ⋃ i, S i, f p ∂(μ.prod (μ.prod (μ.prod μ)))
        + ∫⁻ p in N, f p ∂(μ.prod (μ.prod (μ.prod μ))) := lintegral_union_le _ _ _
    _ = ∫⁻ p in ⋃ i, S i, f p ∂(μ.prod (μ.prod (μ.prod μ))) := by
        rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ ∑' i, ∫⁻ p in S i, f p ∂(μ.prod (μ.prod (μ.prod μ))) := lintegral_iUnion_le _ _
    _ ≤ ∑' i, c i * (μ.prod (μ.prod (μ.prod μ))) (S i) := by
        refine ENNReal.tsum_le_tsum (fun i => ?_)
        calc ∫⁻ p in S i, f p ∂(μ.prod (μ.prod (μ.prod μ)))
            ≤ ∫⁻ _ in S i, c i ∂(μ.prod (μ.prod (μ.prod μ))) := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_restrict_mem (hmeas i)] with p hp
              exact hf i p hp
          _ = c i * (μ.prod (μ.prod (μ.prod μ))) (S i) := setLIntegral_const _ _

/-- The variance scale `eq:variance-scale` is non-negative on `(0,1]`. -/
theorem varScale_nonneg {s r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : 0 ≤ varScale s r := by
  rw [varScale]
  split_ifs
  · exact Real.rpow_nonneg hr0.le _
  · have hlog : 0 ≤ Real.log r⁻¹ := by
      rw [Real.log_inv]
      linarith [Real.log_nonpos hr0.le hr1]
    exact mul_nonneg (Real.rpow_nonneg hr0.le _) (by linarith)
  · exact Real.rpow_nonneg hr0.le _

/-! ### The joint return probability sees the two pairs unordered -/

variable {Ω : Type*} [MeasurableSpace Ω]

omit [IsProbabilityMeasure μ] in
/-- The joint return probability is symmetric in the endpoints of the first interval. -/
theorem jointReturn_swap_left {P : Measure Ω} (W : ℝ≥0 → Ω → Plane) (r : ℝ) (t u t' u' : ℝ) :
    jointReturn W P r t.toNNReal u.toNNReal t'.toNNReal u'.toNNReal
      = jointReturn W P r u.toNNReal t.toNNReal t'.toNNReal u'.toNNReal := by
  unfold jointReturn
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [dist_comm (W u.toNNReal ω) (W t.toNNReal ω)]

omit [IsProbabilityMeasure μ] in
/-- The joint return probability is symmetric in the endpoints of the second interval. -/
theorem jointReturn_swap_right {P : Measure Ω} (W : ℝ≥0 → Ω → Plane) (r : ℝ) (t u t' u' : ℝ) :
    jointReturn W P r t.toNNReal u.toNNReal t'.toNNReal u'.toNNReal
      = jointReturn W P r t.toNNReal u.toNNReal u'.toNNReal t'.toNNReal := by
  unfold jointReturn
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [dist_comm (W u'.toNNReal ω) (W t'.toNNReal ω)]

omit [IsProbabilityMeasure μ] in
/-- The joint return probability is symmetric in the two intervals. -/
theorem jointReturn_swap_pairs {P : Measure Ω} (W : ℝ≥0 → Ω → Plane) (r : ℝ) (t u t' u' : ℝ) :
    jointReturn W P r t.toNNReal u.toNNReal t'.toNNReal u'.toNNReal
      = jointReturn W P r t'.toNNReal u'.toNNReal t.toNNReal u.toNNReal := by
  unfold jointReturn
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  exact and_comm

end FourPointIntegral

set_option linter.unusedVariables false in
open FourPointIntegral in
/-- `thm:four-point-integral`, `eq:four-point-integral`: the joint return probability
integrates over the overlap set to `O(V_s(r))`.  The hypothesis is the conclusion of
`thm:endpoint-block-mass` at the dyadic values, `audit_endpoint_block_mass_dyadic`; the
proof is the covering of the overlap set by the permuted dyadic blocks and the four
dyadic sums of `thm:four-point-integral`. -/
theorem four_point_integral_of_block {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ)
    (hblock : ∃ C > 0, ∀ j l : ℕ,
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
          ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}
        ≤ ENNReal.ofReal (C * (((1:ℝ)/2) ^ j) ^ s * (((1:ℝ)/2) ^ l) ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        ((1:ℝ)/2) ^ j / 2 < x₃ - x₂ → x₃ - x₂ ≤ ((1:ℝ)/2) ^ j →
        ((1:ℝ)/2) ^ l / 2 < (x₂ - x₁) + (x₄ - x₃) →
        (x₂ - x₁) + (x₄ - x₃) ≤ ((1:ℝ)/2) ^ l →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l)))) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ p : ℝ × ℝ × ℝ × ℝ in {p | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2},
        jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
        ∂(μ.prod (μ.prod (μ.prod μ)))
      ≤ ENNReal.ofReal (C * varScale s r) := by
  classical
  obtain ⟨K, hK0, hK⟩ := hblock
  obtain ⟨D, hD0, hD⟩ := tsum_master_le hs0 hs1
  have hcard : (0:ℝ) < (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨(Fintype.card (Equiv.Perm (Fin 4)) : ℝ) * (K * K * D),
    mul_pos hcard (by positivity), ?_⟩
  intro r hr0 hr1
  set F : ℝ → ℝ → ℝ → ℝ → ℝ≥0∞ := fun t u t' u' =>
    jointReturn W P r t.toNNReal u.toNNReal t'.toNNReal u'.toNNReal with hFdef
  have hswapL : ∀ t u t' u' : ℝ, F t u t' u' = F u t t' u' := fun t u t' u' =>
    jointReturn_swap_left W r t u t' u'
  have hswapR : ∀ t u t' u' : ℝ, F t u t' u' = F t u u' t' := fun t u t' u' =>
    jointReturn_swap_right W r t u t' u'
  have hswapP : ∀ t u t' u' : ℝ, F t u t' u' = F t' u' t u := fun t u t' u' =>
    jointReturn_swap_pairs W r t u t' u'
  have hmin0 : ∀ j l : ℕ, (0:ℝ) ≤ min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
      (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) := fun j l =>
    le_min zero_le_one (le_min (by positivity) (by positivity))
  have hcover : {p : ℝ × ℝ × ℝ × ℝ | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2}
      ⊆ (⋃ x : Equiv.Perm (Fin 4) × ℕ × ℕ, piece F x) ∪ (unitSetᶜ ∪ tieSet) := by
    intro p hp
    by_cases hu : p ∈ unitSet
    · by_cases ht : p ∈ tieSet
      · exact Or.inr (Or.inr ht)
      · obtain ⟨σ, hpair, j, l, hjl⟩ := cover_mem F hswapL hswapR hswapP hp hu ht
        refine Or.inl (Set.mem_iUnion.2 ⟨(σ, j, l), ?_⟩)
        rw [piece, if_pos hpair]
        exact ⟨hjl, hu⟩
    · exact Or.inr (Or.inl hu)
  have hN : (μ.prod (μ.prod (μ.prod μ))) (unitSetᶜ ∪ tieSet) = 0 :=
    measure_union_null (measure_unitSet_compl hμ) (measure_tieSet hs0 hμ)
  have hbound : ∀ x : Equiv.Perm (Fin 4) × ℕ × ℕ, ∀ p ∈ piece F x,
      jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
        ≤ ENNReal.ofReal (K * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
            (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2)))) := by
    rintro ⟨σ, j, l⟩ p hp
    rw [piece] at hp
    split_ifs at hp with hpair
    · obtain ⟨hb, hu⟩ := hp
      obtain ⟨h12, h23, h34, hj1, hj2, hl1, hl2⟩ := hb
      have h0 : 0 ≤ (perm4 σ p).1 := (hu (σ 0)).1
      have hret := (hK j l).2 r hr0 (perm4 σ p).1 (perm4 σ p).2.1 (perm4 σ p).2.2.1
        (perm4 σ p).2.2.2 h0 h12 h23 h34 hj1 hj2 hl1 hl2
      rcases hpair with hp1 | hp1
      · have hEq : jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal
            p.2.2.2.toNNReal
            = jointReturn W P r (perm4 σ p).1.toNNReal (perm4 σ p).2.2.1.toNNReal
              (perm4 σ p).2.1.toNNReal (perm4 σ p).2.2.2.toNNReal := hp1 p
        rw [hEq]
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P _)
          (mul_nonneg hK0.le (hmin0 j l))).2 hret.1
      · have hEq : jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal
            p.2.2.2.toNNReal
            = jointReturn W P r (perm4 σ p).1.toNNReal (perm4 σ p).2.2.2.toNNReal
              (perm4 σ p).2.1.toNNReal (perm4 σ p).2.2.1.toNNReal := hp1 p
        rw [hEq]
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P _)
          (mul_nonneg hK0.le (hmin0 j l))).2 hret.2
    · exact absurd hp (by simp)
  have hmass : ∀ x : Equiv.Perm (Fin 4) × ℕ × ℕ,
      (μ.prod (μ.prod (μ.prod μ))) (piece F x)
        ≤ ENNReal.ofReal (K * (((1:ℝ)/2) ^ x.2.1) ^ s * (((1:ℝ)/2) ^ x.2.2) ^ (2 * s)) := by
    intro x
    calc (μ.prod (μ.prod (μ.prod μ))) (piece F x)
        ≤ (μ.prod (μ.prod (μ.prod μ))) ((perm4 x.1) ⁻¹' (blockSet x.2.1 x.2.2)) :=
          measure_mono (piece_subset F x)
      _ = (μ.prod (μ.prod (μ.prod μ))) (blockSet x.2.1 x.2.2) :=
          (measurePreserving_perm4 x.1).measure_preimage
            (measurableSet_blockSet _ _).nullMeasurableSet
      _ ≤ _ := (hK x.2.1 x.2.2).1
  refine le_trans (lintegral_le_tsum _ _ (piece F) (unitSetᶜ ∪ tieSet)
    (fun x => ENNReal.ofReal (K * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
      (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2))))) hcover hN
    (measurableSet_piece F) hbound) ?_
  have hterm : ∀ x : Equiv.Perm (Fin 4) × ℕ × ℕ,
      ENNReal.ofReal (K * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
          (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2))))
        * ENNReal.ofReal (K * (((1:ℝ)/2) ^ x.2.1) ^ s * (((1:ℝ)/2) ^ x.2.2) ^ (2 * s))
      = (ENNReal.ofReal K * ENNReal.ofReal K)
        * (ENNReal.ofReal (min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
            (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2))))
          * ENNReal.ofReal ((((1:ℝ)/2) ^ x.2.1) ^ s * (((1:ℝ)/2) ^ x.2.2) ^ (2 * s))) := by
    intro x
    rw [ENNReal.ofReal_mul hK0.le, mul_assoc K, ENNReal.ofReal_mul hK0.le]
    ring
  calc ∑' x : Equiv.Perm (Fin 4) × ℕ × ℕ,
        ENNReal.ofReal (K * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
          (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2))))
          * (μ.prod (μ.prod (μ.prod μ))) (piece F x)
      ≤ ∑' x : Equiv.Perm (Fin 4) × ℕ × ℕ,
          ENNReal.ofReal (K * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
            (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2))))
            * ENNReal.ofReal (K * (((1:ℝ)/2) ^ x.2.1) ^ s * (((1:ℝ)/2) ^ x.2.2) ^ (2 * s)) := by
        exact ENNReal.tsum_le_tsum (fun x => by gcongr; exact hmass x)
    _ = (ENNReal.ofReal K * ENNReal.ofReal K) * ∑' x : Equiv.Perm (Fin 4) × ℕ × ℕ,
          (ENNReal.ofReal (min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ x.2.1 + ((1:ℝ)/2) ^ x.2.2))
              (r ^ 4 / (((1:ℝ)/2) ^ x.2.1 * ((1:ℝ)/2) ^ x.2.2))))
            * ENNReal.ofReal ((((1:ℝ)/2) ^ x.2.1) ^ s * (((1:ℝ)/2) ^ x.2.2) ^ (2 * s))) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr hterm
    _ = (ENNReal.ofReal K * ENNReal.ofReal K) * ((Fintype.card (Equiv.Perm (Fin 4)) : ℝ≥0∞)
          * ∑' y : ℕ × ℕ,
            (ENNReal.ofReal (min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ y.1 + ((1:ℝ)/2) ^ y.2))
                (r ^ 4 / (((1:ℝ)/2) ^ y.1 * ((1:ℝ)/2) ^ y.2))))
              * ENNReal.ofReal ((((1:ℝ)/2) ^ y.1) ^ s * (((1:ℝ)/2) ^ y.2) ^ (2 * s)))) := by
        congr 1
        rw [ENNReal.tsum_prod', tsum_fintype]
        simp
    _ ≤ (ENNReal.ofReal K * ENNReal.ofReal K) * ((Fintype.card (Equiv.Perm (Fin 4)) : ℝ≥0∞)
          * ENNReal.ofReal (D * varScale s r)) := by
        gcongr
        exact hD r hr0 hr1
    _ = ENNReal.ofReal ((Fintype.card (Equiv.Perm (Fin 4)) : ℝ) * (K * K * D) * varScale s r) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hK0.le, ← ENNReal.ofReal_mul (mul_nonneg hK0.le hK0.le)]
        congr 1
        ring

/-- `thm:variance`: the four-point variance bound.  Two inputs.  The first
is the dyadic block bound of `thm:endpoint-block-mass`, which `four_point_integral_of_block`
turns into `eq:four-point-integral`.  The second, `hcov`, is the opening sentence of the
proof of `thm:variance`: expanding the variance and applying Fubini writes it as the
`μ⁴`-integral of the covariance of the two return events, that covariance vanishes off the
overlap set because disjoint increments are independent (`disjoint_increments_indep`), and
on the overlap set it is at most the joint return probability.  The Fubini step needs joint
measurability of the process in time and sample point, which this development does not yet
have, so it is carried as a hypothesis. -/
theorem variance_of_block {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ)
    (hblock : ∃ C > 0, ∀ j l : ℕ,
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
          ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}
        ≤ ENNReal.ofReal (C * (((1:ℝ)/2) ^ j) ^ s * (((1:ℝ)/2) ^ l) ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        ((1:ℝ)/2) ^ j / 2 < x₃ - x₂ → x₃ - x₂ ≤ ((1:ℝ)/2) ^ j →
        ((1:ℝ)/2) ^ l / 2 < (x₂ - x₁) + (x₄ - x₃) →
        (x₂ - x₁) + (x₄ - x₃) ≤ ((1:ℝ)/2) ^ l →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))))
    (hcov : ∀ r : ℝ, 0 < r → r ≤ 1 →
      variance (fun ω => (corr (occupation W μ ω) r).toReal) P
        ≤ (∫⁻ p : ℝ × ℝ × ℝ × ℝ in {p | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2},
            jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
            ∂(μ.prod (μ.prod (μ.prod μ)))).toReal) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      variance (fun ω => (corr (occupation W μ ω) r).toReal) P
        ≤ C * varScale s r := by
  obtain ⟨C, hC0, hC⟩ := four_point_integral_of_block hW hs0 hs1 hμ hblock
  refine ⟨C, hC0, fun r hr0 hr1 => ?_⟩
  refine le_trans (hcov r hr0 hr1) ?_
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC r hr0 hr1)) ?_
  exact le_of_eq (ENNReal.toReal_ofReal
    (mul_nonneg hC0.le (FourPointIntegral.varScale_nonneg hr0 hr1)))

/-- `thm:variance` as one statement: the bound of `thm:variance` together with the
`o(r^{4s})` consequence.  The second half is `varScale_div_tendsto_zero`; the first is
`variance_of_block` and carries its two hypotheses. -/
theorem thm_variance_of_block {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ)
    (hblock : ∃ C > 0, ∀ j l : ℕ,
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
          ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}
        ≤ ENNReal.ofReal (C * (((1:ℝ)/2) ^ j) ^ s * (((1:ℝ)/2) ^ l) ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        ((1:ℝ)/2) ^ j / 2 < x₃ - x₂ → x₃ - x₂ ≤ ((1:ℝ)/2) ^ j →
        ((1:ℝ)/2) ^ l / 2 < (x₂ - x₁) + (x₄ - x₃) →
        (x₂ - x₁) + (x₄ - x₃) ≤ ((1:ℝ)/2) ^ l →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))))
    (hcov : ∀ r : ℝ, 0 < r → r ≤ 1 →
      variance (fun ω => (corr (occupation W μ ω) r).toReal) P
        ≤ (∫⁻ p : ℝ × ℝ × ℝ × ℝ in {p | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2},
            jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
            ∂(μ.prod (μ.prod (μ.prod μ)))).toReal) :
    (∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
        variance (fun ω => (corr (occupation W μ ω) r).toReal) P ≤ C * varScale s r) ∧
      Tendsto (fun r : ℝ => varScale s r / r ^ (4 * s)) (𝓝[>] 0) (𝓝 0) :=
  ⟨variance_of_block hW hs0 hs1 hμ hblock hcov, varScale_div_tendsto_zero hs0 hs1⟩

end BrownianImages

