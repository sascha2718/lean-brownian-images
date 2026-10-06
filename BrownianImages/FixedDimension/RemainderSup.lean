/-
The sup bound `|Δ| ≤ 1296 s α p^{-1-s}` of the proof of `thm:remainder-derivative` on the
disc, and Cauchy's estimate `|Δ'(p)| ≤ 2592 s α p^{-2-s}`.

* `tsum_rpow_succ_le`: `∑_{n≥0} (n+1)^{-s-1} ≤ 1 + 1/s`, by the antitone Riemann bound.
* `one_sub_betaP_pow_rpow_le`: `(1 - β^{n+1})^{-s-1} ≤ 2^{s+1} (1 + (2s/((n+1)p))^{s+1})`.
* `tsum_disc_le`: `∑ (3p/2)(1 - p/2)ⁿ (1 - β^{n+1})^{-s-1} ≤ 27 p^{-s}`.
* `norm_complexDelta_le`, `norm_deriv_complexDelta_le`: the sup bound and Cauchy's estimate.
-/
import BrownianImages.FixedDimension.RemainderBound
import BrownianImages.FixedDimension.RiemannSum

namespace BrownianImages

open MeasureTheory Filter Set Metric
open scoped Topology

noncomputable section

/-! ### The zeta-type sum -/

/-- `∑_{n≥0} (n+1)^{-s-1} ≤ 1 + 1/s`. -/
theorem tsum_rpow_succ_le {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(s + 1)) ≤ 1 + 1 / s := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(s + 1))) (Ici 1) := by
    intro x hx y _ hxy
    exact rpow_neg_antitone (by linarith [mem_Ici.1 hx]) hxy (by linarith)
  have hnn : ∀ x ∈ Ici (1:ℝ), 0 ≤ x ^ (-(s + 1)) := fun x hx =>
    Real.rpow_nonneg (by linarith [mem_Ici.1 hx]) _
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  obtain ⟨-, -, h⟩ := tsum_le_integral_add one_pos hanti hnn hint
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos] at h
  simp only [one_mul, mul_one] at h
  have e : -(1:ℝ) ^ (-(s + 1) + 1) / (-(s + 1) + 1) = 1 / s := by
    rw [Real.one_rpow, show (-(s + 1) + 1 : ℝ) = -s by ring, neg_div_neg_eq]
  rw [e, Real.one_rpow] at h
  linarith

/-- `(1 - β^{n+1})^{-s-1} ≤ 2^{s+1} (1 + ((n+1)p/(2s))^{-s-1})`. -/
theorem one_sub_betaP_pow_rpow_le {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (1 - betaP s p ^ (n + 1)) ^ (-s - 1)
      ≤ 2 ^ (s + 1) * (1 + (((n:ℝ) + 1) * p / (2 * s)) ^ (-(s + 1))) := by
  set x := ((n:ℝ) + 1) * p / (2 * s) with hx
  have hx0 : 0 < x := by positivity
  -- `β^{n+1} ≤ e^{-x}`
  have hβ : betaP s p ^ (n + 1) ≤ Real.exp (-x) := by
    calc betaP s p ^ (n + 1) ≤ Real.exp (-(p / (2 * s))) ^ (n + 1) :=
          pow_le_pow_left₀ (betaP_nonneg hp1) (betaP_le_exp hs hp1) _
      _ = Real.exp (-x) := by
          rw [← Real.exp_nat_mul]; congr 1; rw [hx]; push_cast; ring
  -- `1 - e^{-x} ≥ ½ min(x, 1)`
  have hmin : min x 1 / 2 ≤ 1 - Real.exp (-x) := by
    have h := one_sub_exp_neg_ge hx0.le
    rcases le_or_gt x 1 with hx1 | hx1
    · rw [min_eq_left hx1]
      have : x / 2 ≤ x / (1 + x) := div_le_div_of_nonneg_left hx0.le (by linarith) (by linarith)
      linarith
    · rw [min_eq_right hx1.le]
      have : 1 / 2 ≤ x / (1 + x) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      linarith
  have hmin0 : 0 < min x 1 / 2 := by
    have := lt_min hx0 one_pos; positivity
  have h1 : (1 - betaP s p ^ (n + 1)) ^ (-s - 1) ≤ (min x 1 / 2) ^ (-s - 1) := by
    rw [show (-s - 1) = -(s + 1) by ring]
    exact rpow_neg_antitone hmin0 (by linarith) (by linarith)
  -- `(min x 1 / 2)^{-s-1} = 2^{s+1} (min x 1)^{-s-1} ≤ 2^{s+1} (1 + x^{-s-1})`
  have h2 : (min x 1 / 2) ^ (-s - 1) = 2 ^ (s + 1) * (min x 1) ^ (-(s + 1)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), show (-s - 1) = -(s + 1) by ring,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have h3 : (min x 1) ^ (-(s + 1)) ≤ 1 + x ^ (-(s + 1)) := by
    rcases le_or_gt x 1 with hx1 | hx1
    · rw [min_eq_left hx1]
      linarith [Real.rpow_nonneg hx0.le (-(s + 1))]
    · rw [min_eq_right hx1.le, Real.one_rpow]
      linarith [Real.rpow_nonneg hx0.le (-(s + 1))]
  calc (1 - betaP s p ^ (n + 1)) ^ (-s - 1) ≤ (min x 1 / 2) ^ (-s - 1) := h1
    _ = 2 ^ (s + 1) * (min x 1) ^ (-(s + 1)) := h2
    _ ≤ 2 ^ (s + 1) * (1 + x ^ (-(s + 1))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

theorem two_rpow_succ_le {s : ℝ} (hs1 : s ≤ 1/2) : (2:ℝ) ^ (s + 1) ≤ 2.83 := by
  have h : (2:ℝ) ^ (s + 1) ≤ (2:ℝ) ^ ((1/2 : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e : (2:ℝ) ^ ((1/2 : ℝ) + 1) = 2 * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]; ring
  have hsqrt : Real.sqrt 2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

theorem four_rpow_succ_le {s : ℝ} (hs1 : s ≤ 1/2) : (4:ℝ) ^ (s + 1) ≤ 8 := by
  have h : (4:ℝ) ^ (s + 1) ≤ (4:ℝ) ^ ((1/2 : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e : (4:ℝ) ^ ((1/2 : ℝ) + 1) = 8 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow,
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  linarith

/-- `∑_{n≥0} (3p/2)(1 - p/2)ⁿ (1 - β^{n+1})^{-s-1} ≤ 27 p^{-s}`. -/
theorem tsum_disc_le {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' n : ℕ, 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)
      ≤ 27 * p ^ (-s) := by
  have hq : 0 ≤ 1 - p / 2 := by linarith
  have hq1 : 1 - p / 2 < 1 := by linarith
  set c := (2 * s / p) ^ (s + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  -- the majorant
  have hmaj : ∀ n : ℕ, 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)
      ≤ 3 * p / 2 * 2 ^ (s + 1) * (1 - p / 2) ^ n
        + 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1)) := by
    intro n
    have h := one_sub_betaP_pow_rpow_le hs hp0 hp1 n
    have hx : (((n:ℝ) + 1) * p / (2 * s)) ^ (-(s + 1)) = c * ((n:ℝ) + 1) ^ (-(s + 1)) := by
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      rw [hc, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity),
        show (((n:ℝ) + 1) * p / (2 * s))⁻¹ = (2 * s / p) * ((n:ℝ) + 1)⁻¹ by field_simp,
        Real.mul_rpow (by positivity) (inv_nonneg.2 hn.le), Real.inv_rpow hn.le,
        ← Real.rpow_neg hn.le]
    have hqn : (1 - p / 2) ^ n ≤ 1 := pow_le_one₀ hq hq1.le
    have hqn0 : 0 ≤ (1 - p / 2) ^ n := by positivity
    calc 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)
        ≤ 3 * p / 2 * (1 - p / 2) ^ n * (2 ^ (s + 1) * (1 + c * ((n:ℝ) + 1) ^ (-(s + 1)))) := by
          rw [hx] at h
          exact mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * p / 2 * 2 ^ (s + 1) * (1 - p / 2) ^ n
          + 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1)) * (1 - p / 2) ^ n := by ring
      _ ≤ 3 * p / 2 * 2 ^ (s + 1) * (1 - p / 2) ^ n
          + 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1)) * 1 := by
          refine add_le_add le_rfl ?_
          apply mul_le_mul_of_nonneg_left hqn
          have := Real.rpow_nonneg (show (0:ℝ) ≤ (n:ℝ) + 1 by positivity) (-(s + 1))
          positivity
      _ = _ := by ring
  have hsum1 : Summable fun n : ℕ => 3 * p / 2 * 2 ^ (s + 1) * (1 - p / 2) ^ n :=
    (summable_geometric_of_lt_one hq hq1).mul_left _
  have hsum2 : Summable fun n : ℕ => 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1)) := by
    have h : Summable fun n : ℕ => ((n:ℝ)) ^ (-(s + 1)) :=
      Real.summable_nat_rpow.2 (by linarith)
    have h' : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-(s + 1)) :=
      (summable_nat_add_iff 1).2 h
    refine (h'.mul_left (3 * p / 2 * 2 ^ (s + 1) * c)).congr fun n => ?_
    push_cast; ring
  have hterm0 : ∀ n : ℕ, 0 ≤ 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) := by
    intro n
    have := one_sub_betaP_pow_pos hs hp0 hp1 n
    positivity
  have hsum0 : Summable fun n : ℕ => 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) :=
    Summable.of_nonneg_of_le hterm0 hmaj (hsum1.add hsum2)
  -- evaluate the majorant sums
  have hS1 : ∑' n : ℕ, 3 * p / 2 * 2 ^ (s + 1) * (1 - p / 2) ^ n = 3 * 2 ^ (s + 1) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, show (1:ℝ) - (1 - p / 2) = p / 2 by ring]
    field_simp
  have hS2 : ∑' n : ℕ, 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1))
      ≤ 3 * p / 2 * 2 ^ (s + 1) * c * (1 + 1 / s) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_rpow_succ_le hs) (by positivity)
  have h2s := two_rpow_succ_le hs1
  have h4s := four_rpow_succ_le hs1
  -- `c = (2s/p)^{s+1} = (2s)^{s+1} p^{-s-1}` and `(2s)^{s+1} ≤ 2^{s+1} s^s s ≤ ...`
  have hc' : 3 * p / 2 * 2 ^ (s + 1) * c * (1 + 1 / s) ≤ 18 * p ^ (-s) := by
    have e : c = (2 * s) ^ (s + 1) * p ^ (-(s + 1)) := by
      rw [hc, div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
        Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
    have hss : (2 * s) ^ (s + 1) ≤ 2 ^ (s + 1) * s := by
      rw [Real.mul_rpow (by norm_num) hs.le, Real.rpow_add hs, Real.rpow_one]
      have h1 : s ^ s ≤ 1 := Real.rpow_le_one hs.le (by linarith) hs.le
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hs.le h1) (by positivity)
    have hp' : p * p ^ (-(s + 1)) = p ^ (-s) := by
      rw [show (-s : ℝ) = 1 + -(s + 1) by ring, Real.rpow_add hp0, Real.rpow_one]
    have hpos : 0 < p ^ (-s) := Real.rpow_pos_of_pos hp0 _
    have h44 : (2:ℝ) ^ (s + 1) * 2 ^ (s + 1) = 4 ^ (s + 1) := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    calc 3 * p / 2 * 2 ^ (s + 1) * c * (1 + 1 / s)
        = 3 / 2 * (2 ^ (s + 1) * (2 * s) ^ (s + 1)) * (p * p ^ (-(s + 1))) * ((s + 1) / s) := by
          rw [e]; field_simp
      _ ≤ 3 / 2 * (2 ^ (s + 1) * (2 ^ (s + 1) * s)) * p ^ (-s) * ((s + 1) / s) := by
          rw [hp']
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hpos.le
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hss (by positivity)
      _ = 3 / 2 * 4 ^ (s + 1) * (s + 1) * p ^ (-s) := by
          rw [← h44]; field_simp
      _ ≤ 3 / 2 * 8 * (3 / 2) * p ^ (-s) := by
          apply mul_le_mul_of_nonneg_right _ hpos.le
          apply mul_le_mul (mul_le_mul_of_nonneg_left h4s (by norm_num)) (by linarith)
            (by linarith) (by positivity)
      _ = 18 * p ^ (-s) := by ring
  have hp1' : 1 ≤ p ^ (-s) := by
    calc (1:ℝ) = 1 ^ (-s) := (Real.one_rpow _).symm
      _ ≤ p ^ (-s) := rpow_neg_antitone hp0 hp1.le hs.le
  calc ∑' n : ℕ, 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)
      ≤ ∑' n : ℕ, (3 * p / 2 * 2 ^ (s + 1) * (1 - p / 2) ^ n
          + 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1))) :=
        hsum0.tsum_le_tsum hmaj (hsum1.add hsum2)
    _ = 3 * 2 ^ (s + 1) + ∑' n : ℕ, 3 * p / 2 * 2 ^ (s + 1) * c * ((n:ℝ) + 1) ^ (-(s + 1)) := by
        rw [hsum1.tsum_add hsum2, hS1]
    _ ≤ 3 * 2.83 + 18 * p ^ (-s) := by linarith
    _ ≤ 27 * p ^ (-s) := by linarith

/-! ### The sup bound and Cauchy's estimate -/

section Sup

variable {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
include hs hs1 hp0 hp

/-- `C_n/(1 - r) ≤ 12 s α (1 - β^{n+1})^{-s-1} · (4/p)`. -/
theorem incC_div_le (n : ℕ) :
    incC s p n / (1 - discR s p)
      ≤ 48 * s * alphaP s p / p * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) := by
  have hp1 := hp1_of hp
  have hδ := one_sub_discR_ge hs hs1 hp0 hp
  have hδ0 : 0 < 1 - discR s p := by linarith
  have hB : discB p ^ 2 ≤ 1.01 := by
    unfold discB
    have : 1 + p / 5 ≤ 1.004 := by linarith
    nlinarith
  have h2s := two_rpow_succ_le hs1
  have hα := alphaP_nonneg (s := s) hp0
  have hpos := one_sub_betaP_pow_pos hs hp0 hp1 n
  have hr : 0 ≤ ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) := by positivity
  -- `L_n = s α 2^{s+1} (1 - β^{n+1})^{-s-1}`
  have hL : kernelLip s p n = s * alphaP s p * 2 ^ (s + 1) * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) := by
    unfold kernelLip
    rw [Real.div_rpow hpos.le (by norm_num), show (-s - 1) = -(s + 1) by ring,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have hr' : 0 ≤ (1 - betaP s p ^ (n + 1)) ^ (-s - 1) := by positivity
  calc incC s p n / (1 - discR s p) ≤ incC s p n / (p / 4) :=
        div_le_div_of_nonneg_left (by unfold incC; have := kernelLip_nonneg hs hp0 hp1 n; positivity)
          (by positivity) hδ
    _ = 4 * kernelLip s p n * discB p ^ 2 * 4 / p := by unfold incC; field_simp
    _ ≤ 4 * (s * alphaP s p * 2.83 * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)) * 1.01 * 4 / p := by
        rw [hL]
        apply div_le_div_of_nonneg_right _ hp0.le
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        apply mul_le_mul _ hB (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ hr'
        exact mul_le_mul_of_nonneg_left h2s (by positivity)
    _ ≤ 48 * s * alphaP s p / p * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hp0.le
        nlinarith [mul_nonneg (mul_nonneg hs.le hα) hr']

/-- `|Δ(z)| ≤ 1296 s α p^{-1-s}` on the disc. -/
theorem norm_complexDelta_le {z : ℂ} (hz : z ∈ discP p) :
    ‖complexDelta s z‖ ≤ 1296 * s * alphaP s p * p ^ (-1 - s) := by
  have hp1 := hp1_of hp
  have hα := alphaP_nonneg (s := s) hp0
  set K := 48 * s * alphaP s p / p with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs.le) hα) hp0.le
  have hterm : ∀ n : ℕ, ‖z * (1 - z) ^ n * (kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ)))‖
      ≤ K * (3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)) := by
    intro n
    have h1 := norm_term_le hp0 hp (incC s p n / (1 - discR s p)) n hz
      (norm_kernelLimit_sub_le hs hs1 hp0 hp n hz)
    have h2 := incC_div_le hs hs1 hp0 hp n
    calc ‖z * (1 - z) ^ n * (kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ)))‖
        ≤ 3 * p / 2 * (1 - p / 2) ^ n * (incC s p n / (1 - discR s p)) := h1
      _ ≤ 3 * p / 2 * (1 - p / 2) ^ n * (K * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (by positivity) (pow_nonneg (by linarith) n))
      _ = K * (3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)) := by ring
  have hmaj : Summable fun n : ℕ => K * (3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)) := by
    have hq : 0 ≤ 1 - p / 2 := by linarith
    have hq1 : 1 - p / 2 < 1 := by linarith
    -- summability from the majorant of `tsum_disc_le`
    have h : Summable fun n : ℕ => 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (((summable_geometric_of_lt_one hq hq1).mul_left (3 * p / 2 * ((1 - betaP s p) / 2) ^ (-s - 1))))
      · have := one_sub_betaP_pow_pos hs hp0 hp1 n; positivity
      · have h0 : 0 < (1 - betaP s p) / 2 := by linarith [betaP_lt_one hs hp0 hp1]
        have h2 : (1 - betaP s p) / 2 ≤ 1 - betaP s p ^ (n + 1) := by
          linarith [betaP_pow_le hs hp0 hp1 n, betaP_nonneg (s := s) hp1]
        have h3 : (1 - betaP s p ^ (n + 1)) ^ (-s - 1) ≤ ((1 - betaP s p) / 2) ^ (-s - 1) := by
          rw [show (-s - 1) = -(s + 1) by ring]
          exact rpow_neg_antitone h0 h2 (by linarith)
        calc 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)
            ≤ 3 * p / 2 * (1 - p / 2) ^ n * ((1 - betaP s p) / 2) ^ (-s - 1) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = 3 * p / 2 * ((1 - betaP s p) / 2) ^ (-s - 1) * (1 - p / 2) ^ n := by ring
    exact h.mul_left K
  have hsum : Summable fun n : ℕ => z * (1 - z) ^ n * (kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))) :=
    Summable.of_norm_bounded hmaj hterm
  calc ‖complexDelta s z‖
      ≤ ∑' n : ℕ, ‖z * (1 - z) ^ n * (kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, K * (3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1)) :=
        hsum.norm.tsum_le_tsum hterm hmaj
    _ = K * ∑' n : ℕ, 3 * p / 2 * (1 - p / 2) ^ n * (1 - betaP s p ^ (n + 1)) ^ (-s - 1) :=
        tsum_mul_left
    _ ≤ K * (27 * p ^ (-s)) := mul_le_mul_of_nonneg_left (tsum_disc_le hs hs1 hp0 hp1) hK0
    _ = 1296 * s * alphaP s p * p ^ (-1 - s) := by
        rw [hK, show (-1 - s) = (-s) + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
        field_simp
        ring

/-- **Cauchy's estimate** for `Δ` at `p`: `|Δ'(p)| ≤ 2592 s α p^{-2-s}`. -/
theorem norm_deriv_complexDelta_le :
    ‖deriv (complexDelta s) (p : ℂ)‖ ≤ 2592 * s * alphaP s p * p ^ (-2 - s) := by
  have hR : 0 < p / 2 := by positivity
  have hd : DiffContOnCl ℂ (complexDelta s) (ball (p : ℂ) (p / 2)) := by
    refine ⟨differentiableOn_complexDelta hs hs1 hp0 hp, ?_⟩
    rw [closure_ball _ hR.ne']
    exact continuousOn_complexDelta hs hs1 hp0 hp
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd
    (C := 1296 * s * alphaP s p * p ^ (-1 - s)) fun z hz =>
      norm_complexDelta_le hs hs1 hp0 hp (sphere_subset_closedBall hz)
  refine h.trans (le_of_eq ?_)
  rw [show (-2 - s) = (-1 - s) + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  field_simp
  ring

end Sup

end

end BrownianImages
