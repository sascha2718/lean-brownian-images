/-
The holomorphic extension of the proof of `thm:remainder-derivative`: on the disc
`|z - p| ≤ p/2`, the functions `M_z = ∑ z(1-z)ⁿ Λ_n(z)` and
`Σ(z) = ∑ z(1-z)ⁿ (1 - b^{n+1})^{-s}`, their difference `Δ`, the bound
`|Δ| ≤ 1296 s α p^{-1-s}` on the disc, and Cauchy's estimate `|Δ'(p)| ≤ 2592 s α p^{-2-s}`.

* `norm_add_norm_one_sub_le`: `|z| + |1 - z| ≤ 1 + p/5` on the disc.
* `incrementBound_kernel`: the increment bound for the level sums of `φ_n`.
* `kernelLimit`, `complexMoment`, `complexMainTerm`, `complexDelta`: `Λ_n`, `M_z`, `Σ(z)`, `Δ`.
* `differentiableOn_complexDelta`, `continuousOn_complexDelta`, `norm_complexDelta_le`,
  `norm_deriv_complexDelta_le`: holomorphy, the sup bound and Cauchy's estimate.
-/
import BrownianImages.FixedDimension.Kernel

namespace BrownianImages

open Filter Set Metric
open scoped Topology

noncomputable section

section Disc

variable {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)

/-- `|z| ≤ 9p/8 + Re(z - p)` on the disc, by `(9/8 + t)² - (5/4 + 2t) = (t + 1/8)²`. -/
theorem norm_le_of_mem_discP' (hp0 : 0 < p) {z : ℂ} (hz : z ∈ discP p) :
    ‖z‖ ≤ 9 * p / 8 + (z - p).re := by
  rw [mem_discP] at hz
  set u := (z - p).re with hu
  set v := (z - p).im with hv
  have hw : u ^ 2 + v ^ 2 ≤ (p / 2) ^ 2 := by
    have := Complex.sq_norm (z - p)
    rw [Complex.normSq_apply] at this
    have h2 : ‖z - p‖ ^ 2 ≤ (p / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith
  have hu0 : -(p / 2) ≤ u := by
    have := Complex.abs_re_le_norm (z - p); rw [← hu] at this
    have := neg_le_of_abs_le this; linarith
  have hz2 : ‖z‖ ^ 2 = (p + u) ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have e1 : z.re = p + u := by simp [hu]
    have e2 : z.im = v := by simp [hv]
    rw [e1, e2]; ring
  have hle : ‖z‖ ^ 2 ≤ (9 * p / 8 + u) ^ 2 := by
    rw [hz2]; nlinarith [sq_nonneg (p / 8 + u)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 hle

/-- `|1 - z| ≤ 1 - p - Re(z - p) + p²/(8(1 - 3p/2))` on the disc. -/
theorem norm_one_sub_le_of_mem_discP' (hp0 : 0 < p) (hp : p ≤ 1/50) {z : ℂ} (hz : z ∈ discP p) :
    ‖1 - z‖ ≤ 1 - p - (z - p).re + p ^ 2 / (8 * (1 - 3 * p / 2)) := by
  rw [mem_discP] at hz
  set u := (z - p).re with hu
  set v := (z - p).im with hv
  have hw : u ^ 2 + v ^ 2 ≤ (p / 2) ^ 2 := by
    have := Complex.sq_norm (z - p)
    rw [Complex.normSq_apply] at this
    have h2 : ‖z - p‖ ^ 2 ≤ (p / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith
  have hu1 : u ≤ p / 2 := by
    have := Complex.abs_re_le_norm (z - p); rw [← hu] at this
    have := le_of_abs_le this; linarith
  set A := 1 - p - u with hA
  have hA0 : 1 - 3 * p / 2 ≤ A := by rw [hA]; linarith
  have hApos : 0 < A := by linarith
  have hz2 : ‖1 - z‖ ^ 2 = A ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have e1 : (1 - z).re = A := by simp [hA, hu]
    have e2 : (1 - z).im = -v := by simp [hv]
    rw [e1, e2]; ring
  -- `sqrt(A² + v²) ≤ A + v²/(2A)`
  have hle : ‖1 - z‖ ^ 2 ≤ (A + v ^ 2 / (2 * A)) ^ 2 := by
    rw [hz2]
    have : (A + v ^ 2 / (2 * A)) ^ 2 = A ^ 2 + v ^ 2 + (v ^ 2 / (2 * A)) ^ 2 := by
      field_simp; ring
    rw [this]; nlinarith [sq_nonneg (v ^ 2 / (2 * A))]
  have h1 : ‖1 - z‖ ≤ A + v ^ 2 / (2 * A) :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle
  have h2 : v ^ 2 / (2 * A) ≤ p ^ 2 / (8 * (1 - 3 * p / 2)) := by
    have hv2 : v ^ 2 ≤ p ^ 2 / 4 := by nlinarith [sq_nonneg u]
    calc v ^ 2 / (2 * A) ≤ (p ^ 2 / 4) / (2 * A) :=
          div_le_div_of_nonneg_right hv2 (by positivity)
      _ ≤ (p ^ 2 / 4) / (2 * (1 - 3 * p / 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      _ = p ^ 2 / (8 * (1 - 3 * p / 2)) := by rw [div_div]; congr 1; ring
  linarith

/-- `|z| + |1 - z| ≤ 1 + p/5` on the disc. -/
theorem norm_add_norm_one_sub_le (hp0 : 0 < p) (hp : p ≤ 1/50) {z : ℂ} (hz : z ∈ discP p) :
    ‖z‖ + ‖1 - z‖ ≤ 1 + p / 5 := by
  have h1 := norm_le_of_mem_discP' hp0 hz
  have h2 := norm_one_sub_le_of_mem_discP' hp0 hp hz
  have h3 : p ^ 2 / (8 * (1 - 3 * p / 2)) ≤ p / 40 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  linarith

end Disc

/-! ### The increment bound for the kernels -/

/-- `B = 1 + p/5` and `r = β B²`. -/
def discB (p : ℝ) : ℝ := 1 + p / 5

def discR (s p : ℝ) : ℝ := betaP s p * discB p ^ 2

/-- The constant `C_n = 4 L_n B²` of the increment bound. -/
def incC (s p : ℝ) (n : ℕ) : ℝ := 4 * kernelLip s p n * discB p ^ 2

theorem hp1_of {p : ℝ} (hp : p ≤ 1/50) : p < 1 := by linarith

section Bounds

variable {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
include hs hs1 hp0 hp

omit hs1 in
theorem alphaP_le_betaP : alphaP s p ≤ betaP s p := by
  unfold alphaP betaP
  exact Real.rpow_le_rpow (by linarith) (by linarith) (inv_nonneg.2 hs.le)

theorem alphaP_le_fifth : alphaP s p ≤ 1 / 5 := by
  have := alphaP_le_sq hs hs1 hp0 hp
  nlinarith

/-- `r = βB² ≤ e^{-3p/(10s)}` and `1 - r ≥ p/4`, `eq:contraction-disc`. -/
theorem discR_le : discR s p ≤ Real.exp (-(3 * p / (10 * s))) := by
  unfold discR discB
  have hβ := betaP_le_exp hs (hp1_of hp)
  have hB : (1 + p / 5) ^ 2 ≤ Real.exp (2 * p / 5) := by
    have h := Real.add_one_le_exp (p / 5)
    have h0 : 0 ≤ 1 + p / 5 := by linarith
    calc (1 + p / 5) ^ 2 ≤ Real.exp (p / 5) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
      _ = Real.exp (2 * p / 5) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc betaP s p * (1 + p / 5) ^ 2 ≤ Real.exp (-(p / (2 * s))) * Real.exp (2 * p / 5) :=
        mul_le_mul hβ hB (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(p / (2 * s)) + 2 * p / 5) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(3 * p / (10 * s))) := by
        apply Real.exp_le_exp.2
        have : 2 * p / 5 ≤ p / (5 * s) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
        have e : p / (2 * s) - p / (5 * s) = 3 * p / (10 * s) := by field_simp; ring
        linarith

omit hs hs1 in
theorem discR_nonneg : 0 ≤ discR s p := by
  unfold discR discB
  have := betaP_nonneg (s := s) (hp1_of hp)
  positivity

theorem discR_lt_one : discR s p < 1 := by
  have := discR_le hs hs1 hp0 hp
  have : Real.exp (-(3 * p / (10 * s))) < 1 := Real.exp_lt_one_iff.2 (by
    have : 0 < 3 * p / (10 * s) := by positivity
    linarith)
  linarith

theorem one_sub_discR_ge : p / 4 ≤ 1 - discR s p := by
  have hr := discR_le hs hs1 hp0 hp
  set x := 3 * p / (10 * s) with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 := one_sub_exp_neg_ge hx0
  have h2 : p / 4 ≤ x / (1 + x) := by
    rcases le_or_gt x 1 with hx1 | hx1
    · have : x / 2 ≤ x / (1 + x) :=
        div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
      have : p / 4 ≤ x / 2 := by
        rw [hx, div_le_div_iff₀ (by norm_num) (by norm_num)]
        have : 3 * p / (10 * s) ≥ 3 * p / 5 := by
          rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
        nlinarith
      linarith
    · have : 1 / 2 ≤ x / (1 + x) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      linarith
  linarith

/-- The increment bound for the level sums of `φ_n` on the disc. -/
theorem incrementBound_kernel (n : ℕ) :
    IncrementBound (ca s) (cb s) (kernelN s n) (discP p) (incC s p n) (discR s p) := by
  intro z hz m
  have hp1 := hp1_of hp
  have ha : ‖ca s z‖ < 1 := by
    have := norm_ca_le hs hp0 hz
    have := alphaP_le_fifth hs hs1 hp0 hp
    linarith
  have hb : ‖cb s z‖ ≤ 1 := (norm_cb_le hs hp1 hz).trans (betaP_lt_one hs hp0 hp1).le
  have hρ : max ‖ca s z‖ ‖cb s z‖ ≤ betaP s p :=
    max_le ((norm_ca_le hs hp0 hz).trans (alphaP_le_betaP hs hp0 hp)) (norm_cb_le hs hp1 hz)
  have hB := norm_add_norm_one_sub_le hp0 hp hz
  have hR₀ : 2 / (1 - ‖ca s z‖) ≤ 5 / 2 := by
    have := norm_ca_le hs hp0 hz
    have := alphaP_le_fifth hs hs1 hp0 hp
    rw [div_le_iff₀ (by linarith)]; linarith
  have h := norm_levelSum_succ_sub_le (ca s) (cb s) (kernelN s n) m ha hb hρ hB hR₀
    (kernelLip_nonneg hs hp0 hp1 n)
    (fun x y x' y' hx hy hx' hy' => norm_kernelN_sub_le hs hs1 hp0 hp n hz x y x' y' hx hy hx' hy')
  calc ‖levelSum (ca s) (cb s) (kernelN s n) (m + 1) z - levelSum (ca s) (cb s) (kernelN s n) m z‖
      ≤ 4 * kernelLip s p n * discB p ^ (2 * m + 2) * betaP s p ^ m := h
    _ = incC s p n * discR s p ^ m := by
        unfold incC discR discB
        rw [mul_pow, ← pow_mul]
        ring

end Bounds

/-! ### The holomorphic functions on the disc -/

/-- `Λ_n(z)`, the limit of the level sums of `φ_n`. -/
def kernelLimit (s : ℝ) (n : ℕ) (z : ℂ) : ℂ := limitSum (ca s) (cb s) (kernelN s n) z

/-- `M_z = ∑_{n≥0} z (1 - z)ⁿ Λ_n(z)`. -/
def complexMoment (s : ℝ) (z : ℂ) : ℂ := ∑' n : ℕ, z * (1 - z) ^ n * kernelLimit s n z

/-- `Σ(z) = ∑_{n≥0} z (1 - z)ⁿ (1 - b(z)^{n+1})^{-s}`. -/
def complexMainTerm (s : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z * (1 - z) ^ n * (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))

/-- `Δ = M_z - Σ(z)`, written as a series. -/
def complexDelta (s : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z * (1 - z) ^ n * (kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ)))

section Holomorphic

variable {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
include hs hs1 hp0 hp

omit hs1 in
theorem one_sub_cb_pow_mem_slitPlane (n : ℕ) {z : ℂ} (hz : z ∈ discP p) :
    1 - cb s z ^ (n + 1) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hp1 := hp1_of hp
  have h1 : ‖cb s z ^ (n + 1)‖ ≤ betaP s p ^ (n + 1) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_cb_le hs hp1 hz) _
  have h2 := Complex.re_le_norm (cb s z ^ (n + 1))
  have h3 := one_sub_betaP_pow_pos hs hp0 hp1 n
  simp only [Complex.sub_re, Complex.one_re]
  linarith

omit hs1 hp0 in
theorem norm_one_sub_cb_pow_ge (n : ℕ) {z : ℂ} (hz : z ∈ discP p) :
    1 - betaP s p ^ (n + 1) ≤ ‖1 - cb s z ^ (n + 1)‖ := by
  have hp1 := hp1_of hp
  have h1 : ‖cb s z ^ (n + 1)‖ ≤ betaP s p ^ (n + 1) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_cb_le hs hp1 hz) _
  have h2 := Complex.re_le_norm (cb s z ^ (n + 1))
  calc 1 - betaP s p ^ (n + 1) ≤ (1 - cb s z ^ (n + 1)).re := by
        simp only [Complex.sub_re, Complex.one_re]; linarith
    _ ≤ ‖1 - cb s z ^ (n + 1)‖ := Complex.re_le_norm _

omit hs1 in
theorem norm_one_sub_cb_pow_cpow_le (n : ℕ) {z : ℂ} (hz : z ∈ discP p) :
    ‖(1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))‖ ≤ (1 - betaP s p) ^ (-s) := by
  have hp1 := hp1_of hp
  rw [norm_cpow_neg_real]
  have h1 := norm_one_sub_cb_pow_ge hs hp n hz
  have h2 : 1 - betaP s p ≤ 1 - betaP s p ^ (n + 1) := by linarith [betaP_pow_le hs hp0 hp1 n]
  have h0 : 0 < 1 - betaP s p := by linarith [betaP_lt_one hs hp0 hp1]
  exact rpow_neg_antitone h0 (h2.trans h1) hs.le

/-- `Λ_n(z) - (1 - b^{n+1})^{-s}` is at most `C_n/(1 - r)` on the disc. -/
theorem norm_kernelLimit_sub_le (n : ℕ) {z : ℂ} (hz : z ∈ discP p) :
    ‖kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))‖ ≤ incC s p n / (1 - discR s p) := by
  have h := norm_limitSum_sub_le (discR_nonneg hp0 hp) (discR_lt_one hs hs1 hp0 hp)
    (incrementBound_kernel hs hs1 hp0 hp n) hz
  have e : kernelN s n z 0 0 = (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ)) := by
    unfold kernelN kernelBase; simp
  rw [kernelLimit, ← e]
  exact h

omit hs1 in
/-- A uniform bound on `C_n/(1 - r)`: `incC s p n ≤ incC s p 0`. -/
theorem incC_le (n : ℕ) : incC s p n ≤ 4 * (s * alphaP s p * ((1 - betaP s p) / 2) ^ (-s - 1)) *
    discB p ^ 2 := by
  unfold incC kernelLip
  have hp1 := hp1_of hp
  have h0 : 0 < (1 - betaP s p) / 2 := by linarith [betaP_lt_one hs hp0 hp1]
  have h2 : (1 - betaP s p) / 2 ≤ (1 - betaP s p ^ (n + 1)) / 2 := by
    linarith [betaP_pow_le hs hp0 hp1 n]
  have h3 : ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) ≤ ((1 - betaP s p) / 2) ^ (-s - 1) := by
    rw [show (-s - 1) = -(s + 1) by ring]
    exact rpow_neg_antitone h0 h2 (by linarith)
  have hα := alphaP_nonneg (s := s) hp0
  have hB : 0 ≤ discB p ^ 2 := by positivity
  calc 4 * (s * alphaP s p * ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1)) * discB p ^ 2
      ≤ 4 * (s * alphaP s p * ((1 - betaP s p) / 2) ^ (-s - 1)) * discB p ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The uniform bound `K` on `|Λ_n|` on the disc. -/
def limitBound (s p : ℝ) : ℝ :=
  (1 - betaP s p) ^ (-s) +
    4 * (s * alphaP s p * ((1 - betaP s p) / 2) ^ (-s - 1)) * discB p ^ 2 / (1 - discR s p)

theorem norm_kernelLimit_le (n : ℕ) {z : ℂ} (hz : z ∈ discP p) :
    ‖kernelLimit s n z‖ ≤ limitBound s p := by
  have h1 := norm_kernelLimit_sub_le hs hs1 hp0 hp n hz
  have h2 := norm_one_sub_cb_pow_cpow_le hs hp0 hp n hz
  have h3 := incC_le hs hp0 hp n
  have hδ : 0 < 1 - discR s p := by linarith [one_sub_discR_ge hs hs1 hp0 hp]
  have h4 : incC s p n / (1 - discR s p)
      ≤ 4 * (s * alphaP s p * ((1 - betaP s p) / 2) ^ (-s - 1)) * discB p ^ 2 / (1 - discR s p) :=
    div_le_div_of_nonneg_right h3 hδ.le
  unfold limitBound
  calc ‖kernelLimit s n z‖
      = ‖(kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))) + (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖kernelLimit s n z - (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))‖ + ‖(1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))‖ :=
        norm_add_le _ _
    _ ≤ _ := by linarith

omit hs hs1 in
theorem norm_term_le (K : ℝ) (n : ℕ) {z : ℂ} (hz : z ∈ discP p) {w : ℂ}
    (hw : ‖w‖ ≤ K) : ‖z * (1 - z) ^ n * w‖ ≤ 3 * p / 2 * (1 - p / 2) ^ n * K := by
  have hp1 := hp1_of hp
  rw [norm_mul, norm_mul, norm_pow]
  have h1 := norm_le_of_mem_discP hp0 hz
  have h2 := norm_one_sub_le_of_mem_discP hp1 hz
  have h3 : ‖1 - z‖ ^ n ≤ (1 - p / 2) ^ n := pow_le_pow_left₀ (norm_nonneg _) h2 n
  calc ‖z‖ * ‖1 - z‖ ^ n * ‖w‖ ≤ (3 * p / 2) * (1 - p / 2) ^ n * K :=
        mul_le_mul (mul_le_mul h1 h3 (by positivity) (by linarith)) hw (norm_nonneg _)
          (mul_nonneg (by positivity) (pow_nonneg (by linarith) n))

omit hs hs1 in
theorem summable_geom_term (K : ℝ) : Summable fun n : ℕ => 3 * p / 2 * (1 - p / 2) ^ n * K := by
  have hp1 := hp1_of hp
  have : Summable fun n : ℕ => (1 - p / 2) ^ n :=
    summable_geometric_of_lt_one (by linarith) (by linarith)
  exact (this.mul_left (3 * p / 2)).mul_right K

theorem differentiableOn_kernelLimit (n : ℕ) :
    DifferentiableOn ℂ (kernelLimit s n) (ball (p : ℂ) (p / 2)) :=
  differentiableOn_limitSum (discR_nonneg hp0 hp) (discR_lt_one hs hs1 hp0 hp)
    (incrementBound_kernel hs hs1 hp0 hp n) isOpen_ball ball_subset_closedBall
    fun m => (differentiableOn_levelSum_kernel hs hs1 hp0 hp n m).mono ball_subset_closedBall

theorem continuousOn_kernelLimit (n : ℕ) : ContinuousOn (kernelLimit s n) (discP p) :=
  continuousOn_limitSum (discR_nonneg hp0 hp) (discR_lt_one hs hs1 hp0 hp)
    (incrementBound_kernel hs hs1 hp0 hp n)
    fun m => (differentiableOn_levelSum_kernel hs hs1 hp0 hp n m).continuousOn

omit hs1 in
theorem differentiableOn_one_sub_cb_pow_cpow (n : ℕ) :
    DifferentiableOn ℂ (fun z => (1 - cb s z ^ (n + 1)) ^ (-(s : ℂ))) (discP p) :=
  ((differentiableOn_const _).sub ((differentiableOn_cb hp0 hp).pow (n + 1))).cpow_const
    fun _ hz => one_sub_cb_pow_mem_slitPlane hs hp0 hp n hz

theorem limitBound_nonneg : 0 ≤ limitBound s p := by
  unfold limitBound
  have hp1 := hp1_of hp
  have := betaP_lt_one hs hp0 hp1
  have hδ : 0 < 1 - discR s p := by linarith [one_sub_discR_ge hs hs1 hp0 hp]
  have := alphaP_nonneg (s := s) hp0
  have h0 : 0 < 1 - betaP s p := by linarith
  positivity

/-- `Δ` is holomorphic on the open disc. -/
theorem differentiableOn_complexDelta :
    DifferentiableOn ℂ (complexDelta s) (ball (p : ℂ) (p / 2)) := by
  unfold complexDelta
  refine Complex.differentiableOn_tsum_of_summable_norm
    (summable_geom_term hp0 hp (incC s p 0 / (1 - discR s p))) ?_ isOpen_ball ?_
  · intro n
    refine (differentiableOn_id.mul ((differentiableOn_const _).sub differentiableOn_id |>.pow n)).mul ?_
    exact ((differentiableOn_kernelLimit hs hs1 hp0 hp n).sub
      ((differentiableOn_one_sub_cb_pow_cpow hs hp0 hp n).mono ball_subset_closedBall))
  · intro n z hz
    have hz' : z ∈ discP p := ball_subset_closedBall hz
    refine norm_term_le hp0 hp _ n hz' ?_
    · refine (norm_kernelLimit_sub_le hs hs1 hp0 hp n hz').trans ?_
      have hδ : 0 < 1 - discR s p := by linarith [one_sub_discR_ge hs hs1 hp0 hp]
      apply div_le_div_of_nonneg_right _ hδ.le
      unfold incC kernelLip
      have hp1 := hp1_of hp
      have h0 : 0 < (1 - betaP s p) / 2 := by linarith [betaP_lt_one hs hp0 hp1]
      have h2 : (1 - betaP s p ^ (0 + 1)) / 2 ≤ (1 - betaP s p ^ (n + 1)) / 2 := by
        simp only [zero_add, pow_one]
        linarith [betaP_pow_le hs hp0 hp1 n]
      have h3 : ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1)
          ≤ ((1 - betaP s p ^ (0 + 1)) / 2) ^ (-s - 1) := by
        rw [show (-s - 1) = -(s + 1) by ring]
        refine rpow_neg_antitone ?_ h2 (by linarith)
        simp only [zero_add, pow_one]; exact h0
      have hα := alphaP_nonneg (s := s) hp0
      have hB : 0 ≤ discB p ^ 2 := by positivity
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `Δ` is continuous on the closed disc. -/
theorem continuousOn_complexDelta : ContinuousOn (complexDelta s) (discP p) := by
  unfold complexDelta
  refine continuousOn_tsum ?_
    (summable_geom_term hp0 hp (incC s p 0 / (1 - discR s p))) ?_
  · intro n
    refine (continuousOn_id.mul ((continuousOn_const.sub continuousOn_id).pow n)).mul ?_
    exact (continuousOn_kernelLimit hs hs1 hp0 hp n).sub
      (differentiableOn_one_sub_cb_pow_cpow hs hp0 hp n).continuousOn
  · intro n z hz
    refine norm_term_le hp0 hp _ n hz ?_
    · refine (norm_kernelLimit_sub_le hs hs1 hp0 hp n hz).trans ?_
      have hδ : 0 < 1 - discR s p := by linarith [one_sub_discR_ge hs hs1 hp0 hp]
      apply div_le_div_of_nonneg_right _ hδ.le
      unfold incC kernelLip
      have hp1 := hp1_of hp
      have h0 : 0 < (1 - betaP s p) / 2 := by linarith [betaP_lt_one hs hp0 hp1]
      have h2 : (1 - betaP s p ^ (0 + 1)) / 2 ≤ (1 - betaP s p ^ (n + 1)) / 2 := by
        simp only [zero_add, pow_one]
        linarith [betaP_pow_le hs hp0 hp1 n]
      have h3 : ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1)
          ≤ ((1 - betaP s p ^ (0 + 1)) / 2) ^ (-s - 1) := by
        rw [show (-s - 1) = -(s + 1) by ring]
        refine rpow_neg_antitone ?_ h2 (by linarith)
        simp only [zero_add, pow_one]; exact h0
      have hα := alphaP_nonneg (s := s) hp0
      have hB : 0 ≤ discB p ^ 2 := by positivity
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left h3 (by positivity)

end Holomorphic

end

end BrownianImages
