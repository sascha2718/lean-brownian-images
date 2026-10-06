/-
The kernel of the proof of `thm:remainder-derivative`: the complex contractions
`a(z) = z^{1/s}` and `b(z) = (1 - z)^{1/s}`, and
`φ_n(z; x, y) = (1 - b^{n+1} - a (x - b^{n+1} y))^{-s}`, on the disc `|z - p| ≤ p/2`.

* `ca`, `cb`, `kernelBase`, `kernelN`, `alphaP`, `betaP`: the objects, with `ca_ofReal`,
  `cb_ofReal` and `kernelN_ofReal` identifying them at real parameters.
* `norm_ca_le`, `norm_cb_le`, `five_alphaP_le`: `|a| ≤ α = (3p/2)^{1/s}`,
  `|b| ≤ β = (1 - p/2)^{1/s}`, and `eq:alpha-beta`, `5α ≤ (1 - β)/2`.
* `re_kernelBase_ge`, `kernelBase_mem_slitPlane`, `norm_kernelN_le`: the base has real
  part at least `(1 - β^{n+1})/2`, which bounds the kernel, `eq:phi-bounds`.
* `norm_kernelN_sub_le`: the Lipschitz bound on the bidisc of radius `5/2`.
* `differentiableOn_cpointSeq`, `differentiableOn_weightSeq`, `differentiableOn_levelSum`:
  holomorphy of the level sums of the kernel on the disc.
-/
import BrownianImages.FixedDimension.LevelSums
import BrownianImages.FixedDimension.MainTerm

namespace BrownianImages

open Filter Set Metric
open scoped Topology

noncomputable section

/-! ### The objects -/

/-- `a(z) = z^{1/s}`, with the principal branch. -/
def ca (s : ℝ) (z : ℂ) : ℂ := z ^ ((s⁻¹ : ℝ) : ℂ)

/-- `b(z) = (1 - z)^{1/s}`, with the principal branch. -/
def cb (s : ℝ) (z : ℂ) : ℂ := (1 - z) ^ ((s⁻¹ : ℝ) : ℂ)

/-- `α = (3p/2)^{1/s}`, the bound on `|a|` on the disc. -/
def alphaP (s p : ℝ) : ℝ := (3 * p / 2) ^ s⁻¹

/-- `β = (1 - p/2)^{1/s}`, the bound on `|b|` on the disc. -/
def betaP (s p : ℝ) : ℝ := (1 - p / 2) ^ s⁻¹

/-- The base `1 - b^{n+1} - a (x - b^{n+1} y)` of the kernel. -/
def kernelBase (s : ℝ) (n : ℕ) (z x y : ℂ) : ℂ :=
  1 - cb s z ^ (n + 1) - ca s z * (x - cb s z ^ (n + 1) * y)

/-- `φ_n(z; x, y) = (1 - b^{n+1} - a (x - b^{n+1} y))^{-s}`. -/
def kernelN (s : ℝ) (n : ℕ) (z x y : ℂ) : ℂ := kernelBase s n z x y ^ (-(s : ℂ))

/-- The disc `|z - p| ≤ p/2`. -/
def discP (p : ℝ) : Set ℂ := closedBall (p : ℂ) (p / 2)

theorem ca_ofReal {s x : ℝ} (hx : 0 ≤ x) : ca s (x : ℂ) = ((fixedA s x : ℝ) : ℂ) := by
  unfold ca fixedA; rw [Complex.ofReal_cpow hx]

theorem cb_ofReal {s x : ℝ} (hx : x ≤ 1) : cb s (x : ℂ) = ((fixedB s x : ℝ) : ℂ) := by
  unfold cb fixedB
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_cpow (by linarith)]

/-- At a real parameter and real points the kernel is the real power
`(1 - b^{n+1} - a(x - b^{n+1} y))^{-s}`. -/
theorem kernelN_ofReal {s p x y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    kernelN s n (p : ℂ) (x : ℂ) (y : ℂ)
      = (((1 - fixedB s p ^ (n + 1) - fixedA s p * (x - fixedB s p ^ (n + 1) * y)) ^ (-s) : ℝ) : ℂ) := by
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have hb1 := fixedB_le_one hs hp0 hp1
  have hab := fixedA_add_fixedB_lt_one hs hs1 hp0 hp1
  have hbn : fixedB s p ^ (n + 1) ≤ fixedB s p := by
    calc fixedB s p ^ (n + 1) ≤ fixedB s p ^ 1 := pow_le_pow_of_le_one hb0.le hb1 (by omega)
      _ = fixedB s p := pow_one _
  have hbn0 : 0 ≤ fixedB s p ^ (n + 1) := by positivity
  have hbase : 0 ≤ 1 - fixedB s p ^ (n + 1) - fixedA s p * (x - fixedB s p ^ (n + 1) * y) := by
    have h1 : x - fixedB s p ^ (n + 1) * y ≤ 1 := by nlinarith [hx.2, hy.1]
    have h2 : fixedA s p * (x - fixedB s p ^ (n + 1) * y) ≤ fixedA s p * 1 :=
      mul_le_mul_of_nonneg_left h1 ha0.le
    linarith
  unfold kernelN kernelBase
  rw [ca_ofReal hp0.le, cb_ofReal hp1.le, Complex.ofReal_cpow hbase]
  push_cast
  ring_nf

/-! ### Bounds on the disc -/

theorem mem_discP {p : ℝ} {z : ℂ} : z ∈ discP p ↔ ‖z - p‖ ≤ p / 2 := by
  rw [discP, Metric.mem_closedBall, dist_eq_norm]

theorem norm_le_of_mem_discP {p : ℝ} (hp0 : 0 < p) {z : ℂ} (hz : z ∈ discP p) :
    ‖z‖ ≤ 3 * p / 2 := by
  rw [mem_discP] at hz
  calc ‖z‖ = ‖(p : ℂ) + (z - p)‖ := by ring_nf
    _ ≤ ‖(p : ℂ)‖ + ‖z - p‖ := norm_add_le _ _
    _ ≤ p + p / 2 := by rw [Complex.norm_real, Real.norm_of_nonneg hp0.le]; linarith
    _ = 3 * p / 2 := by ring

theorem norm_one_sub_le_of_mem_discP {p : ℝ} (hp1 : p < 1) {z : ℂ}
    (hz : z ∈ discP p) : ‖1 - z‖ ≤ 1 - p / 2 := by
  rw [mem_discP] at hz
  calc ‖1 - z‖ = ‖((1 - p : ℝ) : ℂ) - (z - p)‖ := by push_cast; ring_nf
    _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖z - p‖ := norm_sub_le _ _
    _ ≤ (1 - p) + p / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    _ = 1 - p / 2 := by ring

theorem re_ge_of_mem_discP {p : ℝ} {z : ℂ} (hz : z ∈ discP p) : p / 2 ≤ z.re := by
  rw [mem_discP] at hz
  have h := Complex.abs_re_le_norm (z - p)
  rw [Complex.sub_re, Complex.ofReal_re] at h
  have := neg_le_of_abs_le h
  linarith

theorem re_one_sub_pos_of_mem_discP {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/50) {z : ℂ}
    (hz : z ∈ discP p) : 0 < (1 - z).re := by
  have := Complex.re_le_norm z
  have := norm_le_of_mem_discP hp0 hz
  rw [Complex.sub_re, Complex.one_re]
  linarith

theorem re_pos_of_mem_discP {p : ℝ} (hp0 : 0 < p) {z : ℂ} (hz : z ∈ discP p) : 0 < z.re :=
  lt_of_lt_of_le (by linarith) (re_ge_of_mem_discP hz)

theorem norm_ca_le {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) {z : ℂ} (hz : z ∈ discP p) :
    ‖ca s z‖ ≤ alphaP s p := by
  unfold ca alphaP
  rw [Complex.norm_cpow_real]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_le_of_mem_discP hp0 hz) (inv_nonneg.2 hs.le)

theorem norm_cb_le {s p : ℝ} (hs : 0 < s) (hp1 : p < 1) {z : ℂ} (hz : z ∈ discP p) :
    ‖cb s z‖ ≤ betaP s p := by
  unfold cb betaP
  rw [Complex.norm_cpow_real]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_one_sub_le_of_mem_discP hp1 hz)
    (inv_nonneg.2 hs.le)

theorem alphaP_nonneg {s p : ℝ} (hp0 : 0 < p) : 0 ≤ alphaP s p :=
  Real.rpow_nonneg (by linarith) _

theorem betaP_nonneg {s p : ℝ} (hp1 : p < 1) : 0 ≤ betaP s p :=
  Real.rpow_nonneg (by linarith) _

theorem betaP_lt_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : betaP s p < 1 :=
  Real.rpow_lt_one (by linarith) (by linarith) (inv_pos.2 hs)

/-- `β ≤ e^{-p/(2s)}`. -/
theorem betaP_le_exp {s p : ℝ} (hs : 0 < s) (hp1 : p < 1) :
    betaP s p ≤ Real.exp (-(p / (2 * s))) := by
  unfold betaP
  have h1 : 1 - p / 2 ≤ Real.exp (-(p / 2)) := by
    have := Real.add_one_le_exp (-(p / 2)); linarith
  calc (1 - p / 2) ^ s⁻¹ ≤ Real.exp (-(p / 2)) ^ s⁻¹ :=
        Real.rpow_le_rpow (by linarith) h1 (inv_nonneg.2 hs.le)
    _ = Real.exp (-(p / (2 * s))) := by
        rw [← Real.exp_mul]; congr 1; field_simp

/-- `α ≤ (3p/2)²` for `s ≤ 1/2` and `3p/2 ≤ 1`. -/
theorem alphaP_le_sq {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50) :
    alphaP s p ≤ (3 * p / 2) ^ 2 := by
  unfold alphaP
  have h2 : (2:ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]; linarith
  calc (3 * p / 2) ^ s⁻¹ ≤ (3 * p / 2) ^ (2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) h2
    _ = (3 * p / 2) ^ 2 := by rw [Real.rpow_two]

/-- `1 - e^{-x} ≥ x/(1 + x)`. -/
theorem one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have hpos : 0 < 1 + x := by linarith
  have : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) hpos]
    linarith
  have e : x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
  linarith

/-- `eq:alpha-beta`: `5α ≤ (1 - β)/2` for `0 < s ≤ 1/2` and `0 < p ≤ 1/50`. -/
theorem five_alphaP_le {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50) :
    5 * alphaP s p ≤ (1 - betaP s p) / 2 := by
  have hα := alphaP_le_sq hs hs1 hp0 hp
  have hβ := betaP_le_exp hs (by linarith : p < 1)
  set x := p / (2 * s) with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : x / (1 + x) ≤ 1 - betaP s p := by
    have := one_sub_exp_neg_ge hx0
    linarith
  rcases le_or_gt x 1 with hx1 | hx1
  · -- `x/(1+x) ≥ x/2`, and `5 α ≤ 45 p²/4 ≤ p/(8s)`
    have h2 : x / 2 ≤ x / (1 + x) := by
      apply div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
    have h3 : 5 * alphaP s p ≤ x / 4 := by
      have e : x / 4 = p / (8 * s) := by rw [hx]; field_simp; ring
      rw [e]
      have h4 : 45 * p ^ 2 / 4 ≤ p / (8 * s) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have h5 : 90 * s * p ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h5 (show (0:ℝ) ≤ 4 * p by positivity)]
      nlinarith
    linarith
  · -- `x/(1+x) ≥ 1/2`, and `5α ≤ 45 p²/4 ≤ 1/4`
    have h2 : 1 / 2 ≤ x / (1 + x) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    have h3 : 5 * alphaP s p ≤ 1 / 4 := by
      have : (3 * p / 2) ^ 2 ≤ 1 / 20 := by nlinarith
      linarith
    linarith

/-! ### The kernel on the bidisc -/

theorem betaP_pow_le {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    betaP s p ^ (n + 1) ≤ betaP s p := by
  have h0 := betaP_nonneg (s := s) hp1
  have h1 := (betaP_lt_one hs hp0 hp1).le
  calc betaP s p ^ (n + 1) ≤ betaP s p ^ 1 := pow_le_pow_of_le_one h0 h1 (by omega)
    _ = betaP s p := pow_one _

theorem one_sub_betaP_pow_pos {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    0 < 1 - betaP s p ^ (n + 1) := by
  have := betaP_pow_le hs hp0 hp1 n
  have := betaP_lt_one hs hp0 hp1
  linarith

/-- The base has real part at least `(1 - β^{n+1})/2` on the bidisc of radius `5/2`. -/
theorem re_kernelBase_ge {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (n : ℕ) {z x y : ℂ} (hz : z ∈ discP p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    (1 - betaP s p ^ (n + 1)) / 2 ≤ (kernelBase s n z x y).re := by
  have hp1 : p < 1 := by linarith
  have ha := norm_ca_le hs hp0 hz
  have hb := norm_cb_le hs hp1 hz
  have hβ0 := betaP_nonneg (s := s) hp1
  have hα := five_alphaP_le hs hs1 hp0 hp
  have hbn : ‖cb s z ^ (n + 1)‖ ≤ betaP s p ^ (n + 1) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hb _
  have hbn1 : betaP s p ^ (n + 1) ≤ 1 := by
    have := betaP_pow_le hs hp0 hp1 n
    have := betaP_lt_one hs hp0 hp1
    linarith
  -- the correction term
  have hcorr : ‖ca s z * (x - cb s z ^ (n + 1) * y)‖ ≤ 5 * alphaP s p := by
    rw [norm_mul]
    have : ‖x - cb s z ^ (n + 1) * y‖ ≤ 5 := by
      calc ‖x - cb s z ^ (n + 1) * y‖ ≤ ‖x‖ + ‖cb s z ^ (n + 1) * y‖ := norm_sub_le _ _
        _ ≤ 5/2 + 1 * (5/2) := by
            rw [norm_mul]
            exact add_le_add hx (mul_le_mul (hbn.trans hbn1) hy (norm_nonneg _) zero_le_one)
        _ = 5 := by norm_num
    calc ‖ca s z‖ * ‖x - cb s z ^ (n + 1) * y‖ ≤ alphaP s p * 5 :=
          mul_le_mul ha this (norm_nonneg _) (alphaP_nonneg hp0)
      _ = 5 * alphaP s p := by ring
  have hre1 : -(betaP s p ^ (n + 1)) ≤ -(cb s z ^ (n + 1)).re := by
    have := Complex.re_le_norm (cb s z ^ (n + 1)); linarith
  have hre2 : -(5 * alphaP s p) ≤ -(ca s z * (x - cb s z ^ (n + 1) * y)).re := by
    have := Complex.re_le_norm (ca s z * (x - cb s z ^ (n + 1) * y)); linarith
  have hβ : 1 - betaP s p ≤ 1 - betaP s p ^ (n + 1) := by linarith [betaP_pow_le hs hp0 hp1 n]
  unfold kernelBase
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem kernelBase_mem_slitPlane {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) (n : ℕ) {z x y : ℂ} (hz : z ∈ discP p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    kernelBase s n z x y ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have := re_kernelBase_ge hs hs1 hp0 hp n hz hx hy
  have := one_sub_betaP_pow_pos hs hp0 (by linarith) n
  linarith

theorem norm_kernelBase_ge {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (n : ℕ) {z x y : ℂ} (hz : z ∈ discP p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    (1 - betaP s p ^ (n + 1)) / 2 ≤ ‖kernelBase s n z x y‖ :=
  (re_kernelBase_ge hs hs1 hp0 hp n hz hx hy).trans (Complex.re_le_norm _)

/-- `‖w ^ (-s)‖ = ‖w‖^{-s}` for a real exponent. -/
theorem norm_cpow_neg_real (w : ℂ) (s : ℝ) : ‖w ^ (-(s : ℂ))‖ = ‖w‖ ^ (-s) := by
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]

theorem norm_cpow_neg_real_sub_one (w : ℂ) (s : ℝ) :
    ‖w ^ (-(s : ℂ) - 1)‖ = ‖w‖ ^ (-s - 1) := by
  rw [show -(s : ℂ) - 1 = ((-s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]

/-- `eq:phi-bounds`, the bound on the kernel. -/
theorem norm_kernelN_le {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (n : ℕ) {z x y : ℂ} (hz : z ∈ discP p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    ‖kernelN s n z x y‖ ≤ ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s) := by
  unfold kernelN
  rw [norm_cpow_neg_real]
  have hpos := one_sub_betaP_pow_pos hs hp0 (by linarith) n
  exact rpow_neg_antitone (by linarith) (norm_kernelBase_ge hs hs1 hp0 hp n hz hx hy) hs.le

/-- The Lipschitz constant `L_n = s α ((1 - β^{n+1})/2)^{-s-1}` of `eq:phi-bounds`. -/
def kernelLip (s p : ℝ) (n : ℕ) : ℝ :=
  s * alphaP s p * ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1)

theorem kernelLip_nonneg {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    0 ≤ kernelLip s p n := by
  unfold kernelLip
  have := one_sub_betaP_pow_pos hs hp0 hp1 n
  have := alphaP_nonneg (s := s) hp0
  positivity

/-- The derivative of the kernel in `x`, with its bound. -/
theorem hasDerivAt_kernelN_x {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (n : ℕ) {z x y : ℂ} (hz : z ∈ discP p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    HasDerivAt (fun x => kernelN s n z x y)
      (-(s : ℂ) * kernelBase s n z x y ^ (-(s : ℂ) - 1) * (-(ca s z * 1))) x ∧
    ‖-(s : ℂ) * kernelBase s n z x y ^ (-(s : ℂ) - 1) * (-(ca s z * 1))‖ ≤ kernelLip s p n := by
  have hbase : HasDerivAt (fun x => kernelBase s n z x y) (-(ca s z * 1)) x := by
    unfold kernelBase
    exact (((hasDerivAt_id x).sub_const (cb s z ^ (n + 1) * y)).const_mul (ca s z)).const_sub _
  constructor
  · exact hbase.cpow_const (kernelBase_mem_slitPlane hs hs1 hp0 hp n hz hx hy)
  · rw [norm_mul, norm_mul, norm_neg, norm_neg, mul_one, norm_cpow_neg_real_sub_one]
    have hpos := one_sub_betaP_pow_pos hs hp0 (by linarith) n
    have hpos2 : 0 < (1 - betaP s p ^ (n + 1)) / 2 := by linarith
    have h1 : ‖kernelBase s n z x y‖ ^ (-s - 1) ≤ ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) := by
      rw [show (-s - 1) = -(s + 1) by ring]
      exact rpow_neg_antitone hpos2 (norm_kernelBase_ge hs hs1 hp0 hp n hz hx hy) (by linarith)
    rw [show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
    unfold kernelLip
    calc s * ‖kernelBase s n z x y‖ ^ (-s - 1) * ‖ca s z‖
        ≤ s * ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) * alphaP s p :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hs.le) (norm_ca_le hs hp0 hz) (norm_nonneg _)
            (by positivity)
      _ = s * alphaP s p * ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) := by ring

/-- The derivative of the kernel in `y`, with its bound. -/
theorem hasDerivAt_kernelN_y {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (n : ℕ) {z x y : ℂ} (hz : z ∈ discP p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    HasDerivAt (fun y => kernelN s n z x y)
      (-(s : ℂ) * kernelBase s n z x y ^ (-(s : ℂ) - 1) * (-(ca s z * -(cb s z ^ (n + 1) * 1)))) y ∧
    ‖-(s : ℂ) * kernelBase s n z x y ^ (-(s : ℂ) - 1) * (-(ca s z * -(cb s z ^ (n + 1) * 1)))‖
      ≤ kernelLip s p n := by
  have hp1 : p < 1 := by linarith
  have hbase : HasDerivAt (fun y => kernelBase s n z x y)
      (-(ca s z * -(cb s z ^ (n + 1) * 1))) y := by
    unfold kernelBase
    exact ((((hasDerivAt_id y).const_mul (cb s z ^ (n + 1))).const_sub x).const_mul (ca s z)).const_sub _
  constructor
  · exact hbase.cpow_const (kernelBase_mem_slitPlane hs hs1 hp0 hp n hz hx hy)
  · rw [norm_mul, norm_mul, norm_neg, norm_neg, norm_cpow_neg_real_sub_one]
    have hpos := one_sub_betaP_pow_pos hs hp0 hp1 n
    have hpos2 : 0 < (1 - betaP s p ^ (n + 1)) / 2 := by linarith
    have h1 : ‖kernelBase s n z x y‖ ^ (-s - 1) ≤ ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) := by
      rw [show (-s - 1) = -(s + 1) by ring]
      exact rpow_neg_antitone hpos2 (norm_kernelBase_ge hs hs1 hp0 hp n hz hx hy) (by linarith)
    have hbn : ‖cb s z ^ (n + 1)‖ ≤ 1 := by
      rw [norm_pow]
      have := betaP_pow_le hs hp0 hp1 n
      have := betaP_lt_one hs hp0 hp1
      calc ‖cb s z‖ ^ (n + 1) ≤ betaP s p ^ (n + 1) :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_cb_le hs hp1 hz) _
        _ ≤ 1 := by linarith
    have h2 : ‖ca s z * -(cb s z ^ (n + 1) * 1)‖ ≤ alphaP s p := by
      rw [norm_mul, norm_neg, mul_one]
      calc ‖ca s z‖ * ‖cb s z ^ (n + 1)‖ ≤ alphaP s p * 1 :=
            mul_le_mul (norm_ca_le hs hp0 hz) hbn (norm_nonneg _) (alphaP_nonneg hp0)
        _ = alphaP s p := mul_one _
    rw [show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
    unfold kernelLip
    calc s * ‖kernelBase s n z x y‖ ^ (-s - 1) * ‖ca s z * -(cb s z ^ (n + 1) * 1)‖
        ≤ s * ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) * alphaP s p :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hs.le) h2 (norm_nonneg _) (by positivity)
      _ = s * alphaP s p * ((1 - betaP s p ^ (n + 1)) / 2) ^ (-s - 1) := by ring

/-- The Lipschitz bound of `eq:phi-bounds` on the bidisc of radius `5/2`. -/
theorem norm_kernelN_sub_le {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p) (hp : p ≤ 1/50)
    (n : ℕ) {z : ℂ} (hz : z ∈ discP p) (x y x' y' : ℂ) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2)
    (hx' : ‖x'‖ ≤ 5/2) (hy' : ‖y'‖ ≤ 5/2) :
    ‖kernelN s n z x' y' - kernelN s n z x y‖ ≤ kernelLip s p n * (‖x' - x‖ + ‖y' - y‖) := by
  have hconv : Convex ℝ (closedBall (0:ℂ) (5/2)) := convex_closedBall _ _
  have hmem : ∀ w : ℂ, ‖w‖ ≤ 5/2 → w ∈ closedBall (0:ℂ) (5/2) := fun w hw => by
    simpa [mem_closedBall_iff_norm] using hw
  -- in `x`, at `y'`
  have h1 : ‖kernelN s n z x' y' - kernelN s n z x y'‖ ≤ kernelLip s p n * ‖x' - x‖ := by
    refine hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => kernelN s n z x y') (f' := fun x => -(s : ℂ) * kernelBase s n z x y' ^ (-(s : ℂ) - 1) * (-(ca s z * 1)))
      (fun w hw => ((hasDerivAt_kernelN_x hs hs1 hp0 hp n hz (by simpa [mem_closedBall_iff_norm] using hw) hy').1).hasDerivWithinAt)
      (fun w hw => (hasDerivAt_kernelN_x hs hs1 hp0 hp n hz (by simpa [mem_closedBall_iff_norm] using hw) hy').2)
      (hmem x hx) (hmem x' hx')
  -- in `y`, at `x`
  have h2 : ‖kernelN s n z x y' - kernelN s n z x y‖ ≤ kernelLip s p n * ‖y' - y‖ := by
    refine hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => kernelN s n z x y) (f' := fun y => -(s : ℂ) * kernelBase s n z x y ^ (-(s : ℂ) - 1) * (-(ca s z * -(cb s z ^ (n + 1) * 1))))
      (fun w hw => ((hasDerivAt_kernelN_y hs hs1 hp0 hp n hz hx (by simpa [mem_closedBall_iff_norm] using hw)).1).hasDerivWithinAt)
      (fun w hw => (hasDerivAt_kernelN_y hs hs1 hp0 hp n hz hx (by simpa [mem_closedBall_iff_norm] using hw)).2)
      (hmem y hy) (hmem y' hy')
  calc ‖kernelN s n z x' y' - kernelN s n z x y‖
      = ‖(kernelN s n z x' y' - kernelN s n z x y') + (kernelN s n z x y' - kernelN s n z x y)‖ := by
        ring_nf
    _ ≤ ‖kernelN s n z x' y' - kernelN s n z x y'‖ + ‖kernelN s n z x y' - kernelN s n z x y‖ :=
        norm_add_le _ _
    _ ≤ kernelLip s p n * ‖x' - x‖ + kernelLip s p n * ‖y' - y‖ := add_le_add h1 h2
    _ = kernelLip s p n * (‖x' - x‖ + ‖y' - y‖) := by ring

/-! ### Holomorphy on the disc -/

theorem differentiableOn_ca {s p : ℝ} (hp0 : 0 < p) : DifferentiableOn ℂ (ca s) (discP p) := by
  unfold ca
  exact differentiableOn_id.cpow_const fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_pos_of_mem_discP hp0 hz))

theorem differentiableOn_cb {s p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/50) :
    DifferentiableOn ℂ (cb s) (discP p) := by
  unfold cb
  exact ((differentiableOn_const _).sub differentiableOn_id).cpow_const fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_one_sub_pos_of_mem_discP hp0 hp hz))

theorem differentiableOn_cpointSeq {s p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/50) (m : ℕ)
    (ω : ℕ → Fin 2) :
    DifferentiableOn ℂ (fun z => cpointSeq (ca s z) (cb s z) m ω) (discP p) := by
  induction m generalizing ω with
  | zero => simp only [cpointSeq_zero]; exact differentiableOn_const 0
  | succ m ih =>
    simp only [cpointSeq_succ, cmap, cratioOf, cshiftOf]
    have ha := differentiableOn_ca (s := s) hp0
    have hb := differentiableOn_cb (s := s) hp0 hp
    split_ifs
    · exact (ha.mul (ih _)).add (differentiableOn_const 0)
    · exact (hb.mul (ih _)).add ((differentiableOn_const _).sub hb)

theorem differentiableOn_weightSeq (m : ℕ) (ω : ℕ → Fin 2) (S : Set ℂ) :
    DifferentiableOn ℂ (fun z => weightSeq z m ω) S := by
  induction m generalizing ω with
  | zero => simp only [weightSeq_zero]; exact differentiableOn_const 1
  | succ m ih =>
    simp only [weightSeq_succ]
    split_ifs
    · exact differentiableOn_id.mul (ih _)
    · exact ((differentiableOn_const _).sub differentiableOn_id).mul (ih _)

/-- The level sums of the kernel are holomorphic on the disc. -/
theorem differentiableOn_levelSum_kernel {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) (n m : ℕ) :
    DifferentiableOn ℂ (levelSum (ca s) (cb s) (kernelN s n) m) (discP p) := by
  have hp1 : p < 1 := by linarith
  unfold levelSum
  refine DifferentiableOn.fun_sum fun u _ => ?_
  refine DifferentiableOn.fun_sum fun v _ => ?_
  refine ((differentiableOn_weightSeq m (extend u) (discP p)).mul
    (differentiableOn_weightSeq m (extend v) (discP p))).mul ?_
  -- the kernel at the coded points
  have hpt : ∀ (w : Fin m → Fin 2) (z : ℂ), z ∈ discP p →
      ‖cpointSeq (ca s z) (cb s z) m (extend w)‖ ≤ 5/2 := by
    intro w z hz
    have ha : ‖ca s z‖ < 1 := by
      have := norm_ca_le hs hp0 hz
      have := alphaP_le_sq hs hs1 hp0 hp
      nlinarith
    have hb : ‖cb s z‖ ≤ 1 := (norm_cb_le hs hp1 hz).trans (betaP_lt_one hs hp0 hp1).le
    have h := norm_cpointSeq_le ha hb m (extend w)
    have ha' : ‖ca s z‖ ≤ 1/5 := by
      have := norm_ca_le hs hp0 hz
      have := alphaP_le_sq hs hs1 hp0 hp
      nlinarith
    calc ‖cpointSeq (ca s z) (cb s z) m (extend w)‖ ≤ 2 / (1 - ‖ca s z‖) := h
      _ ≤ 5/2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
  unfold kernelN kernelBase
  refine DifferentiableOn.cpow_const ?_ fun z hz =>
    kernelBase_mem_slitPlane hs hs1 hp0 hp n hz (hpt u z hz) (hpt v z hz)
  have ha := differentiableOn_ca (s := s) hp0
  have hb := differentiableOn_cb (s := s) hp0 hp
  have hX := differentiableOn_cpointSeq (s := s) hp0 hp m (extend u)
  have hY := differentiableOn_cpointSeq (s := s) hp0 hp m (extend v)
  exact ((differentiableOn_const _).sub (hb.pow (n + 1))).sub
    (ha.mul (hX.sub ((hb.pow (n + 1)).mul hY)))

end

end BrownianImages
