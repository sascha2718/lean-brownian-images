/-
`thm:second-derivative-small-s`: for `0 < s ≤ 2·10⁻⁵` and `10⁻⁴ ≤ p ≤ 1/2`, the moment
`M_p(s)` is twice differentiable at `p` with `|M_p''| ≤ 10¹¹ s γ`, `γ = (1 - 5·10⁻⁵)^{1/s}`.

On the disc `|z - p| ≤ r = 5·10⁻⁵` both complex contractions have modulus at most `γ ≤ 1/12`,
the cross kernel `φ(z; x, y) = (1 - b + by - ax)^{-s}` is within `18 s γ` of `1` on the bidisc
of radius `5/2`, and its level sums converge to a holomorphic `M_z` with `|M_z - 1| ≤ 32 s γ`;
at real parameters `M_z = M_x(s)`, and Cauchy's estimate bounds the second derivative.

* `radQ`, `discQ`, `gammaQ`, `crossBase`, `crossKernelC`: the objects.
* `gammaQ_le`: `γ ≤ 1/12`.
* `norm_crossKernelC_sub_one_le`, `norm_crossKernelC_sub_le`: the kernel bounds.
* `incrementBound_cross`, `norm_crossLimit_sub_one_le`: the level sums and their limit.
* `crossLimit_ofReal`: `M_x = M_x(s)` at real parameters.
* `fixedMoment_second_derivative`: the second-derivative bound.
-/
import BrownianImages.FixedDimension.Remainder

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- The radius `r = 5·10⁻⁵`. -/
def radQ : ℝ := 5 / 100000

/-- The disc `|z - p| ≤ r`. -/
def discQ (p : ℝ) : Set ℂ := closedBall (p : ℂ) radQ

/-- `γ = (1 - r)^{1/s}`. -/
def gammaQ (s : ℝ) : ℝ := (1 - radQ) ^ s⁻¹

/-- The base `1 - b + by - ax` of the cross kernel. -/
def crossBase (s : ℝ) (z x y : ℂ) : ℂ := 1 - cb s z + cb s z * y - ca s z * x

/-- The cross kernel `(1 - b + by - ax)^{-s}`. -/
def crossKernelC (s : ℝ) (z x y : ℂ) : ℂ := crossBase s z x y ^ (-(s : ℂ))

theorem radQ_eq : radQ = 5 / 100000 := rfl

theorem mem_discQ {p : ℝ} {z : ℂ} : z ∈ discQ p ↔ ‖z - p‖ ≤ radQ := by
  rw [discQ, Metric.mem_closedBall, dist_eq_norm]

/-! ### The disc -/

theorem norm_le_of_mem_discQ {p : ℝ} (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ}
    (hz : z ∈ discQ p) : ‖z‖ ≤ 1/2 + radQ := by
  rw [mem_discQ] at hz
  calc ‖z‖ = ‖(p : ℂ) + (z - p)‖ := by ring_nf
    _ ≤ ‖(p : ℂ)‖ + ‖z - p‖ := norm_add_le _ _
    _ ≤ 1/2 + radQ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith

theorem norm_one_sub_le_of_mem_discQ {p : ℝ} (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ}
    (hz : z ∈ discQ p) : ‖1 - z‖ ≤ 1 - radQ := by
  rw [mem_discQ] at hz
  calc ‖1 - z‖ = ‖((1 - p : ℝ) : ℂ) - (z - p)‖ := by push_cast; ring_nf
    _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖z - p‖ := norm_sub_le _ _
    _ ≤ (1 - p) + radQ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    _ ≤ 1 - radQ := by rw [radQ_eq] at hz ⊢; linarith

theorem re_pos_of_mem_discQ {p : ℝ} (hp0 : 1 / 10000 ≤ p) {z : ℂ} (hz : z ∈ discQ p) :
    0 < z.re := by
  rw [mem_discQ] at hz
  have h := Complex.abs_re_le_norm (z - p)
  rw [Complex.sub_re, Complex.ofReal_re] at h
  have := neg_le_of_abs_le h
  rw [radQ_eq] at hz; linarith

theorem re_one_sub_pos_of_mem_discQ {p : ℝ} (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ}
    (hz : z ∈ discQ p) : 0 < (1 - z).re := by
  have := Complex.re_le_norm z
  have := norm_le_of_mem_discQ hp0 hp1 hz
  rw [Complex.sub_re, Complex.one_re]; rw [radQ_eq] at *; linarith

theorem norm_add_norm_one_sub_le_discQ {p : ℝ} (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ}
    (hz : z ∈ discQ p) : ‖z‖ + ‖1 - z‖ ≤ 1 + 2 * radQ := by
  rw [mem_discQ] at hz
  have h1 : ‖z‖ ≤ p + radQ := by
    calc ‖z‖ = ‖(p : ℂ) + (z - p)‖ := by ring_nf
      _ ≤ ‖(p : ℂ)‖ + ‖z - p‖ := norm_add_le _ _
      _ ≤ p + radQ := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have h2 : ‖1 - z‖ ≤ (1 - p) + radQ := by
    calc ‖1 - z‖ = ‖((1 - p : ℝ) : ℂ) - (z - p)‖ := by push_cast; ring_nf
      _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖z - p‖ := norm_sub_le _ _
      _ ≤ (1 - p) + radQ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  linarith

theorem gammaQ_nonneg (s : ℝ) : 0 ≤ gammaQ s := Real.rpow_nonneg (by rw [radQ_eq]; norm_num) _

theorem norm_ca_le_gammaQ {s p : ℝ} (hs : 0 < s) (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ}
    (hz : z ∈ discQ p) : ‖ca s z‖ ≤ gammaQ s := by
  unfold ca gammaQ
  rw [Complex.norm_cpow_real]
  have := norm_le_of_mem_discQ hp0 hp1 hz
  exact Real.rpow_le_rpow (norm_nonneg _) (by rw [radQ_eq] at *; linarith) (inv_nonneg.2 hs.le)

theorem norm_cb_le_gammaQ {s p : ℝ} (hs : 0 < s) (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ}
    (hz : z ∈ discQ p) : ‖cb s z‖ ≤ gammaQ s := by
  unfold cb gammaQ
  rw [Complex.norm_cpow_real]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_one_sub_le_of_mem_discQ hp0 hp1 hz)
    (inv_nonneg.2 hs.le)

/-- `e^{5/2} ≥ 12`. -/
theorem exp_five_halves_ge : (12 : ℝ) ≤ Real.exp (5 / 2) := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (1:ℝ) + 1/2 + (1/2) ^ 2 / 2 ≤ Real.exp (1/2) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have e : Real.exp (5 / 2) = Real.exp 1 * Real.exp 1 * Real.exp (1/2) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [e]
  have h3 : (2.7182818283 : ℝ) * 2.7182818283 * (1 + 1/2 + (1/2) ^ 2 / 2) ≤
      Real.exp 1 * Real.exp 1 * Real.exp (1/2) := by
    apply mul_le_mul (mul_le_mul h1.le h1.le (by norm_num) (Real.exp_pos _).le) h2 (by norm_num)
      (by positivity)
  linarith [show (12 : ℝ) ≤ 2.7182818283 * 2.7182818283 * (1 + 1/2 + (1/2) ^ 2 / 2) by norm_num]

/-- `γ ≤ 1/12` for `s ≤ 2·10⁻⁵`. -/
theorem gammaQ_le {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) : gammaQ s ≤ 1 / 12 := by
  unfold gammaQ
  have h1 : 1 - radQ ≤ Real.exp (-radQ) := by
    have := Real.add_one_le_exp (-radQ); linarith
  have h2 : (1 - radQ) ^ s⁻¹ ≤ Real.exp (-radQ) ^ s⁻¹ :=
    Real.rpow_le_rpow (by rw [radQ_eq]; norm_num) h1 (inv_nonneg.2 hs.le)
  have h3 : Real.exp (-radQ) ^ s⁻¹ = Real.exp (-(radQ / s)) := by
    rw [← Real.exp_mul]; congr 1; ring
  have h4 : (5 / 2 : ℝ) ≤ radQ / s := by
    rw [radQ_eq, le_div_iff₀ hs]; linarith
  have h5 : Real.exp (-(radQ / s)) ≤ Real.exp (-(5 / 2)) := Real.exp_le_exp.2 (by linarith)
  have h6 : Real.exp (-(5 / 2)) ≤ 1 / 12 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), inv_div, div_one]
    exact exp_five_halves_ge
  rw [h3] at h2
  linarith

/-! ### The cross kernel on the bidisc -/

theorem norm_crossBase_sub_one_le {s p : ℝ} (hs : 0 < s) (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2)
    {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    ‖crossBase s z x y - 1‖ ≤ 6 * gammaQ s := by
  have ha := norm_ca_le_gammaQ hs hp0 hp1 hz
  have hb := norm_cb_le_gammaQ hs hp0 hp1 hz
  have e : crossBase s z x y - 1 = cb s z * (y - 1) - ca s z * x := by unfold crossBase; ring
  rw [e]
  have hy1 : ‖y - 1‖ ≤ 7/2 := by
    calc ‖y - 1‖ ≤ ‖y‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ ≤ 7/2 := by rw [norm_one]; linarith
  calc ‖cb s z * (y - 1) - ca s z * x‖ ≤ ‖cb s z * (y - 1)‖ + ‖ca s z * x‖ := norm_sub_le _ _
    _ = ‖cb s z‖ * ‖y - 1‖ + ‖ca s z‖ * ‖x‖ := by rw [norm_mul, norm_mul]
    _ ≤ gammaQ s * (7/2) + gammaQ s * (5/2) :=
        add_le_add (mul_le_mul hb hy1 (norm_nonneg _) (gammaQ_nonneg s))
          (mul_le_mul ha hx (norm_nonneg _) (gammaQ_nonneg s))
    _ = 6 * gammaQ s := by ring

theorem re_crossBase_ge {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    1/2 ≤ (crossBase s z x y).re := by
  have h := norm_crossBase_sub_one_le hs hp0 hp1 hz hx hy
  have hγ := gammaQ_le hs hsQ
  have h2 := Complex.abs_re_le_norm (crossBase s z x y - 1)
  rw [Complex.sub_re, Complex.one_re] at h2
  have := neg_le_of_abs_le h2
  linarith

theorem crossBase_mem_slitPlane {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    crossBase s z x y ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have := re_crossBase_ge hs hsQ hp0 hp1 hz hx hy; linarith

theorem norm_crossBase_ge {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) :
    1/2 ≤ ‖crossBase s z x y‖ :=
  (re_crossBase_ge hs hsQ hp0 hp1 hz hx hy).trans (Complex.re_le_norm _)

/-- `‖w‖^{-s-1} ≤ 3` for `‖w‖ ≥ 1/2` and `s ≤ 1/2`. -/
theorem norm_rpow_neg_succ_le {w : ℂ} {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (hw : 1/2 ≤ ‖w‖) :
    ‖w‖ ^ (-s - 1) ≤ 3 := by
  calc ‖w‖ ^ (-s - 1) ≤ (1/2 : ℝ) ^ (-s - 1) := by
        rw [show (-s - 1) = -(s + 1) by ring]
        exact rpow_neg_antitone (by norm_num) hw (by linarith)
    _ = 2 ^ (s + 1) := by
        rw [show (-s - 1) = -(s + 1) by ring, Real.rpow_neg (by norm_num), one_div,
          Real.inv_rpow (by norm_num), inv_inv]
    _ ≤ 3 := (two_rpow_succ_le hs1).trans (by norm_num)

theorem hsQ_le_half {s : ℝ} (hsQ : s ≤ 2 / 100000) : s ≤ 1/2 := by linarith

/-- The derivative of the kernel in `x`, with its bound `3 s γ`. -/
theorem hasDerivAt_crossKernelC_x {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2)
    (hy : ‖y‖ ≤ 5/2) :
    HasDerivAt (fun x => crossKernelC s z x y)
      (-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (-(ca s z * 1))) x ∧
    ‖-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (-(ca s z * 1))‖ ≤ 3 * s * gammaQ s := by
  have hbase : HasDerivAt (fun x => crossBase s z x y) (-(ca s z * 1)) x := by
    unfold crossBase
    exact ((hasDerivAt_id x).const_mul (ca s z)).const_sub _
  refine ⟨hbase.cpow_const (crossBase_mem_slitPlane hs hsQ hp0 hp1 hz hx hy), ?_⟩
  rw [norm_mul, norm_mul, norm_neg, norm_neg, mul_one, norm_cpow_neg_real_sub_one,
    show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
  have h1 := norm_rpow_neg_succ_le hs.le (hsQ_le_half hsQ) (norm_crossBase_ge hs hsQ hp0 hp1 hz hx hy)
  have h2 := norm_ca_le_gammaQ hs hp0 hp1 hz
  calc s * ‖crossBase s z x y‖ ^ (-s - 1) * ‖ca s z‖ ≤ s * 3 * gammaQ s :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hs.le) h2 (norm_nonneg _) (by positivity)
    _ = 3 * s * gammaQ s := by ring

/-- The derivative of the kernel in `y`, with its bound `3 s γ`. -/
theorem hasDerivAt_crossKernelC_y {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2)
    (hy : ‖y‖ ≤ 5/2) :
    HasDerivAt (fun y => crossKernelC s z x y)
      (-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (cb s z * 1)) y ∧
    ‖-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (cb s z * 1)‖ ≤ 3 * s * gammaQ s := by
  have hbase : HasDerivAt (fun y => crossBase s z x y) (cb s z * 1) y := by
    unfold crossBase
    exact (((hasDerivAt_id y).const_mul (cb s z)).const_add _).sub_const _
  refine ⟨hbase.cpow_const (crossBase_mem_slitPlane hs hsQ hp0 hp1 hz hx hy), ?_⟩
  rw [norm_mul, norm_mul, norm_neg, mul_one, norm_cpow_neg_real_sub_one,
    show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
  have h1 := norm_rpow_neg_succ_le hs.le (hsQ_le_half hsQ) (norm_crossBase_ge hs hsQ hp0 hp1 hz hx hy)
  have h2 := norm_cb_le_gammaQ hs hp0 hp1 hz
  calc s * ‖crossBase s z x y‖ ^ (-s - 1) * ‖cb s z‖ ≤ s * 3 * gammaQ s :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hs.le) h2 (norm_nonneg _) (by positivity)
    _ = 3 * s * gammaQ s := by ring

/-- The Lipschitz bound on the bidisc. -/
theorem norm_crossKernelC_sub_le {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ} (hz : z ∈ discQ p) (x y x' y' : ℂ)
    (hx : ‖x‖ ≤ 5/2) (hy : ‖y‖ ≤ 5/2) (hx' : ‖x'‖ ≤ 5/2) (hy' : ‖y'‖ ≤ 5/2) :
    ‖crossKernelC s z x' y' - crossKernelC s z x y‖ ≤ 3 * s * gammaQ s * (‖x' - x‖ + ‖y' - y‖) := by
  have hconv : Convex ℝ (closedBall (0:ℂ) (5/2)) := convex_closedBall _ _
  have hmem : ∀ w : ℂ, ‖w‖ ≤ 5/2 → w ∈ closedBall (0:ℂ) (5/2) := fun w hw => by
    simpa [mem_closedBall_iff_norm] using hw
  have h1 : ‖crossKernelC s z x' y' - crossKernelC s z x y'‖ ≤ 3 * s * gammaQ s * ‖x' - x‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => crossKernelC s z x y')
      (f' := fun x => -(s : ℂ) * crossBase s z x y' ^ (-(s : ℂ) - 1) * (-(ca s z * 1)))
      (fun w hw => ((hasDerivAt_crossKernelC_x hs hsQ hp0 hp1 hz
        (by simpa [mem_closedBall_iff_norm] using hw) hy').1).hasDerivWithinAt)
      (fun w hw => (hasDerivAt_crossKernelC_x hs hsQ hp0 hp1 hz
        (by simpa [mem_closedBall_iff_norm] using hw) hy').2)
      (hmem x hx) (hmem x' hx')
  have h2 : ‖crossKernelC s z x y' - crossKernelC s z x y‖ ≤ 3 * s * gammaQ s * ‖y' - y‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => crossKernelC s z x y)
      (f' := fun y => -(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (cb s z * 1))
      (fun w hw => ((hasDerivAt_crossKernelC_y hs hsQ hp0 hp1 hz hx
        (by simpa [mem_closedBall_iff_norm] using hw)).1).hasDerivWithinAt)
      (fun w hw => (hasDerivAt_crossKernelC_y hs hsQ hp0 hp1 hz hx
        (by simpa [mem_closedBall_iff_norm] using hw)).2)
      (hmem y hy) (hmem y' hy')
  calc ‖crossKernelC s z x' y' - crossKernelC s z x y‖
      = ‖(crossKernelC s z x' y' - crossKernelC s z x y') + (crossKernelC s z x y' - crossKernelC s z x y)‖ := by
        ring_nf
    _ ≤ ‖crossKernelC s z x' y' - crossKernelC s z x y'‖ + ‖crossKernelC s z x y' - crossKernelC s z x y‖ :=
        norm_add_le _ _
    _ ≤ 3 * s * gammaQ s * ‖x' - x‖ + 3 * s * gammaQ s * ‖y' - y‖ := add_le_add h1 h2
    _ = 3 * s * gammaQ s * (‖x' - x‖ + ‖y' - y‖) := by ring

/-- `|φ - 1| ≤ 18 s γ` on the bidisc, by the mean value inequality for `ζ ↦ ζ^{-s}` on the
disc `|ζ - 1| ≤ 1/2`. -/
theorem norm_crossKernelC_sub_one_le {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z x y : ℂ} (hz : z ∈ discQ p) (hx : ‖x‖ ≤ 5/2)
    (hy : ‖y‖ ≤ 5/2) : ‖crossKernelC s z x y - 1‖ ≤ 18 * s * gammaQ s := by
  have hconv : Convex ℝ (closedBall (1:ℂ) (1/2)) := convex_closedBall _ _
  have hslit : ∀ w ∈ closedBall (1:ℂ) (1/2), w ∈ Complex.slitPlane := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    rw [Complex.mem_slitPlane_iff]; left
    have := Complex.abs_re_le_norm (w - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    have := neg_le_of_abs_le this
    linarith
  have hnorm : ∀ w ∈ closedBall (1:ℂ) (1/2), 1/2 ≤ ‖w‖ := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    have := norm_sub_norm_le (1:ℂ) w
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hd : ∀ w ∈ closedBall (1:ℂ) (1/2),
      HasDerivWithinAt (fun ζ => ζ ^ (-(s : ℂ))) (-(s : ℂ) * w ^ (-(s : ℂ) - 1) * 1)
        (closedBall (1:ℂ) (1/2)) w := fun w hw =>
    ((hasDerivAt_id w).cpow_const (hslit w hw)).hasDerivWithinAt
  have hbound : ∀ w ∈ closedBall (1:ℂ) (1/2), ‖-(s : ℂ) * w ^ (-(s : ℂ) - 1) * 1‖ ≤ 3 * s := by
    intro w hw
    rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one, norm_cpow_neg_real_sub_one,
      show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
    have := norm_rpow_neg_succ_le hs.le (hsQ_le_half hsQ) (hnorm w hw)
    nlinarith
  have hb := norm_crossBase_sub_one_le hs hp0 hp1 hz hx hy
  have hγ := gammaQ_le hs hsQ
  have hmemb : crossBase s z x y ∈ closedBall (1:ℂ) (1/2) := by
    rw [mem_closedBall_iff_norm]; linarith
  have hmem1 : (1:ℂ) ∈ closedBall (1:ℂ) (1/2) := mem_closedBall_self (by norm_num)
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound hmem1 hmemb
  rw [Complex.one_cpow] at h
  calc ‖crossKernelC s z x y - 1‖ ≤ 3 * s * ‖crossBase s z x y - 1‖ := h
    _ ≤ 3 * s * (6 * gammaQ s) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 18 * s * gammaQ s := by ring

/-! ### Holomorphy and the level sums -/

theorem differentiableOn_ca_discQ {s p : ℝ} (hp0 : 1 / 10000 ≤ p) :
    DifferentiableOn ℂ (ca s) (discQ p) := by
  unfold ca
  exact differentiableOn_id.cpow_const fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_pos_of_mem_discQ hp0 hz))

theorem differentiableOn_cb_discQ {s p : ℝ} (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) :
    DifferentiableOn ℂ (cb s) (discQ p) := by
  unfold cb
  exact ((differentiableOn_const _).sub differentiableOn_id).cpow_const fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_one_sub_pos_of_mem_discQ hp0 hp1 hz))

theorem differentiableOn_cpointSeq_discQ {s p : ℝ} (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) (m : ℕ)
    (ω : ℕ → Fin 2) :
    DifferentiableOn ℂ (fun z => cpointSeq (ca s z) (cb s z) m ω) (discQ p) := by
  induction m generalizing ω with
  | zero => simp only [cpointSeq_zero]; exact differentiableOn_const 0
  | succ m ih =>
    simp only [cpointSeq_succ, cmap, cratioOf, cshiftOf]
    have ha := differentiableOn_ca_discQ (s := s) hp0
    have hb := differentiableOn_cb_discQ (s := s) hp0 hp1
    split_ifs
    · exact (ha.mul (ih _)).add (differentiableOn_const 0)
    · exact (hb.mul (ih _)).add ((differentiableOn_const _).sub hb)

theorem norm_cpointSeq_discQ_le {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ} (hz : z ∈ discQ p) (m : ℕ) (ω : ℕ → Fin 2) :
    ‖cpointSeq (ca s z) (cb s z) m ω‖ ≤ 5/2 := by
  have hγ := gammaQ_le hs hsQ
  have ha := norm_ca_le_gammaQ hs hp0 hp1 hz
  have hb := norm_cb_le_gammaQ hs hp0 hp1 hz
  have h := norm_cpointSeq_le (a := ca s z) (b := cb s z) (by linarith) (by linarith) m ω
  calc ‖cpointSeq (ca s z) (cb s z) m ω‖ ≤ 2 / (1 - ‖ca s z‖) := h
    _ ≤ 5/2 := by rw [div_le_iff₀ (by linarith)]; linarith

theorem differentiableOn_levelSum_cross {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) (m : ℕ) :
    DifferentiableOn ℂ (levelSum (ca s) (cb s) (crossKernelC s) m) (discQ p) := by
  unfold levelSum
  refine DifferentiableOn.fun_sum fun u _ => ?_
  refine DifferentiableOn.fun_sum fun v _ => ?_
  refine ((differentiableOn_weightSeq m (extend u) (discQ p)).mul
    (differentiableOn_weightSeq m (extend v) (discQ p))).mul ?_
  unfold crossKernelC crossBase
  refine DifferentiableOn.cpow_const ?_ fun z hz =>
    crossBase_mem_slitPlane hs hsQ hp0 hp1 hz (norm_cpointSeq_discQ_le hs hsQ hp0 hp1 hz m _)
      (norm_cpointSeq_discQ_le hs hsQ hp0 hp1 hz m _)
  have ha := differentiableOn_ca_discQ (s := s) hp0
  have hb := differentiableOn_cb_discQ (s := s) hp0 hp1
  have hX := differentiableOn_cpointSeq_discQ (s := s) hp0 hp1 m (extend u)
  have hY := differentiableOn_cpointSeq_discQ (s := s) hp0 hp1 m (extend v)
  exact (((differentiableOn_const _).sub hb).add (hb.mul hY)).sub (ha.mul hX)

/-- `B = 1 + 2r`, `r' = γ B²`, and the increment constant. -/
def discBQ : ℝ := 1 + 2 * radQ

def discRQ (s : ℝ) : ℝ := gammaQ s * discBQ ^ 2

theorem discBQ_sq_le : discBQ ^ 2 ≤ 1.0003 := by unfold discBQ radQ; norm_num

theorem discRQ_nonneg (s : ℝ) : 0 ≤ discRQ s := by
  unfold discRQ discBQ radQ; have := gammaQ_nonneg s; positivity

theorem discRQ_le {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) : discRQ s ≤ 1 / 11 := by
  unfold discRQ
  have h1 := gammaQ_le hs hsQ
  have h2 := discBQ_sq_le
  have := gammaQ_nonneg s
  nlinarith

theorem discRQ_lt_one {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) : discRQ s < 1 := by
  have := discRQ_le hs hsQ; linarith

theorem incrementBound_cross {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) :
    IncrementBound (ca s) (cb s) (crossKernelC s) (discQ p) (4 * (3 * s * gammaQ s) * discBQ ^ 2)
      (discRQ s) := by
  intro z hz m
  have hγ := gammaQ_le hs hsQ
  have ha' := norm_ca_le_gammaQ hs hp0 hp1 hz
  have hb' := norm_cb_le_gammaQ hs hp0 hp1 hz
  have ha : ‖ca s z‖ < 1 := by linarith
  have hb : ‖cb s z‖ ≤ 1 := by linarith
  have hρ : max ‖ca s z‖ ‖cb s z‖ ≤ gammaQ s := max_le ha' hb'
  have hB := norm_add_norm_one_sub_le_discQ hp0 hp1 hz
  have hR₀ : 2 / (1 - ‖ca s z‖) ≤ 5 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h := norm_levelSum_succ_sub_le (ca s) (cb s) (crossKernelC s) m ha hb hρ hB hR₀
    (mul_nonneg (mul_nonneg (by norm_num) hs.le) (gammaQ_nonneg s))
    (fun x y x' y' hx hy hx' hy' => norm_crossKernelC_sub_le hs hsQ hp0 hp1 hz x y x' y' hx hy hx' hy')
  calc ‖levelSum (ca s) (cb s) (crossKernelC s) (m + 1) z - levelSum (ca s) (cb s) (crossKernelC s) m z‖
      ≤ 4 * (3 * s * gammaQ s) * (1 + 2 * radQ) ^ (2 * m + 2) * gammaQ s ^ m := h
    _ = 4 * (3 * s * gammaQ s) * discBQ ^ 2 * discRQ s ^ m := by
        unfold discRQ discBQ
        rw [mul_pow, ← pow_mul]
        ring

/-- `M_z = lim Λ^{(m)}(z)` for the cross kernel. -/
def crossLimit (s : ℝ) (z : ℂ) : ℂ := limitSum (ca s) (cb s) (crossKernelC s) z

theorem norm_crossLimit_sub_one_le {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) {z : ℂ} (hz : z ∈ discQ p) :
    ‖crossLimit s z - 1‖ ≤ 32 * s * gammaQ s := by
  have h1 := norm_limitSum_sub_le (discRQ_nonneg s) (discRQ_lt_one hs hsQ)
    (incrementBound_cross hs hsQ hp0 hp1) hz
  have h2 := norm_crossKernelC_sub_one_le hs hsQ hp0 hp1 hz (x := 0) (y := 0) (by norm_num) (by norm_num)
  have hδ : 10 / 11 ≤ 1 - discRQ s := by linarith [discRQ_le hs hsQ]
  have hγ := gammaQ_nonneg s
  have h3 : 4 * (3 * s * gammaQ s) * discBQ ^ 2 / (1 - discRQ s) ≤ 14 * s * gammaQ s := by
    rw [div_le_iff₀ (by linarith)]
    have := discBQ_sq_le
    have h4 : 4 * (3 * s * gammaQ s) * discBQ ^ 2 ≤ 12 * s * gammaQ s * 1.0003 := by
      have : 0 ≤ 12 * s * gammaQ s := by positivity
      nlinarith
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 14) hs.le) hγ]
  unfold crossLimit
  calc ‖limitSum (ca s) (cb s) (crossKernelC s) z - 1‖
      = ‖(limitSum (ca s) (cb s) (crossKernelC s) z - crossKernelC s z 0 0) + (crossKernelC s z 0 0 - 1)‖ := by
        ring_nf
    _ ≤ ‖limitSum (ca s) (cb s) (crossKernelC s) z - crossKernelC s z 0 0‖ + ‖crossKernelC s z 0 0 - 1‖ :=
        norm_add_le _ _
    _ ≤ 14 * s * gammaQ s + 18 * s * gammaQ s := add_le_add (h1.trans h3) h2
    _ = 32 * s * gammaQ s := by ring

theorem differentiableOn_crossLimit {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) :
    DifferentiableOn ℂ (crossLimit s) (ball (p : ℂ) radQ) :=
  differentiableOn_limitSum (discRQ_nonneg s) (discRQ_lt_one hs hsQ)
    (incrementBound_cross hs hsQ hp0 hp1) isOpen_ball ball_subset_closedBall
    fun m => (differentiableOn_levelSum_cross hs hsQ hp0 hp1 m).mono ball_subset_closedBall

theorem continuousOn_crossLimit {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) : ContinuousOn (crossLimit s) (discQ p) :=
  continuousOn_limitSum (discRQ_nonneg s) (discRQ_lt_one hs hsQ)
    (incrementBound_cross hs hsQ hp0 hp1)
    fun m => (differentiableOn_levelSum_cross hs hsQ hp0 hp1 m).continuousOn

/-! ### Real parameters -/

theorem ofReal_mem_discQ {p x : ℝ} (hx : x ∈ Icc (p - radQ) (p + radQ)) : (x : ℂ) ∈ discQ p := by
  rw [mem_discQ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem pos_of_mem_Q {p x : ℝ} (hp0 : 1 / 10000 ≤ p) (hx : x ∈ Icc (p - radQ) (p + radQ)) :
    0 < x := by rw [radQ_eq] at hx; linarith [hx.1]

theorem lt_one_of_mem_Q {p x : ℝ} (hp1 : p ≤ 1/2) (hx : x ∈ Icc (p - radQ) (p + radQ)) :
    x < 1 := by rw [radQ_eq] at hx; linarith [hx.2]

/-- The cross kernel at a real parameter and real points is the real power. -/
theorem crossKernelC_ofReal {s x X Y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1) :
    crossKernelC s (x : ℂ) (X : ℂ) (Y : ℂ) = ((fixedCross s x X Y ^ (-s) : ℝ) : ℂ) := by
  have hpos := fixedCross_pos hs hs1 hx0 hx1 hX hY
  unfold crossKernelC crossBase
  rw [ca_ofReal hx0.le, cb_ofReal hx1.le, Complex.ofReal_cpow hpos.le]
  unfold fixedCross
  push_cast
  try rfl

/-- The cross kernel at the coded points of the first `m` letters. -/
def crossSeq (s x : ℝ) (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (m : ℕ) (ω ω' : ℕ → Fin 2) : ℂ :=
  crossKernelC s (x : ℂ) ((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ)
    ((codeSeq (fixedSystem s x hs hx0 hx1) ω' m : ℝ) : ℂ)

/-- The cross kernel at the coded points. -/
def crossCode (s x : ℝ) (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (ω ω' : ℕ → Fin 2) : ℂ :=
  crossKernelC s (x : ℂ) ((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ)
    ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ)

theorem measurable_crossKernelC_comp {s x : ℝ} {X Y : (ℕ → Fin 2) × (ℕ → Fin 2) → ℝ}
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable fun q => crossKernelC s (x : ℂ) (X q : ℂ) (Y q : ℂ) := by
  unfold crossKernelC crossBase
  have hX' : Measurable fun q => (X q : ℂ) := Complex.measurable_ofReal.comp hX
  have hY' : Measurable fun q => (Y q : ℂ) := Complex.measurable_ofReal.comp hY
  exact (((measurable_const.sub measurable_const).add (measurable_const.mul hY')).sub
    (measurable_const.mul hX')).pow measurable_const

theorem measurable_crossSeq {s x : ℝ} (hs : 0 < s) (hx0 : 0 < x) (hx1 : x < 1) (m : ℕ) :
    Measurable (Function.uncurry (crossSeq s x hs hx0 hx1 m)) :=
  measurable_crossKernelC_comp ((continuous_codeSeq _ m).measurable.comp measurable_fst)
    ((continuous_codeSeq _ m).measurable.comp measurable_snd)

theorem norm_crossSeq_le {s p x : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) (hx : x ∈ Icc (p - radQ) (p + radQ)) (m : ℕ) (ω ω' : ℕ → Fin 2) :
    ‖crossSeq s x hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) m ω ω'‖ ≤ 2 := by
  have h := norm_crossKernelC_sub_one_le hs hsQ hp0 hp1 (ofReal_mem_discQ hx)
    (norm_ofReal_codeSeq_le hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) ω m)
    (norm_ofReal_codeSeq_le hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) ω' m)
  have hγ := gammaQ_le hs hsQ
  have hγ0 := gammaQ_nonneg s
  have : 18 * s * gammaQ s ≤ 1 := by nlinarith
  unfold crossSeq
  calc ‖crossKernelC s (x : ℂ) _ _‖ = ‖(crossKernelC s (x : ℂ) _ _ - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖crossKernelC s (x : ℂ) _ _ - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

theorem levelSum_cross_ofReal {s p x : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) (hx : x ∈ Icc (p - radQ) (p + radQ)) (m : ℕ) :
    levelSum (ca s) (cb s) (crossKernelC s) m (x : ℂ)
      = ∫ ω', ∫ ω, crossSeq s x hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) m ω ω'
          ∂twoBern (1 - x) ∂twoBern (1 - x) := by
  have hx0 := pos_of_mem_Q hp0 hx
  have hx1 := lt_one_of_mem_Q hp1 hx
  have hcode : ∀ ω : ℕ → Fin 2, cpointSeq (ca s (x : ℂ)) (cb s (x : ℂ)) m ω
      = ((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ) := fun ω => by
    rw [ca_ofReal hx0.le, cb_ofReal hx1.le, cpointSeq_ofReal hs hx0 hx1]
  have hdep : ∀ ω₁ ω₁' ω₂ ω₂' : ℕ → Fin 2, (∀ k < m, ω₁ k = ω₁' k) → (∀ k < m, ω₂ k = ω₂' k) →
      crossSeq s x hs hx0 hx1 m ω₁ ω₂ = crossSeq s x hs hx0 hx1 m ω₁' ω₂' := by
    intro ω₁ ω₁' ω₂ ω₂' h₁ h₂
    unfold crossSeq
    rw [← hcode, ← hcode, ← hcode ω₁', ← hcode ω₂', cpointSeq_congr _ _ m h₁,
      cpointSeq_congr _ _ m h₂]
  rw [integral_integral_eq_sum_weight hx0.le hx1.le m (measurable_crossSeq hs hx0 hx1 m)
    (fun ω ω' => norm_crossSeq_le hs hsQ hp0 hp1 hx m ω ω') hdep]
  unfold levelSum
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [weightSeq_ofReal, weightSeq_ofReal, hcode, hcode]
  rfl

theorem tendsto_integral_cross_codeSeq {s p x : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) (hx : x ∈ Icc (p - radQ) (p + radQ)) :
    Tendsto (fun m => ∫ ω', ∫ ω, crossSeq s x hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) m ω ω'
        ∂twoBern (1 - x) ∂twoBern (1 - x)) atTop
      (𝓝 (∫ ω', ∫ ω, crossCode s x hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) ω ω'
        ∂twoBern (1 - x) ∂twoBern (1 - x))) := by
  have hx0 := pos_of_mem_Q hp0 hx
  have hx1 := lt_one_of_mem_Q hp1 hx
  have hprob : IsProbabilityMeasure (twoBern (1 - x)) := isProbabilityMeasure_twoBern_fixed hx0 hx1
  have hpt : ∀ ω ω' : ℕ → Fin 2, Tendsto (fun m => crossSeq s x hs hx0 hx1 m ω ω') atTop
      (𝓝 (crossCode s x hs hx0 hx1 ω ω')) := by
    intro ω ω'
    have h1 : Tendsto (fun m => (((codeSeq (fixedSystem s x hs hx0 hx1) ω m : ℝ) : ℂ),
          ((codeSeq (fixedSystem s x hs hx0 hx1) ω' m : ℝ) : ℂ))) atTop
        (𝓝 (((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ),
          ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ))) :=
      ((Complex.continuous_ofReal.tendsto _).comp (tendsto_codeSeq _ ω)).prodMk_nhds
        ((Complex.continuous_ofReal.tendsto _).comp (tendsto_codeSeq _ ω'))
    have hcont : ContinuousAt (fun q : ℂ × ℂ => crossKernelC s (x : ℂ) q.1 q.2)
        (((code (fixedSystem s x hs hx0 hx1) ω : ℝ) : ℂ),
          ((code (fixedSystem s x hs hx0 hx1) ω' : ℝ) : ℂ)) := by
      unfold crossKernelC crossBase
      refine ContinuousAt.cpow ?_ continuousAt_const ?_
      · exact ((continuousAt_const.sub continuousAt_const).add
          (continuousAt_const.mul continuousAt_snd)).sub (continuousAt_const.mul continuousAt_fst)
      · exact crossBase_mem_slitPlane hs hsQ hp0 hp1 (ofReal_mem_discQ hx)
          (norm_ofReal_code_le hs hx0 hx1 ω) (norm_ofReal_code_le hs hx0 hx1 ω')
    have h2 := hcont.tendsto.comp h1
    unfold crossSeq crossCode
    exact h2
  have hinner : ∀ ω', Tendsto (fun m => ∫ ω, crossSeq s x hs hx0 hx1 m ω ω' ∂twoBern (1 - x))
      atTop (𝓝 (∫ ω, crossCode s x hs hx0 hx1 ω ω' ∂twoBern (1 - x))) := by
    intro ω'
    refine tendsto_integral_of_dominated_convergence (fun _ => (2:ℝ)) (fun m => ?_)
      ((integrable_const (2:ℝ) : Integrable (fun _ : ℕ → Fin 2 => (2:ℝ)) (twoBern (1 - x))))
      (fun m => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => hpt ω ω')
    · exact ((measurable_crossSeq hs hx0 hx1 m).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · exact norm_crossSeq_le hs hsQ hp0 hp1 hx m ω ω'
  refine tendsto_integral_of_dominated_convergence (fun _ => (2:ℝ)) (fun m => ?_)
    ((integrable_const (2:ℝ) : Integrable (fun _ : ℕ → Fin 2 => (2:ℝ)) (twoBern (1 - x))))
    (fun m => Eventually.of_forall fun ω' => ?_) (Eventually.of_forall hinner)
  · exact ((measurable_crossSeq hs hx0 hx1 m).stronglyMeasurable.integral_prod_left'
      (μ := twoBern (1 - x))).aestronglyMeasurable
  · have h := norm_integral_le_of_norm_le_const (μ := twoBern (1 - x))
      (f := fun ω => crossSeq s x hs hx0 hx1 m ω ω')
      (Eventually.of_forall fun ω => norm_crossSeq_le hs hsQ hp0 hp1 hx m ω ω')
    rwa [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at h

/-- `M_x = M_x(s)` at a real parameter of the disc. -/
theorem crossLimit_ofReal {s p x : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) (hp0 : 1 / 10000 ≤ p)
    (hp1 : p ≤ 1/2) (hx : x ∈ Icc (p - radQ) (p + radQ)) :
    crossLimit s (x : ℂ) = ((fixedMoment s x : ℝ) : ℂ) := by
  have hx0 := pos_of_mem_Q hp0 hx
  have hx1 := lt_one_of_mem_Q hp1 hx
  have hs1 : s < 1 := by linarith
  have h1 : Tendsto (fun m => levelSum (ca s) (cb s) (crossKernelC s) m (x : ℂ)) atTop
      (𝓝 (crossLimit s (x : ℂ))) :=
    tendsto_levelSum (discRQ_nonneg s) (discRQ_lt_one hs hsQ)
      (incrementBound_cross hs hsQ hp0 hp1) (ofReal_mem_discQ hx)
  have h2 := tendsto_integral_cross_codeSeq hs hsQ hp0 hp1 hx
  simp_rw [← levelSum_cross_ofReal hs hsQ hp0 hp1 hx] at h2
  rw [tendsto_nhds_unique h1 h2]
  have hreal : ∀ ω ω' : ℕ → Fin 2,
      crossCode s x hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) ω ω'
        = ((fixedKernel s x ω ω' : ℝ) : ℂ) := by
    intro ω ω'
    unfold crossCode fixedKernel
    rw [crossKernelC_ofReal hs hs1 hx0 hx1 (code_mem_Icc _ ω) (code_mem_Icc _ ω'),
      fixedCode_eq hs hx0 hx1, fixedCode_eq hs hx0 hx1]
  have hinner : ∀ ω' : ℕ → Fin 2,
      (∫ ω, crossCode s x hs (pos_of_mem_Q hp0 hx) (lt_one_of_mem_Q hp1 hx) ω ω' ∂twoBern (1 - x))
        = ((∫ ω, fixedKernel s x ω ω' ∂twoBern (1 - x) : ℝ) : ℂ) := by
    intro ω'
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun ω => hreal ω ω')
  rw [integral_congr_ae (Eventually.of_forall hinner), integral_complex_ofReal]
  rfl

/-! ### `thm:second-derivative-small-s` -/

/-- The real derivative of `M` at a real point of the open disc is `Re M_z'`. -/
theorem hasDerivAt_fixedMoment_of_mem {s p x : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) (hx : x ∈ Ioo (p - radQ) (p + radQ)) :
    HasDerivAt (fixedMoment s) (deriv (crossLimit s) (x : ℂ)).re x := by
  have hball : (x : ℂ) ∈ ball (p : ℂ) radQ := by
    rw [mem_ball_iff_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hdiff : DifferentiableAt ℂ (crossLimit s) (x : ℂ) :=
    (differentiableOn_crossLimit hs hsQ hp0 hp1).differentiableAt (isOpen_ball.mem_nhds hball)
  have hr := hdiff.hasDerivAt.real_of_complex
  refine hr.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [crossLimit_ofReal hs hsQ hp0 hp1 ⟨hy.1.le, hy.2.le⟩, Complex.ofReal_re]

/-- **`thm:second-derivative-small-s`.**  For `0 < s ≤ 2·10⁻⁵` and `10⁻⁴ ≤ p ≤ 1/2`, the
moment is differentiable near `p`, and its derivative is differentiable at `p` with
`|M_p''| ≤ 10¹¹ s γ`. -/
theorem fixedMoment_second_derivative {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) :
    (∀ x ∈ Ioo (p - radQ) (p + radQ), HasDerivAt (fixedMoment s) (deriv (fixedMoment s) x) x) ∧
    ∃ D, HasDerivAt (deriv (fixedMoment s)) D p ∧ |D| ≤ 10 ^ 11 * s * gammaQ s := by
  have hR : 0 < radQ := by rw [radQ_eq]; norm_num
  have hdiff := differentiableOn_crossLimit hs hsQ hp0 hp1
  refine ⟨fun x hx => (hasDerivAt_fixedMoment_of_mem hs hsQ hp0 hp1 hx).congr_deriv
    (hasDerivAt_fixedMoment_of_mem hs hsQ hp0 hp1 hx).deriv.symm, ?_⟩
  -- the complex derivative is holomorphic on the open disc
  have hderiv : DifferentiableOn ℂ (deriv (crossLimit s)) (ball (p : ℂ) radQ) :=
    (hdiff.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hpmem : (p : ℂ) ∈ ball (p : ℂ) radQ := mem_ball_self hR
  have hc : HasDerivAt (deriv (crossLimit s)) (deriv (deriv (crossLimit s)) (p : ℂ)) (p : ℂ) :=
    (hderiv.differentiableAt (isOpen_ball.mem_nhds hpmem)).hasDerivAt
  refine ⟨(deriv (deriv (crossLimit s)) (p : ℂ)).re, ?_, ?_⟩
  · refine hc.real_of_complex.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show p - radQ < p by linarith) (show p < p + radQ by linarith)]
      with x hx
    exact ((hasDerivAt_fixedMoment_of_mem hs hsQ hp0 hp1 hx).deriv)
  · -- Cauchy's estimate for the second derivative of `M_z - 1`
    have hd : DiffContOnCl ℂ (fun z => crossLimit s z - 1) (ball (p : ℂ) radQ) := by
      refine ⟨hdiff.sub (differentiableOn_const _), ?_⟩
      rw [closure_ball _ hR.ne']
      exact (continuousOn_crossLimit hs hsQ hp0 hp1).sub continuousOn_const
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hd
      (C := 32 * s * gammaQ s) fun z hz =>
        norm_crossLimit_sub_one_le hs hsQ hp0 hp1 (sphere_subset_closedBall hz)
    have e : iteratedDeriv 2 (fun z => crossLimit s z - 1) (p : ℂ)
        = deriv (deriv (crossLimit s)) (p : ℂ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      congr 1
      funext z
      exact deriv_sub_const 1
    rw [e] at h
    refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
    rw [radQ_eq]
    have := gammaQ_nonneg s
    have : 0 ≤ s * gammaQ s := by positivity
    norm_num
    nlinarith

end

end BrownianImages
