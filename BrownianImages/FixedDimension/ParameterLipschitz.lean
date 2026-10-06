/-
The dependence of the contractions and of the coded points on the parameter, in the proof of
`thm:fixed-dimension-analyticity`: on a disc `|z - p₀| ≤ r` around a real `p₀ ∈ (0,1)`, the
branches `a(z) = z^{1/s}` and `b(z) = (1-z)^{1/s}` are Lipschitz with constant
`L = (3/2)^{1/s-1}/s`, their moduli stay below `γ = (1 + γ₀)/2` with `γ₀ = max(a(p₀), b(p₀))`,
and every coded point moves by at most `C|z - p₀|`, `C = L(R+1)/(1-γ₀)`, `R = 4/(1-γ₀)`.

* `GoodRadius`: the conditions on the radius used here and in `Analyticity`.
* `norm_ca_sub_le`, `norm_cb_sub_le`: the Lipschitz bounds on the branches.
* `norm_ca_le_gamma1`, `norm_cb_le_gamma1`: the moduli on the disc.
* `norm_cpointSeq_sub_le`: `|x_w(z) - x_w(p₀)| ≤ C|z - p₀|`.
-/
import BrownianImages.FixedDimension.RealLevelSums

namespace BrownianImages

open Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- `γ₀ = max(a, b)` at the real parameter. -/
def gamma0 (s p : ℝ) : ℝ := max (fixedA s p) (fixedB s p)

/-- The Lipschitz constant `L = (3/2)^{1/s-1}/s` of the branches on the disc. -/
def lipA (s : ℝ) : ℝ := s⁻¹ * (3/2 : ℝ) ^ (s⁻¹ - 1)

/-- `γ = (1 + γ₀)/2`. -/
def gamma1 (s p : ℝ) : ℝ := (1 + gamma0 s p) / 2

/-- `R = 4/(1 - γ₀) = 2/(1 - γ)`, a bound on the coded points. -/
def radR (s p : ℝ) : ℝ := 4 / (1 - gamma0 s p)

/-- `C = L (R + 1)/(1 - γ₀)`, the Lipschitz constant of the coded points in the parameter. -/
def lipC (s p : ℝ) : ℝ := lipA s * (radR s p + 1) / (1 - gamma0 s p)

/-- The conditions on the radius of the disc around `p₀`. -/
structure GoodRadius (s p r : ℝ) : Prop where
  pos : 0 < r
  le_half : r ≤ min p (1 - p) / 2
  lip : lipA s * r ≤ (1 - gamma0 s p) / 2
  small : r ≤ (1 - gamma1 s p) / 8
  delta_le_one : lipC s p * r ≤ 1
  gap : r * (5 * lipA s + 2 * gamma0 s p * lipC s p) ≤ crossGap s p / 2

theorem gamma0_nonneg {s p : ℝ} (hp0 : 0 < p) : 0 ≤ gamma0 s p :=
  le_max_of_le_left (fixedA_pos (s := s) hp0).le

theorem gamma0_lt_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : gamma0 s p < 1 :=
  max_lt (fixedA_lt_one hs hp0 hp1) (fixedB_lt_one hs hp0 hp1)

theorem fixedA_le_gamma0 (s p : ℝ) : fixedA s p ≤ gamma0 s p := le_max_left _ _

theorem fixedB_le_gamma0 (s p : ℝ) : fixedB s p ≤ gamma0 s p := le_max_right _ _

theorem gamma1_lt_one {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : gamma1 s p < 1 := by
  unfold gamma1; linarith [gamma0_lt_one hs hp0 hp1]

theorem gamma1_nonneg {s p : ℝ} (hp0 : 0 < p) : 0 ≤ gamma1 s p := by
  unfold gamma1; linarith [gamma0_nonneg (s := s) hp0]

theorem radR_pos {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : 0 < radR s p := by
  unfold radR; have := gamma0_lt_one hs hp0 hp1; positivity

theorem lipA_pos {s : ℝ} (hs : 0 < s) : 0 < lipA s := by unfold lipA; positivity

theorem lipC_pos {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) : 0 < lipC s p := by
  unfold lipC
  have := gamma0_lt_one hs hp0 hp1
  have := radR_pos hs hp0 hp1
  have := lipA_pos hs
  positivity

theorem two_div_one_sub_gamma1 {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    2 / (1 - gamma1 s p) = radR s p := by
  unfold gamma1 radR
  have := gamma0_lt_one hs hp0 hp1
  field_simp
  ring

/-- A good radius exists. -/
theorem exists_goodRadius {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ r, GoodRadius s p r := by
  have hγ0 := gamma0_lt_one hs hp0 hp1
  have hγ1 := gamma1_lt_one hs hp0 hp1
  have hL := lipA_pos hs
  have hC := lipC_pos hs hp0 hp1
  have hg := crossGap_pos hs hs1 hp0 hp1
  have hγ0' := gamma0_nonneg (s := s) hp0
  have hden : 0 < 5 * lipA s + 2 * gamma0 s p * lipC s p := by positivity
  have h₁ : 0 < min p (1 - p) / 2 := by
    have : 0 < min p (1 - p) := lt_min hp0 (by linarith)
    positivity
  have h₂ : 0 < (1 - gamma0 s p) / (2 * lipA s) := div_pos (by linarith) (by positivity)
  have h₃ : 0 < (1 - gamma1 s p) / 8 := div_pos (by linarith) (by norm_num)
  have h₄ : 0 < 1 / lipC s p := by positivity
  have h₅ : 0 < crossGap s p / (2 * (5 * lipA s + 2 * gamma0 s p * lipC s p)) := by positivity
  set r₁ := min p (1 - p) / 2 with hr₁
  set r₂ := (1 - gamma0 s p) / (2 * lipA s) with hr₂
  set r₃ := (1 - gamma1 s p) / 8 with hr₃
  set r₄ := 1 / lipC s p with hr₄
  set r₅ := crossGap s p / (2 * (5 * lipA s + 2 * gamma0 s p * lipC s p)) with hr₅
  refine ⟨min (min r₁ r₂) (min (min r₃ r₄) r₅), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min h₁ h₂) (lt_min (lt_min h₃ h₄) h₅)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · have h : min (min r₁ r₂) (min (min r₃ r₄) r₅) ≤ r₂ :=
      (min_le_left _ _).trans (min_le_right _ _)
    calc lipA s * min (min r₁ r₂) (min (min r₃ r₄) r₅) ≤ lipA s * r₂ :=
          mul_le_mul_of_nonneg_left h hL.le
      _ = (1 - gamma0 s p) / 2 := by rw [hr₂]; field_simp
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  · have h : min (min r₁ r₂) (min (min r₃ r₄) r₅) ≤ r₄ :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    calc lipC s p * min (min r₁ r₂) (min (min r₃ r₄) r₅) ≤ lipC s p * r₄ :=
          mul_le_mul_of_nonneg_left h hC.le
      _ = 1 := by rw [hr₄]; field_simp
  · have h : min (min r₁ r₂) (min (min r₃ r₄) r₅) ≤ r₅ :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc min (min r₁ r₂) (min (min r₃ r₄) r₅) * (5 * lipA s + 2 * gamma0 s p * lipC s p)
        ≤ r₅ * (5 * lipA s + 2 * gamma0 s p * lipC s p) :=
          mul_le_mul_of_nonneg_right h hden.le
      _ = crossGap s p / 2 := by rw [hr₅]; field_simp

/-! ### The disc -/

theorem r_le_p {s p r : ℝ} (hr : GoodRadius s p r) : r ≤ p / 2 := by
  have := hr.le_half
  have : min p (1 - p) ≤ p := min_le_left _ _
  linarith

theorem r_le_one_sub_p {s p r : ℝ} (hr : GoodRadius s p r) : r ≤ (1 - p) / 2 := by
  have := hr.le_half
  have : min p (1 - p) ≤ 1 - p := min_le_right _ _
  linarith

theorem norm_sub_le_of_mem_disc {p r : ℝ} {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) :
    ‖z - p‖ ≤ r := by
  rwa [mem_closedBall, dist_eq_norm] at hz

theorem re_pos_of_mem_disc {s p r : ℝ} (hp0 : 0 < p) (hr : GoodRadius s p r) {z : ℂ}
    (hz : z ∈ closedBall (p : ℂ) r) : 0 < z.re := by
  have h := Complex.abs_re_le_norm (z - p)
  rw [Complex.sub_re, Complex.ofReal_re] at h
  have := neg_le_of_abs_le h
  have := norm_sub_le_of_mem_disc hz
  have := r_le_p hr
  linarith

theorem re_one_sub_pos_of_mem_disc {s p r : ℝ} (hp1 : p < 1) (hr : GoodRadius s p r) {z : ℂ}
    (hz : z ∈ closedBall (p : ℂ) r) : 0 < (1 - z).re := by
  have h := Complex.abs_re_le_norm (z - p)
  rw [Complex.sub_re, Complex.ofReal_re] at h
  have := le_of_abs_le h
  have := norm_sub_le_of_mem_disc hz
  have := r_le_one_sub_p hr
  rw [Complex.sub_re, Complex.one_re]
  linarith

theorem norm_le_of_mem_disc {s p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : GoodRadius s p r)
    {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) : ‖z‖ ≤ 3/2 := by
  have := norm_sub_le_of_mem_disc hz
  have := r_le_one_sub_p hr
  calc ‖z‖ = ‖(p : ℂ) + (z - p)‖ := by ring_nf
    _ ≤ ‖(p : ℂ)‖ + ‖z - p‖ := norm_add_le _ _
    _ ≤ 3/2 := by rw [Complex.norm_real, Real.norm_of_nonneg hp0.le]; linarith

theorem norm_one_sub_le_of_mem_disc {s p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) : ‖1 - z‖ ≤ 3/2 := by
  have := norm_sub_le_of_mem_disc hz
  have := r_le_p hr
  calc ‖1 - z‖ = ‖((1 - p : ℝ) : ℂ) - (z - p)‖ := by push_cast; ring_nf
    _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖z - p‖ := norm_sub_le _ _
    _ ≤ 3/2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith

theorem norm_add_norm_one_sub_le_of_mem_disc {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {z : ℂ}
    (hz : z ∈ closedBall (p : ℂ) r) : ‖z‖ + ‖1 - z‖ ≤ 1 + 2 * r := by
  have h := norm_sub_le_of_mem_disc hz
  have h1 : ‖z‖ ≤ p + r := by
    calc ‖z‖ = ‖(p : ℂ) + (z - p)‖ := by ring_nf
      _ ≤ ‖(p : ℂ)‖ + ‖z - p‖ := norm_add_le _ _
      _ ≤ p + r := by rw [Complex.norm_real, Real.norm_of_nonneg hp0.le]; linarith
  have h2 : ‖1 - z‖ ≤ (1 - p) + r := by
    calc ‖1 - z‖ = ‖((1 - p : ℝ) : ℂ) - (z - p)‖ := by push_cast; ring_nf
      _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖z - p‖ := norm_sub_le _ _
      _ ≤ (1 - p) + r := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  linarith

/-- `‖w‖^{1/s - 1} ≤ (3/2)^{1/s - 1}` for `‖w‖ ≤ 3/2`. -/
theorem norm_rpow_inv_sub_one_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {w : ℂ} (hw : ‖w‖ ≤ 3/2) :
    ‖w‖ ^ (s⁻¹ - 1) ≤ (3/2 : ℝ) ^ (s⁻¹ - 1) := by
  have : (1:ℝ) < s⁻¹ := one_lt_inv_iff₀.2 ⟨hs, hs1⟩
  exact Real.rpow_le_rpow (norm_nonneg _) hw (by linarith)

theorem hasDerivAt_ca {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) :
    HasDerivAt (ca s) (((s⁻¹ : ℝ) : ℂ) * z ^ (((s⁻¹ : ℝ) : ℂ) - 1) * 1) z ∧
    ‖((s⁻¹ : ℝ) : ℂ) * z ^ (((s⁻¹ : ℝ) : ℂ) - 1) * 1‖ ≤ lipA s := by
  have hslit : z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (re_pos_of_mem_disc hp0 hr hz))
  refine ⟨(hasDerivAt_id z).cpow_const hslit, ?_⟩
  rw [mul_one, norm_mul, show (((s⁻¹ : ℝ) : ℂ) - 1) = ((s⁻¹ - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  unfold lipA
  exact mul_le_mul_of_nonneg_left
    (norm_rpow_inv_sub_one_le hs hs1 (norm_le_of_mem_disc hp0 hp1 hr hz)) (inv_nonneg.2 hs.le)

theorem hasDerivAt_cb {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) :
    HasDerivAt (cb s) (((s⁻¹ : ℝ) : ℂ) * (1 - z) ^ (((s⁻¹ : ℝ) : ℂ) - 1) * (-1)) z ∧
    ‖((s⁻¹ : ℝ) : ℂ) * (1 - z) ^ (((s⁻¹ : ℝ) : ℂ) - 1) * (-1)‖ ≤ lipA s := by
  have hslit : 1 - z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (re_one_sub_pos_of_mem_disc hp1 hr hz))
  refine ⟨((hasDerivAt_id z).const_sub 1).cpow_const hslit, ?_⟩
  rw [norm_mul, norm_neg, norm_one, mul_one, norm_mul,
    show (((s⁻¹ : ℝ) : ℂ) - 1) = ((s⁻¹ - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  unfold lipA
  exact mul_le_mul_of_nonneg_left
    (norm_rpow_inv_sub_one_le hs hs1 (norm_one_sub_le_of_mem_disc hp0 hp1 hr hz))
    (inv_nonneg.2 hs.le)

/-- `|a(z) - a(w)| ≤ L|z - w|` on the disc. -/
theorem norm_ca_sub_le {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z w : ℂ} (hz : z ∈ closedBall (p : ℂ) r)
    (hw : w ∈ closedBall (p : ℂ) r) : ‖ca s z - ca s w‖ ≤ lipA s * ‖z - w‖ :=
  (convex_closedBall _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ca s) (f' := fun z => ((s⁻¹ : ℝ) : ℂ) * z ^ (((s⁻¹ : ℝ) : ℂ) - 1) * 1)
    (fun _ hv => (hasDerivAt_ca hs hs1 hp0 hp1 hr hv).1.hasDerivWithinAt)
    (fun _ hv => (hasDerivAt_ca hs hs1 hp0 hp1 hr hv).2) hw hz

/-- `|b(z) - b(w)| ≤ L|z - w|` on the disc. -/
theorem norm_cb_sub_le {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z w : ℂ} (hz : z ∈ closedBall (p : ℂ) r)
    (hw : w ∈ closedBall (p : ℂ) r) : ‖cb s z - cb s w‖ ≤ lipA s * ‖z - w‖ :=
  (convex_closedBall _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := cb s) (f' := fun z => ((s⁻¹ : ℝ) : ℂ) * (1 - z) ^ (((s⁻¹ : ℝ) : ℂ) - 1) * (-1))
    (fun _ hv => (hasDerivAt_cb hs hs1 hp0 hp1 hr hv).1.hasDerivWithinAt)
    (fun _ hv => (hasDerivAt_cb hs hs1 hp0 hp1 hr hv).2) hw hz

theorem ofReal_mem_disc {s p r : ℝ} (hr : GoodRadius s p r) : (p : ℂ) ∈ closedBall (p : ℂ) r :=
  mem_closedBall_self hr.pos.le

theorem norm_ca_ofReal {s p : ℝ} (hp0 : 0 < p) : ‖ca s (p : ℂ)‖ = fixedA s p := by
  rw [ca_ofReal hp0.le, Complex.norm_real, Real.norm_of_nonneg (fixedA_pos (s := s) hp0).le]

theorem norm_cb_ofReal {s p : ℝ} (hp1 : p < 1) : ‖cb s (p : ℂ)‖ = fixedB s p := by
  rw [cb_ofReal hp1.le, Complex.norm_real, Real.norm_of_nonneg (fixedB_pos (s := s) hp1).le]

/-- `|a(z)| ≤ γ` on the disc. -/
theorem norm_ca_le_gamma1 {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) :
    ‖ca s z‖ ≤ gamma1 s p := by
  have h := norm_ca_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)
  have h2 := norm_sub_le_of_mem_disc hz
  have h3 : lipA s * ‖z - p‖ ≤ lipA s * r := mul_le_mul_of_nonneg_left h2 (lipA_pos hs).le
  have h4 := hr.lip
  have h5 := fixedA_le_gamma0 s p
  unfold gamma1
  calc ‖ca s z‖ = ‖ca s (p : ℂ) + (ca s z - ca s (p : ℂ))‖ := by ring_nf
    _ ≤ ‖ca s (p : ℂ)‖ + ‖ca s z - ca s (p : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 + gamma0 s p) / 2 := by rw [norm_ca_ofReal hp0]; linarith

/-- `|b(z)| ≤ γ` on the disc. -/
theorem norm_cb_le_gamma1 {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) :
    ‖cb s z‖ ≤ gamma1 s p := by
  have h := norm_cb_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)
  have h2 := norm_sub_le_of_mem_disc hz
  have h3 : lipA s * ‖z - p‖ ≤ lipA s * r := mul_le_mul_of_nonneg_left h2 (lipA_pos hs).le
  have h4 := hr.lip
  have h5 := fixedB_le_gamma0 s p
  unfold gamma1
  calc ‖cb s z‖ = ‖cb s (p : ℂ) + (cb s z - cb s (p : ℂ))‖ := by ring_nf
    _ ≤ ‖cb s (p : ℂ)‖ + ‖cb s z - cb s (p : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 + gamma0 s p) / 2 := by rw [norm_cb_ofReal hp1]; linarith

theorem norm_ca_lt_one {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) : ‖ca s z‖ < 1 :=
  (norm_ca_le_gamma1 hs hs1 hp0 hp1 hr hz).trans_lt (gamma1_lt_one hs hp0 hp1)

theorem norm_cb_le_one {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) : ‖cb s z‖ ≤ 1 :=
  ((norm_cb_le_gamma1 hs hs1 hp0 hp1 hr hz).trans_lt (gamma1_lt_one hs hp0 hp1)).le

/-- `|x_w(z)| ≤ R` on the disc. -/
theorem norm_cpointSeq_le_radR {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) (m : ℕ)
    (ω : ℕ → Fin 2) : ‖cpointSeq (ca s z) (cb s z) m ω‖ ≤ radR s p := by
  have h := norm_cpointSeq_le (norm_ca_lt_one hs hs1 hp0 hp1 hr hz)
    (norm_cb_le_one hs hs1 hp0 hp1 hr hz) m ω
  refine h.trans ?_
  rw [← two_div_one_sub_gamma1 hs hp0 hp1]
  have h1 := norm_ca_le_gamma1 hs hs1 hp0 hp1 hr hz
  have h2 := gamma1_lt_one hs hp0 hp1
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- The ratio of a letter is Lipschitz in the parameter. -/
theorem norm_cratioOf_sub_le {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) (i : Fin 2) :
    ‖cratioOf (ca s z) (cb s z) i - cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) i‖
      ≤ lipA s * ‖z - p‖ := by
  rcases fin_two_cases i with rfl | rfl
  · simp only [cratioOf, ite_true]
    exact norm_ca_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)
  · simp only [cratioOf, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
    exact norm_cb_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)

/-- The shift of a letter is Lipschitz in the parameter. -/
theorem norm_cshiftOf_sub_le {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) (i : Fin 2) :
    ‖cshiftOf (cb s z) i - cshiftOf (cb s (p : ℂ)) i‖ ≤ lipA s * ‖z - p‖ := by
  rcases fin_two_cases i with rfl | rfl
  · simp only [cshiftOf, ite_true, sub_zero, norm_zero]
    have := lipA_pos hs
    positivity
  · simp only [cshiftOf, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
    rw [show (1 - cb s z) - (1 - cb s (p : ℂ)) = -(cb s z - cb s (p : ℂ)) by ring, norm_neg]
    exact norm_cb_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)

theorem norm_cratioOf_ofReal_le {s p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin 2) :
    ‖cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) i‖ ≤ gamma0 s p := by
  rcases fin_two_cases i with rfl | rfl
  · simp only [cratioOf, ite_true]
    rw [norm_ca_ofReal hp0]; exact fixedA_le_gamma0 s p
  · simp only [cratioOf, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
    rw [norm_cb_ofReal hp1]; exact fixedB_le_gamma0 s p

/-- **`|x_w(z) - x_w(p₀)| ≤ C|z - p₀|`**, uniformly in the word. -/
theorem norm_cpointSeq_sub_le {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hr : GoodRadius s p r) {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) (m : ℕ) (ω : ℕ → Fin 2) :
    ‖cpointSeq (ca s z) (cb s z) m ω - cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m ω‖
      ≤ lipC s p * ‖z - p‖ := by
  have hC := lipC_pos hs hp0 hp1
  have hγ0 := gamma0_lt_one hs hp0 hp1
  have hγ0' := gamma0_nonneg (s := s) hp0
  have hR := radR_pos hs hp0 hp1
  have hL := lipA_pos hs
  have hzp : 0 ≤ ‖z - p‖ := norm_nonneg _
  induction m generalizing ω with
  | zero => simp only [cpointSeq_zero, sub_zero, norm_zero]; positivity
  | succ m ih =>
    rw [cpointSeq_succ, cpointSeq_succ]
    set x := cpointSeq (ca s z) (cb s z) m (tail ω)
    set x' := cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m (tail ω)
    have hx := norm_cpointSeq_le_radR hs hs1 hp0 hp1 hr hz m (tail ω)
    have hxx := ih (tail ω)
    have e : cmap (ca s z) (cb s z) (ω 0) x - cmap (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0) x'
        = (cratioOf (ca s z) (cb s z) (ω 0) - cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0)) * x
          + cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0) * (x - x')
          + (cshiftOf (cb s z) (ω 0) - cshiftOf (cb s (p : ℂ)) (ω 0)) := by
      unfold cmap; ring
    rw [e]
    have h1 := norm_cratioOf_sub_le hs hs1 hp0 hp1 hr hz (ω 0)
    have h2 := norm_cratioOf_ofReal_le (s := s) hp0 hp1 (ω 0)
    have h3 := norm_cshiftOf_sub_le hs hs1 hp0 hp1 hr hz (ω 0)
    have hkey : lipA s * (radR s p + 1) + gamma0 s p * lipC s p = lipC s p := by
      have hne : 1 - gamma0 s p ≠ 0 := by linarith
      unfold lipC; field_simp; ring
    calc ‖(cratioOf (ca s z) (cb s z) (ω 0) - cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0)) * x
          + cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0) * (x - x')
          + (cshiftOf (cb s z) (ω 0) - cshiftOf (cb s (p : ℂ)) (ω 0))‖
        ≤ ‖(cratioOf (ca s z) (cb s z) (ω 0) - cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0)) * x‖
          + ‖cratioOf (ca s (p : ℂ)) (cb s (p : ℂ)) (ω 0) * (x - x')‖
          + ‖cshiftOf (cb s z) (ω 0) - cshiftOf (cb s (p : ℂ)) (ω 0)‖ := norm_add₃_le
      _ ≤ lipA s * ‖z - p‖ * radR s p + gamma0 s p * (lipC s p * ‖z - p‖)
          + lipA s * ‖z - p‖ := by
          rw [norm_mul, norm_mul]
          gcongr
      _ = (lipA s * (radR s p + 1) + gamma0 s p * lipC s p) * ‖z - p‖ := by ring
      _ = lipC s p * ‖z - p‖ := by rw [hkey]

end

end BrownianImages
