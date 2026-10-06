/-
`thm:fixed-dimension-analyticity`: for every `s ∈ (0,1)`, `p ↦ M_p(s)` and `p ↦ H̄_s(p)` are
real analytic on `(0,1)`.

On the disc `|z - p₀| ≤ r` of `GoodRadius`, the coded points stay in the `δ`-neighbourhood
`D` of `[0,1]`, `δ = C r`, every cross distance `d_{u,v}(z)` has real part at least `g₀/2`,
so the kernel `d^{-s}` is holomorphic and Lipschitz on `D × D`, the level sums converge
uniformly to a holomorphic `M_z` with `M_x = M_x(s)` on the real diameter, and the restriction
of a holomorphic function to the real line is real analytic.

* `nbhdIcc`: the neighbourhood `D`.
* `re_crossBase_ge_of_mem`: the lower bound on the cross distances.
* `incrementBound_disc`: the telescoping bound on the disc.
* `crossLimit_eq_fixedMoment_of_mem`: `M_x = M_x(s)` on the real diameter.
* `analyticAt_fixedMoment`, `analyticAt_fixedMean`: `thm:fixed-dimension-analyticity`.
-/
import BrownianImages.FixedDimension.ParameterLipschitz
import BrownianImages.FixedDimension.LevelSumsDomain

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- The `δ`-neighbourhood of `[0,1]` in `ℂ`. -/
def nbhdIcc (δ : ℝ) : Set ℂ := {x | ∃ t : ℝ, t ∈ Icc (0:ℝ) 1 ∧ ‖x - t‖ ≤ δ}

theorem mem_nbhdIcc {δ : ℝ} {x : ℂ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (h : ‖x - t‖ ≤ δ) :
    x ∈ nbhdIcc δ := ⟨t, ht, h⟩

theorem convex_nbhdIcc (δ : ℝ) : Convex ℝ (nbhdIcc δ) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨u, hu, hyu⟩ := hy
  refine ⟨a * t + b * u, (convex_Icc (0:ℝ) 1) ht hu ha hb hab, ?_⟩
  have e : a • x + b • y - ((a * t + b * u : ℝ) : ℂ) = a • (x - t) + b • (y - u) := by
    push_cast; simp only [Complex.real_smul]; ring
  rw [e]
  calc ‖a • (x - (t : ℂ)) + b • (y - (u : ℂ))‖
      ≤ ‖a • (x - (t : ℂ))‖ + ‖b • (y - (u : ℂ))‖ := norm_add_le _ _
    _ = a * ‖x - t‖ + b * ‖y - u‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * δ + b * δ :=
        add_le_add (mul_le_mul_of_nonneg_left hxt ha) (mul_le_mul_of_nonneg_left hyu hb)
    _ = δ := by rw [← add_mul, hab, one_mul]

theorem norm_le_of_mem_nbhdIcc {δ : ℝ} {x : ℂ} (hx : x ∈ nbhdIcc δ) : ‖x‖ ≤ 1 + δ := by
  obtain ⟨t, ht, hxt⟩ := hx
  calc ‖x‖ = ‖(t : ℂ) + (x - t)‖ := by ring_nf
    _ ≤ ‖(t : ℂ)‖ + ‖x - t‖ := norm_add_le _ _
    _ ≤ 1 + δ := by
        rw [Complex.norm_real, Real.norm_of_nonneg ht.1]
        exact add_le_add ht.2 hxt

theorem ofReal_mem_nbhdIcc {δ : ℝ} (hδ : 0 ≤ δ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (t : ℂ) ∈ nbhdIcc δ := ⟨t, ht, by rw [sub_self, norm_zero]; exact hδ⟩

section Disc

variable {s p r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
  (hr : GoodRadius s p r)
include hs hs1 hp0 hp1 hr

/-- The coded points of the disc lie in the `δ`-neighbourhood of `[0,1]`, `δ = C r`. -/
theorem cpointSeq_mem_nbhdIcc {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) (m : ℕ) (ω : ℕ → Fin 2) :
    cpointSeq (ca s z) (cb s z) m ω ∈ nbhdIcc (lipC s p * r) := by
  refine mem_nbhdIcc (codeSeq_mem_Icc (fixedSystem s p hs hp0 hp1) ω m) ?_
  rw [← cpointSeq_ofReal hs hp0 hp1, ← ca_ofReal hp0.le, ← cb_ofReal hp1.le]
  refine (norm_cpointSeq_sub_le hs hs1 hp0 hp1 hr hz m ω).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_disc hz) (lipC_pos hs hp0 hp1).le

omit hs1 in
theorem delta_nonneg : 0 ≤ lipC s p * r := mul_nonneg (lipC_pos hs hp0 hp1).le hr.pos.le

/-- Every cross distance of the disc has real part at least `g₀/2`. -/
theorem re_crossBase_ge_of_mem {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) {x y : ℂ}
    (hx : x ∈ nbhdIcc (lipC s p * r)) (hy : y ∈ nbhdIcc (lipC s p * r)) :
    crossGap s p / 2 ≤ (crossBase s z x y).re := by
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨u, hu, hyu⟩ := hy
  set δ := lipC s p * r with hδ
  have hδ0 : 0 ≤ δ := delta_nonneg hs hp0 hp1 hr
  have hδ1 : δ ≤ 1 := hr.delta_le_one
  have hzp := norm_sub_le_of_mem_disc hz
  have hL := lipA_pos hs
  have hΔa : ‖ca s z - ca s (p : ℂ)‖ ≤ lipA s * r :=
    (norm_ca_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)).trans
      (mul_le_mul_of_nonneg_left hzp hL.le)
  have hΔb : ‖cb s z - cb s (p : ℂ)‖ ≤ lipA s * r :=
    (norm_cb_sub_le hs hs1 hp0 hp1 hr hz (ofReal_mem_disc hr)).trans
      (mul_le_mul_of_nonneg_left hzp hL.le)
  have ha0 : ‖ca s (p : ℂ)‖ ≤ gamma0 s p := by rw [norm_ca_ofReal hp0]; exact fixedA_le_gamma0 s p
  have hb0 : ‖cb s (p : ℂ)‖ ≤ gamma0 s p := by rw [norm_cb_ofReal hp1]; exact fixedB_le_gamma0 s p
  have hxn : ‖x‖ ≤ 1 + δ := norm_le_of_mem_nbhdIcc ⟨t, ht, hxt⟩
  have hyn : ‖y‖ ≤ 1 + δ := norm_le_of_mem_nbhdIcc ⟨u, hu, hyu⟩
  have hγ0 := gamma0_nonneg (s := s) hp0
  -- the decomposition of the cross distance
  set D : ℂ := -(cb s z - cb s (p : ℂ)) + (cb s z - cb s (p : ℂ)) * y + cb s (p : ℂ) * (y - u)
    + (-((ca s z - ca s (p : ℂ)) * x)) + (-(ca s (p : ℂ) * (x - t))) with hD
  have e : crossBase s z x y = crossBase s (p : ℂ) t u + D := by
    rw [hD]; unfold crossBase; ring
  have hDn : ‖D‖ ≤ lipA s * r + lipA s * r * (1 + δ) + gamma0 s p * δ + lipA s * r * (1 + δ)
      + gamma0 s p * δ := by
    rw [hD]
    refine norm_add₃_le.trans (add_le_add_three (norm_add₃_le.trans (add_le_add_three ?_ ?_ ?_))
      ?_ ?_)
    · rw [norm_neg]; exact hΔb
    · rw [norm_mul]; exact mul_le_mul hΔb hyn (norm_nonneg _) (mul_nonneg hL.le hr.pos.le)
    · rw [norm_mul]; exact mul_le_mul hb0 hyu (norm_nonneg _) hγ0
    · rw [norm_neg, norm_mul]; exact mul_le_mul hΔa hxn (norm_nonneg _) (mul_nonneg hL.le hr.pos.le)
    · rw [norm_neg, norm_mul]; exact mul_le_mul ha0 hxt (norm_nonneg _) hγ0
  have hgap := hr.gap
  have hDn' : ‖D‖ ≤ crossGap s p / 2 := by
    have h5 : lipA s * r + lipA s * r * (1 + δ) + lipA s * r * (1 + δ) ≤ 5 * lipA s * r := by
      have : 0 ≤ lipA s * r := mul_nonneg hL.le hr.pos.le
      nlinarith
    have h6 : gamma0 s p * δ + gamma0 s p * δ = 2 * gamma0 s p * lipC s p * r := by
      rw [hδ]; ring
    have : lipA s * r + lipA s * r * (1 + δ) + gamma0 s p * δ + lipA s * r * (1 + δ)
        + gamma0 s p * δ ≤ r * (5 * lipA s + 2 * gamma0 s p * lipC s p) := by nlinarith
    linarith
  have hreal : (crossBase s (p : ℂ) t u).re = fixedCross s p t u := by
    rw [crossBase_ofReal hp0.le hp1.le, Complex.ofReal_re]
  have hcross := (fixedCross_mem hs hp0 hp1 ht hu).1
  have hDre : -‖D‖ ≤ D.re := by
    have := Complex.abs_re_le_norm D
    linarith [neg_le_of_abs_le this]
  rw [e, Complex.add_re, hreal]
  unfold crossGap at hDn' ⊢
  linarith

theorem crossBase_mem_slitPlane_of_mem {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) {x y : ℂ}
    (hx : x ∈ nbhdIcc (lipC s p * r)) (hy : y ∈ nbhdIcc (lipC s p * r)) :
    crossBase s z x y ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have := re_crossBase_ge_of_mem hs hs1 hp0 hp1 hr hz hx hy
  have := crossGap_pos hs hs1 hp0 hp1
  linarith

theorem norm_crossBase_ge_of_mem {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) {x y : ℂ}
    (hx : x ∈ nbhdIcc (lipC s p * r)) (hy : y ∈ nbhdIcc (lipC s p * r)) :
    crossGap s p / 2 ≤ ‖crossBase s z x y‖ :=
  (re_crossBase_ge_of_mem hs hs1 hp0 hp1 hr hz hx hy).trans (Complex.re_le_norm _)

omit hr in
/-- The Lipschitz constant `s (g₀/2)^{-s-1}` of the kernel on `D × D`. -/
theorem lipK_nonneg : 0 ≤ s * (crossGap s p / 2) ^ (-s - 1) :=
  mul_nonneg hs.le (Real.rpow_nonneg (by linarith [crossGap_pos hs hs1 hp0 hp1]) _)

/-- The derivative of the kernel in `x`, with its bound. -/
theorem hasDerivAt_crossKernelC_x_disc {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) {x y : ℂ}
    (hx : x ∈ nbhdIcc (lipC s p * r)) (hy : y ∈ nbhdIcc (lipC s p * r)) :
    HasDerivAt (fun x => crossKernelC s z x y)
      (-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (-(ca s z * 1))) x ∧
    ‖-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (-(ca s z * 1))‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) := by
  have hbase : HasDerivAt (fun x => crossBase s z x y) (-(ca s z * 1)) x := by
    unfold crossBase
    exact ((hasDerivAt_id x).const_mul (ca s z)).const_sub _
  refine ⟨hbase.cpow_const (crossBase_mem_slitPlane_of_mem hs hs1 hp0 hp1 hr hz hx hy), ?_⟩
  rw [norm_mul, norm_mul, norm_neg, norm_neg, mul_one, norm_cpow_neg_real_sub_one,
    show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
  have hg : 0 < crossGap s p / 2 := by linarith [crossGap_pos hs hs1 hp0 hp1]
  have h1 : ‖crossBase s z x y‖ ^ (-s - 1) ≤ (crossGap s p / 2) ^ (-s - 1) := by
    rw [show (-s - 1) = -(s + 1) by ring]
    exact rpow_neg_antitone hg (norm_crossBase_ge_of_mem hs hs1 hp0 hp1 hr hz hx hy) (by linarith)
  have h2 : ‖ca s z‖ ≤ 1 := (norm_ca_lt_one hs hs1 hp0 hp1 hr hz).le
  calc s * ‖crossBase s z x y‖ ^ (-s - 1) * ‖ca s z‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hs.le) h2 (norm_nonneg _) (by positivity)
    _ = s * (crossGap s p / 2) ^ (-s - 1) := mul_one _

/-- The derivative of the kernel in `y`, with its bound. -/
theorem hasDerivAt_crossKernelC_y_disc {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) {x y : ℂ}
    (hx : x ∈ nbhdIcc (lipC s p * r)) (hy : y ∈ nbhdIcc (lipC s p * r)) :
    HasDerivAt (fun y => crossKernelC s z x y)
      (-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (cb s z * 1)) y ∧
    ‖-(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (cb s z * 1)‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) := by
  have hbase : HasDerivAt (fun y => crossBase s z x y) (cb s z * 1) y := by
    unfold crossBase
    exact (((hasDerivAt_id y).const_mul (cb s z)).const_add _).sub_const _
  refine ⟨hbase.cpow_const (crossBase_mem_slitPlane_of_mem hs hs1 hp0 hp1 hr hz hx hy), ?_⟩
  rw [norm_mul, norm_mul, norm_neg, mul_one, norm_cpow_neg_real_sub_one,
    show ‖(s : ℂ)‖ = s by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]]
  have hg : 0 < crossGap s p / 2 := by linarith [crossGap_pos hs hs1 hp0 hp1]
  have h1 : ‖crossBase s z x y‖ ^ (-s - 1) ≤ (crossGap s p / 2) ^ (-s - 1) := by
    rw [show (-s - 1) = -(s + 1) by ring]
    exact rpow_neg_antitone hg (norm_crossBase_ge_of_mem hs hs1 hp0 hp1 hr hz hx hy) (by linarith)
  have h2 : ‖cb s z‖ ≤ 1 := norm_cb_le_one hs hs1 hp0 hp1 hr hz
  calc s * ‖crossBase s z x y‖ ^ (-s - 1) * ‖cb s z‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hs.le) h2 (norm_nonneg _) (by positivity)
    _ = s * (crossGap s p / 2) ^ (-s - 1) := mul_one _

/-- The kernel is Lipschitz on `D × D`. -/
theorem norm_crossKernelC_sub_le_disc {z : ℂ} (hz : z ∈ closedBall (p : ℂ) r) (x y x' y' : ℂ)
    (hx : x ∈ nbhdIcc (lipC s p * r)) (hy : y ∈ nbhdIcc (lipC s p * r))
    (hx' : x' ∈ nbhdIcc (lipC s p * r)) (hy' : y' ∈ nbhdIcc (lipC s p * r)) :
    ‖crossKernelC s z x' y' - crossKernelC s z x y‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) * (‖x' - x‖ + ‖y' - y‖) := by
  have hconv := convex_nbhdIcc (lipC s p * r)
  have h1 : ‖crossKernelC s z x' y' - crossKernelC s z x y'‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) * ‖x' - x‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => crossKernelC s z x y')
      (f' := fun x => -(s : ℂ) * crossBase s z x y' ^ (-(s : ℂ) - 1) * (-(ca s z * 1)))
      (fun w hw => (hasDerivAt_crossKernelC_x_disc hs hs1 hp0 hp1 hr hz hw hy').1.hasDerivWithinAt)
      (fun w hw => (hasDerivAt_crossKernelC_x_disc hs hs1 hp0 hp1 hr hz hw hy').2) hx hx'
  have h2 : ‖crossKernelC s z x y' - crossKernelC s z x y‖
      ≤ s * (crossGap s p / 2) ^ (-s - 1) * ‖y' - y‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => crossKernelC s z x y)
      (f' := fun y => -(s : ℂ) * crossBase s z x y ^ (-(s : ℂ) - 1) * (cb s z * 1))
      (fun w hw => (hasDerivAt_crossKernelC_y_disc hs hs1 hp0 hp1 hr hz hx hw).1.hasDerivWithinAt)
      (fun w hw => (hasDerivAt_crossKernelC_y_disc hs hs1 hp0 hp1 hr hz hx hw).2) hy hy'
  calc ‖crossKernelC s z x' y' - crossKernelC s z x y‖
      = ‖(crossKernelC s z x' y' - crossKernelC s z x y') +
          (crossKernelC s z x y' - crossKernelC s z x y)‖ := by ring_nf
    _ ≤ ‖crossKernelC s z x' y' - crossKernelC s z x y'‖ +
          ‖crossKernelC s z x y' - crossKernelC s z x y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = s * (crossGap s p / 2) ^ (-s - 1) * (‖x' - x‖ + ‖y' - y‖) := by ring

omit hs1 hr in
theorem gamma1_mul_sq_lt_one (hr : GoodRadius s p r) : gamma1 s p * (1 + 2 * r) ^ 2 < 1 := by
  have hγ := gamma1_lt_one hs hp0 hp1
  have hγ0 := gamma1_nonneg (s := s) hp0
  have hsmall := hr.small
  have hr0 := hr.pos
  have hr4 : r ≤ 1/4 := by
    have := hr.le_half
    have : min p (1 - p) ≤ p := min_le_left _ _
    have : min p (1 - p) ≤ 1 - p := min_le_right _ _
    linarith
  have h1 : (1 + 2 * r) ^ 2 ≤ 1 + 6 * r := by nlinarith
  have h2 : gamma1 s p * (1 + 6 * r) < 1 := by nlinarith
  calc gamma1 s p * (1 + 2 * r) ^ 2 ≤ gamma1 s p * (1 + 6 * r) :=
        mul_le_mul_of_nonneg_left h1 hγ0
    _ < 1 := h2

/-- The telescoping bound on the disc. -/
theorem incrementBound_disc :
    IncrementBound (ca s) (cb s) (crossKernelC s) (closedBall (p : ℂ) r)
      (4 * (s * (crossGap s p / 2) ^ (-s - 1)) * (1 + 2 * r) ^ 2)
      (gamma1 s p * (1 + 2 * r) ^ 2) := by
  intro z hz m
  have hb : ‖cb s z‖ ≤ 1 := norm_cb_le_one hs hs1 hp0 hp1 hr hz
  have hρ : max ‖ca s z‖ ‖cb s z‖ ≤ gamma1 s p :=
    max_le (norm_ca_le_gamma1 hs hs1 hp0 hp1 hr hz) (norm_cb_le_gamma1 hs hs1 hp0 hp1 hr hz)
  have hB := norm_add_norm_one_sub_le_of_mem_disc hp0 hp1 hz
  have h := norm_levelSum_succ_sub_le_of_mem (ca s) (cb s) (crossKernelC s) m hb hρ hB
    (fun n ω => cpointSeq_mem_nbhdIcc hs hs1 hp0 hp1 hr hz n ω) (lipK_nonneg hs hs1 hp0 hp1)
    (fun x y x' y' hx hy hx' hy' =>
      norm_crossKernelC_sub_le_disc hs hs1 hp0 hp1 hr hz x y x' y' hx hy hx' hy')
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul]
  ring

omit hs hs1 hp1 in
theorem differentiableOn_ca_disc : DifferentiableOn ℂ (ca s) (closedBall (p : ℂ) r) := by
  unfold ca
  exact differentiableOn_id.cpow_const fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_pos_of_mem_disc hp0 hr hz))

omit hs hs1 hp0 in
theorem differentiableOn_cb_disc : DifferentiableOn ℂ (cb s) (closedBall (p : ℂ) r) := by
  unfold cb
  exact ((differentiableOn_const _).sub differentiableOn_id).cpow_const fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_one_sub_pos_of_mem_disc hp1 hr hz))

omit hs hs1 in
theorem differentiableOn_cpointSeq_disc (m : ℕ) (ω : ℕ → Fin 2) :
    DifferentiableOn ℂ (fun z => cpointSeq (ca s z) (cb s z) m ω) (closedBall (p : ℂ) r) := by
  induction m generalizing ω with
  | zero => simp only [cpointSeq_zero]; exact differentiableOn_const 0
  | succ m ih =>
    simp only [cpointSeq_succ, cmap, cratioOf, cshiftOf]
    have ha := differentiableOn_ca_disc (s := s) hp0 hr
    have hb := differentiableOn_cb_disc (s := s) hp1 hr
    split_ifs
    · exact (ha.mul (ih _)).add (differentiableOn_const 0)
    · exact (hb.mul (ih _)).add ((differentiableOn_const _).sub hb)

theorem differentiableOn_levelSum_disc (m : ℕ) :
    DifferentiableOn ℂ (levelSum (ca s) (cb s) (crossKernelC s) m) (closedBall (p : ℂ) r) := by
  unfold levelSum
  refine DifferentiableOn.fun_sum fun u _ => ?_
  refine DifferentiableOn.fun_sum fun v _ => ?_
  refine ((differentiableOn_weightSeq m (extend u) _).mul
    (differentiableOn_weightSeq m (extend v) _)).mul ?_
  unfold crossKernelC
  refine DifferentiableOn.cpow_const ?_ fun z hz =>
    crossBase_mem_slitPlane_of_mem hs hs1 hp0 hp1 hr hz
      (cpointSeq_mem_nbhdIcc hs hs1 hp0 hp1 hr hz m _)
      (cpointSeq_mem_nbhdIcc hs hs1 hp0 hp1 hr hz m _)
  unfold crossBase
  have ha := differentiableOn_ca_disc (s := s) hp0 hr
  have hb := differentiableOn_cb_disc (s := s) hp1 hr
  have hX := differentiableOn_cpointSeq_disc hp0 hp1 hr m (extend u)
  have hY := differentiableOn_cpointSeq_disc hp0 hp1 hr m (extend v)
  exact (((differentiableOn_const _).sub hb).add (hb.mul hY)).sub (ha.mul hX)

omit hs hs1 hp1 hr in
theorem discRatio_nonneg : 0 ≤ gamma1 s p * (1 + 2 * r) ^ 2 :=
  mul_nonneg (gamma1_nonneg (s := s) hp0) (by positivity)

/-- `M_z` is holomorphic on the open disc. -/
theorem differentiableOn_crossLimit_disc :
    DifferentiableOn ℂ (crossLimit s) (ball (p : ℂ) r) :=
  differentiableOn_limitSum (discRatio_nonneg (s := s) (r := r) hp0) (gamma1_mul_sq_lt_one hs hp0 hp1 hr)
    (incrementBound_disc hs hs1 hp0 hp1 hr) isOpen_ball ball_subset_closedBall
    fun m => (differentiableOn_levelSum_disc hs hs1 hp0 hp1 hr m).mono ball_subset_closedBall

theorem continuousOn_crossLimit_disc : ContinuousOn (crossLimit s) (closedBall (p : ℂ) r) :=
  continuousOn_limitSum (discRatio_nonneg (s := s) (r := r) hp0) (gamma1_mul_sq_lt_one hs hp0 hp1 hr)
    (incrementBound_disc hs hs1 hp0 hp1 hr)
    fun m => (differentiableOn_levelSum_disc hs hs1 hp0 hp1 hr m).continuousOn

omit hs hs1 hp0 hp1 hr in
theorem ofReal_mem_closedBall_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (p - r) (p + r)) :
    (x : ℂ) ∈ closedBall (p : ℂ) r := by
  rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_le]
  constructor <;> linarith [hx.1, hx.2]

omit hs hs1 in
theorem mem_Ioo_zero_one_of_mem {x : ℝ} (hx : x ∈ Ioo (p - r) (p + r)) : 0 < x ∧ x < 1 := by
  have := r_le_p hr
  have := r_le_one_sub_p hr
  constructor <;> linarith [hx.1, hx.2]

/-- **`M_x = M_x(s)`** on the real diameter of the disc. -/
theorem crossLimit_eq_fixedMoment_of_mem {x : ℝ} (hx : x ∈ Ioo (p - r) (p + r)) :
    crossLimit s (x : ℂ) = ((fixedMoment s x : ℝ) : ℂ) := by
  obtain ⟨hx0, hx1⟩ := mem_Ioo_zero_one_of_mem hp0 hp1 hr hx
  have h1 := tendsto_levelSum (discRatio_nonneg (s := s) (r := r) hp0)
    (gamma1_mul_sq_lt_one hs hp0 hp1 hr) (incrementBound_disc hs hs1 hp0 hp1 hr)
    (ofReal_mem_closedBall_of_mem_Ioo hx)
  have h2 := tendsto_levelSum_ofReal hs hs1 hx0 hx1
  exact tendsto_nhds_unique h1 h2

end Disc

/-! ### `thm:fixed-dimension-analyticity` -/

/-- **`thm:fixed-dimension-analyticity`** for the moment: `p ↦ M_p(s)` is real analytic at
every `p ∈ (0,1)`. -/
theorem analyticAt_fixedMoment {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    AnalyticAt ℝ (fixedMoment s) p := by
  obtain ⟨r, hr⟩ := exists_goodRadius hs hs1 hp0 hp1
  have hdiff := differentiableOn_crossLimit_disc hs hs1 hp0 hp1 hr
  have hA : AnalyticAt ℂ (crossLimit s) (p : ℂ) :=
    (hdiff.analyticOnNhd isOpen_ball) _ (mem_ball_self hr.pos)
  have hA' : AnalyticAt ℝ (crossLimit s) (p : ℂ) := hA.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : ℝ => (crossLimit s (x : ℂ)).re) p :=
    (Complex.reCLM.analyticAt _).comp (hA'.comp (Complex.ofRealCLM.analyticAt p))
  refine hcomp.congr ?_
  filter_upwards [Ioo_mem_nhds (show p - r < p by linarith [hr.pos])
    (show p < p + r by linarith [hr.pos])] with x hx
  rw [crossLimit_eq_fixedMoment_of_mem hs hs1 hp0 hp1 hr hx, Complex.ofReal_re]

theorem analyticAt_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : AnalyticAt ℝ entropy p := by
  have h1 : AnalyticAt ℝ (fun x : ℝ => x * Real.log x) p :=
    analyticAt_id.mul (analyticAt_log hp0)
  have h2 : AnalyticAt ℝ (fun x : ℝ => (1 - x) * Real.log (1 - x)) p := by
    have hl : AnalyticAt ℝ (fun x : ℝ => Real.log (1 - x)) p :=
      (analyticAt_log (show (0:ℝ) < 1 - p by linarith)).comp (analyticAt_const.sub analyticAt_id)
    exact (analyticAt_const.sub analyticAt_id).mul hl
  exact h1.neg.sub h2

/-- **`thm:fixed-dimension-analyticity`** for the mean: `p ↦ H̄_s(p)` is real analytic at
every `p ∈ (0,1)`. -/
theorem analyticAt_fixedMean {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    AnalyticAt ℝ (fixedMean s) p := by
  have hE := analyticAt_entropy hp0 hp1
  have hE0 : entropy p ≠ 0 := (entropy_pos hp0 hp1).ne'
  have hF : AnalyticAt ℝ (fun x : ℝ => x * (1 - x) / entropy x) p :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).div hE hE0
  have hM := analyticAt_fixedMoment hs hs1 hp0 hp1
  exact (analyticAt_const.mul hF).mul hM

theorem analyticOnNhd_fixedMean {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    AnalyticOnNhd ℝ (fixedMean s) (Ioo 0 1) :=
  fun _ hp => analyticAt_fixedMean hs hs1 hp.1 hp.2

theorem analyticOnNhd_fixedMoment {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    AnalyticOnNhd ℝ (fixedMoment s) (Ioo 0 1) :=
  fun _ hp => analyticAt_fixedMoment hs hs1 hp.1 hp.2

/-- The derivative of the mean is real analytic on `(0,1)`. -/
theorem analyticOnNhd_deriv_fixedMean {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    AnalyticOnNhd ℝ (deriv (fixedMean s)) (Ioo 0 1) :=
  (analyticOnNhd_fixedMean hs hs1).deriv

end

end BrownianImages
