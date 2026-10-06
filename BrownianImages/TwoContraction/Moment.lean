/-
`thm:parameter-steps`: how the moment `M(s) = 𝔼 Z_{c(s)}^{-s}` of
`thm:two-contraction-distinction` moves with `s`, through the three sources of parameter
dependence separated in `J(α, b, v) = 𝔼 Z^{-α}`: the exponent `α`, the contraction `b` and
the weight `v`.

Each step is a finite difference, so no differentiability of `J` is needed: the exponent
step is monotone because `Z ≤ 1`; the
contraction step is monotone near the natural parameters, by the word-by-word bound
`twoCode_param`, the tangent line of `u ↦ u^{-α}` and Chebyshev's inequality with
`𝔼 Y ≤ 1/2`; and the weight step loses at most a factor
`1 - (v' - v) 2αb(1-b)/((1/2 - b)(1 - v))`, by a monotone coupling of the two
Bernoulli measures on a three-letter alphabet.

* `crossKernel`, `crossJ`: the kernel `Z^{-α}` at two coded points and its mean `J`.
* `crossJ_mono_exponent`, `crossJ_mono_contraction`, `crossJ_weight_ge`: the three steps.
* `crossMoment_eq_crossJ`: `M_c(s) = J(s, c, c^s)` for the natural measure.
-/
import BrownianImages.TwoContraction.Coding

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology ENNReal

noncomputable section

/-! ### Elementary tools -/

/-- The tangent line inequality for `u ↦ u^{-α}`, `α ≥ 0`, on `(0, ∞)`:
`u^{-α} ≥ w^{-α} - α w^{-α-1}(u - w)`. -/
theorem rpow_neg_tangent {u w α : ℝ} (hu : 0 < u) (hw : 0 < w) (hα : 0 ≤ α) :
    w ^ (-α) - α * w ^ (-α - 1) * (u - w) ≤ u ^ (-α) := by
  have hq : 0 < u / w := div_pos hu hw
  have h1 : 1 - α * (u / w - 1) ≤ (u / w) ^ (-α) := by
    rw [Real.rpow_def_of_pos hq]
    have hlog := Real.log_le_sub_one_of_pos hq
    have hexp := Real.add_one_le_exp (Real.log (u / w) * -α)
    have hmul := mul_le_mul_of_nonneg_left hlog hα
    linarith
  have hwα : 0 < w ^ (-α) := Real.rpow_pos_of_pos hw _
  have h2 : u ^ (-α) = w ^ (-α) * (u / w) ^ (-α) := by
    rw [Real.div_rpow hu.le hw.le, mul_div_cancel₀ _ hwα.ne']
  have h3 : w ^ (-α - 1) = w ^ (-α) / w := Real.rpow_sub_one hw.ne' _
  rw [h2, h3]
  calc w ^ (-α) - α * (w ^ (-α) / w) * (u - w) = w ^ (-α) * (1 - α * (u / w - 1)) := by
        field_simp
    _ ≤ w ^ (-α) * (u / w) ^ (-α) := mul_le_mul_of_nonneg_left h1 hwα.le

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_abs_le {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ a, |f a| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hC a)

/-- **Chebyshev's integral inequality**: two similarly ordered bounded measurable
functions are non-negatively correlated. -/
theorem integral_mul_le_of_similar {P : Measure Ω} [IsProbabilityMeasure P] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) {Cf Cg : ℝ} (hCf : ∀ a, |f a| ≤ Cf)
    (hCg : ∀ a, |g a| ≤ Cg) (hfg : ∀ a b, 0 ≤ (f a - f b) * (g a - g b)) :
    (∫ a, f a ∂P) * (∫ a, g a ∂P) ≤ ∫ a, f a * g a ∂P := by
  have hfi : Integrable f P := integrable_of_abs_le hf hCf
  have hgi : Integrable g P := integrable_of_abs_le hg hCg
  have hfgi : Integrable (fun a => f a * g a) P := integrable_of_abs_le (hf.mul hg)
    (C := Cf * Cg) fun a => by
      rw [abs_mul]
      exact mul_le_mul (hCf a) (hCg a) (abs_nonneg _) ((abs_nonneg _).trans (hCf a))
  have hinner : ∀ a, ∫ b, (f a - f b) * (g a - g b) ∂P
      = f a * g a - f a * (∫ b, g b ∂P) - g a * (∫ b, f b ∂P) + ∫ b, f b * g b ∂P := by
    intro a
    have hrw : (fun b => (f a - f b) * (g a - g b))
        = fun b => f a * g a - f a * g b - g a * f b + f b * g b := by
      funext b; ring
    have i1 : Integrable (fun b => f a * g a - f a * g b) P :=
      (integrable_const _).sub (hgi.const_mul _)
    have i2 : Integrable (fun b => f a * g a - f a * g b - g a * f b) P :=
      i1.sub (hfi.const_mul _)
    rw [hrw, integral_add i2 hfgi, integral_sub i1 (hfi.const_mul _),
      integral_sub (integrable_const _) (hgi.const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
  have hpos : 0 ≤ ∫ a, ∫ b, (f a - f b) * (g a - g b) ∂P ∂P :=
    integral_nonneg fun a => integral_nonneg fun b => hfg a b
  simp only [hinner] at hpos
  have j1 : Integrable (fun a => f a * g a - f a * ∫ b, g b ∂P) P :=
    hfgi.sub (hfi.mul_const _)
  have j2 : Integrable (fun a => f a * g a - f a * (∫ b, g b ∂P) - g a * ∫ b, f b ∂P) P :=
    j1.sub (hgi.mul_const _)
  rw [integral_add j2 (integrable_const _), integral_sub j1 (hgi.mul_const _),
    integral_sub hfgi (hfi.mul_const _), integral_mul_const,
    integral_mul_const, integral_const, probReal_univ, one_smul] at hpos
  linarith

/-- Monotonicity of an iterated integral of bounded jointly measurable integrands. -/
theorem iterated_integral_mono {P : Measure Ω} [IsProbabilityMeasure P] {F G : Ω → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G)) {C : ℝ}
    (hFb : ∀ a b, |F a b| ≤ C) (hGb : ∀ a b, |G a b| ≤ C) (hle : ∀ a b, F a b ≤ G a b) :
    ∫ b, ∫ a, F a b ∂P ∂P ≤ ∫ b, ∫ a, G a b ∂P ∂P := by
  have hFi : ∀ b, Integrable (fun a => F a b) P := fun b =>
    integrable_of_abs_le (hF.comp (measurable_id.prodMk measurable_const)) fun a => hFb a b
  have hGi : ∀ b, Integrable (fun a => G a b) P := fun b =>
    integrable_of_abs_le (hG.comp (measurable_id.prodMk measurable_const)) fun a => hGb a b
  have hFo : Integrable (fun b => ∫ a, F a b ∂P) P :=
    Integrable.of_bound (hF.stronglyMeasurable.integral_prod_left).aestronglyMeasurable C
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ a, |F a b| ∂P ≤ ∫ _a, C ∂P :=
              integral_mono (hFi b).abs (integrable_const _) fun a => hFb a b
          _ = C := by rw [integral_const, probReal_univ, one_smul])
  have hGo : Integrable (fun b => ∫ a, G a b ∂P) P :=
    Integrable.of_bound (hG.stronglyMeasurable.integral_prod_left).aestronglyMeasurable C
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ a, |G a b| ∂P ≤ ∫ _a, C ∂P :=
              integral_mono (hGi b).abs (integrable_const _) fun a => hGb a b
          _ = C := by rw [integral_const, probReal_univ, one_smul])
  exact integral_mono hFo hGo fun b => integral_mono (hFi b) (hGi b) fun a => hle a b

end Integrals

/-! ### The kernel and its mean -/

/-- The kernel `Z^{-α}` of `J` at the coded points of two words, `X` coding the first and
`Y` the second.  It is irreducible, so that unification never unfolds it into the coding
map. -/
@[irreducible] def crossKernel (α b : ℝ) (ω ω' : ℕ → Fin 2) : ℝ :=
  crossDist b (twoCode b ω) (twoCode b ω') ^ (-α)

theorem crossKernel_def (α b : ℝ) (ω ω' : ℕ → Fin 2) :
    crossKernel α b ω ω' = crossDist b (twoCode b ω) (twoCode b ω') ^ (-α) := by
  unfold crossKernel; rfl

/-- `J(α, b, v) = 𝔼 Z^{-α}` of the proof of `thm:two-contraction-distinction`: `X` and
`Y` are independent, coded with contraction `b` from Bernoulli words with right-letter
probability `v`. -/
def crossJ (α b v : ℝ) : ℝ := ∫ ω', ∫ ω, crossKernel α b ω ω' ∂twoBern v ∂twoBern v

/-- At two coded points the cross-distance lies in `[1/2 - b, 1]`. -/
theorem crossDist_twoCode_mem {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (ω ω' : ℕ → Fin 2) :
    1/2 - b ≤ crossDist b (twoCode b ω) (twoCode b ω') ∧
      crossDist b (twoCode b ω) (twoCode b ω') ≤ 1 :=
  crossDist_mem hb0.le (twoCode_mem_Icc hb0 hb ω) (twoCode_mem_Icc hb0 hb ω')

/-- The cross-distance at two coded points is positive. -/
theorem crossDist_twoCode_pos {b : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (ω ω' : ℕ → Fin 2) :
    0 < crossDist b (twoCode b ω) (twoCode b ω') :=
  lt_of_lt_of_le (by linarith) (crossDist_twoCode_mem hb0 hb ω ω').1

/-- The kernel is jointly measurable in the two words. -/
theorem measurable_crossKernel (α b : ℝ) :
    Measurable (Function.uncurry (crossKernel α b)) := by
  have h1 : Measurable fun p : (ℕ → Fin 2) × (ℕ → Fin 2) => twoCode b p.1 :=
    (measurable_twoCode b).comp measurable_fst
  have h2 : Measurable fun p : (ℕ → Fin 2) × (ℕ → Fin 2) => twoCode b p.2 :=
    (measurable_twoCode b).comp measurable_snd
  unfold crossKernel crossDist
  exact (((measurable_const.sub measurable_const).add (measurable_const.mul h2)).sub
    (h1.div_const 2)).pow_const _

/-- The kernel lies in `[1, (1/2 - b)^{-α}]`. -/
theorem crossKernel_mem {α b : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hb : b < 1/2)
    (ω ω' : ℕ → Fin 2) :
    1 ≤ crossKernel α b ω ω' ∧ crossKernel α b ω ω' ≤ (1/2 - b) ^ (-α) := by
  obtain ⟨h1, h2⟩ := crossDist_twoCode_mem hb0 hb ω ω'
  have hpos := crossDist_twoCode_pos hb0 hb ω ω'
  rw [crossKernel_def]
  exact ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos h2 (by linarith),
    Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)⟩

/-- The kernel is bounded in absolute value by `(1/2 - b)^{-α}`. -/
theorem abs_crossKernel_le {α b : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hb : b < 1/2)
    (ω ω' : ℕ → Fin 2) : |crossKernel α b ω ω'| ≤ (1/2 - b) ^ (-α) := by
  obtain ⟨h1, h2⟩ := crossKernel_mem hα hb0 hb ω ω'
  rw [abs_of_nonneg (by linarith)]
  exact h2

/-- `J ≥ 1`, since the kernel is. -/
theorem one_le_crossJ {α b v : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hb : b < 1/2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : 1 ≤ crossJ α b v := by
  have := isProbabilityMeasure_twoBern hv0 hv1
  have h := iterated_integral_mono (P := twoBern v) (F := fun _ _ => (1:ℝ))
    (G := crossKernel α b) measurable_const (measurable_crossKernel α b)
    (C := (1/2 - b) ^ (-α))
    (fun _ _ => by
      rw [abs_one]
      exact (crossKernel_mem hα hb0 hb 0 0).1.trans (crossKernel_mem hα hb0 hb 0 0).2)
    (fun ω ω' => abs_crossKernel_le hα hb0 hb ω ω') fun ω ω' => (crossKernel_mem hα hb0 hb ω ω').1
  simpa [crossJ] using h

/-! ### The exponent -/

/-- **`eq:exponent-step` of `thm:parameter-steps`**: `J` is non-decreasing in the
exponent, because `Z ≤ 1`. -/
theorem crossJ_mono_exponent {α α' b v : ℝ} (hα : 0 ≤ α) (hαα : α ≤ α') (hb0 : 0 < b)
    (hb : b < 1/2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : crossJ α b v ≤ crossJ α' b v := by
  have := isProbabilityMeasure_twoBern hv0 hv1
  refine iterated_integral_mono (measurable_crossKernel α b) (measurable_crossKernel α' b)
    (C := (1/2 - b) ^ (-α')) (fun ω ω' => ?_) (fun ω ω' => abs_crossKernel_le
      (hα.trans hαα) hb0 hb ω ω') fun ω ω' => ?_
  · refine (abs_crossKernel_le hα hb0 hb ω ω').trans ?_
    exact Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
  · obtain ⟨h1, h2⟩ := crossDist_twoCode_mem hb0 hb ω ω'
    rw [crossKernel_def, crossKernel_def]
    exact Real.rpow_le_rpow_of_exponent_ge (crossDist_twoCode_pos hb0 hb ω ω') h2
      (by linarith)

/-! ### The contraction -/

/-- The word-by-word bound behind the contraction step: for `b ≤ b'`,
`Z_{b'} - Z_b ≤ (b' - b)(Y_b - 1/2)`. -/
theorem crossDist_param_le {b b' : ℝ} (hb0 : 0 < b) (hbb : b ≤ b') (hb' : b' < 1/2)
    (ω ω' : ℕ → Fin 2) :
    crossDist b' (twoCode b' ω) (twoCode b' ω') - crossDist b (twoCode b ω) (twoCode b ω')
      ≤ (b' - b) * (twoCode b ω' - 1/2) := by
  obtain ⟨d1, d2⟩ := twoCode_param hb0 hbb hb' ω
  obtain ⟨d1', d2'⟩ := twoCode_param hb0 hbb hb' ω'
  have hprod := mul_nonneg (show (0:ℝ) ≤ b' by linarith) d1'
  unfold crossDist
  nlinarith

/-- The tangent line at `Z_b` bounds the kernel at `b'` from below:
`Z_{b'}^{-α} ≥ Z_b^{-α} + α(b' - b) Z_b^{-α-1}(1/2 - Y_b)`. -/
theorem crossKernel_param_ge {α b b' : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hbb : b ≤ b')
    (hb' : b' < 1/2) (ω ω' : ℕ → Fin 2) :
    crossKernel α b ω ω' + α * (b' - b) * (crossKernel (α + 1) b ω ω' * (1/2 - twoCode b ω'))
      ≤ crossKernel α b' ω ω' := by
  have hb : b < 1/2 := lt_of_le_of_lt hbb hb'
  have hw := crossDist_twoCode_pos hb0 hb ω ω'
  have hu := crossDist_twoCode_pos (lt_of_lt_of_le hb0 hbb) hb' ω ω'
  have htan := rpow_neg_tangent hu hw hα
  have hdiff := crossDist_param_le hb0 hbb hb' ω ω'
  have hW : 0 ≤ α * crossDist b (twoCode b ω) (twoCode b ω') ^ (-α - 1) :=
    mul_nonneg hα (Real.rpow_nonneg hw.le _)
  unfold crossKernel
  rw [show -(α + 1) = -α - 1 by ring]
  nlinarith [mul_le_mul_of_nonneg_left hdiff hW]

/-- `𝔼 Y ≤ 1/2` exactly when `v(3 - 2b) ≤ 1`; at the natural parameters this is the
inequality `q(1-c) < p/2` of the proof of `thm:two-contraction-distinction`. -/
theorem integral_twoCode_le_half {b v : ℝ} (hb0 : 0 < b) (hb : b < 1/2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (hv : v * (3 - 2 * b) ≤ 1) :
    ∫ ω, twoCode b ω ∂twoBern v ≤ 1/2 := by
  rw [integral_twoCode hb0 hb hv0 hv1, div_le_iff₀ (by nlinarith)]
  nlinarith

/-- **`eq:contraction-step` of `thm:parameter-steps`**: where `v(3 - 2b) ≤ 1`, `J` is
non-decreasing in the contraction.  The tangent line gives
`J(b') - J(b) ≥ α(b' - b) 𝔼[(1/2 - Y) Z^{-α-1}]`, and Chebyshev's inequality for the
two decreasing functions `1/2 - y` and `𝔼_X Z^{-α-1}` of `Y` bounds this below by
`α(b' - b)(1/2 - 𝔼 Y) 𝔼 Z^{-α-1} ≥ 0`. -/
theorem crossJ_mono_contraction {α b b' v : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hbb : b ≤ b')
    (hb' : b' < 1/2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hv : v * (3 - 2 * b) ≤ 1) :
    crossJ α b v ≤ crossJ α b' v := by
  have hb : b < 1/2 := lt_of_le_of_lt hbb hb'
  have hb0' : 0 < b' := lt_of_lt_of_le hb0 hbb
  have := isProbabilityMeasure_twoBern hv0 hv1
  set P := twoBern v with hP
  set W : (ℕ → Fin 2) → (ℕ → Fin 2) → ℝ := crossKernel (α + 1) b with hW
  set Y : (ℕ → Fin 2) → ℝ := twoCode b with hY
  set g : (ℕ → Fin 2) → ℝ := fun ω' => ∫ ω, W ω ω' ∂P with hg
  set CW := (1/2 - b) ^ (-(α + 1)) with hCW
  have hWb : ∀ ω ω', |W ω ω'| ≤ CW := fun ω ω' => abs_crossKernel_le (by linarith) hb0 hb ω ω'
  have hWm := measurable_crossKernel (α + 1) b
  have hYb : ∀ ω, |1/2 - Y ω| ≤ 1/2 := fun ω => by
    have := twoCode_mem_Icc hb0 hb ω
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hYm : Measurable Y := measurable_twoCode b
  have hgm : Measurable g := (hWm.stronglyMeasurable.integral_prod_left).measurable
  have hWi : ∀ ω', Integrable (fun ω => W ω ω') P := fun ω' =>
    integrable_of_abs_le (hWm.of_uncurry_right (y := ω')) fun ω => hWb ω ω'
  have hgb : ∀ ω', |g ω'| ≤ CW := fun ω' => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |W ω ω'| ∂P ≤ ∫ _ω, CW ∂P :=
          integral_mono (hWi ω').abs (integrable_const _) fun ω => hWb ω ω'
      _ = CW := by rw [integral_const, probReal_univ, one_smul]
  -- the lower bound by the tangent line
  set R : (ℕ → Fin 2) → (ℕ → Fin 2) → ℝ :=
    fun ω ω' => crossKernel α b ω ω' + α * (b' - b) * (W ω ω' * (1/2 - Y ω')) with hR
  have hRm : Measurable (Function.uncurry R) :=
    (measurable_crossKernel α b).add (measurable_const.mul (hWm.mul
      (measurable_const.sub (hYm.comp measurable_snd))))
  set CR := (1/2 - b) ^ (-α) + α * (b' - b) * (CW * (1/2)) with hCR
  have hRb : ∀ ω ω', |R ω ω'| ≤ max CR ((1/2 - b') ^ (-α)) := by
    intro ω ω'
    refine le_trans ?_ (le_max_left _ _)
    refine (abs_add_le _ _).trans (add_le_add (abs_crossKernel_le hα hb0 hb ω ω') ?_)
    rw [abs_mul, abs_of_nonneg (mul_nonneg hα (by linarith)), abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hWb ω ω') (hYb ω') (abs_nonneg _)
      ((abs_nonneg _).trans (hWb ω ω'))) (mul_nonneg hα (by linarith))
  have hKb' : ∀ ω ω', |crossKernel α b' ω ω'| ≤ max CR ((1/2 - b') ^ (-α)) := fun ω ω' =>
    (abs_crossKernel_le hα hb0' hb' ω ω').trans (le_max_right _ _)
  have hstep := iterated_integral_mono (P := P) hRm (measurable_crossKernel α b') hRb hKb'
    fun ω ω' => crossKernel_param_ge hα hb0 hbb hb' ω ω'
  -- split the lower bound
  have hKi : ∀ ω', Integrable (fun ω => crossKernel α b ω ω') P := fun ω' =>
    integrable_of_abs_le ((measurable_crossKernel α b).of_uncurry_right (y := ω')) fun ω =>
        abs_crossKernel_le hα hb0 hb ω ω'
  have hinner : ∀ ω', ∫ ω, R ω ω' ∂P
      = (∫ ω, crossKernel α b ω ω' ∂P) + α * (b' - b) * ((1/2 - Y ω') * g ω') := by
    intro ω'
    rw [integral_add (hKi ω') (((hWi ω').mul_const _).const_mul _), integral_const_mul,
      integral_mul_const]
    ring
  have hKo : Integrable (fun ω' => ∫ ω, crossKernel α b ω ω' ∂P) P :=
    integrable_of_abs_le ((measurable_crossKernel α b).stronglyMeasurable.integral_prod_left
      ).measurable (C := (1/2 - b) ^ (-α)) fun ω' => by
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ ω, |crossKernel α b ω ω'| ∂P ≤ ∫ _ω, (1/2 - b) ^ (-α) ∂P :=
              integral_mono (hKi ω').abs (integrable_const _) fun ω =>
                abs_crossKernel_le hα hb0 hb ω ω'
          _ = (1/2 - b) ^ (-α) := by rw [integral_const, probReal_univ, one_smul]
  have hfgi : Integrable (fun ω' => (1/2 - Y ω') * g ω') P :=
    integrable_of_abs_le ((measurable_const.sub hYm).mul hgm) (C := 1/2 * CW) fun ω' => by
      rw [abs_mul]
      exact mul_le_mul (hYb ω') (hgb ω') (abs_nonneg _) (by norm_num)
  have hsplit : ∫ ω', ∫ ω, R ω ω' ∂P ∂P
      = crossJ α b v + α * (b' - b) * ∫ ω', (1/2 - Y ω') * g ω' ∂P := by
    simp only [hinner]
    rw [integral_add hKo (hfgi.const_mul _), integral_const_mul]
    rfl
  -- Chebyshev
  have hsim : ∀ a a', 0 ≤ ((1/2 - Y a) - (1/2 - Y a')) * (g a - g a') := by
    intro a a'
    have hmono : ∀ a a', Y a ≤ Y a' → g a' ≤ g a := by
      intro a a' hle
      refine integral_mono (hWi a') (hWi a) fun ω => ?_
      show crossKernel (α + 1) b ω a' ≤ crossKernel (α + 1) b ω a
      rw [crossKernel_def, crossKernel_def]
      have hpos := crossDist_twoCode_pos hb0 hb ω a
      refine Real.rpow_le_rpow_of_nonpos hpos ?_ (by linarith)
      unfold crossDist
      nlinarith
    rcases le_total (Y a) (Y a') with h | h
    · exact mul_nonneg (by linarith) (by linarith [hmono a a' h])
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hmono a' a h])
  have hcheb := integral_mul_le_of_similar (P := P) (f := fun ω' => 1/2 - Y ω') (g := g)
    (measurable_const.sub hYm) hgm hYb hgb hsim
  have hEY : ∫ ω', (1/2 - Y ω') ∂P = 1/2 - ∫ ω', Y ω' ∂P := by
    rw [integral_sub (integrable_const _) (integrable_of_abs_le hYm (C := 1) fun ω => by
        have := twoCode_mem_Icc hb0 hb ω
        rw [abs_of_nonneg this.1]; exact this.2),
      integral_const, probReal_univ, one_smul]
  have hEYle := integral_twoCode_le_half hb0 hb hv0 hv1 hv
  have hgpos : 0 ≤ ∫ ω', g ω' ∂P :=
    integral_nonneg fun ω' => integral_nonneg fun ω =>
      (zero_le_one.trans (crossKernel_mem (by linarith) hb0 hb ω ω').1)
  have hcov : 0 ≤ ∫ ω', (1/2 - Y ω') * g ω' ∂P := by
    refine le_trans ?_ hcheb
    rw [hEY]
    exact mul_nonneg (by linarith) hgpos
  have hJ' : crossJ α b' v = ∫ ω', ∫ ω, crossKernel α b' ω ω' ∂P ∂P := rfl
  rw [hJ']
  refine le_trans ?_ hstep
  rw [hsplit]
  nlinarith [mul_nonneg (mul_nonneg hα (show (0:ℝ) ≤ b' - b by linarith)) hcov]

/-! ### The weight -/

/-- The three-letter law `(1-v')δ₀ + (v'-v)δ₁ + vδ₂` of the monotone coupling of the
Bernoulli measures with right-letter probabilities `v ≤ v'`.  The lower coding reads
`0, 1, 2` as `0, 0, 1` and the upper one as `0, 1, 1`, so letter `1` is where the two
codings differ. -/
def triDigit (v v' : ℝ) : Measure (Fin 3) :=
  ENNReal.ofReal (1 - v') • Measure.dirac 0 + ENNReal.ofReal (v' - v) • Measure.dirac 1 +
    ENNReal.ofReal v • Measure.dirac 2

/-- The coupling measure on three-letter words. -/
def triBern (v v' : ℝ) : Measure (ℕ → Fin 3) := Measure.infinitePi fun _ : ℕ => triDigit v v'

/-- The lower reading of a coupling letter. -/
def lowLetter (i : Fin 3) : Fin 2 := if i = 2 then 1 else 0

/-- The upper reading of a coupling letter. -/
def highLetter (i : Fin 3) : Fin 2 := if i = 0 then 0 else 1

/-- The lower reading of a coupling word. -/
def lowWord (ω : ℕ → Fin 3) : ℕ → Fin 2 := fun n => lowLetter (ω n)

/-- The upper reading of a coupling word. -/
def highWord (ω : ℕ → Fin 3) : ℕ → Fin 2 := fun n => highLetter (ω n)

theorem measurable_lowWord : Measurable lowWord :=
  Measurable.of_eval fun n => (measurable_of_finite lowLetter).comp (measurable_pi_apply n)

theorem measurable_highWord : Measurable highWord :=
  Measurable.of_eval fun n => (measurable_of_finite highLetter).comp (measurable_pi_apply n)

/-- The lower reading lies below the upper one, letter by letter. -/
theorem lowWord_le_highWord (ω : ℕ → Fin 3) (k : ℕ) : lowWord ω k ≤ highWord ω k := by
  simp only [lowWord, highWord]
  generalize ω k = i
  fin_cases i <;> decide

/-- The two readings differ exactly at the letter `1`. -/
theorem letterDiff_low_high (ω : ℕ → Fin 3) (k : ℕ) :
    letterDiff (lowWord ω) (highWord ω) k = if ω k = 1 then 1 else 0 := by
  have key : ∀ i : Fin 3, (if lowLetter i = highLetter i then (0:ℝ) else 1)
      = if i = 1 then 1 else 0 := by
    intro i; fin_cases i <;> simp [lowLetter, highLetter]
  exact key (ω k)

/-- Reading commutes with prefixing a letter. -/
theorem lowWord_cons (i : Fin 3) (ω : ℕ → Fin 3) :
    lowWord (cons i ω) = cons (lowLetter i) (lowWord ω) := by
  funext n; cases n <;> rfl

theorem triDigit_singleton (v v' : ℝ) :
    triDigit v v' {0} = ENNReal.ofReal (1 - v') ∧ triDigit v v' {1} = ENNReal.ofReal (v' - v) ∧
      triDigit v v' {2} = ENNReal.ofReal v := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [triDigit, Measure.dirac_apply' _ (measurableSet_singleton _)]

theorem isProbabilityMeasure_triDigit {v v' : ℝ} (hv0 : 0 ≤ v) (hvv : v ≤ v')
    (hv'1 : v' ≤ 1) : IsProbabilityMeasure (triDigit v v') := by
  constructor
  obtain ⟨h0, h1, h2⟩ := triDigit_singleton v v'
  rw [measure_eq_sum_indicator]
  simp only [Fin.sum_univ_three, h0, h1, h2, Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) hv0]
  simp

/-- The lower reading of the coupling is the Bernoulli measure with weight `v`. -/
theorem map_lowWord_triBern {v v' : ℝ} (hv0 : 0 ≤ v) (hvv : v ≤ v') (hv'1 : v' ≤ 1) :
    (triBern v v').map lowWord = twoBern v := by
  have := isProbabilityMeasure_triDigit hv0 hvv hv'1
  have hdig : (triDigit v v').map lowLetter = twoDigit v := by
    obtain ⟨h0, h1, h2⟩ := triDigit_singleton v v'
    rw [Measure.ext_iff_singleton]
    intro a
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton a),
      measure_eq_sum_indicator]
    simp only [Fin.sum_univ_three, h0, h1, h2]
    rcases fin_two_cases a with rfl | rfl
    · rw [twoDigit_zero]
      simp [lowLetter]
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      ring_nf
    · rw [twoDigit_one]
      simp [lowLetter]
  unfold triBern twoBern lowWord
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_of_finite lowLetter)]
  simp only [hdig]

/-- The upper reading of the coupling is the Bernoulli measure with weight `v'`. -/
theorem map_highWord_triBern {v v' : ℝ} (hv0 : 0 ≤ v) (hvv : v ≤ v') (hv'1 : v' ≤ 1) :
    (triBern v v').map highWord = twoBern v' := by
  have := isProbabilityMeasure_triDigit hv0 hvv hv'1
  have hdig : (triDigit v v').map highLetter = twoDigit v' := by
    obtain ⟨h0, h1, h2⟩ := triDigit_singleton v v'
    rw [Measure.ext_iff_singleton]
    intro a
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton a),
      measure_eq_sum_indicator]
    simp only [Fin.sum_univ_three, h0, h1, h2]
    rcases fin_two_cases a with rfl | rfl
    · rw [twoDigit_zero]
      simp [highLetter]
    · rw [twoDigit_one]
      simp [highLetter]
      rw [← ENNReal.ofReal_add (by linarith) hv0]
      ring_nf
  unfold triBern twoBern highWord
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_of_finite highLetter)]
  simp only [hdig]

@[simp] theorem cons_apply_zero {α : Type*} (i : α) (ω : ℕ → α) : cons i ω 0 = i := rfl

@[simp] theorem cons_apply_succ {α : Type*} (i : α) (ω : ℕ → α) (n : ℕ) :
    cons i ω (n + 1) = ω n := rfl

/-- **The weight of a changed letter**: under the coupling, the event that the two
readings differ at depth `k` carries at most the share `(v' - v)/(1 - v)` of the mean of
any non-negative bounded function of the lower reading.  At depth `0` the letter `1`
has mass `v' - v` and the lower reading cannot tell it from `0`, whose mass is
`1 - v'`; deeper letters reduce to depth `0` by splitting off the first letter. -/
theorem integral_flip_le {v v' : ℝ} (hv0 : 0 ≤ v) (hvv : v ≤ v') (hv'1 : v' ≤ 1)
    (hv1 : v < 1) {C : ℝ} :
    ∀ (k : ℕ) (G : (ℕ → Fin 2) → ℝ), Measurable G → (∀ η, 0 ≤ G η) → (∀ η, G η ≤ C) →
      ∫ ω, (if ω k = 1 then (1:ℝ) else 0) * G (lowWord ω) ∂triBern v v'
        ≤ (v' - v) / (1 - v) * ∫ ω, G (lowWord ω) ∂triBern v v' := by
  have := isProbabilityMeasure_triDigit hv0 hvv hv'1
  have hQ : IsProbabilityMeasure (triBern v v') := by unfold triBern; infer_instance
  obtain ⟨h0, h1, h2⟩ := triDigit_singleton v v'
  have hr0 : (triDigit v v' {0}).toReal = 1 - v' := by
    rw [h0, ENNReal.toReal_ofReal (by linarith)]
  have hr1 : (triDigit v v' {1}).toReal = v' - v := by
    rw [h1, ENNReal.toReal_ofReal (by linarith)]
  have hr2 : (triDigit v v' {2}).toReal = v := by rw [h2, ENNReal.toReal_ofReal hv0]
  have hsplit : ∀ F : (ℕ → Fin 3) → ℝ, Measurable F → (∀ ω, |F ω| ≤ C) →
      ∫ ω, F ω ∂triBern v v' = (1 - v') * ∫ ω, F (cons 0 ω) ∂triBern v v'
        + (v' - v) * ∫ ω, F (cons 1 ω) ∂triBern v v' + v * ∫ ω, F (cons 2 ω) ∂triBern v v' := by
    intro F hF hFC
    have h := integral_infinitePi_cons (triDigit v v') hF hFC
    rw [Fin.sum_univ_three, hr0, hr1, hr2] at h
    exact h
  have hr : 0 ≤ (v' - v) / (1 - v) := div_nonneg (by linarith) (by linarith)
  intro k
  induction k with
  | zero =>
    intro G hGm hG0 hGC
    have hC : 0 ≤ C := (hG0 fun _ => 0).trans (hGC _)
    have hind : ∀ ω : ℕ → Fin 3, |(if ω 0 = 1 then (1:ℝ) else 0) * G (lowWord ω)| ≤ C := by
      intro ω
      rw [abs_mul, abs_of_nonneg (hG0 _)]
      split_ifs <;> simp [hGC, hC]
    have hGb : ∀ ω : ℕ → Fin 3, |G (lowWord ω)| ≤ C := fun ω => by
      rw [abs_of_nonneg (hG0 _)]; exact hGC _
    have hm1 : Measurable fun ω : ℕ → Fin 3 => (if ω 0 = 1 then (1:ℝ) else 0) * G (lowWord ω) :=
      (Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
        measurable_const measurable_const).mul (hGm.comp measurable_lowWord)
    rw [hsplit _ hm1 hind, hsplit (fun ω => G (lowWord ω)) (hGm.comp measurable_lowWord) hGb]
    simp only [cons_apply_zero, lowWord_cons]
    have hl0 : lowLetter 0 = 0 := rfl
    have hl1 : lowLetter 1 = 0 := rfl
    have hl2 : lowLetter 2 = 1 := rfl
    simp only [hl0, hl1, hl2, show ((0 : Fin 3) = 1) = False from by decide,
      show ((2 : Fin 3) = 1) = False from by decide, ite_true, ite_false, zero_mul, one_mul,
      integral_zero, mul_zero, zero_add, add_zero]
    set I0 := ∫ ω, G (cons 0 (lowWord ω)) ∂triBern v v'
    set I2 := ∫ ω, G (cons 1 (lowWord ω)) ∂triBern v v'
    have hI0 : 0 ≤ I0 := integral_nonneg fun _ => hG0 _
    have hI2 : 0 ≤ I2 := integral_nonneg fun _ => hG0 _
    have hden : 0 < 1 - v := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [mul_nonneg (show 0 ≤ v' - v by linarith) (mul_nonneg hv0 hI2)]
  | succ k ih =>
    intro G hGm hG0 hGC
    have hC : 0 ≤ C := (hG0 fun _ => 0).trans (hGC _)
    have hind : ∀ ω : ℕ → Fin 3,
        |(if ω (k + 1) = 1 then (1:ℝ) else 0) * G (lowWord ω)| ≤ C := by
      intro ω
      rw [abs_mul, abs_of_nonneg (hG0 _)]
      split_ifs <;> simp [hGC, hC]
    have hGb : ∀ ω : ℕ → Fin 3, |G (lowWord ω)| ≤ C := fun ω => by
      rw [abs_of_nonneg (hG0 _)]; exact hGC _
    have hm1 : Measurable fun ω : ℕ → Fin 3 =>
        (if ω (k + 1) = 1 then (1:ℝ) else 0) * G (lowWord ω) :=
      (Measurable.ite (measurableSet_eq_fun (measurable_pi_apply (k + 1)) measurable_const)
        measurable_const measurable_const).mul (hGm.comp measurable_lowWord)
    rw [hsplit _ hm1 hind, hsplit (fun ω => G (lowWord ω)) (hGm.comp measurable_lowWord) hGb]
    simp only [cons_apply_succ, lowWord_cons]
    have e : ∀ i : Fin 3, ∫ ω, (if ω k = 1 then (1:ℝ) else 0) * G (cons (lowLetter i) (lowWord ω))
          ∂triBern v v'
        ≤ (v' - v) / (1 - v) * ∫ ω, G (cons (lowLetter i) (lowWord ω)) ∂triBern v v' :=
      fun i => ih (fun η => G (cons (lowLetter i) η)) (hGm.comp (measurable_cons' _))
        (fun η => hG0 _) (fun η => hGC _)
    have e0 := mul_le_mul_of_nonneg_left (e 0) (show (0:ℝ) ≤ 1 - v' by linarith)
    have e1 := mul_le_mul_of_nonneg_left (e 1) (show (0:ℝ) ≤ v' - v by linarith)
    have e2 := mul_le_mul_of_nonneg_left (e 2) hv0
    refine (add_le_add (add_le_add e0 e1) e2).trans (le_of_eq ?_)
    ring

/-- Reading `J` on the coupling. -/
theorem crossJ_eq_coupling {α b v w v' : ℝ} [IsProbabilityMeasure (triBern v v')]
    (φ : (ℕ → Fin 3) → ℕ → Fin 2) (hφ : Measurable φ)
    (hmap : (triBern v v').map φ = twoBern w) :
    crossJ α b w = ∫ ω', ∫ ω, crossKernel α b (φ ω) (φ ω') ∂triBern v v' ∂triBern v v' := by
  have hKm := measurable_crossKernel α b
  unfold crossJ
  rw [← hmap, integral_map hφ.aemeasurable
    (hKm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable]
  congr 1
  funext ω'
  rw [integral_map hφ.aemeasurable (hKm.of_uncurry_right).aestronglyMeasurable]

/-- The changed letters of the coupling, weighted by depth: the bound `D_N` on how far the
upper reading moves the coded point above the lower one. -/
def flipWeight (b : ℝ) (N : ℕ) (ω : ℕ → Fin 3) : ℝ :=
  ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k * (if ω k = 1 then (1:ℝ) else 0) + (1/2) ^ N

theorem flipWeight_nonneg {b : ℝ} (hb : b < 1/2) (N : ℕ) (ω : ℕ → Fin 3) :
    0 ≤ flipWeight b N ω := by
  refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) (by positivity)
  refine mul_nonneg (mul_nonneg (by linarith) (by positivity)) ?_
  split_ifs <;> norm_num

theorem flipWeight_le {b : ℝ} (hb0 : 0 < b) (N : ℕ) (ω : ℕ → Fin 3) :
    flipWeight b N ω ≤ 3 := by
  have hgeom : ∑ k ∈ Finset.range N, (1/2 : ℝ) ^ k ≤ 2 := by
    have := sum_geometric_two_le N
    simpa [one_div] using this
  have hterm : ∀ k ∈ Finset.range N, (1 - b) * (1/2 : ℝ) ^ k * (if ω k = 1 then (1:ℝ) else 0)
      ≤ (1/2) ^ k := by
    intro k _
    have hk : (0:ℝ) ≤ (1/2) ^ k := by positivity
    split_ifs <;> nlinarith
  have hN : (1/2 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold flipWeight
  linarith [Finset.sum_le_sum hterm]

theorem measurable_flipWeight (b : ℝ) (N : ℕ) : Measurable (flipWeight b N) := by
  unfold flipWeight
  refine Finset.measurable_sum _ (fun k _ => measurable_const.mul ?_) |>.add measurable_const
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply k) measurable_const)
    measurable_const measurable_const

/-- The pointwise bound of the weight step: on the coupling,
`Z(X_high, Y_high)^{-α} ≥ Z(X_low, Y_low)^{-α} (1 - αb D_N/(1/2 - b))`.  Raising `X` only
raises the kernel, and raising `Y` by at most `D_N` costs at most this factor, by the
tangent line. -/
theorem crossKernel_coupling_ge {α b : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hb : b < 1/2)
    (N : ℕ) (ω ω' : ℕ → Fin 3) :
    crossKernel α b (lowWord ω) (lowWord ω') * (1 - α * b / (1/2 - b) * flipWeight b N ω')
      ≤ crossKernel α b (highWord ω) (highWord ω') := by
  have hX : crossKernel α b (lowWord ω) (highWord ω')
      ≤ crossKernel α b (highWord ω) (highWord ω') := by
    unfold crossKernel
    have hx := twoCode_mono hb0 hb (lowWord_le_highWord ω)
    refine Real.rpow_le_rpow_of_nonpos (crossDist_twoCode_pos hb0 hb _ _) ?_ (by linarith)
    unfold crossDist
    linarith
  refine le_trans ?_ hX
  have hdy : twoCode b (highWord ω') - twoCode b (lowWord ω') ≤ flipWeight b N ω' := by
    have h := twoCode_sub_le hb0 hb N (lowWord ω') (highWord ω')
    simp only [letterDiff_low_high] at h
    exact h
  have hD0 := flipWeight_nonneg hb N ω'
  have hw := (crossDist_twoCode_mem hb0 hb (lowWord ω) (lowWord ω')).1
  have hw0 := crossDist_twoCode_pos hb0 hb (lowWord ω) (lowWord ω')
  have hu0 := crossDist_twoCode_pos hb0 hb (lowWord ω) (highWord ω')
  have htan := rpow_neg_tangent hu0 hw0 hα
  unfold crossKernel
  set x := twoCode b (lowWord ω)
  set y := twoCode b (lowWord ω')
  set y' := twoCode b (highWord ω')
  set D := flipWeight b N ω'
  set w := crossDist b x y with hwdef
  set u := crossDist b x y' with hudef
  have huw : u - w = b * (y' - y) := by rw [hwdef, hudef]; unfold crossDist; ring
  have hwα : 0 < w ^ (-α) := Real.rpow_pos_of_pos hw0 _
  have h3 : w ^ (-α - 1) = w ^ (-α) / w := Real.rpow_sub_one hw0.ne' _
  have key1 : α * w ^ (-α - 1) * (u - w) ≤ α * w ^ (-α - 1) * (b * D) := by
    rw [huw]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdy hb0.le)
      (mul_nonneg hα (Real.rpow_nonneg hw0.le _))
  have key2 : α * w ^ (-α - 1) * (b * D) ≤ w ^ (-α) * (α * b / (1/2 - b) * D) := by
    rw [h3]
    have hfrac : α * b * D / w ≤ α * b * D / (1/2 - b) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hw
    calc α * (w ^ (-α) / w) * (b * D) = w ^ (-α) * (α * b * D / w) := by
          field_simp
      _ ≤ w ^ (-α) * (α * b * D / (1/2 - b)) := mul_le_mul_of_nonneg_left hfrac hwα.le
      _ = w ^ (-α) * (α * b / (1/2 - b) * D) := by ring
  nlinarith

/-- **`eq:weight-step` of `thm:parameter-steps`**: raising the weight from `v` to `v'`
loses at most the factor
`1 - (v' - v) 2αb(1-b)/((1/2 - b)(1 - v))`.  On the monotone coupling the pointwise bound
`crossKernel_coupling_ge` holds with the changed letters weighted by depth; each changed
letter carries at most the share `(v' - v)/(1 - v)` of `J`, by `integral_flip_le`, and
the depth weights sum to at most `2(1-b)`. -/
theorem crossJ_weight_ge {α b v v' : ℝ} (hα : 0 ≤ α) (hb0 : 0 < b) (hb : b < 1/2)
    (hv0 : 0 ≤ v) (hvv : v ≤ v') (hv'1 : v' ≤ 1) (hv1 : v < 1) :
    crossJ α b v * (1 - (v' - v) * (2 * α * b * (1 - b) / ((1/2 - b) * (1 - v))))
      ≤ crossJ α b v' := by
  have := isProbabilityMeasure_triDigit hv0 hvv hv'1
  have hQ : IsProbabilityMeasure (triBern v v') := by unfold triBern; infer_instance
  have hKm := measurable_crossKernel α b
  set CK := (1/2 - b) ^ (-α) with hCK
  have hCK0 : 0 ≤ CK := (abs_nonneg _).trans (abs_crossKernel_le hα hb0 hb 0 0)
  set c0 := α * b / (1/2 - b) with hc0
  have hc00 : 0 ≤ c0 := div_nonneg (mul_nonneg hα hb0.le) (by linarith)
  set r := (v' - v) / (1 - v) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hlow := crossJ_eq_coupling (α := α) (b := b) lowWord measurable_lowWord
    (map_lowWord_triBern hv0 hvv hv'1)
  have hhigh := crossJ_eq_coupling (α := α) (b := b) highWord measurable_highWord
    (map_highWord_triBern hv0 hvv hv'1)
  -- the inner mean of the lower kernel, as a function of the lower reading of `ω'`
  obtain ⟨G, hG⟩ : ∃ G : (ℕ → Fin 2) → ℝ,
      G = fun η => ∫ ω, crossKernel α b (lowWord ω) η ∂triBern v v' := ⟨_, rfl⟩
  have hLm : Measurable (Function.uncurry fun (ω : ℕ → Fin 3) (η : ℕ → Fin 2) =>
      crossKernel α b (lowWord ω) η) :=
    hKm.comp (measurable_lowWord.prodMap measurable_id)
  have hGm : Measurable G := by
    rw [hG]; exact (hLm.stronglyMeasurable.integral_prod_left).measurable
  have hLi : ∀ η, Integrable (fun ω => crossKernel α b (lowWord ω) η) (triBern v v') :=
    fun η => integrable_of_abs_le (hLm.of_uncurry_right (y := η)) fun ω =>
      abs_crossKernel_le hα hb0 hb _ _
  have hG0 : ∀ η, 0 ≤ G η := fun η => by
    rw [hG]; exact integral_nonneg fun ω =>
      zero_le_one.trans (crossKernel_mem hα hb0 hb _ _).1
  have hGC : ∀ η, G η ≤ CK := fun η => by
    rw [hG]
    calc ∫ ω, crossKernel α b (lowWord ω) η ∂triBern v v' ≤ ∫ _ω, CK ∂triBern v v' :=
          integral_mono (hLi η) (integrable_const _) fun ω => (crossKernel_mem hα hb0 hb _ _).2
      _ = CK := by rw [integral_const, probReal_univ, one_smul]
  have hGb : ∀ η, |G η| ≤ CK := fun η => by rw [abs_of_nonneg (hG0 η)]; exact hGC η
  have hJv : crossJ α b v = ∫ ω', G (lowWord ω') ∂triBern v v' := by rw [hlow, hG]
  have hJ0 : 0 ≤ crossJ α b v := zero_le_one.trans (one_le_crossJ hα hb0 hb hv0 (by linarith))
  -- the bound at each truncation depth
  have hN : ∀ N : ℕ, crossJ α b v - c0 * (2 * (1 - b) * r + (1/2) ^ N) * crossJ α b v
      ≤ crossJ α b v' := by
    intro N
    have hFm : Measurable (Function.uncurry fun (ω ω' : ℕ → Fin 3) =>
        crossKernel α b (lowWord ω) (lowWord ω') * (1 - c0 * flipWeight b N ω')) :=
      (hKm.comp (measurable_lowWord.prodMap measurable_lowWord)).mul
        (measurable_const.sub (measurable_const.mul
          ((measurable_flipWeight b N).comp measurable_snd)))
    have hHm : Measurable (Function.uncurry fun (ω ω' : ℕ → Fin 3) =>
        crossKernel α b (highWord ω) (highWord ω')) :=
      hKm.comp (measurable_highWord.prodMap measurable_highWord)
    have hbd : ∀ ω ω' : ℕ → Fin 3,
        |crossKernel α b (lowWord ω) (lowWord ω') * (1 - c0 * flipWeight b N ω')|
          ≤ CK * (1 + c0 * 3) := by
      intro ω ω'
      rw [abs_mul]
      refine mul_le_mul (abs_crossKernel_le hα hb0 hb _ _) ?_ (abs_nonneg _) hCK0
      have h1 := flipWeight_nonneg hb N ω'
      have h2 := flipWeight_le hb0 N ω'
      rw [abs_le]; constructor <;> nlinarith
    have hbd' : ∀ ω ω' : ℕ → Fin 3, |crossKernel α b (highWord ω) (highWord ω')|
        ≤ CK * (1 + c0 * 3) := fun ω ω' =>
      (abs_crossKernel_le hα hb0 hb _ _).trans (le_mul_of_one_le_right hCK0 (by nlinarith))
    have hmono := iterated_integral_mono (P := triBern v v') hFm hHm hbd hbd'
      fun ω ω' => crossKernel_coupling_ge hα hb0 hb N ω ω'
    rw [← hhigh] at hmono
    refine le_trans ?_ hmono
    -- the lower side
    have hinner : ∀ ω', ∫ ω, crossKernel α b (lowWord ω) (lowWord ω') *
        (1 - c0 * flipWeight b N ω') ∂triBern v v'
        = G (lowWord ω') - c0 * (flipWeight b N ω' * G (lowWord ω')) := by
      intro ω'
      rw [integral_mul_const, hG]
      ring
    simp only [hinner]
    have hGl : Integrable (fun ω' => G (lowWord ω')) (triBern v v') :=
      integrable_of_abs_le (hGm.comp measurable_lowWord) fun ω' => hGb _
    have hind : ∀ k, Integrable (fun ω' : ℕ → Fin 3 =>
        (if ω' k = 1 then (1:ℝ) else 0) * G (lowWord ω')) (triBern v v') := by
      intro k
      refine integrable_of_abs_le ((Measurable.ite (measurableSet_eq_fun
        (measurable_pi_apply k) measurable_const) measurable_const measurable_const).mul
        (hGm.comp measurable_lowWord)) (C := CK) fun ω' => ?_
      rw [abs_mul]
      split_ifs <;> simp [hGb, hCK0]
    have hDG : ∫ ω', flipWeight b N ω' * G (lowWord ω') ∂triBern v v'
        = ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k *
            ∫ ω', (if ω' k = 1 then (1:ℝ) else 0) * G (lowWord ω') ∂triBern v v'
          + (1/2) ^ N * ∫ ω', G (lowWord ω') ∂triBern v v' := by
      have hrw : (fun ω' => flipWeight b N ω' * G (lowWord ω'))
          = fun ω' => ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k *
              ((if ω' k = 1 then (1:ℝ) else 0) * G (lowWord ω')) + (1/2) ^ N * G (lowWord ω') := by
        funext ω'
        simp only [flipWeight, add_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hrw, integral_add (integrable_finsetSum _ fun k _ => (hind k).const_mul _)
        (hGl.const_mul _), integral_finsetSum _ fun k _ => (hind k).const_mul _,
        integral_const_mul]
      congr 1
      exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    have hflip : ∀ k, ∫ ω', (if ω' k = 1 then (1:ℝ) else 0) * G (lowWord ω') ∂triBern v v'
        ≤ r * crossJ α b v := by
      intro k
      rw [hJv]
      exact integral_flip_le hv0 hvv hv'1 hv1 k G hGm hG0 hGC
    have hsumle : ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k *
        ∫ ω', (if ω' k = 1 then (1:ℝ) else 0) * G (lowWord ω') ∂triBern v v'
        ≤ 2 * (1 - b) * r * crossJ α b v := by
      calc ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k *
            ∫ ω', (if ω' k = 1 then (1:ℝ) else 0) * G (lowWord ω') ∂triBern v v'
          ≤ ∑ k ∈ Finset.range N, (1 - b) * (1/2) ^ k * (r * crossJ α b v) :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hflip k)
              (mul_nonneg (by linarith) (by positivity))
        _ = (∑ k ∈ Finset.range N, (1/2 : ℝ) ^ k) * ((1 - b) * r * crossJ α b v) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ 2 * ((1 - b) * r * crossJ α b v) := by
            refine mul_le_mul_of_nonneg_right ?_
              (mul_nonneg (mul_nonneg (by linarith) hr0) hJ0)
            have := sum_geometric_two_le N
            simpa [one_div] using this
        _ = 2 * (1 - b) * r * crossJ α b v := by ring
    have hDGi : Integrable (fun ω' => flipWeight b N ω' * G (lowWord ω')) (triBern v v') :=
      integrable_of_abs_le ((measurable_flipWeight b N).mul (hGm.comp measurable_lowWord))
        (C := 3 * CK) fun ω' => by
          show |flipWeight b N ω' * G (lowWord ω')| ≤ 3 * CK
          rw [abs_mul, abs_of_nonneg (flipWeight_nonneg hb N ω')]
          exact mul_le_mul (flipWeight_le hb0 N ω') (hGb _) (abs_nonneg _) (by norm_num)
    have hsubi : Integrable (fun ω' => c0 * (flipWeight b N ω' * G (lowWord ω')))
        (triBern v v') := hDGi.const_mul _
    rw [integral_sub hGl hsubi, integral_const_mul, hDG, ← hJv]
    nlinarith [mul_le_mul_of_nonneg_left hsumle hc00]
  -- let the truncation depth go to infinity
  have hlim : Tendsto (fun N : ℕ => crossJ α b v - c0 * (2 * (1 - b) * r + (1/2) ^ N) *
      crossJ α b v) atTop (𝓝 (crossJ α b v - c0 * (2 * (1 - b) * r + 0) * crossJ α b v)) :=
    tendsto_const_nhds.sub (((tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num) (by norm_num))).const_mul c0).mul_const _)
  have hfinal := le_of_tendsto' hlim hN
  refine le_trans (le_of_eq ?_) hfinal
  have hd1 : (1/2 - b) ≠ 0 := by linarith
  have hd2 : (1 - v) ≠ 0 := by linarith
  rw [hc0, hr, add_zero]
  field_simp

end

end BrownianImages
