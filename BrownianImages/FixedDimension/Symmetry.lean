/-
The symmetry `M_p = M_{1-p}` used in the proof of `thm:small-dimension-monotone`, in the form
`M_{1/2}' = 0`.

Flipping every letter conjugates the system of `z` to the system of `1 - z` through the
reflection `x ↦ 1 - x`, up to the base point: the coded point of the flipped word in the
flipped system is `1 - x_u - r_u`, where `r_u` is the contraction of the word. The cross
kernel is invariant under the reflection of both arguments, so the level sums of `z` and of
`1 - z` differ by at most `6 s γ (γ B²)^m`, and their limits agree. At `p = 1/2` the real
derivative of the moment is the real part of a complex derivative that vanishes by the symmetry.

* `flipDigit`, `flipWord`: the letter flip.
* `one_sub_cpointSeq_eq`: the reflected coded point.
* `crossLimit_one_sub`: `M_{1-z} = M_z` on the disc around `1/2`.
* `deriv_fixedMoment_half`: `M_{1/2}' = 0`.
-/
import BrownianImages.FixedDimension.SecondDerivative

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- The flip of a letter. -/
def flipDigit (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- The flip of every letter of a word. -/
def flipWord (ω : ℕ → Fin 2) : ℕ → Fin 2 := fun k => flipDigit (ω k)

theorem flipDigit_zero : flipDigit 0 = 1 := rfl

theorem flipDigit_one : flipDigit 1 = 0 := rfl

theorem flipDigit_flipDigit (i : Fin 2) : flipDigit (flipDigit i) = i := by
  rcases fin_two_cases i with rfl | rfl <;> rfl

theorem flipDigit_involutive : Function.Involutive flipDigit := flipDigit_flipDigit

theorem tail_flipWord (ω : ℕ → Fin 2) : tail (flipWord ω) = flipWord (tail ω) := rfl

theorem flipWord_apply (ω : ℕ → Fin 2) (k : ℕ) : flipWord ω k = flipDigit (ω k) := rfl

theorem cratioOf_flip (a b : ℂ) (i : Fin 2) : cratioOf b a (flipDigit i) = cratioOf a b i := by
  rcases fin_two_cases i with rfl | rfl <;> rfl

/-- The weights of the flipped word in the flipped system. -/
theorem weightSeq_flip (z : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    weightSeq (1 - z) m (flipWord ω) = weightSeq z m ω := by
  induction m generalizing ω with
  | zero => rfl
  | succ m ih =>
    rw [weightSeq_succ, weightSeq_succ, tail_flipWord, ih, flipWord_apply]
    rcases fin_two_cases (ω 0) with h | h <;> simp [h, flipDigit]

/-- The contraction of the flipped word in the flipped system. -/
theorem cratioSeq_flip (a b : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    cratioSeq b a m (flipWord ω) = cratioSeq a b m ω := by
  induction m generalizing ω with
  | zero => rfl
  | succ m ih =>
    rw [cratioSeq_succ, cratioSeq_succ, tail_flipWord, ih, flipWord_apply, cratioOf_flip]

/-- The reflected coded point: `1 - x_u(a, b) = x_{σu}(b, a) + r_u`. -/
theorem one_sub_cpointSeq_eq (a b : ℂ) (m : ℕ) (ω : ℕ → Fin 2) :
    1 - cpointSeq a b m ω = cpointSeq b a m (flipWord ω) + cratioSeq a b m ω := by
  induction m generalizing ω with
  | zero => simp
  | succ m ih =>
    rw [cpointSeq_succ, cpointSeq_succ, cratioSeq_succ, tail_flipWord, flipWord_apply]
    have h := ih (tail ω)
    rcases fin_two_cases (ω 0) with h0 | h0
    · rw [h0, flipDigit_zero, cmap_zero, cmap_one]
      unfold cratioOf; simp only [ite_true]
      linear_combination a * h
    · rw [h0, flipDigit_one, cmap_one, cmap_zero]
      unfold cratioOf; simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
      linear_combination b * h

/-- The coded point of a base point `y` with `|y - 1| ≤ (1 + |a|)/(1 - |a|)` satisfies the
same bound. -/
theorem norm_cpointSeq_add_cratioSeq_mul_sub_one_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1)
    (m : ℕ) (ω : ℕ → Fin 2) {y : ℂ} (hy : ‖y - 1‖ ≤ (1 + ‖a‖) / (1 - ‖a‖)) :
    ‖cpointSeq a b m ω + cratioSeq a b m ω * y - 1‖ ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  induction m generalizing ω with
  | zero => simpa using hy
  | succ m ih =>
    rw [cpointSeq_succ, cratioSeq_succ, mul_assoc, ← cmap_add]
    set x := cpointSeq a b m (tail ω) + cratioSeq a b m (tail ω) * y with hx
    have ihx := ih (tail ω)
    rw [← hx] at ihx
    rcases fin_two_cases (ω 0) with h | h
    · rw [h, cmap_zero]
      have hxn : ‖x‖ ≤ (1 + ‖a‖) / (1 - ‖a‖) + 1 := by
        calc ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ ≤ _ := by rw [norm_one]; linarith
      calc ‖a * x - 1‖ ≤ ‖a * x‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = ‖a‖ * ‖x‖ + 1 := by rw [norm_mul, norm_one]
        _ ≤ ‖a‖ * ((1 + ‖a‖) / (1 - ‖a‖) + 1) + 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hxn (norm_nonneg _)) le_rfl
        _ = (1 + ‖a‖) / (1 - ‖a‖) := by field_simp; ring
    · rw [h, cmap_one]
      have e : b * x + (1 - b) - 1 = b * (x - 1) := by ring
      rw [e, norm_mul]
      calc ‖b‖ * ‖x - 1‖ ≤ 1 * ((1 + ‖a‖) / (1 - ‖a‖)) :=
            mul_le_mul hb ihx (norm_nonneg _) zero_le_one
        _ = _ := one_mul _

/-- The coded point of the base point `1` lies in the disc of radius `2/(1 - |a|)`. -/
theorem norm_cpointSeq_add_cratioSeq_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) (m : ℕ)
    (ω : ℕ → Fin 2) : ‖cpointSeq a b m ω + cratioSeq a b m ω‖ ≤ 2 / (1 - ‖a‖) := by
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  have h := norm_cpointSeq_add_cratioSeq_mul_sub_one_le ha hb m ω (y := 1)
    (by rw [sub_self, norm_zero]; positivity)
  rw [mul_one] at h
  calc ‖cpointSeq a b m ω + cratioSeq a b m ω‖
      = ‖(cpointSeq a b m ω + cratioSeq a b m ω - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖cpointSeq a b m ω + cratioSeq a b m ω - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ (1 + ‖a‖) / (1 - ‖a‖) + 1 := by rw [norm_one]; exact add_le_add h le_rfl
    _ = 2 / (1 - ‖a‖) := by field_simp; ring

theorem ca_one_sub (s : ℝ) (z : ℂ) : ca s (1 - z) = cb s z := rfl

theorem cb_one_sub (s : ℝ) (z : ℂ) : cb s (1 - z) = ca s z := by
  unfold cb ca; rw [sub_sub_cancel]

/-- The cross kernel is invariant under the reflection of both arguments. -/
theorem crossKernelC_one_sub (s : ℝ) (z x y : ℂ) :
    crossKernelC s (1 - z) (1 - x) (1 - y) = crossKernelC s z y x := by
  unfold crossKernelC crossBase
  rw [ca_one_sub, cb_one_sub]
  congr 1; ring

theorem one_sub_mem_discQ_half {z : ℂ} (hz : z ∈ discQ (1/2)) : 1 - z ∈ discQ (1/2) := by
  rw [mem_discQ] at hz ⊢
  calc ‖1 - z - ((1/2 : ℝ) : ℂ)‖ = ‖z - ((1/2 : ℝ) : ℂ)‖ := by
        rw [← norm_neg]; congr 1; push_cast; ring
    _ ≤ radQ := hz

/-- The flip of a finite word. -/
def flipFin {m : ℕ} (u : Fin m → Fin 2) : Fin m → Fin 2 := fun k => flipDigit (u k)

theorem flipFin_flipFin {m : ℕ} (u : Fin m → Fin 2) : flipFin (flipFin u) = u := by
  funext k; exact flipDigit_flipDigit _

/-- The flip as a permutation of the finite words. -/
def flipPerm (m : ℕ) : Equiv.Perm (Fin m → Fin 2) :=
  Function.Involutive.toPerm flipFin flipFin_flipFin

theorem flipPerm_apply {m : ℕ} (u : Fin m → Fin 2) : flipPerm m u = flipFin u := rfl

theorem extend_flipFin_agree {m : ℕ} (u : Fin m → Fin 2) :
    ∀ k < m, extend (flipFin u) k = flipWord (extend u) k := by
  intro k hk
  simp [extend, hk, flipWord, flipFin]

/-- The level sums of `z` and `1 - z` differ by at most `6 s γ (γ B²)^m`. -/
theorem norm_levelSum_one_sub_sub_le {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) {z : ℂ}
    (hz : z ∈ discQ (1/2)) (m : ℕ) :
    ‖levelSum (ca s) (cb s) (crossKernelC s) m (1 - z) -
        levelSum (ca s) (cb s) (crossKernelC s) m z‖ ≤
      6 * s * gammaQ s * discRQ s ^ m := by
  have hp0 : (1:ℝ) / 10000 ≤ 1/2 := by norm_num
  have hp1 : (1:ℝ) / 2 ≤ 1/2 := le_rfl
  have hz' := one_sub_mem_discQ_half hz
  have hγ := gammaQ_le hs hsQ
  have hγ0 := gammaQ_nonneg s
  have ha := norm_ca_le_gammaQ hs hp0 hp1 hz
  have hb := norm_cb_le_gammaQ hs hp0 hp1 hz
  have ha1 : ‖ca s z‖ < 1 := by linarith
  have hb1 : ‖cb s z‖ < 1 := by linarith
  have hR : 2 / (1 - ‖cb s z‖) ≤ 5 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hR' : 2 / (1 - ‖ca s z‖) ≤ 5 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  -- the reflected points
  have hpt : ∀ u : Fin m → Fin 2,
      cpointSeq (ca s (1 - z)) (cb s (1 - z)) m (extend (flipFin u))
        = 1 - cpointSeq (ca s z) (cb s z) m (extend u) - cratioSeq (ca s z) (cb s z) m (extend u) := by
    intro u
    rw [ca_one_sub, cb_one_sub, cpointSeq_congr _ _ m (extend_flipFin_agree u),
      one_sub_cpointSeq_eq]
    ring
  have hw : ∀ u : Fin m → Fin 2,
      weightSeq (1 - z) m (extend (flipFin u)) = weightSeq z m (extend u) := by
    intro u
    rw [weightSeq_congr _ m (extend_flipFin_agree u), weightSeq_flip]
  -- bounds on the points
  have hbound : ∀ u : Fin m → Fin 2, ‖cpointSeq (ca s z) (cb s z) m (extend u)‖ ≤ 5/2 :=
    fun u => norm_cpointSeq_discQ_le hs hsQ hp0 hp1 hz m _
  have hbound' : ∀ u : Fin m → Fin 2,
      ‖1 - cpointSeq (ca s z) (cb s z) m (extend u)‖ ≤ 5/2 := by
    intro u
    rw [one_sub_cpointSeq_eq, ← cratioSeq_flip (ca s z) (cb s z) m (extend u)]
    exact (norm_cpointSeq_add_cratioSeq_le hb1 ha1.le m _).trans hR
  have hbound'' : ∀ u : Fin m → Fin 2,
      ‖1 - cpointSeq (ca s z) (cb s z) m (extend u) - cratioSeq (ca s z) (cb s z) m (extend u)‖
        ≤ 5/2 := by
    intro u
    rw [← hpt, ca_one_sub, cb_one_sub]
    exact (norm_cpointSeq_le hb1 ha1.le m _).trans hR
  have hr : ∀ u : Fin m → Fin 2, ‖cratioSeq (ca s z) (cb s z) m (extend u)‖ ≤ gammaQ s ^ m :=
    fun u => (norm_cratioSeq_le _ _ m _).trans (pow_le_pow_left₀ (by positivity) (max_le ha hb) m)
  -- reindex the level sum at `1 - z`
  have e1 : levelSum (ca s) (cb s) (crossKernelC s) m (1 - z)
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          weightSeq z m (extend u) * weightSeq z m (extend v) *
            crossKernelC s (1 - z)
              (1 - cpointSeq (ca s z) (cb s z) m (extend u) - cratioSeq (ca s z) (cb s z) m (extend u))
              (1 - cpointSeq (ca s z) (cb s z) m (extend v) - cratioSeq (ca s z) (cb s z) m (extend v)) := by
    unfold levelSum
    refine (Fintype.sum_equiv (flipPerm m) _ _ fun u => ?_).symm
    refine Fintype.sum_equiv (flipPerm m) _ _ fun v => ?_
    simp only [flipPerm_apply]
    rw [hw, hw, hpt, hpt]
  have e2 : levelSum (ca s) (cb s) (crossKernelC s) m z
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          weightSeq z m (extend u) * weightSeq z m (extend v) *
            crossKernelC s (1 - z)
              (1 - cpointSeq (ca s z) (cb s z) m (extend u))
              (1 - cpointSeq (ca s z) (cb s z) m (extend v)) := by
    unfold levelSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [crossKernelC_one_sub]; ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun u _ => norm_sum_le _ _).trans ?_
  have hterm : ∀ u v : Fin m → Fin 2,
      ‖weightSeq z m (extend u) * weightSeq z m (extend v) *
        (crossKernelC s (1 - z)
            (1 - cpointSeq (ca s z) (cb s z) m (extend u) - cratioSeq (ca s z) (cb s z) m (extend u))
            (1 - cpointSeq (ca s z) (cb s z) m (extend v) - cratioSeq (ca s z) (cb s z) m (extend v)) -
          crossKernelC s (1 - z) (1 - cpointSeq (ca s z) (cb s z) m (extend u))
            (1 - cpointSeq (ca s z) (cb s z) m (extend v)))‖
        ≤ ‖weightSeq z m (extend u)‖ * ‖weightSeq z m (extend v)‖ * (6 * s * gammaQ s * gammaQ s ^ m) := by
    intro u v
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := norm_crossKernelC_sub_le hs hsQ hp0 hp1 hz' _ _ _ _ (hbound' u) (hbound' v)
      (hbound'' u) (hbound'' v)
    refine h.trans ?_
    have e : ∀ u : Fin m → Fin 2,
        1 - cpointSeq (ca s z) (cb s z) m (extend u) - cratioSeq (ca s z) (cb s z) m (extend u) -
          (1 - cpointSeq (ca s z) (cb s z) m (extend u)) = -cratioSeq (ca s z) (cb s z) m (extend u) :=
      fun u => by ring
    rw [e, e, norm_neg, norm_neg]
    have := hr u; have := hr v
    have h0 : 0 ≤ 3 * s * gammaQ s := by positivity
    nlinarith
  refine (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v).trans ?_
  have e : (∑ u : Fin m → Fin 2, ‖weightSeq z m (extend u)‖) *
      (∑ v : Fin m → Fin 2, ‖weightSeq z m (extend v)‖) * (6 * s * gammaQ s * gammaQ s ^ m)
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          ‖weightSeq z m (extend u)‖ * ‖weightSeq z m (extend v)‖ *
            (6 * s * gammaQ s * gammaQ s ^ m) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
  rw [← e, sum_norm_weightSeq]
  have hB := norm_add_norm_one_sub_le_discQ hp0 hp1 hz
  have hB0 : 0 ≤ ‖z‖ + ‖1 - z‖ := by positivity
  have hpow : (‖z‖ + ‖1 - z‖) ^ m * (‖z‖ + ‖1 - z‖) ^ m ≤ (discBQ ^ 2) ^ m := by
    rw [← mul_pow, ← pow_two, ← pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by unfold discBQ; nlinarith) m
  have hK : 0 ≤ 6 * s * gammaQ s := by positivity
  calc (‖z‖ + ‖1 - z‖) ^ m * (‖z‖ + ‖1 - z‖) ^ m * (6 * s * gammaQ s * gammaQ s ^ m)
      = (‖z‖ + ‖1 - z‖) ^ m * (‖z‖ + ‖1 - z‖) ^ m * gammaQ s ^ m * (6 * s * gammaQ s) := by ring
    _ ≤ (discBQ ^ 2) ^ m * gammaQ s ^ m * (6 * s * gammaQ s) := by
        gcongr
    _ = 6 * s * gammaQ s * discRQ s ^ m := by
        unfold discRQ; rw [mul_pow]; ring

/-- `M_{1-z} = M_z` on the disc around `1/2`. -/
theorem crossLimit_one_sub {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) {z : ℂ}
    (hz : z ∈ discQ (1/2)) : crossLimit s (1 - z) = crossLimit s z := by
  have hp0 : (1:ℝ) / 10000 ≤ 1/2 := by norm_num
  have hp1 : (1:ℝ) / 2 ≤ 1/2 := le_rfl
  have hz' := one_sub_mem_discQ_half hz
  have h1 := tendsto_levelSum (discRQ_nonneg s) (discRQ_lt_one hs hsQ)
    (incrementBound_cross hs hsQ hp0 hp1) hz'
  have h2 := tendsto_levelSum (discRQ_nonneg s) (discRQ_lt_one hs hsQ)
    (incrementBound_cross hs hsQ hp0 hp1) hz
  have h3 : Tendsto (fun m => levelSum (ca s) (cb s) (crossKernelC s) m (1 - z) -
      levelSum (ca s) (cb s) (crossKernelC s) m z) atTop (𝓝 0) := by
    have hg : Tendsto (fun m : ℕ => 6 * s * gammaQ s * discRQ s ^ m) atTop (𝓝 0) := by
      rw [← mul_zero (6 * s * gammaQ s)]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (discRQ_nonneg s)
        (discRQ_lt_one hs hsQ)).const_mul _
    exact squeeze_zero_norm (fun m => norm_levelSum_one_sub_sub_le hs hsQ hz m) hg
  have h4 := h1.sub h2
  have := tendsto_nhds_unique h4 h3
  unfold crossLimit
  exact sub_eq_zero.1 this

/-- `M_{1/2}' = 0`, by the symmetry `M_p = M_{1-p}`. -/
theorem deriv_fixedMoment_half {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) :
    deriv (fixedMoment s) (1/2) = 0 := by
  have hp0 : (1:ℝ) / 10000 ≤ 1/2 := by norm_num
  have hp1 : (1:ℝ) / 2 ≤ 1/2 := le_rfl
  have hR : 0 < radQ := by rw [radQ_eq]; norm_num
  have hmem : (1/2 : ℝ) ∈ Ioo (1/2 - radQ) (1/2 + radQ) := ⟨by linarith, by linarith⟩
  have hd := hasDerivAt_fixedMoment_of_mem hs hsQ hp0 hp1 hmem
  rw [hd.deriv]
  -- the complex derivative vanishes
  have hball : ((1/2 : ℝ) : ℂ) ∈ ball ((1/2 : ℝ) : ℂ) radQ := mem_ball_self hR
  have hdiff : DifferentiableAt ℂ (crossLimit s) ((1/2 : ℝ) : ℂ) :=
    (differentiableOn_crossLimit hs hsQ hp0 hp1).differentiableAt (isOpen_ball.mem_nhds hball)
  set D := deriv (crossLimit s) ((1/2 : ℝ) : ℂ) with hD
  have hD1 : HasDerivAt (crossLimit s) D ((1/2 : ℝ) : ℂ) := hdiff.hasDerivAt
  have hhalf : (1 : ℂ) - ((1/2 : ℝ) : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  have hD2 : HasDerivAt (fun w => crossLimit s (1 - w)) (D * (-1)) ((1/2 : ℝ) : ℂ) := by
    have hinner : HasDerivAt (fun w : ℂ => 1 - w) (-1) ((1/2 : ℝ) : ℂ) :=
      (hasDerivAt_id _).const_sub 1
    have hD1' : HasDerivAt (crossLimit s) D (1 - ((1/2 : ℝ) : ℂ)) := by rw [hhalf]; exact hD1
    exact hD1'.comp _ hinner
  have hD3 : HasDerivAt (crossLimit s) (D * (-1)) ((1/2 : ℝ) : ℂ) := by
    refine hD2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hball] with w hw
    exact (crossLimit_one_sub hs hsQ (ball_subset_closedBall hw)).symm
  have : D = D * (-1) := hD1.unique hD3
  have hD0 : D = 0 := by linear_combination this / 2
  rw [hD0, Complex.zero_re]

end

end BrownianImages
