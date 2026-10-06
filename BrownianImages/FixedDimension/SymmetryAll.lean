/-
The symmetry `M_p = M_{1-p}` and `H̄_s(p) = H̄_s(1-p)` of `sec:fixed-dimension-separation`,
for every `p ∈ (0,1)`: reflection in `1/2` takes `μ_p` to `μ_{1-p}` and preserves pair
distances.  The proof flips every letter in the level sums, which reflects the coded points
up to the base point, `1 - x_u = x'_{σu} + r_u`; the cross kernel is Lipschitz on `[0,1]²`
with constant `s (1 - a - b)^{-s-1}`, so the level sums of `p` and `1 - p` differ by
`O(γ^m)` and their limits agree.

* `abs_rpow_fixedCross_sub_le`: the Lipschitz bound of the real kernel on `[0,1]²`.
* `norm_levelSum_one_sub_sub_le'`: the level sums of `p` and `1 - p`.
* `fixedMoment_symm`, `fixedMean_symm`: the symmetry.
-/
import BrownianImages.FixedDimension.RealLevelSums
import BrownianImages.FixedDimension.Symmetry

namespace BrownianImages

open MeasureTheory Filter Set Metric Hutchinson
open scoped Topology

noncomputable section

/-- The Lipschitz constant `s (1 - a - b)^{-s-1}` of the kernel on `[0,1]²`. -/
def crossLip (s p : ℝ) : ℝ := s * crossGap s p ^ (-s - 1)

theorem crossLip_nonneg {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ crossLip s p :=
  mul_nonneg hs.le (Real.rpow_nonneg (crossGap_pos hs hs1 hp0 hp1).le _)

/-- The derivative of the real kernel in its first argument, with its bound. -/
theorem hasDerivAt_rpow_fixedCross_x {s p X Y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun X => fixedCross s p X Y ^ (-s))
      (-(fixedA s p * 1) * (-s) * fixedCross s p X Y ^ (-s - 1)) X ∧
    |-(fixedA s p * 1) * (-s) * fixedCross s p X Y ^ (-s - 1)| ≤ crossLip s p := by
  have hpos := fixedCross_pos hs hs1 hp0 hp1 hX hY
  have hbase : HasDerivAt (fun X => fixedCross s p X Y) (-(fixedA s p * 1)) X := by
    unfold fixedCross
    exact ((hasDerivAt_id X).const_mul (fixedA s p)).const_sub _
  refine ⟨hbase.rpow_const (Or.inl hpos.ne'), ?_⟩
  have ha0 := fixedA_pos (s := s) hp0
  have ha1 := fixedA_le_one hs hp0 hp1
  have hg := crossGap_pos hs hs1 hp0 hp1
  have hmem := (fixedCross_mem hs hp0 hp1 hX hY).1
  have hr : fixedCross s p X Y ^ (-s - 1) ≤ crossGap s p ^ (-s - 1) := by
    rw [show (-s - 1) = -(s + 1) by ring]
    exact rpow_neg_antitone hg hmem (by linarith)
  have hr0 : 0 ≤ fixedCross s p X Y ^ (-s - 1) := Real.rpow_nonneg hpos.le _
  have e : -(fixedA s p * 1) * (-s) * fixedCross s p X Y ^ (-s - 1)
      = fixedA s p * (s * fixedCross s p X Y ^ (-s - 1)) := by ring
  rw [e, abs_of_nonneg (by positivity)]
  unfold crossLip
  calc fixedA s p * (s * fixedCross s p X Y ^ (-s - 1))
      ≤ 1 * (s * crossGap s p ^ (-s - 1)) :=
        mul_le_mul ha1 (mul_le_mul_of_nonneg_left hr hs.le) (by positivity) zero_le_one
    _ = s * crossGap s p ^ (-s - 1) := one_mul _

/-- The derivative of the real kernel in its second argument, with its bound. -/
theorem hasDerivAt_rpow_fixedCross_y {s p X Y : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun Y => fixedCross s p X Y ^ (-s))
      (fixedB s p * 1 * (-s) * fixedCross s p X Y ^ (-s - 1)) Y ∧
    |fixedB s p * 1 * (-s) * fixedCross s p X Y ^ (-s - 1)| ≤ crossLip s p := by
  have hpos := fixedCross_pos hs hs1 hp0 hp1 hX hY
  have hbase : HasDerivAt (fun Y => fixedCross s p X Y) (fixedB s p * 1) Y := by
    unfold fixedCross
    exact (((hasDerivAt_id Y).const_mul (fixedB s p)).const_add _).sub_const _
  refine ⟨hbase.rpow_const (Or.inl hpos.ne'), ?_⟩
  have hb0 := fixedB_pos (s := s) hp1
  have hb1 := fixedB_le_one hs hp0 hp1
  have hg := crossGap_pos hs hs1 hp0 hp1
  have hmem := (fixedCross_mem hs hp0 hp1 hX hY).1
  have hr : fixedCross s p X Y ^ (-s - 1) ≤ crossGap s p ^ (-s - 1) := by
    rw [show (-s - 1) = -(s + 1) by ring]
    exact rpow_neg_antitone hg hmem (by linarith)
  have hr0 : 0 ≤ fixedCross s p X Y ^ (-s - 1) := Real.rpow_nonneg hpos.le _
  have e : fixedB s p * 1 * (-s) * fixedCross s p X Y ^ (-s - 1)
      = -(fixedB s p * (s * fixedCross s p X Y ^ (-s - 1))) := by ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  unfold crossLip
  calc fixedB s p * (s * fixedCross s p X Y ^ (-s - 1))
      ≤ 1 * (s * crossGap s p ^ (-s - 1)) :=
        mul_le_mul hb1 (mul_le_mul_of_nonneg_left hr hs.le) (by positivity) zero_le_one
    _ = s * crossGap s p ^ (-s - 1) := one_mul _

/-- The real kernel is Lipschitz on `[0,1]²`. -/
theorem abs_rpow_fixedCross_sub_le {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {X Y X' Y' : ℝ} (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1)
    (hX' : X' ∈ Icc (0:ℝ) 1) (hY' : Y' ∈ Icc (0:ℝ) 1) :
    |fixedCross s p X' Y' ^ (-s) - fixedCross s p X Y ^ (-s)|
      ≤ crossLip s p * (|X' - X| + |Y' - Y|) := by
  have hconv : Convex ℝ (Icc (0:ℝ) 1) := convex_Icc _ _
  have h1 : ‖fixedCross s p X' Y' ^ (-s) - fixedCross s p X Y' ^ (-s)‖
      ≤ crossLip s p * ‖X' - X‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun X => fixedCross s p X Y' ^ (-s))
      (f' := fun X => -(fixedA s p * 1) * (-s) * fixedCross s p X Y' ^ (-s - 1))
      (fun w hw => (hasDerivAt_rpow_fixedCross_x hs hs1 hp0 hp1 hw hY').1.hasDerivWithinAt)
      (fun w hw => by
        rw [Real.norm_eq_abs]; exact (hasDerivAt_rpow_fixedCross_x hs hs1 hp0 hp1 hw hY').2)
      hX hX'
  have h2 : ‖fixedCross s p X Y' ^ (-s) - fixedCross s p X Y ^ (-s)‖
      ≤ crossLip s p * ‖Y' - Y‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun Y => fixedCross s p X Y ^ (-s))
      (f' := fun Y => fixedB s p * 1 * (-s) * fixedCross s p X Y ^ (-s - 1))
      (fun w hw => (hasDerivAt_rpow_fixedCross_y hs hs1 hp0 hp1 hX hw).1.hasDerivWithinAt)
      (fun w hw => by
        rw [Real.norm_eq_abs]; exact (hasDerivAt_rpow_fixedCross_y hs hs1 hp0 hp1 hX hw).2)
      hY hY'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1 h2
  calc |fixedCross s p X' Y' ^ (-s) - fixedCross s p X Y ^ (-s)|
      = |(fixedCross s p X' Y' ^ (-s) - fixedCross s p X Y' ^ (-s)) +
          (fixedCross s p X Y' ^ (-s) - fixedCross s p X Y ^ (-s))| := by ring_nf
    _ ≤ |fixedCross s p X' Y' ^ (-s) - fixedCross s p X Y' ^ (-s)| +
          |fixedCross s p X Y' ^ (-s) - fixedCross s p X Y ^ (-s)| := abs_add_le _ _
    _ ≤ crossLip s p * |X' - X| + crossLip s p * |Y' - Y| := add_le_add h1 h2
    _ = crossLip s p * (|X' - X| + |Y' - Y|) := by ring

/-- The complex kernel at a real parameter and real points of `[0,1]` is Lipschitz. -/
theorem norm_crossKernelC_ofReal_sub_le {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) {X Y X' Y' : ℝ} (hX : X ∈ Icc (0:ℝ) 1) (hY : Y ∈ Icc (0:ℝ) 1)
    (hX' : X' ∈ Icc (0:ℝ) 1) (hY' : Y' ∈ Icc (0:ℝ) 1) :
    ‖crossKernelC s (p : ℂ) (X' : ℂ) (Y' : ℂ) - crossKernelC s (p : ℂ) (X : ℂ) (Y : ℂ)‖
      ≤ crossLip s p * (‖(X' : ℂ) - X‖ + ‖(Y' : ℂ) - Y‖) := by
  rw [crossKernelC_ofReal hs hs1 hp0 hp1 hX hY, crossKernelC_ofReal hs hs1 hp0 hp1 hX' hY',
    ← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_rpow_fixedCross_sub_le hs hs1 hp0 hp1 hX hY hX' hY'

theorem ofReal_one_sub (p : ℝ) : ((1 - p : ℝ) : ℂ) = 1 - (p : ℂ) := by push_cast; ring

/-- The level sums of `p` and of `1 - p` differ by at most `2 L γ^m`, with `L` the Lipschitz
constant of the kernel at `1 - p` and `γ = max(a, b)`. -/
theorem norm_levelSum_one_sub_sub_le' {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) :
    ‖levelSum (ca s) (cb s) (crossKernelC s) m (1 - (p : ℂ)) -
        levelSum (ca s) (cb s) (crossKernelC s) m (p : ℂ)‖ ≤
      2 * crossLip s (1 - p) * max (fixedA s p) (fixedB s p) ^ m := by
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have ha := ca_ofReal (s := s) hp0.le
  have hb := cb_ofReal (s := s) hp1.le
  have hγ0 : 0 ≤ max (fixedA s p) (fixedB s p) :=
    le_max_of_le_left (fixedA_pos (s := s) hp0).le
  -- the points
  set S := fixedSystem s p hs hp0 hp1
  set S' := fixedSystem s (1 - p) hs hq0 hq1
  have hX : ∀ u : Fin m → Fin 2, cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m (extend u)
      = ((codeSeq S (extend u) m : ℝ) : ℂ) := fun u => by
    rw [ha, hb, cpointSeq_ofReal hs hp0 hp1]
  have hX' : ∀ u : Fin m → Fin 2,
      cpointSeq (ca s (1 - (p : ℂ))) (cb s (1 - (p : ℂ))) m (extend (flipFin u))
        = ((codeSeq S' (extend (flipFin u)) m : ℝ) : ℂ) := fun u => by
    rw [← ofReal_one_sub, ca_ofReal hq0.le, cb_ofReal hq1.le, cpointSeq_ofReal hs hq0 hq1]
  have hpt : ∀ u : Fin m → Fin 2,
      cpointSeq (ca s (1 - (p : ℂ))) (cb s (1 - (p : ℂ))) m (extend (flipFin u))
        = 1 - cpointSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m (extend u)
          - cratioSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m (extend u) := by
    intro u
    rw [ca_one_sub, cb_one_sub, cpointSeq_congr _ _ m (extend_flipFin_agree u),
      one_sub_cpointSeq_eq]
    ring
  have hw : ∀ u : Fin m → Fin 2,
      weightSeq (1 - (p : ℂ)) m (extend (flipFin u)) = weightSeq (p : ℂ) m (extend u) := by
    intro u
    rw [weightSeq_congr _ m (extend_flipFin_agree u), weightSeq_flip]
  have hr : ∀ u : Fin m → Fin 2, ‖cratioSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m (extend u)‖
      ≤ max (fixedA s p) (fixedB s p) ^ m := by
    intro u
    refine (norm_cratioSeq_le _ _ m _).trans (le_of_eq ?_)
    rw [ha, hb, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (fixedA_pos (s := s) hp0).le,
      Real.norm_of_nonneg (fixedB_pos (s := s) hp1).le]
  -- reindex the level sum at `1 - p`
  have e1 : levelSum (ca s) (cb s) (crossKernelC s) m (1 - (p : ℂ))
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          weightSeq (p : ℂ) m (extend u) * weightSeq (p : ℂ) m (extend v) *
            crossKernelC s (1 - (p : ℂ)) ((codeSeq S' (extend (flipFin u)) m : ℝ) : ℂ)
              ((codeSeq S' (extend (flipFin v)) m : ℝ) : ℂ) := by
    unfold levelSum
    refine (Fintype.sum_equiv (flipPerm m) _ _ fun u => ?_).symm
    refine Fintype.sum_equiv (flipPerm m) _ _ fun v => ?_
    simp only [flipPerm_apply]
    rw [hw, hw, hX', hX']
  have e2 : levelSum (ca s) (cb s) (crossKernelC s) m (p : ℂ)
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          weightSeq (p : ℂ) m (extend u) * weightSeq (p : ℂ) m (extend v) *
            crossKernelC s (1 - (p : ℂ)) ((1 - codeSeq S (extend u) m : ℝ) : ℂ)
              ((1 - codeSeq S (extend v) m : ℝ) : ℂ) := by
    unfold levelSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hX, hX, ofReal_one_sub, ofReal_one_sub, crossKernelC_one_sub]; ring
  -- the termwise bound
  have hterm : ∀ u v : Fin m → Fin 2,
      ‖weightSeq (p : ℂ) m (extend u) * weightSeq (p : ℂ) m (extend v) *
        (crossKernelC s (1 - (p : ℂ)) ((codeSeq S' (extend (flipFin u)) m : ℝ) : ℂ)
            ((codeSeq S' (extend (flipFin v)) m : ℝ) : ℂ) -
          crossKernelC s (1 - (p : ℂ)) ((1 - codeSeq S (extend u) m : ℝ) : ℂ)
            ((1 - codeSeq S (extend v) m : ℝ) : ℂ))‖
        ≤ ‖weightSeq (p : ℂ) m (extend u)‖ * ‖weightSeq (p : ℂ) m (extend v)‖ *
            (2 * crossLip s (1 - p) * max (fixedA s p) (fixedB s p) ^ m) := by
    intro u v
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hmem : ∀ w : Fin m → Fin 2, 1 - codeSeq S (extend w) m ∈ Icc (0:ℝ) 1 := by
      intro w
      have := codeSeq_mem_Icc S (extend w) m
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    have h := norm_crossKernelC_ofReal_sub_le hs hs1 hq0 hq1
      (X := 1 - codeSeq S (extend u) m) (Y := 1 - codeSeq S (extend v) m)
      (X' := codeSeq S' (extend (flipFin u)) m) (Y' := codeSeq S' (extend (flipFin v)) m)
      (hmem u) (hmem v) (codeSeq_mem_Icc _ _ _) (codeSeq_mem_Icc _ _ _)
    rw [show ((1 - p : ℝ) : ℂ) = 1 - (p : ℂ) from ofReal_one_sub p] at h
    refine h.trans ?_
    have e : ∀ w : Fin m → Fin 2,
        ((codeSeq S' (extend (flipFin w)) m : ℝ) : ℂ) - ((1 - codeSeq S (extend w) m : ℝ) : ℂ)
          = -cratioSeq (ca s (p : ℂ)) (cb s (p : ℂ)) m (extend w) := by
      intro w
      rw [← hX', hpt, ofReal_one_sub, hX]; ring
    rw [e, e, norm_neg, norm_neg]
    have := hr u; have := hr v
    have h0 : 0 ≤ crossLip s (1 - p) := crossLip_nonneg hs hs1 hq0 hq1
    nlinarith
  rw [e1, e2, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun u _ => norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v).trans ?_
  have e : (∑ u : Fin m → Fin 2, ‖weightSeq (p : ℂ) m (extend u)‖) *
      (∑ v : Fin m → Fin 2, ‖weightSeq (p : ℂ) m (extend v)‖) *
      (2 * crossLip s (1 - p) * max (fixedA s p) (fixedB s p) ^ m)
      = ∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2,
          ‖weightSeq (p : ℂ) m (extend u)‖ * ‖weightSeq (p : ℂ) m (extend v)‖ *
            (2 * crossLip s (1 - p) * max (fixedA s p) (fixedB s p) ^ m) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
  rw [← e, sum_norm_weightSeq]
  have hnorm : ‖(p : ℂ)‖ + ‖1 - (p : ℂ)‖ = 1 := by
    rw [← ofReal_one_sub, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hp0.le,
      Real.norm_of_nonneg hq0.le]; ring
  rw [hnorm, one_pow, one_mul, one_mul]

/-- **`M_p = M_{1-p}`** for every `p ∈ (0,1)`. -/
theorem fixedMoment_symm {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    fixedMoment s (1 - p) = fixedMoment s p := by
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have h1 := tendsto_levelSum_ofReal hs hs1 hq0 hq1
  have h2 := tendsto_levelSum_ofReal hs hs1 hp0 hp1
  simp_rw [ofReal_one_sub] at h1
  have hγ : max (fixedA s p) (fixedB s p) < 1 :=
    max_lt (fixedA_lt_one hs hp0 hp1) (fixedB_lt_one hs hp0 hp1)
  have hγ0 : 0 ≤ max (fixedA s p) (fixedB s p) :=
    le_max_of_le_left (fixedA_pos (s := s) hp0).le
  have h3 : Tendsto (fun m => levelSum (ca s) (cb s) (crossKernelC s) m (1 - (p : ℂ)) -
      levelSum (ca s) (cb s) (crossKernelC s) m (p : ℂ)) atTop (𝓝 0) := by
    have hg : Tendsto (fun m : ℕ => 2 * crossLip s (1 - p) * max (fixedA s p) (fixedB s p) ^ m)
        atTop (𝓝 0) := by
      rw [← mul_zero (2 * crossLip s (1 - p))]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ).const_mul _
    exact squeeze_zero_norm (fun m => norm_levelSum_one_sub_sub_le' hs hs1 hp0 hp1 m) hg
  have := tendsto_nhds_unique (h1.sub h2) h3
  exact_mod_cast sub_eq_zero.1 this

theorem entropy_one_sub (p : ℝ) : entropy (1 - p) = entropy p := by
  unfold entropy; rw [sub_sub_cancel]; ring

/-- **`H̄_s(p) = H̄_s(1-p)`** for every `p ∈ (0,1)`. -/
theorem fixedMean_symm {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    fixedMean s (1 - p) = fixedMean s p := by
  unfold fixedMean
  rw [fixedMoment_symm hs hs1 hp0 hp1, entropy_one_sub, sub_sub_cancel, mul_comm (1 - p) p]

end

end BrownianImages
