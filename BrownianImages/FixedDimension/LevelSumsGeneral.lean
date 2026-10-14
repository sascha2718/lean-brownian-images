module

/-
The general analytic part of `thm:level-sums`, for an arbitrary holomorphic kernel
on `U × D × D`. The derivative assumptions are converted to the Lipschitz estimate
used by the telescoping argument; the resulting limit is uniform on the whole of `U`.

* `norm_kernel_sub_le_of_deriv_bound`: the two-coordinate mean-value estimate.
* `tendstoUniformlyOn_levelSum`: uniform convergence from geometric increments.
* `levelSums_holomorphic`: uniform convergence, holomorphy and the exact bound in
  `eq:level-sum-bound`, with no restriction to the kernels used later in the paper.
-/
public import BrownianImages.FixedDimension.LevelSumsDomain
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

namespace BrownianImages

open MeasureTheory Filter Set Hutchinson
open scoped Topology

noncomputable section

/-- `thm:level-sums`: holomorphy of every finite coded point for holomorphic contractions. -/
theorem differentiableOn_cpointSeq_general {a b : ℂ → ℂ} {U : Set ℂ}
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (m : ℕ) (ω : ℕ → Fin 2) :
    DifferentiableOn ℂ (fun z => cpointSeq (a z) (b z) m ω) U := by
  induction m generalizing ω with
  | zero => simp only [cpointSeq_zero]; exact differentiableOn_const 0
  | succ m ih =>
    simp only [cpointSeq_succ, cmap, cratioOf, cshiftOf]
    split_ifs
    · exact (ha.mul (ih _)).add (differentiableOn_const 0)
    · exact (hb.mul (ih _)).add ((differentiableOn_const _).sub hb)

/-- `thm:level-sums`: the word weights are holomorphic on any parameter domain. -/
theorem differentiableOn_weightSeq_general (m : ℕ) (ω : ℕ → Fin 2) (U : Set ℂ) :
    DifferentiableOn ℂ (fun z => weightSeq z m ω) U := by
  induction m generalizing ω with
  | zero => simp only [weightSeq_zero]; exact differentiableOn_const 1
  | succ m ih =>
    simp only [weightSeq_succ]
    split_ifs
    · exact differentiableOn_id.mul (ih _)
    · exact ((differentiableOn_const _).sub differentiableOn_id).mul (ih _)

/-- `thm:level-sums`: holomorphy of the finite sums follows from joint holomorphy
of the kernel and holomorphy of the contractions. -/
theorem differentiableOn_levelSum_general {a b : ℂ → ℂ} {φ : ℂ → ℂ → ℂ → ℂ}
    {U D : Set ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hφ : DifferentiableOn ℂ (fun w : ℂ × ℂ × ℂ => φ w.1 w.2.1 w.2.2)
      (U ×ˢ (D ×ˢ D)))
    (hD : ∀ z ∈ U, ∀ (m : ℕ) (ω : ℕ → Fin 2), cpointSeq (a z) (b z) m ω ∈ D)
    (m : ℕ) : DifferentiableOn ℂ (levelSum a b φ m) U := by
  unfold levelSum
  refine DifferentiableOn.fun_sum fun u _ => ?_
  refine DifferentiableOn.fun_sum fun v _ => ?_
  refine ((differentiableOn_weightSeq_general m (extend u) U).mul
    (differentiableOn_weightSeq_general m (extend v) U)).mul ?_
  exact hφ.comp (differentiableOn_id.prodMk
    ((differentiableOn_cpointSeq_general ha hb m (extend u)).prodMk
      (differentiableOn_cpointSeq_general ha hb m (extend v))))
    (fun z hz => ⟨hz, hD z hz m _, hD z hz m _⟩)

/-- `thm:level-sums`: bounded partial derivatives on an open convex kernel domain
imply the Lipschitz bound used in the level-sum estimate. -/
theorem norm_kernel_sub_le_of_deriv_bound {φ : ℂ → ℂ → ℂ → ℂ} {U D : Set ℂ}
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hφ : DifferentiableOn ℂ (fun w : ℂ × ℂ × ℂ => φ w.1 w.2.1 w.2.2)
      (U ×ˢ (D ×ˢ D))) {z : ℂ} (hz : z ∈ U) {L : ℝ}
    (hLx : ∀ x ∈ D, ∀ y ∈ D, ‖deriv (fun t => φ z t y) x‖ ≤ L)
    (hLy : ∀ x ∈ D, ∀ y ∈ D, ‖deriv (fun t => φ z x t) y‖ ≤ L)
    (x y x' y' : ℂ) (hx : x ∈ D) (hy : y ∈ D) (hx' : x' ∈ D) (hy' : y' ∈ D) :
    ‖φ z x' y' - φ z x y‖ ≤ L * (‖x' - x‖ + ‖y' - y‖) := by
  have hdx : DifferentiableOn ℂ (fun t => φ z t y') D :=
    hφ.comp ((differentiableOn_const _).prodMk
      (differentiableOn_id.prodMk (differentiableOn_const _)))
      (fun t ht => ⟨hz, ht, hy'⟩)
  have hdy : DifferentiableOn ℂ (fun t => φ z x t) D :=
    hφ.comp ((differentiableOn_const _).prodMk
      ((differentiableOn_const _).prodMk differentiableOn_id))
      (fun t ht => ⟨hz, hx, ht⟩)
  have h1 := hDc.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => ((hdx t ht).differentiableAt (hDo.mem_nhds ht)).hasDerivAt.hasDerivWithinAt)
    (fun t ht => hLx t ht y' hy') hx hx'
  have h2 := hDc.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => ((hdy t ht).differentiableAt (hDo.mem_nhds ht)).hasDerivAt.hasDerivWithinAt)
    (fun t ht => hLy x hx t ht) hy hy'
  calc
    ‖φ z x' y' - φ z x y‖ = ‖(φ z x' y' - φ z x y') + (φ z x y' - φ z x y)‖ := by ring_nf
    _ ≤ ‖φ z x' y' - φ z x y'‖ + ‖φ z x y' - φ z x y‖ := norm_add_le _ _
    _ ≤ L * ‖x' - x‖ + L * ‖y' - y‖ := add_le_add h1 h2
    _ = L * (‖x' - x‖ + ‖y' - y‖) := by ring

/-- `thm:level-sums`: geometric increments give convergence uniform on the entire
parameter domain, not just pointwise or locally uniformly. -/
theorem tendstoUniformlyOn_levelSum {a b : ℂ → ℂ} {φ : ℂ → ℂ → ℂ → ℂ}
    {U : Set ℂ} {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hinc : IncrementBound a b φ U C r) :
    TendstoUniformlyOn (levelSum a b φ) (limitSum a b φ) atTop U := by
  have h := tendstoUniformlyOn_tsum_nat
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    (fun m z hz => hinc z hz m)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn z hz
  convert hn z hz using 1
  simp only [limitSum, dist_eq_norm]
  rw [Finset.sum_range_sub (fun k => levelSum a b φ k z)]
  congr 1
  ring

/-- The general analytic assertions of `thm:level-sums`. The constants `B` and `ρ`
can be any uniform majorants, so in particular `B` may be the supremum used in the
paper. Boundedness of `D` and the disc shape of `U` are unnecessary for this part. -/
theorem levelSums_holomorphic {a b : ℂ → ℂ} {φ : ℂ → ℂ → ℂ → ℂ}
    {U D : Set ℂ} {ρ B L : ℝ}
    (hU : IsOpen U) (hDo : IsOpen D) (hDc : Convex ℝ D)
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hsmall : ρ * B ^ 2 < 1)
    (hρ : ∀ z ∈ U, max ‖a z‖ ‖b z‖ ≤ ρ)
    (hB : ∀ z ∈ U, ‖z‖ + ‖1 - z‖ ≤ B)
    (hD : ∀ z ∈ U, ∀ (m : ℕ) (ω : ℕ → Fin 2), cpointSeq (a z) (b z) m ω ∈ D)
    (hφ : DifferentiableOn ℂ (fun w : ℂ × ℂ × ℂ => φ w.1 w.2.1 w.2.2)
      (U ×ˢ (D ×ˢ D)))
    (hL0 : 0 ≤ L)
    (hLx : ∀ z ∈ U, ∀ x ∈ D, ∀ y ∈ D, ‖deriv (fun t => φ z t y) x‖ ≤ L)
    (hLy : ∀ z ∈ U, ∀ x ∈ D, ∀ y ∈ D, ‖deriv (fun t => φ z x t) y‖ ≤ L) :
    TendstoUniformlyOn (levelSum a b φ) (limitSum a b φ) atTop U ∧
    DifferentiableOn ℂ (limitSum a b φ) U ∧
    ∀ z ∈ U, ‖limitSum a b φ z - φ z 0 0‖ ≤ 4 * L * B ^ 2 / (1 - ρ * B ^ 2) := by
  have hr0 : 0 ≤ ρ * B ^ 2 := mul_nonneg hρ0 (sq_nonneg B)
  have hinc : IncrementBound a b φ U (4 * L * B ^ 2) (ρ * B ^ 2) := by
    intro z hz m
    have hb1 : ‖b z‖ ≤ 1 := ((le_max_right _ _).trans (hρ z hz)).trans hρ1.le
    have h := norm_levelSum_succ_sub_le_of_mem a b φ m hb1 (hρ z hz) (hB z hz)
      (hD z hz) hL0
      (norm_kernel_sub_le_of_deriv_bound hDo hDc hφ hz (hLx z hz) (hLy z hz))
    convert h using 1
    ring
  exact ⟨tendstoUniformlyOn_levelSum hr0 hsmall hinc,
    differentiableOn_limitSum hr0 hsmall hinc hU (fun _ hz => hz)
      (differentiableOn_levelSum_general ha hb hφ hD),
    fun z hz => norm_limitSum_sub_le hr0 hsmall hinc hz⟩

/-- The supremum `B` in `thm:level-sums` is finite on an open disc. -/
theorem bddAbove_disc_weight_norms (z₀ : ℂ) (r : ℝ) :
    BddAbove ((fun z : ℂ => ‖z‖ + ‖1 - z‖) '' Metric.ball z₀ r) := by
  refine ⟨1 + 2 * (‖z₀‖ + r), ?_⟩
  rintro t ⟨z, hz, rfl⟩
  have hz' : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hn : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - z₀) z₀
  have h1 : ‖(1 : ℂ) - z‖ ≤ 1 + ‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  linarith

/-- Every weight norm is bounded by the actual supremum `B` used in `thm:level-sums`. -/
theorem norm_weights_le_disc_sup {z₀ z : ℂ} {r : ℝ} (hz : z ∈ Metric.ball z₀ r) :
    ‖z‖ + ‖1 - z‖ ≤ sSup ((fun w : ℂ => ‖w‖ + ‖1 - w‖) '' Metric.ball z₀ r) :=
  le_csSup (bddAbove_disc_weight_norms z₀ r) ⟨z, hz, rfl⟩

/-- The analytic conclusions of `thm:level-sums`, with the paper's open disc and
its actual supremum `B`. Nonnegativity of the derivative and contraction bounds is
derived from the assumptions rather than added as a hypothesis. -/
theorem levelSums_holomorphic_disc {a b : ℂ → ℂ} {φ : ℂ → ℂ → ℂ → ℂ}
    {z₀ : ℂ} {r ρ L : ℝ} {D : Set ℂ} (hr : 0 < r)
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (ha : DifferentiableOn ℂ a (Metric.ball z₀ r))
    (hb : DifferentiableOn ℂ b (Metric.ball z₀ r))
    (hρ1 : ρ < 1)
    (hsmall : ρ * (sSup ((fun z : ℂ => ‖z‖ + ‖1 - z‖) '' Metric.ball z₀ r)) ^ 2 < 1)
    (hρ : ∀ z ∈ Metric.ball z₀ r, max ‖a z‖ ‖b z‖ ≤ ρ)
    (hD : ∀ z ∈ Metric.ball z₀ r, ∀ (m : ℕ) (ω : ℕ → Fin 2),
      cpointSeq (a z) (b z) m ω ∈ D)
    (hφ : DifferentiableOn ℂ (fun w : ℂ × ℂ × ℂ => φ w.1 w.2.1 w.2.2)
      (Metric.ball z₀ r ×ˢ (D ×ˢ D)))
    (hLx : ∀ z ∈ Metric.ball z₀ r, ∀ x ∈ D, ∀ y ∈ D,
      ‖deriv (fun t => φ z t y) x‖ ≤ L)
    (hLy : ∀ z ∈ Metric.ball z₀ r, ∀ x ∈ D, ∀ y ∈ D,
      ‖deriv (fun t => φ z x t) y‖ ≤ L) :
    TendstoUniformlyOn (levelSum a b φ) (limitSum a b φ) atTop (Metric.ball z₀ r) ∧
    DifferentiableOn ℂ (limitSum a b φ) (Metric.ball z₀ r) ∧
    ∀ z ∈ Metric.ball z₀ r, ‖limitSum a b φ z - φ z 0 0‖ ≤
      4 * L * (sSup ((fun w : ℂ => ‖w‖ + ‖1 - w‖) '' Metric.ball z₀ r)) ^ 2 /
        (1 - ρ * (sSup ((fun w : ℂ => ‖w‖ + ‖1 - w‖) '' Metric.ball z₀ r)) ^ 2) := by
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hρ0 : 0 ≤ ρ := (norm_nonneg (a z₀)).trans ((le_max_left _ _).trans (hρ z₀ hz₀))
  have hzero : (0 : ℂ) ∈ D := hD z₀ hz₀ 0 (fun _ => 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hLx z₀ hz₀ 0 hzero 0 hzero)
  exact levelSums_holomorphic Metric.isOpen_ball hDo hDc ha hb hρ0 hρ1 hsmall hρ
    (fun _ hz => norm_weights_le_disc_sup hz) hD hφ hL0 hLx hLy

end

end BrownianImages
