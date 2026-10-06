/-
`eq:fixed-dimension-correlation` of `thm:fixed-dimension-profiles`: for the natural measure
`μ_p` of the fixed-dimension system and every `r > 0`,
`S_{μ_p}(r) = 2pq ∑_{j,k≥0} C(j+k, j) p^{2j} q^{2k} 𝔼[1 - exp(-r²/(2 a^j b^k Z_p))]`,
and the series converges uniformly in `r`: the remainder after the terms with `j + k < m` is
at most `(p² + q²)^m`.

The proof unfolds Hutchinson's identity in both coordinates: with
`T(c) = ∫ g_r(c|x - y|) d(μ×μ)` and `g_r(t) = 1 - e^{-r²/(2t)}`, the diagonal blocks give
`p² T(ca) + q² T(cb)` and the two off-diagonal blocks the cross term `2pq 𝔼 g_r(c Z_p)`;
iterating along the antidiagonals of `ℕ²` with Pascal's rule produces the binomial weights,
and `0 ≤ T ≤ 1` bounds the remainder by `∑_{j+k=m} C(m,j) p^{2j} q^{2k} = (p² + q²)^m`.

* `retKernel`, `corrScale`, `crossExp`: the kernel, the scaled functional, the cross term.
* `System.IsNatural.lintegral_prod_eq_double_sum`: Hutchinson's identity on `μ × μ`.
* `corrScale_recursion`: `T(c) = p² T(ca) + q² T(cb) + 2pq 𝔼 g_r(c Z_p)`.
* `sum_antidiagonal_succ_pascal`: the Pascal step on the antidiagonals.
* `fixedSystem_correlation`: `eq:fixed-dimension-correlation`.
-/
import BrownianImages.FixedDimension.Profiles
import BrownianImages.Reduction

namespace BrownianImages

open MeasureTheory Filter Set Finset
open scoped Topology ENNReal

noncomputable section

/-! ### The kernel and the functionals -/

/-- The Gaussian return kernel `g_r(t) = 1 - e^{-r²/(2t)}` of `eq:gaussian-reduction`. -/
def retKernel (r t : ℝ) : ℝ := 1 - Real.exp (-(r ^ 2 / (2 * t)))

theorem retKernel_mem (r : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ retKernel r t ∧ retKernel r t ≤ 1 := by
  unfold retKernel
  have h0 : 0 ≤ r ^ 2 / (2 * t) := by positivity
  have h1 : Real.exp (-(r ^ 2 / (2 * t))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  constructor <;> linarith [Real.exp_pos (-(r ^ 2 / (2 * t)))]

theorem measurable_retKernel (r : ℝ) : Measurable (retKernel r) := by
  unfold retKernel; fun_prop

/-- The scaled correlation functional `T(c) = ∫ g_r(c|x - y|) d(μ × μ)`. -/
def corrScale (μ : Measure ℝ) (r c : ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, retKernel r (c * |q.1 - q.2|) ∂(μ.prod μ)

/-- The cross term `𝔼 g_r(c Z_p)`. -/
def crossExp (s p : ℝ) (μ : Measure ℝ) (r c : ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, retKernel r (c * fixedCross s p q.1 q.2) ∂(μ.prod μ)

/-! ### Hutchinson's identity on the product -/

/-- Hutchinson's identity in both coordinates, read on a lower integral over `μ × μ`. -/
theorem System.IsNatural.lintegral_prod_eq_double_sum {ι : Type*} [Fintype ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ) {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ q, F q ∂(μ.prod μ) = ∑ i, ∑ j, ENNReal.ofReal (S.ratio i ^ s) *
      ENNReal.ofReal (S.ratio j ^ s) * ∫⁻ q, F (S.map i q.1, S.map j q.2) ∂(μ.prod μ) := by
  have := hμ.isProbabilityMeasure
  have hG : ∀ i j : ι, Measurable fun q : ℝ × ℝ => F (S.map i q.1, S.map j q.2) := fun i j =>
    hF.comp (((S.measurable_map i).comp measurable_fst).prodMk
      ((S.measurable_map j).comp measurable_snd))
  rw [lintegral_prod _ hF.aemeasurable]
  rw [hμ.lintegral_eq_sum S hF.lintegral_prod_right']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinner : ∀ x, ∫⁻ y, F (S.map i x, y) ∂μ
      = ∑ j, ENNReal.ofReal (S.ratio j ^ s) * ∫⁻ y, F (S.map i x, S.map j y) ∂μ := fun x =>
    hμ.lintegral_eq_sum S (hF.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  rw [lintegral_finsetSum _ fun j _ => ((hG i j).lintegral_prod_right').const_mul _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_const_mul _ (hG i j).lintegral_prod_right', mul_assoc,
    lintegral_prod _ (hG i j).aemeasurable]

/-! ### The recursion -/

section Fixed

variable {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
  {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
include hs hs1 hp0 hp1 hμ

omit hs1 in
theorem corrScale_eq_toReal (r : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    corrScale μ r c
      = (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * |q.1 - q.2|)) ∂(μ.prod μ)).toReal := by
  have := hμ.isProbabilityMeasure
  unfold corrScale
  have hm : Measurable fun q : ℝ × ℝ => c * |q.1 - q.2| := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q =>
      (retKernel_mem r (by positivity)).1)
    ((measurable_retKernel r).comp hm).aestronglyMeasurable]

theorem crossExp_eq_toReal (r : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    crossExp s p μ r c
      = (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2))
          ∂(μ.prod μ)).toReal := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  unfold crossExp
  have hm : Measurable fun q : ℝ × ℝ => c * fixedCross s p q.1 q.2 :=
    (continuous_const.mul (continuous_fixedCross s p)).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (hbox.mono fun q hq =>
      (retKernel_mem r (mul_nonneg hc (fixedCross_pos hs hs1 hp0 hp1 hq.1 hq.2).le)).1)
    ((measurable_retKernel r).comp hm).aestronglyMeasurable]

omit hs hs1 hp0 hp1 hμ in
theorem lintegral_retKernel_le_one {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    {u : ℝ × ℝ → ℝ} (hu : ∀ q, 0 ≤ u q) (r : ℝ) :
    ∫⁻ q, ENNReal.ofReal (retKernel r (u q)) ∂ν ≤ 1 := by
  calc ∫⁻ q, ENNReal.ofReal (retKernel r (u q)) ∂ν ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ν :=
        lintegral_mono fun q => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (retKernel_mem r (hu q)).2
    _ = 1 := by rw [lintegral_const, measure_univ, mul_one]

/-- **The recursion** `T(c) = p² T(ca) + q² T(cb) + 2pq 𝔼 g_r(c Z_p)`. -/
theorem corrScale_recursion (r : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    corrScale μ r c = p ^ 2 * corrScale μ r (c * fixedA s p)
      + (1 - p) ^ 2 * corrScale μ r (c * fixedB s p) + 2 * (p * (1 - p)) * crossExp s p μ r c := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have hq0 : 0 ≤ 1 - p := by linarith
  set F : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (retKernel r (c * |q.1 - q.2|)) with hF
  have hm : Measurable fun q : ℝ × ℝ => c * |q.1 - q.2| := by fun_prop
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp ((measurable_retKernel r).comp hm)
  have hdouble := hμ.lintegral_prod_eq_double_sum _ hFm
  simp only [Fin.sum_univ_two, fixedSystem_ratio_zero, fixedSystem_ratio_one,
    fixedA_rpow hs hp0, fixedB_rpow hs hp1, fixedSystem_map_zero, fixedSystem_map_one] at hdouble
  -- the four blocks
  have h00 : ∫⁻ q, F (fixedA s p * q.1, fixedA s p * q.2) ∂(μ.prod μ)
      = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedA s p * |q.1 - q.2|)) ∂(μ.prod μ) := by
    refine lintegral_congr fun q => ?_
    simp only [hF]
    rw [← mul_sub, abs_mul, abs_of_pos ha0, mul_assoc]
  have h11 : ∫⁻ q, F (fixedB s p * q.1 + (1 - fixedB s p), fixedB s p * q.2 + (1 - fixedB s p))
      ∂(μ.prod μ)
      = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedB s p * |q.1 - q.2|)) ∂(μ.prod μ) := by
    refine lintegral_congr fun q => ?_
    simp only [hF]
    rw [show fixedB s p * q.1 + (1 - fixedB s p) - (fixedB s p * q.2 + (1 - fixedB s p))
      = fixedB s p * (q.1 - q.2) by ring, abs_mul, abs_of_pos hb0, mul_assoc]
  have h01 : ∫⁻ q, F (fixedA s p * q.1, fixedB s p * q.2 + (1 - fixedB s p)) ∂(μ.prod μ)
      = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)) ∂(μ.prod μ) := by
    refine lintegral_congr_ae (hbox.mono fun q hq => ?_)
    simp only [hF]
    have hZ := (fixedCross_mem hs hp0 hp1 hq.1 hq.2).1
    have hg := crossGap_pos hs hs1 hp0 hp1
    unfold crossGap at hg
    rw [show |fixedA s p * q.1 - (fixedB s p * q.2 + (1 - fixedB s p))| = fixedCross s p q.1 q.2 by
      rw [abs_sub_comm, abs_of_nonneg (by unfold fixedCross at hZ; linarith)]
      unfold fixedCross; ring]
  have h10 : ∫⁻ q, F (fixedB s p * q.1 + (1 - fixedB s p), fixedA s p * q.2) ∂(μ.prod μ)
      = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)) ∂(μ.prod μ) := by
    have hswap : ∫⁻ q, F (fixedB s p * q.1 + (1 - fixedB s p), fixedA s p * q.2) ∂(μ.prod μ)
        = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.2 q.1)) ∂(μ.prod μ) := by
      refine lintegral_congr_ae (hbox.mono fun q hq => ?_)
      simp only [hF]
      have hZ := (fixedCross_mem hs hp0 hp1 hq.2 hq.1).1
      have hg := crossGap_pos hs hs1 hp0 hp1
      unfold crossGap at hg
      rw [show |fixedB s p * q.1 + (1 - fixedB s p) - fixedA s p * q.2| = fixedCross s p q.2 q.1 by
        rw [abs_of_nonneg (by unfold fixedCross at hZ; linarith)]
        unfold fixedCross; ring]
    rw [hswap]
    exact lintegral_prod_swap (μ := μ) (ν := μ)
      (fun q : ℝ × ℝ => ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)))
  rw [h00, h11, h01, h10] at hdouble
  -- finiteness of the blocks
  have hle : ∀ u : ℝ × ℝ → ℝ, (∀ q, 0 ≤ u q) →
      ∫⁻ q, ENNReal.ofReal (retKernel r (u q)) ∂(μ.prod μ) ≠ ⊤ := fun u hu =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (lintegral_retKernel_le_one hu r)
  have hA := hle (fun q => c * fixedA s p * |q.1 - q.2|) fun q => by positivity
  have hB := hle (fun q => c * fixedB s p * |q.1 - q.2|) fun q => by positivity
  have hX : ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)) ∂(μ.prod μ)
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)) ∂(μ.prod μ)
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(μ.prod μ) := by
          refine lintegral_mono_ae (hbox.mono fun q hq => ?_)
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (retKernel_mem r
            (mul_nonneg hc (fixedCross_pos hs hs1 hp0 hp1 hq.1 hq.2).le)).2
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  -- back to real integrals
  have f00 : ENNReal.ofReal p * ENNReal.ofReal p *
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedA s p * |q.1 - q.2|)) ∂(μ.prod μ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hA
  have f01 : ENNReal.ofReal p * ENNReal.ofReal (1 - p) *
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)) ∂(μ.prod μ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hX
  have f10 : ENNReal.ofReal (1 - p) * ENNReal.ofReal p *
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedCross s p q.1 q.2)) ∂(μ.prod μ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hX
  have f11 : ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 - p) *
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (retKernel r (c * fixedB s p * |q.1 - q.2|)) ∂(μ.prod μ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hB
  rw [corrScale_eq_toReal hs hp0 hp1 hμ r hc,
    corrScale_eq_toReal hs hp0 hp1 hμ r (mul_nonneg hc ha0.le),
    corrScale_eq_toReal hs hp0 hp1 hμ r (mul_nonneg hc hb0.le),
    crossExp_eq_toReal hs hs1 hp0 hp1 hμ r hc, hdouble,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨f00, f01⟩) (ENNReal.add_ne_top.2 ⟨f10, f11⟩),
    ENNReal.toReal_add f00 f01, ENNReal.toReal_add f10 f11]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0]
  ring

omit hs1 in
theorem corrScale_mem (r : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ corrScale μ r c ∧ corrScale μ r c ≤ 1 := by
  have := hμ.isProbabilityMeasure
  constructor
  · exact integral_nonneg fun q => (retKernel_mem r (by positivity)).1
  · have h := norm_integral_le_of_norm_le_const (μ := μ.prod μ)
      (f := fun q : ℝ × ℝ => retKernel r (c * |q.1 - q.2|)) (C := 1)
      (Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (retKernel_mem r (by positivity)).1]
        exact (retKernel_mem r (by positivity)).2)
    rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h

theorem crossExp_nonneg (r : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ crossExp s p μ r c := by
  have := hμ.isProbabilityMeasure
  have hbox := ae_prod_mem_Icc hμ.support_Icc
  exact integral_nonneg_of_ae (hbox.mono fun q hq =>
    (retKernel_mem r (mul_nonneg hc (fixedCross_pos hs hs1 hp0 hp1 hq.1 hq.2).le)).1)

end Fixed

/-! ### The binomial weights and the Pascal step -/

/-- The weight `C(j+k, j) p^{2j} q^{2k}`. -/
def binWeight (p : ℝ) (jk : ℕ × ℕ) : ℝ :=
  ((jk.1 + jk.2).choose jk.1 : ℝ) * p ^ (2 * jk.1) * (1 - p) ^ (2 * jk.2)

/-- Pascal's rule for the weights. -/
theorem binWeight_pascal (p : ℝ) (j k : ℕ) :
    binWeight p (j + 1, k + 1) = p ^ 2 * binWeight p (j, k + 1) + (1 - p) ^ 2 * binWeight p (j + 1, k) := by
  unfold binWeight
  simp only
  have h : (j + 1 + (k + 1)).choose (j + 1) = (j + (k + 1)).choose j + (j + 1 + k).choose (j + 1) := by
    rw [show j + 1 + (k + 1) = (j + k + 1) + 1 by ring, Nat.choose_succ_succ,
      show j + (k + 1) = j + k + 1 by ring, show j + 1 + k = j + k + 1 by ring]
  rw [h]
  push_cast
  ring

theorem binWeight_left (p : ℝ) (j : ℕ) : binWeight p (j + 1, 0) = p ^ 2 * binWeight p (j, 0) := by
  unfold binWeight
  simp only [add_zero, Nat.choose_self, Nat.cast_one]
  ring

theorem binWeight_right (p : ℝ) (k : ℕ) :
    binWeight p (0, k + 1) = (1 - p) ^ 2 * binWeight p (0, k) := by
  unfold binWeight
  simp only [zero_add, Nat.choose_zero_right, Nat.cast_one]
  ring

/-- **The Pascal step on the antidiagonals**: for every `u`,
`∑_{j+k=m+1} W(j,k) u(j,k) = p² ∑_{j+k=m} W(j,k) u(j+1,k) + q² ∑_{j+k=m} W(j,k) u(j,k+1)`. -/
theorem sum_antidiagonal_succ_pascal (p : ℝ) (u : ℕ × ℕ → ℝ) (m : ℕ) :
    ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal (m + 1), binWeight p jk * u jk
      = p ^ 2 * ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m, binWeight p jk * u (jk.1 + 1, jk.2)
        + (1 - p) ^ 2 * ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m, binWeight p jk * u (jk.1, jk.2 + 1) := by
  -- the two halves as sums over the antidiagonal of `m + 1`
  set f : ℕ × ℕ → ℝ := fun jk => if jk.1 = 0 then 0 else p ^ 2 * binWeight p (jk.1 - 1, jk.2) * u jk
    with hf
  set g : ℕ × ℕ → ℝ := fun jk => if jk.2 = 0 then 0 else (1 - p) ^ 2 * binWeight p (jk.1, jk.2 - 1) * u jk
    with hg
  have hfsum : ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal (m + 1), f jk
      = p ^ 2 * ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m, binWeight p jk * u (jk.1 + 1, jk.2) := by
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.mul_sum]
    simp only [hf, ite_true, zero_add, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun jk _ => ?_
    ring
  have hgsum : ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal (m + 1), g jk
      = (1 - p) ^ 2 * ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m, binWeight p jk * u (jk.1, jk.2 + 1) := by
    rw [Finset.Nat.sum_antidiagonal_succ', Finset.mul_sum]
    simp only [hg, ite_true, zero_add, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun jk _ => ?_
    ring
  rw [← hfsum, ← hgsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun jk hjk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hjk
  obtain ⟨j, k⟩ := jk
  simp only [hf, hg]
  rcases j with _ | j <;> rcases k with _ | k
  · omega
  · simp only [ite_true, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, zero_add]
    rw [binWeight_right]
  · simp only [ite_true, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, add_zero]
    rw [binWeight_left]
  · simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [binWeight_pascal]; ring

/-- The weights of one antidiagonal sum to `(p² + q²)^m`. -/
theorem sum_binWeight_antidiagonal (p : ℝ) (m : ℕ) :
    ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m, binWeight p jk = (p ^ 2 + (1 - p) ^ 2) ^ m := by
  rw [add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j k => binWeight p (j, k))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  unfold binWeight
  simp only
  rw [Nat.add_sub_cancel' hj', ← pow_mul, ← pow_mul]
  ring

/-! ### `eq:fixed-dimension-correlation` -/

/-- The term of `eq:fixed-dimension-correlation` at `(j, k)`. -/
def corrTerm (s p : ℝ) (μ : Measure ℝ) (r : ℝ) (jk : ℕ × ℕ) : ℝ :=
  2 * (p * (1 - p)) * binWeight p jk * crossExp s p μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2)

/-- The triangle `{j + k < m}`. -/
def triangle (m : ℕ) : Finset (ℕ × ℕ) := (Finset.range m).biUnion Finset.HasAntidiagonal.antidiagonal

theorem sum_triangle {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) (m : ℕ) :
    ∑ jk ∈ triangle m, f jk = ∑ n ∈ Finset.range m, ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal n, f jk := by
  unfold triangle
  refine Finset.sum_biUnion ?_
  intro n _ n' _ hnn'
  rw [Function.onFun, Finset.disjoint_left]
  intro jk h1 h2
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
  exact hnn' (h1.symm.trans h2)

theorem triangle_mono {m m' : ℕ} (h : m ≤ m') : triangle m ⊆ triangle m' :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono h)

theorem subset_triangle (u : Finset (ℕ × ℕ)) : u ⊆ triangle (u.sup (fun jk => jk.1 + jk.2) + 1) := by
  intro jk hjk
  unfold triangle
  rw [Finset.mem_biUnion]
  refine ⟨jk.1 + jk.2, Finset.mem_range.2
    (Nat.lt_succ_of_le (Finset.le_sup (f := fun jk : ℕ × ℕ => jk.1 + jk.2) hjk)), ?_⟩
  rw [Finset.HasAntidiagonal.mem_antidiagonal]

theorem sq_add_sq_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p ^ 2 + (1 - p) ^ 2 < 1 := by
  nlinarith

section Series

variable {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
  {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
include hs hs1 hp0 hp1 hμ

/-- The unfolding: `T(1) = ∑_{j+k<m} term + ∑_{j+k=m} W(j,k) T(a^j b^k)`. -/
theorem corrScale_eq_partial (r : ℝ) (m : ℕ) :
    corrScale μ r 1 = (∑ jk ∈ triangle m, corrTerm s p μ r jk)
      + ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m,
          binWeight p jk * corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2) := by
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  induction m with
  | zero =>
    simp [triangle, binWeight]
  | succ m ih =>
    rw [ih, sum_triangle (corrTerm s p μ r) (m + 1), Finset.sum_range_succ, ← sum_triangle,
      add_assoc]
    congr 1
    -- the recursion on every point of the antidiagonal
    have hrec : ∀ jk : ℕ × ℕ, binWeight p jk * corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2)
        = corrTerm s p μ r jk
          + (p ^ 2 * (binWeight p jk * corrScale μ r (fixedA s p ^ (jk.1 + 1) * fixedB s p ^ jk.2))
            + (1 - p) ^ 2 * (binWeight p jk *
              corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ (jk.2 + 1)))) := by
      intro jk
      rw [corrScale_recursion hs hs1 hp0 hp1 hμ r (by positivity)]
      unfold corrTerm
      rw [show fixedA s p ^ jk.1 * fixedB s p ^ jk.2 * fixedA s p
          = fixedA s p ^ (jk.1 + 1) * fixedB s p ^ jk.2 by ring,
        show fixedA s p ^ jk.1 * fixedB s p ^ jk.2 * fixedB s p
          = fixedA s p ^ jk.1 * fixedB s p ^ (jk.2 + 1) by ring]
      ring
    rw [sum_antidiagonal_succ_pascal p
      (fun jk => corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2)) m]
    have hRm : ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m,
        binWeight p jk * corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2)
        = ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal m, (corrTerm s p μ r jk
          + (p ^ 2 * (binWeight p jk * corrScale μ r (fixedA s p ^ (jk.1 + 1) * fixedB s p ^ jk.2))
            + (1 - p) ^ 2 * (binWeight p jk *
              corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ (jk.2 + 1))))) :=
      Finset.sum_congr rfl fun jk _ => hrec jk
    rw [hRm, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The remainder is at most `(p² + q²)^m`, uniformly in `r`. -/
theorem abs_corrScale_sub_triangle_le (r : ℝ) (m : ℕ) :
    |corrScale μ r 1 - ∑ jk ∈ triangle m, corrTerm s p μ r jk| ≤ (p ^ 2 + (1 - p) ^ 2) ^ m := by
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  rw [corrScale_eq_partial hs hs1 hp0 hp1 hμ r m, add_sub_cancel_left, ← sum_binWeight_antidiagonal]
  have hW : ∀ jk : ℕ × ℕ, 0 ≤ binWeight p jk := fun jk => by
    unfold binWeight
    have : 0 ≤ 1 - p := by linarith
    positivity
  rw [abs_of_nonneg (Finset.sum_nonneg fun jk _ => mul_nonneg (hW jk)
    (corrScale_mem hs hp0 hp1 hμ r (by positivity)).1)]
  refine Finset.sum_le_sum fun jk _ => ?_
  calc binWeight p jk * corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2)
      ≤ binWeight p jk * 1 :=
        mul_le_mul_of_nonneg_left (corrScale_mem hs hp0 hp1 hμ r (by positivity)).2 (hW jk)
    _ = binWeight p jk := mul_one _

theorem corrTerm_nonneg (r : ℝ) (jk : ℕ × ℕ) : 0 ≤ corrTerm s p μ r jk := by
  have ha0 := fixedA_pos (s := s) hp0
  have hb0 := fixedB_pos (s := s) hp1
  have hq : 0 ≤ 1 - p := by linarith
  unfold corrTerm binWeight
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (crossExp_nonneg hs hs1 hp0 hp1 hμ r (by positivity))

/-- **`eq:fixed-dimension-correlation`.**  The series converges to `T(1)` and its remainder
after the terms with `j + k < m` is at most `(p² + q²)^m`, uniformly in `r`. -/
theorem fixedSystem_correlation (r : ℝ) :
    HasSum (corrTerm s p μ r) (corrScale μ r 1) ∧
      ∀ m : ℕ, |corrScale μ r 1 - ∑ jk ∈ triangle m, corrTerm s p μ r jk|
        ≤ (p ^ 2 + (1 - p) ^ 2) ^ m := by
  refine ⟨?_, abs_corrScale_sub_triangle_le hs hs1 hp0 hp1 hμ r⟩
  have hnn := corrTerm_nonneg hs hs1 hp0 hp1 hμ r
  -- the triangle sums converge to `T(1)`
  have hlim : Tendsto (fun m => ∑ jk ∈ triangle m, corrTerm s p μ r jk) atTop
      (𝓝 (corrScale μ r 1)) := by
    have hρ0 : 0 ≤ p ^ 2 + (1 - p) ^ 2 := by positivity
    have hρ1 := sq_add_sq_lt_one hp0 hp1
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have := squeeze_zero_norm (fun m => by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact abs_corrScale_sub_triangle_le hs hs1 hp0 hp1 hμ r m) hg
    exact tendsto_sub_nhds_zero_iff.1 this
  -- summability from the bounded triangle sums
  have hsum : Summable (corrTerm s p μ r) := by
    refine summable_of_sum_le (c := corrScale μ r 1) hnn fun u => ?_
    calc ∑ jk ∈ u, corrTerm s p μ r jk
        ≤ ∑ jk ∈ triangle (u.sup (fun jk => jk.1 + jk.2) + 1), corrTerm s p μ r jk :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_triangle u) fun jk _ _ => hnn jk
      _ ≤ corrScale μ r 1 := by
          have h := corrScale_eq_partial hs hs1 hp0 hp1 hμ r (u.sup (fun jk => jk.1 + jk.2) + 1)
          have hW : ∀ jk : ℕ × ℕ, 0 ≤ binWeight p jk := fun jk => by
            unfold binWeight
            have : 0 ≤ 1 - p := by linarith
            positivity
          have ha0 := fixedA_pos (s := s) hp0
          have hb0 := fixedB_pos (s := s) hp1
          have hrem : 0 ≤ ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal (u.sup (fun jk => jk.1 + jk.2) + 1),
              binWeight p jk * corrScale μ r (fixedA s p ^ jk.1 * fixedB s p ^ jk.2) :=
            Finset.sum_nonneg fun jk _ => mul_nonneg (hW jk)
              (corrScale_mem hs hp0 hp1 hμ r (by positivity)).1
          linarith
  -- the sum is the limit along the triangles
  have htri : Tendsto triangle atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun u => ⟨u.sup (fun jk => jk.1 + jk.2) + 1, fun m hm => ?_⟩
    exact (subset_triangle u).trans (triangle_mono hm)
  have h1 : Tendsto (fun m => ∑ jk ∈ triangle m, corrTerm s p μ r jk) atTop
      (𝓝 (∑' jk, corrTerm s p μ r jk)) := hsum.hasSum.comp htri
  have heq : ∑' jk, corrTerm s p μ r jk = corrScale μ r 1 := tendsto_nhds_unique h1 hlim
  exact heq ▸ hsum.hasSum

end Series

end

end BrownianImages
