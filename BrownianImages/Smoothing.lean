/-
`sec:concentration`: the oscillation `d_A`, the gap between the extremes of a non-constant
smoothed profile, together with the analytic facts it rests on.

* `exists_extrema_of_periodic`, `exists_bound_of_continuous_periodic`: a continuous
  function of positive period attains its extremes on one period, and is bounded.
* `smoothOp_integrableOn`, `smoothOp_const`, `smoothOp_sub`: the linearity of `T`, on the
  domination by `M·φ` that makes the integrals converge.
* `kernel_trivial_of_multiplier`, `injective_of_multiplier`,
  `nonconstant_of_multiplier`: `thm:smoothing-injective` reduced to the two multiplier
  facts `eq:fourier-multiplier` and `M_k ≠ 0`.
* `continuous_smoothOp`: the smoothing operator of `eq:periodic-smoothing` preserves
  continuity, by dominated convergence against `M·φ`.
* `exists_measure_closedBall_pos`, `phi_pos`, `G_pos`: `Φ(δ) > 0` for `δ > 0`, hence the
  strict positivity of `G`, which `sec:renewal` uses for the periodic profile.
* `smoothOp_gap`: the oscillation `d_A` is attained and positive, the endpoint
  `audit_lattice_gap`.
-/
import BrownianImages.Kernel
import BrownianImages.Frostman
import BrownianImages.Periodic
import BrownianImages.Periodic
import BrownianImages.Multiplier

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

/-! ### Extrema of a continuous periodic function -/

/-- A continuous function with positive period attains its supremum and its infimum on
one period, and those values bound it on the whole line. -/
theorem exists_extrema_of_periodic {q : ℝ} (hq : 0 < q) {f : ℝ → ℝ}
    (hf : Continuous f) (hper : Function.Periodic f q) :
    ∃ a ∈ Set.Icc (0:ℝ) q, ∃ b ∈ Set.Icc (0:ℝ) q,
      ∀ v, f b ≤ f v ∧ f v ≤ f a := by
  have hne : (Set.Icc (0:ℝ) q).Nonempty := Set.nonempty_Icc.mpr hq.le
  obtain ⟨a, ha, hamax⟩ := isCompact_Icc.exists_isMaxOn hne hf.continuousOn
  obtain ⟨b, hb, hbmin⟩ := isCompact_Icc.exists_isMinOn hne hf.continuousOn
  refine ⟨a, ha, b, hb, fun v => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hq v
  have hyIcc : y ∈ Set.Icc (0:ℝ) q := ⟨hy.1, hy.2.le⟩
  exact ⟨hfy ▸ hbmin hyIcc, hfy ▸ hamax hyIcc⟩

/-! ### Boundedness of a continuous periodic function -/

theorem exists_bound_of_continuous_periodic {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ}
    (hg : Continuous g) (hper : Function.Periodic g p) : ∃ M, ∀ x, |g x| ≤ M := by
  have hb : Bornology.IsBounded (Set.range g) := hper.isBounded_of_continuous hp.ne' hg
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM (g x) ⟨x, rfl⟩⟩

/-! ### Integrability of the smoothing integrand -/

theorem smoothOp_integrableOn (hs0 : 0 < s) (hs1 : s < 1) {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) (v : ℝ) :
    IntegrableOn (fun η : ℝ => kern s η * g (2 * v - Real.log η)) (Set.Ioi 0) := by
  have hlog : ContinuousOn (fun η : ℝ => g (2 * v - Real.log η)) (Set.Ioi 0) :=
    hg.comp_continuousOn (continuousOn_const.sub
      (Real.continuousOn_log.mono (fun η hη => ne_of_gt hη)))
  have hcont : ContinuousOn (fun η : ℝ => kern s η * g (2 * v - Real.log η)) (Set.Ioi 0) :=
    (continuousOn_kern s).mul hlog
  refine Integrable.mono' ((kern_integrableOn hs0 hs1).mul_const M)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
  have hk := kern_pos (s := s) hη
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
  exact mul_le_mul_of_nonneg_left (hM _) hk.le

/-! ### Linearity of the smoothing operator -/

theorem smoothOp_const (a v : ℝ) :
    smoothOp s (fun _ => a) v = (∫ η in Set.Ioi (0:ℝ), kern s η) * a := by
  simp only [smoothOp]
  exact integral_mul_const _ _

/-- The smoothing operator is additive on bounded continuous inputs. -/
theorem smoothOp_sub (hs0 : 0 < s) (hs1 : s < 1) {g₁ g₂ : ℝ → ℝ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) {M₁ M₂ : ℝ}
    (hM₁ : ∀ x, |g₁ x| ≤ M₁) (hM₂ : ∀ x, |g₂ x| ≤ M₂) (v : ℝ) :
    smoothOp s (fun x => g₁ x - g₂ x) v = smoothOp s g₁ v - smoothOp s g₂ v := by
  have h₁ := smoothOp_integrableOn hs0 hs1 hg₁ hM₁ v
  have h₂ := smoothOp_integrableOn hs0 hs1 hg₂ hM₂ v
  simp only [smoothOp]
  rw [← integral_sub h₁ h₂]
  exact setIntegral_congr_fun measurableSet_Ioi fun η _ => by ring

/-! ### The Fourier coefficients of the zero function -/

theorem fourierCoeffP_eq_zero_of_eq_zero {q : ℝ} {f : ℝ → ℝ} (h : ∀ x, f x = 0) (k : ℤ) :
    fourierCoeffP q f k = 0 := by
  simp [fourierCoeffP, h]

/-! ### The reductions of `thm:smoothing-injective` to the multiplier facts -/

-- `hs0`/`hs1` are kept on the reductions so their shape matches the endpoints they serve

/-- `thm:smoothing-injective`, kernel form, from the multiplier facts: a continuous
`p`-periodic `g` with `Tg = 0` vanishes, since each Fourier coefficient of `g` is killed
by a non-vanishing multiplier. -/
theorem kernel_trivial_of_multiplier {s p : ℝ} (_hs0 : 0 < s) (_hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (hmult : ∀ k : ℤ,
      fourierCoeffP (p/2) (smoothOp s g) k = multInt s p k * fourierCoeffP p g k)
    (hne : ∀ k : ℤ, multInt s p k ≠ 0)
    (h : ∀ v, smoothOp s g v = 0) : ∀ x, g x = 0 := by
  refine eq_zero_of_fourierCoeffP_eq_zero hp hg hper fun k => ?_
  have h0 : fourierCoeffP (p/2) (smoothOp s g) k = 0 :=
    fourierCoeffP_eq_zero_of_eq_zero h k
  rw [hmult k] at h0
  exact (mul_eq_zero.mp h0).resolve_left (hne k)

/-- `thm:smoothing-injective` from the multiplier facts: `T` is injective on continuous
`p`-periodic functions. -/
theorem injective_of_multiplier {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    (hmult : ∀ g : ℝ → ℝ, Continuous g → (∃ M, ∀ x, |g x| ≤ M) → Function.Periodic g p →
      ∀ k : ℤ, fourierCoeffP (p/2) (smoothOp s g) k = multInt s p k * fourierCoeffP p g k)
    (hne : ∀ k : ℤ, multInt s p k ≠ 0)
    {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hper₁ : Function.Periodic g₁ p) (hper₂ : Function.Periodic g₂ p)
    (h : ∀ v, smoothOp s g₁ v = smoothOp s g₂ v) : ∀ x, g₁ x = g₂ x := by
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_continuous_periodic hp hg₁ hper₁
  obtain ⟨M₂, hM₂⟩ := exists_bound_of_continuous_periodic hp hg₂ hper₂
  have hdc : Continuous fun x => g₁ x - g₂ x := hg₁.sub hg₂
  have hdper : Function.Periodic (fun x => g₁ x - g₂ x) p := fun x => by
    simp only []; rw [hper₁ x, hper₂ x]
  have hdbdd : ∃ M, ∀ x, |g₁ x - g₂ x| ≤ M :=
    exists_bound_of_continuous_periodic hp hdc hdper
  have hzero : ∀ v, smoothOp s (fun x => g₁ x - g₂ x) v = 0 := fun v => by
    rw [smoothOp_sub hs0 hs1 hg₁ hg₂ hM₁ hM₂ v, h v, sub_self]
  have hkey := kernel_trivial_of_multiplier hs0 hs1 hp hdc hdper
    (hmult _ hdc hdbdd hdper) hne hzero
  exact fun x => sub_eq_zero.mp (hkey x)

/-- `thm:smoothing-injective`, consequence: `T` sends a non-constant continuous
`p`-periodic function to a non-constant one. -/
theorem nonconstant_of_multiplier {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    (hmult : ∀ g : ℝ → ℝ, Continuous g → (∃ M, ∀ x, |g x| ≤ M) → Function.Periodic g p →
      ∀ k : ℤ, fourierCoeffP (p/2) (smoothOp s g) k = multInt s p k * fourierCoeffP p g k)
    (hne : ∀ k : ℤ, multInt s p k ≠ 0)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (hgne : ∃ x y, g x ≠ g y) : ∃ v w, smoothOp s g v ≠ smoothOp s g w := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  obtain ⟨x, y, hxy⟩ := hgne
  have hI : (0:ℝ) < ∫ η in Set.Ioi (0:ℝ), kern s η := integral_kern_pos hs0 hs1
  have hconst : ∀ v, smoothOp s (fun _ => smoothOp s g 0 / (∫ η in Set.Ioi (0:ℝ), kern s η)) v
      = smoothOp s g v := by
    intro v
    rw [smoothOp_const, mul_div_cancel₀ _ hI.ne']
    exact hcon 0 v
  have hkey := injective_of_multiplier hs0 hs1 hp hmult hne continuous_const hg
    (fun _ => rfl) hper hconst
  exact hxy ((hkey x).symm.trans (hkey y))

/-! ### Continuity of the smoothing operator -/

/-- The smoothing operator of `eq:periodic-smoothing` preserves continuity: the
integrand is dominated by `M·φ` with `φ` integrable, so dominated convergence applies. -/
theorem continuous_smoothOp {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {g : ℝ → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) : Continuous (smoothOp s g) := by
  show Continuous fun v => ∫ η in Set.Ioi (0:ℝ), kern s η * g (2 * v - Real.log η)
  refine MeasureTheory.continuous_of_dominated
    (F := fun (v : ℝ) (η : ℝ) => kern s η * g (2 * v - Real.log η))
    (bound := fun η => kern s η * M) (fun v => ?_) (fun v => ?_)
    ((kern_integrableOn hs0 hs1).mul_const M) ?_
  · have hlog : ContinuousOn (fun η : ℝ => g (2 * v - Real.log η)) (Set.Ioi 0) :=
      hg.comp_continuousOn (continuousOn_const.sub
        (Real.continuousOn_log.mono (fun η hη => ne_of_gt hη)))
    exact (((continuousOn_kern s).mul hlog)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with η hη
    have hk := kern_pos (s := s) hη
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left (hM _) hk.le
  · refine Filter.Eventually.of_forall fun η => ?_
    exact continuous_const.mul (hg.comp (by fun_prop))

/-! ### Strict positivity of the pair-distance distribution -/

/-- Some closed ball of any positive radius carries positive mass: the line is covered
by countably many of them. -/
theorem exists_measure_closedBall_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ}
    (hr : 0 < r) : ∃ c : ℝ, 0 < μ (Metric.closedBall c r) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hnull : ∀ n : ℤ, μ (Metric.closedBall ((n : ℝ) * (2 * r)) r) = 0 :=
    fun n => hcon _
  have hcover : (Set.univ : Set ℝ)
      ⊆ ⋃ n : ℤ, Metric.closedBall ((n : ℝ) * (2 * r)) r := by
    intro x _
    have h2r : (0:ℝ) < 2 * r := by linarith
    refine Set.mem_iUnion.mpr ⟨round (x / (2 * r)), ?_⟩
    have habs : |x / (2 * r) - (round (x / (2 * r)) : ℝ)| ≤ 1 / 2 :=
      abs_sub_round (x / (2 * r))
    have hmul : |x - (round (x / (2 * r)) : ℝ) * (2 * r)|
        = |x / (2 * r) - (round (x / (2 * r)) : ℝ)| * (2 * r) := by
      rw [← abs_of_pos h2r, ← abs_mul, abs_of_pos h2r]
      congr 1
      field_simp
    simp only [Metric.mem_closedBall, Real.dist_eq, hmul]
    nlinarith
  have hzero : μ (Set.univ : Set ℝ) = 0 :=
    measure_mono_null hcover (measure_iUnion_null hnull)
  rw [measure_univ] at hzero
  exact one_ne_zero hzero

/-- `Φ(δ) > 0` for every `δ > 0`: this is the strict positivity of `G`, and hence of the
periodic profile, that `sec:renewal` uses. -/
theorem phi_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ) :
    0 < Phi μ δ := by
  obtain ⟨c, hc⟩ := exists_measure_closedBall_pos (μ := μ) (r := δ / 2) (by linarith)
  have hsub : (Metric.closedBall c (δ / 2)) ×ˢ (Metric.closedBall c (δ / 2))
      ⊆ {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Metric.mem_closedBall, Real.dist_eq] at hx hy
    have h1 := abs_le.mp hx
    have h2 := abs_le.mp hy
    simp only [Set.mem_setOf_eq, abs_le]
    constructor <;> linarith
  have hprod : 0 < (μ.prod μ)
      ((Metric.closedBall c (δ / 2)) ×ˢ (Metric.closedBall c (δ / 2))) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hc.ne' hc.ne'
  exact ENNReal.toReal_pos (lt_of_lt_of_le hprod (measure_mono hsub)).ne' (measure_ne_top _ _)

/-- `eq:g-definition`: the normalised profile is strictly positive. -/
theorem G_pos {s : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (w : ℝ) : 0 < G s μ w :=
  mul_pos (Real.exp_pos _) (phi_pos (Real.exp_pos _))

/-! ### The oscillation `d_A` -/

/-- The oscillation `d_A` of `sec:concentration`.  A continuous non-constant smoothed profile attains a strict
maximum and a strict minimum over a period, and the gap between them is positive. -/
theorem smoothOp_gap {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (hne : ∃ v w, smoothOp s g v ≠ smoothOp s g w) :
    ∃ a ∈ Set.Icc (0:ℝ) (p/2), ∃ b ∈ Set.Icc (0:ℝ) (p/2),
      0 < smoothOp s g a - smoothOp s g b ∧
        ∀ v, smoothOp s g b ≤ smoothOp s g v ∧ smoothOp s g v ≤ smoothOp s g a := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_periodic hp hg hper
  have hT : Continuous (smoothOp s g) := continuous_smoothOp hs0 hs1 hg hM
  have hTper : Function.Periodic (smoothOp s g) (p / 2) := smoothOp_periodic hper
  obtain ⟨a, ha, b, hb, hbound⟩ :=
    exists_extrema_of_periodic (by linarith : (0:ℝ) < p / 2) hT hTper
  refine ⟨a, ha, b, hb, ?_, hbound⟩
  obtain ⟨v, w, hvw⟩ := hne
  rcases lt_or_ge (smoothOp s g b) (smoothOp s g a) with h | h
  · linarith
  · exact absurd (by linarith [(hbound v).1, (hbound v).2, (hbound w).1, (hbound w).2]) hvw

end BrownianImages
