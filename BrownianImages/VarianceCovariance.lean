/-
`sec:variance` of `BrownianImagesComplete.tex`: the variance expansion that opens the
proof of `thm:variance`, `eq:variance`.

`C_r(W_*μ)` is the `μ × μ`-mass of the time pairs whose Brownian images are within `r`,
so it is the mass of a section of one measurable set of `(ℝ × ℝ) × Ω`.  Squaring a
section mass is taking the mass of a product section, so the second moment is the mass of
a section of one measurable set of `((ℝ × ℝ) × (ℝ × ℝ)) × Ω`, and Tonelli exchanges the
sample point with the four times in one step each: `𝔼 C_r²` is the integral of
`P(A ∩ A')` over the product of the two pair measures, and `(𝔼 C_r)²` the integral of
`P(A) P(A')`.  Off the overlap set the two increments are independent and the two
integrands agree, so the difference is carried by the overlap set alone, where the
second integrand is dropped and the first is the joint return probability.

The interchange needs the process measurable in time and chance together, which
`IsPlanarBrownian` does not give; `Reduction.exists_modification` supplies the version,
and the null set it exposes is where the modification is traded back for `W`.

* `VarianceCovariance.pairSet`, `VarianceCovariance.quadSet`: the return event of one
  and of two time pairs, as measurable sets of the product.
* `VarianceCovariance.quadEquiv`: the identification of a pair of time pairs with a
  quadruple of times, carrying `(μ × μ) × (μ × μ)` to `μ⁴`.
* `VarianceCovariance.disjoint_of_min_max_le`: the order argument turning a vanishing
  overlap of two non-degenerate intervals into their separation.
* `VarianceCovariance.measure_inter_eq_mul_of_overlap_nonpos`: off the overlap set the
  two return events are independent, the degenerate time pairs included.
* `variance_le_overlap_lintegral`: `eq:variance`, the variance expansion itself.
* `variance_four_point`, `variance_bundled`: `thm:variance`, unconditionally.
-/
import BrownianImages.Endpoints

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace VarianceCovariance

/-! ### The return events as sets of the product -/

/-- The return event of one time pair, as a subset of `(ℝ × ℝ) × Ω`: the pairs of times
and sample points whose two images are within `r`.  The times are read through
`Real.toNNReal`, exactly as `occupation` reads them. -/
def pairSet (V : ℝ≥0 → Ω → Plane) (r : ℝ) : Set ((ℝ × ℝ) × Ω) :=
  {q | dist (V q.1.1.toNNReal q.2) (V q.1.2.toNNReal q.2) < r}

/-- The return event of two time pairs at once, as a subset of
`((ℝ × ℝ) × (ℝ × ℝ)) × Ω`.  Its sections in the sample point are the squares of the
sections of `pairSet`, which is what turns the second moment into a mass. -/
def quadSet (V : ℝ≥0 → Ω → Plane) (r : ℝ) : Set (((ℝ × ℝ) × (ℝ × ℝ)) × Ω) :=
  {q | dist (V q.1.1.1.toNNReal q.2) (V q.1.1.2.toNNReal q.2) < r ∧
    dist (V q.1.2.1.toNNReal q.2) (V q.1.2.2.toNNReal q.2) < r}

/-- `pairSet` is measurable, by joint measurability of the process. -/
theorem measurableSet_pairSet {V : ℝ≥0 → Ω → Plane} (hV : Measurable (Function.uncurry V))
    (r : ℝ) : MeasurableSet (pairSet V r) := by
  have h1 : Measurable fun q : (ℝ × ℝ) × Ω => V q.1.1.toNNReal q.2 :=
    hV.comp ((continuous_real_toNNReal.measurable.comp
      (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have h2 : Measurable fun q : (ℝ × ℝ) × Ω => V q.1.2.toNNReal q.2 :=
    hV.comp ((continuous_real_toNNReal.measurable.comp
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  exact measurableSet_lt (h1.dist h2) measurable_const

/-- `quadSet` is measurable, by joint measurability of the process. -/
theorem measurableSet_quadSet {V : ℝ≥0 → Ω → Plane} (hV : Measurable (Function.uncurry V))
    (r : ℝ) : MeasurableSet (quadSet V r) := by
  have h1 : Measurable fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × Ω => V q.1.1.1.toNNReal q.2 :=
    hV.comp ((continuous_real_toNNReal.measurable.comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk measurable_snd)
  have h2 : Measurable fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × Ω => V q.1.1.2.toNNReal q.2 :=
    hV.comp ((continuous_real_toNNReal.measurable.comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk measurable_snd)
  have h3 : Measurable fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × Ω => V q.1.2.1.toNNReal q.2 :=
    hV.comp ((continuous_real_toNNReal.measurable.comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  have h4 : Measurable fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × Ω => V q.1.2.2.toNNReal q.2 :=
    hV.comp ((continuous_real_toNNReal.measurable.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  exact (measurableSet_lt (h1.dist h2) measurable_const).inter
    (measurableSet_lt (h3.dist h4) measurable_const)

omit [MeasurableSpace Ω] in
/-- The section of `quadSet` at a sample point is the square of the section of
`pairSet`.  This is the whole of the second-moment computation. -/
theorem quadSet_section (V : ℝ≥0 → Ω → Plane) (r : ℝ) (ω : Ω) :
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q, ω)) ⁻¹' quadSet V r
      = ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r) ×ˢ
        ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r) := rfl

/-! ### The quadruple of times as a pair of time pairs -/

/-- The identification of a pair of time pairs with a quadruple of times.  It carries
`(μ × μ) × (μ × μ)` to `μ⁴`, which is what puts the two Fubini interchanges and the
statement of `eq:variance` on the same measure. -/
def quadEquiv : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ᵐ (ℝ × ℝ × ℝ × ℝ) := MeasurableEquiv.prodAssoc

/-- `quadEquiv` reads off the four times in order. -/
theorem quadEquiv_apply (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    quadEquiv q = (q.1.1, q.1.2, q.2.1, q.2.2) := rfl

/-- `quadEquiv` carries `(μ × μ) × (μ × μ)` to `μ⁴`. -/
theorem map_quadEquiv (μ : Measure ℝ) [SFinite μ] :
    Measure.map quadEquiv ((μ.prod μ).prod (μ.prod μ)) = μ.prod (μ.prod (μ.prod μ)) :=
  Measure.prodAssoc_prod

/-! ### The two Fubini interchanges -/

/-- The second moment of the empirical correlation integral, as a mass over the four
times.  The square of a section mass is the mass of the product section, and Tonelli
then exchanges the sample point with the four times. -/
theorem integral_sq_eq {P : Measure Ω} [IsProbabilityMeasure P] {V : ℝ≥0 → Ω → Plane}
    (hV : Measurable (Function.uncurry V)) {μ : Measure ℝ} [IsProbabilityMeasure μ] (r : ℝ) :
    ∫ ω, ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal ^ 2 ∂P
      = (∫⁻ q, P (Prod.mk q ⁻¹' quadSet V r) ∂((μ.prod μ).prod (μ.prod μ))).toReal := by
  have hU : MeasurableSet (quadSet V r) := measurableSet_quadSet hV r
  have hpt : ∀ ω : Ω, ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal ^ 2
      = (((μ.prod μ).prod (μ.prod μ))
          ((fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q, ω)) ⁻¹' quadSet V r)).toReal := by
    intro ω
    rw [quadSet_section, Measure.prod_prod, ENNReal.toReal_mul, sq]
  calc ∫ ω, ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal ^ 2 ∂P
      = ∫ ω, (((μ.prod μ).prod (μ.prod μ))
          ((fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q, ω)) ⁻¹' quadSet V r)).toReal ∂P :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫⁻ ω, ((μ.prod μ).prod (μ.prod μ))
          ((fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q, ω)) ⁻¹' quadSet V r) ∂P).toReal :=
        integral_toReal (measurable_measure_prodMk_right hU).aemeasurable
          (Eventually.of_forall fun ω => measure_lt_top _ _)
    _ = (∫⁻ q, P (Prod.mk q ⁻¹' quadSet V r) ∂((μ.prod μ).prod (μ.prod μ))).toReal := by
        rw [← Measure.prod_apply_symm hU, Measure.prod_apply hU]

/-- The first moment of the empirical correlation integral, as a mass over the two
times: the Fubini interchange of `thm:gaussian-reduction`, before the return probability
is evaluated. -/
theorem integral_eq {P : Measure Ω} [IsProbabilityMeasure P] {V : ℝ≥0 → Ω → Plane}
    (hV : Measurable (Function.uncurry V)) {μ : Measure ℝ} [IsProbabilityMeasure μ] (r : ℝ) :
    ∫ ω, ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal ∂P
      = (∫⁻ p, P (Prod.mk p ⁻¹' pairSet V r) ∂(μ.prod μ)).toReal := by
  have hT : MeasurableSet (pairSet V r) := measurableSet_pairSet hV r
  rw [integral_toReal (measurable_measure_prodMk_right hT).aemeasurable
    (Eventually.of_forall fun ω => measure_lt_top _ _), ← Measure.prod_apply_symm hT,
    Measure.prod_apply hT]

/-- The square of the first moment, as the same mass over the four times: a product of
two integrals is the integral of the product over the product measure. -/
theorem sq_lintegral_eq {P : Measure Ω} [IsProbabilityMeasure P] {V : ℝ≥0 → Ω → Plane}
    (hV : Measurable (Function.uncurry V)) {μ : Measure ℝ} [IsProbabilityMeasure μ] (r : ℝ) :
    (∫⁻ p, P (Prod.mk p ⁻¹' pairSet V r) ∂(μ.prod μ)).toReal ^ 2
      = (∫⁻ q, P (Prod.mk q.1 ⁻¹' pairSet V r) * P (Prod.mk q.2 ⁻¹' pairSet V r)
          ∂((μ.prod μ).prod (μ.prod μ))).toReal := by
  have hT : MeasurableSet (pairSet V r) := measurableSet_pairSet hV r
  have hF : Measurable fun p : ℝ × ℝ => P (Prod.mk p ⁻¹' pairSet V r) :=
    measurable_measure_prodMk_left hT
  rw [lintegral_prod_mul hF.aemeasurable hF.aemeasurable, ENNReal.toReal_mul, sq]

/-! ### The covariance vanishes off the overlap set -/

/-- The order argument behind `eq:variance`: two intervals whose overlap length vanishes
are separated, as soon as neither of them is a point.  This is the hypothesis of
`disjoint_increments_indep`. -/
theorem disjoint_of_min_max_le {α : Type*} [LinearOrder α] {m₁ M₁ m₂ M₂ : α}
    (h : min M₁ M₂ ≤ max m₁ m₂) (h₁ : m₁ < M₁) (h₂ : m₂ < M₂) : M₁ ≤ m₂ ∨ M₂ ≤ m₁ := by
  rcases le_total m₁ m₂ with hm | hm
  · left
    rw [max_eq_right hm] at h
    rcases le_total M₁ M₂ with hM | hM
    · rwa [min_eq_left hM] at h
    · rw [min_eq_right hM] at h
      exact absurd h (not_le.mpr h₂)
  · right
    rw [max_eq_left hm] at h
    rcases le_total M₂ M₁ with hM | hM
    · rwa [min_eq_right hM] at h
    · rw [min_eq_left hM] at h
      exact absurd h (not_le.mpr h₁)

/-- A vanishing overlap of the two real time intervals is a vanishing overlap of the
intervals the process actually reads, since `Real.toNNReal` is monotone. -/
theorem min_max_toNNReal_le {a b c d : ℝ} (h : ¬ 0 < overlap a b c d) :
    min (max a.toNNReal b.toNNReal) (max c.toNNReal d.toNNReal)
      ≤ max (min a.toNNReal b.toNNReal) (min c.toNNReal d.toNNReal) := by
  have hov : overlap a b c d ≤ 0 := not_lt.mp h
  have hle : min (max a b) (max c d) ≤ max (min a b) (min c d) := by
    have h0 : min (max a b) (max c d) - max (min a b) (min c d)
        ≤ max 0 (min (max a b) (max c d) - max (min a b) (min c d)) := le_max_right _ _
    have := h0.trans hov
    linarith
  have hmono := Real.toNNReal_mono hle
  simpa only [Real.toNNReal_monotone.map_min, Real.toNNReal_monotone.map_max] using hmono

/-- `eq:variance`, the vanishing of the covariance off the overlap set.  The two return
events are independent there: either a time pair reads as a single time, and its return
event is everything, or both intervals are non-degenerate and separated, and
`thm:gaussian-four-point` applies. -/
theorem measure_inter_eq_mul_of_overlap_nonpos {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {r : ℝ} (hr : 0 < r) {a b c d : ℝ}
    (h : ¬ 0 < overlap a b c d) :
    P ({ω | dist (W a.toNNReal ω) (W b.toNNReal ω) < r} ∩
        {ω | dist (W c.toNNReal ω) (W d.toNNReal ω) < r})
      = P {ω | dist (W a.toNNReal ω) (W b.toNNReal ω) < r} *
        P {ω | dist (W c.toNNReal ω) (W d.toNNReal ω) < r} := by
  by_cases hab : a.toNNReal = b.toNNReal
  · have huniv : {ω | dist (W a.toNNReal ω) (W b.toNNReal ω) < r} = Set.univ := by
      ext ω
      simp [hab, hr]
    rw [huniv, Set.univ_inter, measure_univ, one_mul]
  by_cases hcd : c.toNNReal = d.toNNReal
  · have huniv : {ω | dist (W c.toNNReal ω) (W d.toNNReal ω) < r} = Set.univ := by
      ext ω
      simp [hcd, hr]
    rw [huniv, Set.inter_univ, measure_univ, mul_one]
  have hdisj : max a.toNNReal b.toNNReal ≤ min c.toNNReal d.toNNReal ∨
      max c.toNNReal d.toNNReal ≤ min a.toNNReal b.toNNReal :=
    disjoint_of_min_max_le (min_max_toNNReal_le h) (min_lt_max.mpr hab) (min_lt_max.mpr hcd)
  have hindep := disjoint_increments_indep hW (t := a.toNNReal) (u := b.toNNReal)
    (t' := c.toNNReal) (u' := d.toNNReal) hdisj
  have hA : {ω | dist (W a.toNNReal ω) (W b.toNNReal ω) < r}
      = (fun ω => W b.toNNReal ω - W a.toNNReal ω) ⁻¹' Metric.ball (0 : Plane) r := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_ball_zero_iff, ← dist_eq_norm]
    exact ⟨fun hx => by rwa [dist_comm], fun hx => by rwa [dist_comm]⟩
  have hB : {ω | dist (W c.toNNReal ω) (W d.toNNReal ω) < r}
      = (fun ω => W d.toNNReal ω - W c.toNNReal ω) ⁻¹' Metric.ball (0 : Plane) r := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_ball_zero_iff, ← dist_eq_norm]
    exact ⟨fun hx => by rwa [dist_comm], fun hx => by rwa [dist_comm]⟩
  rw [hA, hB]
  exact hindep.measure_inter_preimage_eq_mul _ _ measurableSet_ball measurableSet_ball

/-- The joint return probability of `sec:variance`, written as the measure of an
intersection with the two distances in the order `pairSet` reads them. -/
theorem jointReturn_eq_measure_inter (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (r : ℝ)
    (t u t' u' : ℝ≥0) :
    jointReturn W P r t u t' u'
      = P ({ω | dist (W t ω) (W u ω) < r} ∩ {ω | dist (W t' ω) (W u' ω) < r}) := by
  unfold jointReturn
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [dist_comm (W u ω) (W t ω), dist_comm (W u' ω) (W t' ω)]

end VarianceCovariance

/-! ### `eq:variance` -/

open VarianceCovariance in
/-- `thm:variance`, `eq:variance`: the variance expansion.  Expanding the variance and
interchanging the sample point with the times writes `Var(C_r)` as the `μ⁴`-integral of
the covariance of the two return events; that covariance vanishes off the overlap set
and is at most the joint return probability on it.

No Frostman hypothesis enters: the times are read through `Real.toNNReal` on both sides,
so the support condition on `μ` is not needed here, and the variance is that of a random
variable bounded by one, so the bound is not vacuous. -/
theorem variance_le_overlap_lintegral {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    variance (fun ω => (corr (occupation W μ ω) r).toReal) P
      ≤ (∫⁻ p : ℝ × ℝ × ℝ × ℝ in {p | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2},
          jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
          ∂(μ.prod (μ.prod (μ.prod μ)))).toReal := by
  obtain ⟨V, hVmeas, hVcont, M, hMmeas, hMnull, hVW⟩ := Reduction.exists_modification hW
  have hjoint : Measurable (Function.uncurry V) :=
    measurable_uncurry_of_continuous_of_measurable hVcont hVmeas
  have hMc : ∀ᵐ ω ∂P, ω ∉ M := by
    rw [ae_iff]
    simpa using hMnull
  have hT : MeasurableSet (pairSet V r) := measurableSet_pairSet hjoint r
  have hU : MeasurableSet (quadSet V r) := measurableSet_quadSet hjoint r
  -- the empirical correlation integral, as the mass of a section
  have hvar : variance (fun ω => (corr (occupation W μ ω) r).toReal) P
      = variance
          (fun ω => ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal) P := by
    refine variance_congr ?_
    filter_upwards [hMc] with ω hω
    have hfun : (fun t : ℝ => W t.toNNReal ω) = fun t : ℝ => V t.toNNReal ω :=
      funext fun t => (hVW ω hω _).symm
    have hpath : Measurable fun t : ℝ => V t.toNNReal ω :=
      ((hVcont ω).comp continuous_real_toNNReal).measurable
    show (corr (occupation W μ ω) r).toReal
        = ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal
    rw [occupation, hfun, Reduction.corr_map hpath r]
    rfl
  have hZmem : MemLp
      (fun ω => ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' pairSet V r)).toReal) 2 P := by
    refine memLp_of_bounded (a := 0) (b := 1)
      (Eventually.of_forall fun ω => ⟨ENNReal.toReal_nonneg, ?_⟩)
      (measurable_measure_prodMk_right hT).ennreal_toReal.aestronglyMeasurable 2
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  -- the overlap set, read on the pair of time pairs
  have hO' : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2} := by
    have hcont : Continuous fun p : ℝ × ℝ × ℝ × ℝ => overlap p.1 p.2.1 p.2.2.1 p.2.2.2 := by
      unfold overlap
      fun_prop
    exact (isOpen_lt continuous_const hcont).measurableSet
  set O : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    quadEquiv ⁻¹' {p : ℝ × ℝ × ℝ × ℝ | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2} with hOdef
  have hO : MeasurableSet O := quadEquiv.measurable hO'
  -- the two conditional probabilities, and their readings through `W`
  have hFW : ∀ p : ℝ × ℝ, P (Prod.mk p ⁻¹' pairSet V r)
      = P {ω | dist (W p.1.toNNReal ω) (W p.2.toNNReal ω) < r} := by
    intro p
    refine measure_congr ?_
    filter_upwards [hMc] with ω hω
    have h1 := hVW ω hω p.1.toNNReal
    have h2 := hVW ω hω p.2.toNNReal
    show (dist (V p.1.toNNReal ω) (V p.2.toNNReal ω) < r)
        = (dist (W p.1.toNNReal ω) (W p.2.toNNReal ω) < r)
    rw [h1, h2]
  have hGW : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), P (Prod.mk q ⁻¹' quadSet V r)
      = P ({ω | dist (W q.1.1.toNNReal ω) (W q.1.2.toNNReal ω) < r} ∩
          {ω | dist (W q.2.1.toNNReal ω) (W q.2.2.toNNReal ω) < r}) := by
    intro q
    refine measure_congr ?_
    filter_upwards [hMc] with ω hω
    have h1 := hVW ω hω q.1.1.toNNReal
    have h2 := hVW ω hω q.1.2.toNNReal
    have h3 := hVW ω hω q.2.1.toNNReal
    have h4 := hVW ω hω q.2.2.toNNReal
    show (dist (V q.1.1.toNNReal ω) (V q.1.2.toNNReal ω) < r ∧
        dist (V q.2.1.toNNReal ω) (V q.2.2.toNNReal ω) < r)
      = (dist (W q.1.1.toNNReal ω) (W q.1.2.toNNReal ω) < r ∧
        dist (W q.2.1.toNNReal ω) (W q.2.2.toNNReal ω) < r)
    rw [h1, h2, h3, h4]
  -- the two integrands agree off the overlap set
  have hcompl : Set.EqOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => P (Prod.mk q ⁻¹' quadSet V r))
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        P (Prod.mk q.1 ⁻¹' pairSet V r) * P (Prod.mk q.2 ⁻¹' pairSet V r)) Oᶜ := by
    intro q hq
    have hnot : ¬ 0 < overlap q.1.1 q.1.2 q.2.1 q.2.2 := by
      intro hlt
      exact hq (by rw [hOdef]; exact hlt)
    simp only [hGW q, hFW q.1, hFW q.2]
    exact measure_inter_eq_mul_of_overlap_nonpos hW hr hnot
  -- every piece is finite
  have hbound : ∀ (f : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ≥0∞), (∀ q, f q ≤ 1) →
      ∀ s : Set ((ℝ × ℝ) × (ℝ × ℝ)),
        ∫⁻ q in s, f q ∂((μ.prod μ).prod (μ.prod μ)) ≠ ∞ := by
    intro f hf s
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ q in s, f q ∂((μ.prod μ).prod (μ.prod μ))
        ≤ ∫⁻ _ in s, 1 ∂((μ.prod μ).prod (μ.prod μ)) := lintegral_mono hf
      _ = ((μ.prod μ).prod (μ.prod μ)) s := setLIntegral_one s
      _ ≤ 1 := prob_le_one
  have hGle : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), P (Prod.mk q ⁻¹' quadSet V r) ≤ 1 := fun _ => prob_le_one
  have hFle : ∀ q : (ℝ × ℝ) × (ℝ × ℝ),
      P (Prod.mk q.1 ⁻¹' pairSet V r) * P (Prod.mk q.2 ⁻¹' pairSet V r) ≤ 1 := fun _ =>
    mul_le_one' prob_le_one prob_le_one
  -- the variance, split at the overlap set
  rw [hvar, variance_eq_sub hZmem]
  simp only [Pi.pow_apply]
  rw [integral_sq_eq hjoint r, integral_eq hjoint r, sq_lintegral_eq (P := P) hjoint r]
  have hsplitG := lintegral_add_compl
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) => P (Prod.mk q ⁻¹' quadSet V r))
    (μ := (μ.prod μ).prod (μ.prod μ)) hO
  have hsplitF := lintegral_add_compl
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      P (Prod.mk q.1 ⁻¹' pairSet V r) * P (Prod.mk q.2 ⁻¹' pairSet V r))
    (μ := (μ.prod μ).prod (μ.prod μ)) hO
  have key : (∫⁻ q, P (Prod.mk q ⁻¹' quadSet V r) ∂((μ.prod μ).prod (μ.prod μ))).toReal
        - (∫⁻ q, P (Prod.mk q.1 ⁻¹' pairSet V r) * P (Prod.mk q.2 ⁻¹' pairSet V r)
            ∂((μ.prod μ).prod (μ.prod μ))).toReal
      = (∫⁻ q in O, P (Prod.mk q ⁻¹' quadSet V r) ∂((μ.prod μ).prod (μ.prod μ))).toReal
        - (∫⁻ q in O, P (Prod.mk q.1 ⁻¹' pairSet V r) * P (Prod.mk q.2 ⁻¹' pairSet V r)
            ∂((μ.prod μ).prod (μ.prod μ))).toReal := by
    rw [← hsplitG, ← hsplitF, ENNReal.toReal_add (hbound _ hGle O) (hbound _ hGle Oᶜ),
      ENNReal.toReal_add (hbound _ hFle O) (hbound _ hFle Oᶜ),
      setLIntegral_congr_fun hO.compl hcompl]
    ring
  rw [key]
  refine (sub_le_self _ ENNReal.toReal_nonneg).trans (le_of_eq ?_)
  congr 1
  rw [hOdef, ← map_quadEquiv μ, Measure.restrict_map quadEquiv.measurable hO',
    lintegral_map_equiv]
  refine lintegral_congr fun q => ?_
  rw [hGW q]
  exact (jointReturn_eq_measure_inter W P r q.1.1.toNNReal q.1.2.toNNReal
    q.2.1.toNNReal q.2.2.toNNReal).symm

set_option linter.unusedVariables false in
/-- `thm:variance`, `eq:variance`: the four-point variance bound.  The dyadic block bound
of `thm:endpoint-block-mass` is summed by `thm:four-point-integral`, and the variance
expansion above is what feeds the four-point integral. -/
theorem variance_four_point {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      variance (fun ω => (corr (occupation W μ ω) r).toReal) P
        ≤ C * varScale s r :=
  variance_of_block hW hs0 hs1 hμ (endpoint_block_mass_dyadic hW hs0 hμ)
    fun r hr0 _ => variance_le_overlap_lintegral hW hr0

set_option linter.unusedVariables false in
/-- `thm:variance` as one statement: the bound of `eq:variance` together with the
`o(r^{4s})` consequence. -/
theorem variance_bundled {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    (∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
        variance (fun ω => (corr (occupation W μ ω) r).toReal) P ≤ C * varScale s r) ∧
      Tendsto (fun r : ℝ => varScale s r / r ^ (4 * s)) (𝓝[>] 0) (𝓝 0) :=
  thm_variance_of_block hW hs0 hs1 hμ (endpoint_block_mass_dyadic hW hs0 hμ)
    fun r hr0 _ => variance_le_overlap_lintegral hW hr0

end BrownianImages
