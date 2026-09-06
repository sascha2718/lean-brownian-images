/-
`sec:setup` of `BrownianImagesComplete.tex`: `thm:gaussian-reduction`,
`eq:gaussian-reduction`.

The expected correlation integral `S_μ(r) = 𝔼 C_r(W_*μ)` is the Gaussian transform of
the pair-distance law, first against `μ × μ` and then, by the pushforward
`(x,y) ↦ |x - y|`, against `dΦ`.  The chain is the Fubini interchange
`∫_ω (μ×μ)(A_ω) dP = ∫_{μ×μ} P(A_p)`, the planar return probability
`IsPlanarBrownian.return_prob`, and the change of variables defining `pairLaw`.

* `Reduction.exists_modification`: a jointly measurable version of the process, every
  path continuous, agreeing with `W` off one null set.  This is what the Fubini step needs and what `IsBrownianReal` does
  not give directly: it carries measurability of `W t` only up to a null set, one time
  at a time.
* `expCorr_eq_integral_prod`: the first identity of `eq:gaussian-reduction`.
* `expCorr_eq_integral_pairLaw`: the second.
* `gaussian_reduction`: the two together, the shape of `thm:gaussian-reduction`.
-/
import BrownianImages.GaussianFourPoint

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Reduction

variable {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- At a fixed time the planar process of `eq:gaussian-reduction` is almost everywhere
measurable, assembled from the two coordinates through the measurable identification of
`EuclideanSpace ℝ (Fin 2)` with `Fin 2 → ℝ`. -/
theorem aemeasurable_eval (hW : IsPlanarBrownian W P) (t : ℝ≥0) :
    AEMeasurable (fun ω => W t ω) P := by
  have h : ∀ i : Fin 2, AEMeasurable (fun ω => W t ω i) P := fun i =>
    (hW.coord i).toIsPreBrownianReal.aemeasurable t
  exact (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp_aemeasurable (aemeasurable_pi_lambda _ h)

/-- The Fubini step of `thm:gaussian-reduction` needs the process jointly measurable in
time and chance, which `IsBrownianReal` does not supply: it gives measurability of `W t`
only almost everywhere, and only one time at a time.  Killing the process on one null
set repairs both defects at once.  Off a measurable null set `M` the modification `V`
agrees with `W` at every time, every path of `V` is continuous, and `V t` is measurable
for every `t`; `measurable_uncurry_of_continuous_of_measurable` then makes
`Function.uncurry V` measurable. -/
theorem exists_modification (hW : IsPlanarBrownian W P) :
    ∃ V : ℝ≥0 → Ω → Plane, (∀ t, Measurable (V t)) ∧ (∀ ω, Continuous fun t => V t ω) ∧
      ∃ M : Set Ω, MeasurableSet M ∧ P M = 0 ∧ ∀ ω ∉ M, ∀ t, V t ω = W t ω := by
  classical
  set D : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  set N₀ : Set Ω := toMeasurable P {ω | ¬ Continuous fun t : ℝ≥0 => W t ω} with hN₀
  have hN₀meas : MeasurableSet N₀ := measurableSet_toMeasurable _ _
  have hN₀null : P N₀ = 0 := by
    rw [hN₀, measure_toMeasurable]
    exact hW.ae_continuous
  set g : ℕ → Ω → Plane := fun n => (aemeasurable_eval hW (D n)).mk _
  have hgmeas : ∀ n, Measurable (g n) := fun n => (aemeasurable_eval hW (D n)).measurable_mk
  set N : ℕ → Set Ω := fun n => toMeasurable P {ω | W (D n) ω ≠ g n ω} with hN
  have hNmeas : ∀ n, MeasurableSet (N n) := fun n => measurableSet_toMeasurable _ _
  have hNnull : ∀ n, P (N n) = 0 := by
    intro n
    rw [hN, measure_toMeasurable]
    exact (aemeasurable_eval hW (D n)).ae_eq_mk
  set M : Set Ω := N₀ ∪ ⋃ n, N n
  have hMmeas : MeasurableSet M := hN₀meas.union (MeasurableSet.iUnion hNmeas)
  have hMnull : P M = 0 := measure_union_null hN₀null (measure_iUnion_null hNnull)
  set V : ℝ≥0 → Ω → Plane := fun t => M.piecewise (fun _ => 0) (W t)
  have hVout : ∀ ω ∉ M, ∀ t, V t ω = W t ω := fun ω hω t => Set.piecewise_eq_of_notMem _ _ _ hω
  have hVin : ∀ ω ∈ M, ∀ t, V t ω = 0 := fun ω hω t => Set.piecewise_eq_of_mem _ _ _ hω
  have hcont : ∀ ω, Continuous fun t => V t ω := by
    intro ω
    by_cases hω : ω ∈ M
    · simpa [funext fun t => hVin ω hω t] using continuous_const (y := (0 : Plane))
    · have hω₀ : ω ∉ N₀ := fun h => hω (Or.inl h)
      have hc : Continuous fun t : ℝ≥0 => W t ω := by
        by_contra hc
        exact hω₀ (subset_toMeasurable P _ hc)
      simpa [funext fun t => hVout ω hω t] using hc
  have hVD : ∀ n, Measurable (V (D n)) := by
    intro n
    have hpw : V (D n) = M.piecewise (fun _ => 0) (g n) := by
      funext ω
      by_cases hω : ω ∈ M
      · simp [hVin ω hω, Set.piecewise_eq_of_mem _ _ _ hω]
      · have hn : ω ∉ N n := fun h => hω (Or.inr (Set.mem_iUnion.mpr ⟨n, h⟩))
        have hgn : W (D n) ω = g n ω := by
          by_contra hne
          exact hn (subset_toMeasurable P _ hne)
        rw [hVout ω hω, Set.piecewise_eq_of_notMem _ _ _ hω, hgn]
    rw [hpw]
    exact Measurable.piecewise hMmeas measurable_const (hgmeas n)
  have hVmeas : ∀ t, Measurable (V t) := by
    intro t
    have hmem : t ∈ closure (Set.range D) := by
      rw [(TopologicalSpace.denseRange_denseSeq ℝ≥0).closure_eq]
      trivial
    obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp hmem
    have hxm : ∀ j, Measurable (V (x j)) := by
      intro j
      obtain ⟨n, hn⟩ := hx j
      rw [← hn]
      exact hVD n
    refine measurable_of_tendsto_metrizable hxm ?_
    rw [tendsto_pi_nhds]
    intro ω
    exact ((hcont ω).tendsto t).comp hxt
  exact ⟨V, hVmeas, hcont, M, hMmeas, hMnull, hVout⟩

/-- `eq:correlation-functional` for a pushforward: the correlation functional of `f_*μ`
is the `μ × μ`-measure of the pairs whose images are within `r`. -/
theorem corr_map {μ : Measure ℝ} [SFinite μ] {f : ℝ → Plane} (hf : Measurable f) (r : ℝ) :
    corr (μ.map f) r = (μ.prod μ) {p : ℝ × ℝ | dist (f p.1) (f p.2) < r} := by
  rw [corr, Measure.map_prod_map μ μ hf hf,
    Measure.map_apply (hf.prodMap hf) (measurableSet_corrSet r)]
  rfl

/-- The diagonal is `μ × μ`-null for an atomless `μ`.  Without this the identity of
`eq:gaussian-reduction` is false, since real division by zero puts the integrand at `0`
on the diagonal. -/
theorem prod_diagonal_null {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) : (μ.prod μ) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have h := pairLaw_measure_singleton hs hμ 0
  rw [pairLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℝ))] at h
  have hset : (fun p : ℝ × ℝ => |p.1 - p.2|) ⁻¹' {(0 : ℝ)} = {p : ℝ × ℝ | p.1 = p.2} := by
    ext p
    simp [sub_eq_zero]
  rwa [hset] at h

/-- The support condition of `IsFrostman` transfers to the two coordinates of the
product, which is what makes `Real.toNNReal` injective where it is read. -/
theorem prod_fst_mem_Icc {s A : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), p.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  have hset : {p : ℝ × ℝ | ¬ p.1 ∈ Set.Icc (0 : ℝ) 1}
      = (Set.Icc (0 : ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp
  rw [hset, Measure.prod_prod, hμ.support, zero_mul]

/-- The same for the second coordinate. -/
theorem prod_snd_mem_Icc {s A : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), p.2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  have hset : {p : ℝ × ℝ | ¬ p.2 ∈ Set.Icc (0 : ℝ) 1}
      = (Set.univ : Set ℝ) ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ := by
    ext p
    simp
  rw [hset, Measure.prod_prod, hμ.support, mul_zero]

/-- The integrand of `eq:gaussian-reduction` is non-negative at every non-negative
argument, the diagonal included, where it takes the value `0`. -/
theorem gaussTransform_nonneg (r : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ 1 - Real.exp (-(r ^ 2 / (2 * δ))) := by
  have h : Real.exp (-(r ^ 2 / (2 * δ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg r) (by linarith)))
  linarith

end Reduction

/-! ### `thm:gaussian-reduction` -/

section ExpCorr

variable {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- `eq:gaussian-reduction`, the first identity: the expected correlation integral is
the Gaussian transform of the pair-distance law against `μ × μ`.  The Frostman
hypothesis with `0 < s` is what makes `μ` atomless, hence the diagonal null; on the
diagonal the integrand reads `0`, not `1`, so without it the identity is false. -/
theorem expCorr_eq_integral_prod [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {s A : ℝ} (hs0 : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    {r : ℝ} (hr : 0 < r) :
    expCorr W P μ r
      = ∫ p : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 / (2 * |p.1 - p.2|)))) ∂(μ.prod μ) := by
  obtain ⟨V, hVmeas, hVcont, M, hMmeas, hMnull, hVW⟩ := Reduction.exists_modification hW
  have hjoint : Measurable (Function.uncurry V) :=
    measurable_uncurry_of_continuous_of_measurable hVcont hVmeas
  have hpath : ∀ ω : Ω, Measurable fun t : ℝ => V t.toNNReal ω := fun ω =>
    ((hVcont ω).comp continuous_real_toNNReal).measurable
  have hMc : ∀ᵐ ω ∂P, ω ∉ M := by
    rw [ae_iff]
    simpa using hMnull
  have hdiag : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa using Reduction.prod_diagonal_null hs0 hμ
  set T : Set ((ℝ × ℝ) × Ω) :=
    {q : (ℝ × ℝ) × Ω | dist (V q.1.1.toNNReal q.2) (V q.1.2.toNNReal q.2) < r}
  have hTmeas : MeasurableSet T := by
    have h1 : Measurable fun q : (ℝ × ℝ) × Ω => V q.1.1.toNNReal q.2 :=
      hjoint.comp ((continuous_real_toNNReal.measurable.comp
        (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    have h2 : Measurable fun q : (ℝ × ℝ) × Ω => V q.1.2.toNNReal q.2 :=
      hjoint.comp ((continuous_real_toNNReal.measurable.comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    exact measurableSet_lt (h1.dist h2) measurable_const
  have hfub : ∫⁻ ω, (μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' T) ∂P
      = ∫⁻ p : ℝ × ℝ, P (Prod.mk p ⁻¹' T) ∂(μ.prod μ) := by
    rw [← Measure.prod_apply_symm hTmeas, Measure.prod_apply hTmeas]
  have hLHS : expCorr W P μ r
      = (∫⁻ ω, (μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' T) ∂P).toReal := by
    have hcongr : ∀ᵐ ω ∂P, (corr (occupation W μ ω) r).toReal
        = ((μ.prod μ) ((fun p : ℝ × ℝ => (p, ω)) ⁻¹' T)).toReal := by
      filter_upwards [hMc] with ω hω
      have hfun : (fun t : ℝ => W t.toNNReal ω) = fun t : ℝ => V t.toNNReal ω :=
        funext fun t => (hVW ω hω _).symm
      rw [occupation, hfun, Reduction.corr_map (hpath ω) r]
      rfl
    rw [expCorr, integral_congr_ae hcongr]
    refine integral_toReal (measurable_measure_prodMk_right hTmeas).aemeasurable ?_
    exact Eventually.of_forall fun ω => measure_lt_top _ _
  have hRHS : ∫ p : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 / (2 * |p.1 - p.2|)))) ∂(μ.prod μ)
      = (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (1 - Real.exp (-(r ^ 2 / (2 * |p.1 - p.2|)))) ∂(μ.prod μ)).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun p => Reduction.gaussTransform_nonneg r (abs_nonneg _)) ?_
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hkey : ∫⁻ p : ℝ × ℝ, P (Prod.mk p ⁻¹' T) ∂(μ.prod μ)
      = ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (1 - Real.exp (-(r ^ 2 / (2 * |p.1 - p.2|)))) ∂(μ.prod μ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Reduction.prod_fst_mem_Icc hμ, Reduction.prod_snd_mem_Icc hμ, hdiag] with
      p hp1 hp2 hne
    have hc1 : (p.1.toNNReal : ℝ) = p.1 := Real.coe_toNNReal _ hp1.1
    have hc2 : (p.2.toNNReal : ℝ) = p.2 := Real.coe_toNNReal _ hp2.1
    have htu : p.2.toNNReal ≠ p.1.toNNReal := by
      intro h
      exact hne (by rw [← hc1, ← hc2, h])
    have hsets : Prod.mk p ⁻¹' T = {ω | dist (V p.1.toNNReal ω) (V p.2.toNNReal ω) < r} := rfl
    have hVWset : P {ω | dist (V p.1.toNNReal ω) (V p.2.toNNReal ω) < r}
        = P {ω | dist (W p.1.toNNReal ω) (W p.2.toNNReal ω) < r} := by
      refine measure_congr ?_
      filter_upwards [hMc] with ω hω
      show (dist (V p.1.toNNReal ω) (V p.2.toNNReal ω) < r)
            = (dist (W p.1.toNNReal ω) (W p.2.toNNReal ω) < r)
      rw [hVW ω hω, hVW ω hω]
    rw [hsets, hVWset, hW.return_prob hr htu, hc1, hc2]
  rw [hLHS, hRHS, hfub, hkey]

/-- `eq:gaussian-reduction`, the second identity: the Stieltjes form, against the
pair-distance law `dΦ`.  It is the first identity carried along the pushforward
`(x,y) ↦ |x - y|` that defines `pairLaw`. -/
theorem expCorr_eq_integral_pairLaw [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {s A : ℝ} (hs0 : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    {r : ℝ} (hr : 0 < r) :
    expCorr W P μ r = ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ) := by
  rw [expCorr_eq_integral_prod hW hs0 hμ hr, pairLaw,
    integral_map (by fun_prop) (Measurable.aestronglyMeasurable (by fun_prop))]

end ExpCorr

/-- `thm:gaussian-reduction`, `eq:gaussian-reduction`.  The expected correlation
integral is the Gaussian transform of the pair-distance law, in both the `μ × μ` form
and the Stieltjes form against `dΦ`.  The Frostman hypothesis is what makes `μ`
atomless, so that the diagonal, where the exponent is undefined, is null. -/
theorem gaussian_reduction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (_hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    expCorr W P μ r
        = ∫ p : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 / (2 * |p.1 - p.2|)))) ∂(μ.prod μ) ∧
      expCorr W P μ r
        = ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ) :=
  ⟨expCorr_eq_integral_prod hW hs0 hμ hr, expCorr_eq_integral_pairLaw hW hs0 hμ hr⟩

end BrownianImages

