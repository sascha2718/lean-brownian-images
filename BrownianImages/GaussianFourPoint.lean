/-
`sec:setup` and `sec:variance` of `BrownianImagesComplete.tex`.

* `endpoint_block_mass_le`: the mass half of `thm:endpoint-block-mass`,
  `eq:endpoint-block-mass`, with the three Frostman applications behind it
  (`block_inner_le`, `block_mid_le`, `block_relaxed_le`).
* `disjoint_increments_indep`: the first assertion of
  `thm:gaussian-four-point`, together with the two lemmas it rests on:
  `indepFun_pi_of_pair`, the π-system argument that assembles coordinatewise
  independence into independence of `Plane`-valued increments, and
  `IsPlanarBrownian.indepFun_increments`, its ordered form.
* `IsPlanarBrownian.return_prob`: the planar return probability
  `P(|W_u - W_t| < r) = 1 - e^{-r²/(2|u-t|)}` of `eq:gaussian-reduction`,
  through `IsPlanarBrownian.map_increment`, `gaussian_prod_disc` and
  `integral_radial`.
-/
import BrownianImages.Frostman
import BrownianImages.Occupation

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### `sec:variance`: the mass of the dyadic block -/

section BlockMass

variable {s A : ℝ} {μ : Measure ℝ}

/-- The inner two integrations of `eq:endpoint-block-mass`: with `x₂` fixed, the pairs
`(x₃, x₄)` with `x₃` within `β` of `x₂` and `x₄` within `η` of `x₃`. -/
theorem block_inner_le [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    {β η : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1) (x₂ : ℝ) :
    (μ.prod μ) {q : ℝ × ℝ | |q.1 - x₂| ≤ β ∧ |q.2 - q.1| ≤ η}
      ≤ ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s) := by
  have hmeas : MeasurableSet {q : ℝ × ℝ | |q.1 - x₂| ≤ β ∧ |q.2 - q.1| ≤ η} := by
    have h1 : MeasurableSet {q : ℝ × ℝ | |q.1 - x₂| ≤ β} :=
      measurableSet_le (by fun_prop) measurable_const
    have h2 : MeasurableSet {q : ℝ × ℝ | |q.2 - q.1| ≤ η} :=
      measurableSet_le (by fun_prop) measurable_const
    exact h1.inter h2
  rw [Measure.prod_apply hmeas]
  have hsec : ∀ x₃ : ℝ,
      μ (Prod.mk x₃ ⁻¹' {q : ℝ × ℝ | |q.1 - x₂| ≤ β ∧ |q.2 - q.1| ≤ η})
        ≤ (Metric.closedBall x₂ β).indicator (fun _ => ENNReal.ofReal (A * η ^ s)) x₃ := by
    intro x₃
    by_cases hx : |x₃ - x₂| ≤ β
    · have hmem : x₃ ∈ Metric.closedBall x₂ β := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hx
      rw [Set.indicator_of_mem hmem]
      refine le_trans (measure_mono ?_) (hμ.measure_closedBall_le x₃ η hη0 hη1)
      intro x₄ hx₄
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx₄
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx₄.2
    · have hempty : Prod.mk x₃ ⁻¹' {q : ℝ × ℝ | |q.1 - x₂| ≤ β ∧ |q.2 - q.1| ≤ η} = ∅ := by
        ext x₄
        simp [hx]
      rw [hempty]
      simp
  calc ∫⁻ x₃, μ (Prod.mk x₃ ⁻¹' {q : ℝ × ℝ | |q.1 - x₂| ≤ β ∧ |q.2 - q.1| ≤ η}) ∂μ
      ≤ ∫⁻ x₃, (Metric.closedBall x₂ β).indicator
          (fun _ => ENNReal.ofReal (A * η ^ s)) x₃ ∂μ := lintegral_mono hsec
    _ = ENNReal.ofReal (A * η ^ s) * μ (Metric.closedBall x₂ β) :=
        lintegral_indicator_const measurableSet_closedBall _
    _ ≤ ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s) := by
        gcongr
        exact hμ.measure_closedBall_le x₂ β hβ0 hβ1

/-- The three inner integrations of `eq:endpoint-block-mass`: with `x₁` fixed, the
triples `(x₂, x₃, x₄)` with `x₂` within `η` of `x₁`, `x₃` within `β` of `x₂` and `x₄`
within `η` of `x₃`. -/
theorem block_mid_le [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    {β η : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1) (x₁ : ℝ) :
    (μ.prod (μ.prod μ))
        {q : ℝ × ℝ × ℝ | |q.2.1 - q.1| ≤ β ∧ |x₁ - q.1| ≤ η ∧ |q.2.2 - q.2.1| ≤ η}
      ≤ ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
          * ENNReal.ofReal (A * η ^ s) := by
  have hmeas : MeasurableSet
      {q : ℝ × ℝ × ℝ | |q.2.1 - q.1| ≤ β ∧ |x₁ - q.1| ≤ η ∧ |q.2.2 - q.2.1| ≤ η} := by
    have h1 : MeasurableSet {q : ℝ × ℝ × ℝ | |q.2.1 - q.1| ≤ β} :=
      measurableSet_le (by fun_prop) measurable_const
    have h2 : MeasurableSet {q : ℝ × ℝ × ℝ | |x₁ - q.1| ≤ η} :=
      measurableSet_le (by fun_prop) measurable_const
    have h3 : MeasurableSet {q : ℝ × ℝ × ℝ | |q.2.2 - q.2.1| ≤ η} :=
      measurableSet_le (by fun_prop) measurable_const
    exact h1.inter (h2.inter h3)
  rw [Measure.prod_apply hmeas]
  have hsec : ∀ x₂ : ℝ,
      (μ.prod μ) (Prod.mk x₂ ⁻¹'
          {q : ℝ × ℝ × ℝ | |q.2.1 - q.1| ≤ β ∧ |x₁ - q.1| ≤ η ∧ |q.2.2 - q.2.1| ≤ η})
        ≤ (Metric.closedBall x₁ η).indicator
            (fun _ => ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)) x₂ := by
    intro x₂
    by_cases hx : |x₁ - x₂| ≤ η
    · have hmem : x₂ ∈ Metric.closedBall x₁ η := by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
        exact hx
      rw [Set.indicator_of_mem hmem]
      refine le_trans (measure_mono ?_) (block_inner_le hμ hβ0 hβ1 hη0 hη1 x₂)
      intro q hq
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hq ⊢
      exact ⟨hq.1, hq.2.2⟩
    · have hempty : Prod.mk x₂ ⁻¹'
          {q : ℝ × ℝ × ℝ | |q.2.1 - q.1| ≤ β ∧ |x₁ - q.1| ≤ η ∧ |q.2.2 - q.2.1| ≤ η}
          = ∅ := by
        ext q
        simp [hx]
      rw [hempty]
      simp
  calc ∫⁻ x₂, (μ.prod μ) (Prod.mk x₂ ⁻¹'
          {q : ℝ × ℝ × ℝ | |q.2.1 - q.1| ≤ β ∧ |x₁ - q.1| ≤ η ∧ |q.2.2 - q.2.1| ≤ η}) ∂μ
      ≤ ∫⁻ x₂, (Metric.closedBall x₁ η).indicator
          (fun _ => ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)) x₂ ∂μ :=
        lintegral_mono hsec
    _ = ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
          * μ (Metric.closedBall x₁ η) :=
        lintegral_indicator_const measurableSet_closedBall _
    _ ≤ ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
          * ENNReal.ofReal (A * η ^ s) := by
        gcongr
        exact hμ.measure_closedBall_le x₁ η hη0 hη1

/-- The Frostman bound applied three times: the `μ⁴`-mass of the quadruples with
`|x₃ - x₂| ≤ β`, `|x₁ - x₂| ≤ η` and `|x₄ - x₃| ≤ η`, which is the block of
`eq:endpoint-block-mass` with the ordering constraints dropped. -/
theorem block_relaxed_le [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    {β η : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | |p.2.2.1 - p.2.1| ≤ β ∧ |p.1 - p.2.1| ≤ η ∧
          |p.2.2.2 - p.2.2.1| ≤ η}
      ≤ ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
          * ENNReal.ofReal (A * η ^ s) := by
  have hmeas : MeasurableSet
      {p : ℝ × ℝ × ℝ × ℝ | |p.2.2.1 - p.2.1| ≤ β ∧ |p.1 - p.2.1| ≤ η ∧
        |p.2.2.2 - p.2.2.1| ≤ η} := by
    have h1 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | |p.2.2.1 - p.2.1| ≤ β} :=
      measurableSet_le (by fun_prop) measurable_const
    have h2 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | |p.1 - p.2.1| ≤ η} :=
      measurableSet_le (by fun_prop) measurable_const
    have h3 : MeasurableSet {p : ℝ × ℝ × ℝ × ℝ | |p.2.2.2 - p.2.2.1| ≤ η} :=
      measurableSet_le (by fun_prop) measurable_const
    exact h1.inter (h2.inter h3)
  rw [Measure.prod_apply hmeas]
  have hsec : ∀ x₁ : ℝ,
      (μ.prod (μ.prod μ)) (Prod.mk x₁ ⁻¹'
          {p : ℝ × ℝ × ℝ × ℝ | |p.2.2.1 - p.2.1| ≤ β ∧ |p.1 - p.2.1| ≤ η ∧
            |p.2.2.2 - p.2.2.1| ≤ η})
        ≤ ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
            * ENNReal.ofReal (A * η ^ s) := by
    intro x₁
    exact block_mid_le hμ hβ0 hβ1 hη0 hη1 x₁
  calc ∫⁻ x₁, (μ.prod (μ.prod μ)) (Prod.mk x₁ ⁻¹'
          {p : ℝ × ℝ × ℝ × ℝ | |p.2.2.1 - p.2.1| ≤ β ∧ |p.1 - p.2.1| ≤ η ∧
            |p.2.2.2 - p.2.2.1| ≤ η}) ∂μ
      ≤ ∫⁻ _, ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
          * ENNReal.ofReal (A * η ^ s) ∂μ := lintegral_mono hsec
    _ = ENNReal.ofReal (A * η ^ s) * ENNReal.ofReal (A * β ^ s)
          * ENNReal.ofReal (A * η ^ s) := by simp

/-- `thm:endpoint-block-mass`, `eq:endpoint-block-mass`: the `μ⁴`-mass of the dyadic
block of ordered quadruples is `O(β^s η^{2s})`.  On the block `x₃` lies within `β` of
`x₂`, `x₁` within `η` of `x₂` and `x₄` within `η` of `x₃`; dropping the ordering
constraints and integrating in that order applies `eq:frostman` three times, with
constant `A³`. -/
theorem endpoint_block_mass_le {s A : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ β η : ℝ, 0 < β → β ≤ 1 → 0 < η → η ≤ 1 →
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          β / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ β ∧
          η / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ η}
        ≤ ENNReal.ofReal (C * β ^ s * η ^ (2 * s)) := by
  have hA : (1:ℝ) ≤ A := hμ.one_le_const
  have hApos : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨A ^ 3, pow_pos hApos 3, ?_⟩
  intro β η hβ0 hβ1 hη0 hη1
  have hβs : (0:ℝ) < β ^ s := Real.rpow_pos_of_pos hβ0 s
  have hηs : (0:ℝ) < η ^ s := Real.rpow_pos_of_pos hη0 s
  refine le_trans (measure_mono ?_) (le_trans (block_relaxed_le hμ hβ0 hβ1 hη0 hη1) ?_)
  · intro p hp
    obtain ⟨h12, h23, h34, _, hb2, _, hh2⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]
      exact hb2
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : η ^ s * η ^ s = η ^ (2 * s) := by
      rw [← Real.rpow_add hη0]
      congr 1
      ring
    have hprod : A * η ^ s * (A * β ^ s) * (A * η ^ s)
        = A ^ 3 * β ^ s * (η ^ s * η ^ s) := by ring
    rw [hprod, hpow]

end BlockMass


/-! ### `sec:variance`: independence of disjoint increments -/

section Increments

open MeasurableSpace

/-- Independence of two vector-valued random variables from coordinatewise data: if the
pairs `(X i, Y i)` are independent across `i`, and `X i` is independent of `Y i` for each
single `i`, then the vector `(X i)_i` is independent of the vector `(Y i)_i`.  The proof
is the π-system of boxes: on a box the two hypotheses factor the mass into one factor per
coordinate and per side. -/
theorem indepFun_pi_of_pair {ι : Type*} [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hpair : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hcoord : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  classical
  rw [IndepFun_iff_Indep]
  have hmeasX : Measurable (fun ω (i : ι) => X i ω) := measurable_pi_lambda _ hX
  have hmeasY : Measurable (fun ω (i : ι) => Y i ω) := measurable_pi_lambda _ hY
  set πβ : Set (Set (ι → ℝ)) :=
    Set.pi Set.univ '' Set.pi Set.univ fun _ : ι => {s : Set ℝ | MeasurableSet s} with hπβ
  set πX : Set (Set Ω) := {s | ∃ t ∈ πβ, (fun ω (i : ι) => X i ω) ⁻¹' t = s} with hπXdef
  set πY : Set (Set Ω) := {s | ∃ t ∈ πβ, (fun ω (i : ι) => Y i ω) ⁻¹' t = s} with hπYdef
  have hπX_pi : IsPiSystem πX := IsPiSystem.comap isPiSystem_pi _
  have hπY_pi : IsPiSystem πY := IsPiSystem.comap isPiSystem_pi _
  have hπX_gen : MeasurableSpace.pi.comap (fun ω (i : ι) => X i ω) = generateFrom πX := by
    rw [← generateFrom_pi, comap_generateFrom]
    congr
  have hπY_gen : MeasurableSpace.pi.comap (fun ω (i : ι) => Y i ω) = generateFrom πY := by
    rw [← generateFrom_pi, comap_generateFrom]
    congr
  refine IndepSets.indep hmeasX.comap_le hmeasY.comap_le hπX_pi hπY_pi hπX_gen hπY_gen ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at ha hb
  -- the three intersections, as intersections of preimages of boxes under the pairs
  have key : ∀ C : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (C i)) →
      P (⋂ i, (fun ω => (X i ω, Y i ω)) ⁻¹' C i)
        = ∏ i, P ((fun ω => (X i ω, Y i ω)) ⁻¹' C i) := by
    intro C hC
    exact hpair.meas_iInter fun i => ⟨C i, hC i, rfl⟩
  have hXset : (fun ω (i : ι) => X i ω) ⁻¹' Set.pi Set.univ a
      = ⋂ i, (fun ω => (X i ω, Y i ω)) ⁻¹' (a i ×ˢ (Set.univ : Set ℝ)) := by
    ext ω
    simp [Set.mem_pi]
  have hYset : (fun ω (i : ι) => Y i ω) ⁻¹' Set.pi Set.univ b
      = ⋂ i, (fun ω => (X i ω, Y i ω)) ⁻¹' ((Set.univ : Set ℝ) ×ˢ b i) := by
    ext ω
    simp [Set.mem_pi]
  have hXYset : (fun ω (i : ι) => X i ω) ⁻¹' Set.pi Set.univ a
        ∩ (fun ω (i : ι) => Y i ω) ⁻¹' Set.pi Set.univ b
      = ⋂ i, (fun ω => (X i ω, Y i ω)) ⁻¹' (a i ×ˢ b i) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter,
      Set.mem_prod]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  have k1 := key (fun i => a i ×ˢ (Set.univ : Set ℝ)) fun i => (ha i).prod MeasurableSet.univ
  have k2 := key (fun i => (Set.univ : Set ℝ) ×ˢ b i) fun i => MeasurableSet.univ.prod (hb i)
  have k3 := key (fun i => a i ×ˢ b i) fun i => (ha i).prod (hb i)
  rw [hXYset, hXset, hYset, k1, k2, k3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : (fun ω => (X i ω, Y i ω)) ⁻¹' (a i ×ˢ b i) = X i ⁻¹' a i ∩ Y i ⁻¹' b i := rfl
  have h2 : (fun ω => (X i ω, Y i ω)) ⁻¹' (a i ×ˢ (Set.univ : Set ℝ)) = X i ⁻¹' a i := by
    ext ω; simp
  have h3 : (fun ω => (X i ω, Y i ω)) ⁻¹' ((Set.univ : Set ℝ) ×ˢ b i) = Y i ⁻¹' b i := by
    ext ω; simp
  rw [h1, h2, h3]
  exact (hcoord i).measure_inter_preimage_eq_mul _ _ (ha i) (hb i)

/-- `indepFun_pi_of_pair` for coordinates that are only almost everywhere measurable,
which is what the finite-dimensional laws of a Brownian motion give. -/
theorem indepFun_pi_of_pair₀ {ι : Type*} [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : ι → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) P)
    (hpair : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hcoord : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  have hXae : ∀ i, X i =ᵐ[P] (hX i).mk (X i) := fun i => (hX i).ae_eq_mk
  have hYae : ∀ i, Y i =ᵐ[P] (hY i).mk (Y i) := fun i => (hY i).ae_eq_mk
  have hpair' : iIndepFun (fun i ω => ((hX i).mk (X i) ω, (hY i).mk (Y i) ω)) P := by
    refine hpair.congr fun i => ?_
    filter_upwards [hXae i, hYae i] with ω h1 h2
    rw [h1, h2]
  have hcoord' : ∀ i, IndepFun ((hX i).mk (X i)) ((hY i).mk (Y i)) P :=
    fun i => (hcoord i).congr (hXae i) (hYae i)
  have h := indepFun_pi_of_pair (fun i => (hX i).measurable_mk)
    (fun i => (hY i).measurable_mk) hpair' hcoord'
  refine h.congr ?_ ?_
  · filter_upwards [ae_all_iff.mpr hXae] with ω hω
    exact funext fun i => (hω i).symm
  · filter_upwards [ae_all_iff.mpr hYae] with ω hω
    exact funext fun i => (hω i).symm

variable {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- One coordinate at a time: over the ordered times `a ≤ b ≤ c ≤ d` the two increments
of a real Brownian motion are independent, since they are two of the three increments
of the monotone sequence `a, b, c, d`. -/
theorem IsPlanarBrownian.indepFun_coord_increments (hW : IsPlanarBrownian W P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (i : Fin 2) :
    IndepFun (fun ω => W b ω i - W a ω i) (fun ω => W d ω i - W c ω i) P := by
  have hB := (hW.coord i).toIsPreBrownianReal.hasIndepIncrements
  have hmono : Monotone (fun n : ℕ => match n with
      | 0 => a
      | 1 => b
      | 2 => c
      | _ => d) := by
    refine monotone_nat_of_le_succ fun n => ?_
    match n with
    | 0 => exact hab
    | 1 => exact hbc
    | 2 => exact hcd
    | (k + 3) => exact le_rfl
  exact (hB.nat hmono).indepFun (by norm_num : (0 : ℕ) ≠ 2)

/-- `thm:gaussian-four-point`, first assertion, for ordered times: the planar increments
over `[a,b]` and `[c,d]` with `a ≤ b ≤ c ≤ d` are independent.  Coordinatewise
independence of the increments and independence of the two coordinate processes give
independence of the two `Plane`-valued increments. -/
theorem IsPlanarBrownian.indepFun_increments [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    IndepFun (fun ω => W b ω - W a ω) (fun ω => W d ω - W c ω) P := by
  have hXae : ∀ i : Fin 2, AEMeasurable (fun ω => W b ω i - W a ω i) P := fun i =>
    ((hW.coord i).toIsPreBrownianReal.aemeasurable b).sub
      ((hW.coord i).toIsPreBrownianReal.aemeasurable a)
  have hYae : ∀ i : Fin 2, AEMeasurable (fun ω => W d ω i - W c ω i) P := fun i =>
    ((hW.coord i).toIsPreBrownianReal.aemeasurable d).sub
      ((hW.coord i).toIsPreBrownianReal.aemeasurable c)
  have hg : Measurable (fun p : ℝ≥0 → ℝ => (p b - p a, p d - p c)) :=
    ((measurable_pi_apply b).sub (measurable_pi_apply a)).prodMk
      ((measurable_pi_apply d).sub (measurable_pi_apply c))
  have hpairs : iIndepFun (fun (i : Fin 2) (ω : Ω) =>
      (W b ω i - W a ω i, W d ω i - W c ω i)) P :=
    hW.indep.comp (fun _ : Fin 2 => fun p : ℝ≥0 → ℝ => (p b - p a, p d - p c)) fun _ => hg
  have hpi := indepFun_pi_of_pair₀ hXae hYae hpairs
    (fun i => hW.indepFun_coord_increments hab hbc hcd i)
  have hmeasE : Measurable fun v : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin 2) ℝ).symm v :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.measurable
  have hcomp := hpi.comp hmeasE hmeasE
  have h1 : (fun ω => W b ω - W a ω)
      = (fun v : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin 2) ℝ).symm v) ∘
        fun ω (i : Fin 2) => W b ω i - W a ω i := by
    funext ω
    ext i
    simp
  have h2 : (fun ω => W d ω - W c ω)
      = (fun v : Fin 2 → ℝ => (EuclideanSpace.equiv (Fin 2) ℝ).symm v) ∘
        fun ω (i : Fin 2) => W d ω i - W c ω i := by
    funext ω
    ext i
    simp
  rw [h1, h2]
  exact hcomp

/-- `thm:gaussian-four-point`, first assertion: increments over intervals with disjoint
interiors are independent.  The endpoints are unoriented, as in the paper. -/
theorem disjoint_increments_indep {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {t u t' u' : ℝ≥0}
    (hdisj : max t u ≤ min t' u' ∨ max t' u' ≤ min t u) :
    IndepFun (fun ω => W u ω - W t ω) (fun ω => W u' ω - W t' ω) P := by
  have hneg : ∀ x y : ℝ≥0, (fun ω => W x ω - W y ω) = -fun ω => W y ω - W x ω := by
    intro x y
    funext ω
    simp only [Pi.neg_apply, neg_sub]
  have main : ∀ v w v' w' : ℝ≥0, max v w ≤ min v' w' →
      IndepFun (fun ω => W w ω - W v ω) (fun ω => W w' ω - W v' ω) P := by
    intro v w v' w' h
    have key := hW.indepFun_increments (a := min v w) (b := max v w) (c := min v' w')
      (d := max v' w') min_le_max h min_le_max
    rcases le_total v w with hvw | hvw <;> rcases le_total v' w' with hvw' | hvw'
    · rwa [min_eq_left hvw, max_eq_right hvw, min_eq_left hvw', max_eq_right hvw'] at key
    · rw [min_eq_left hvw, max_eq_right hvw, min_eq_right hvw', max_eq_left hvw'] at key
      rw [hneg w' v']
      exact key.neg_right
    · rw [min_eq_right hvw, max_eq_left hvw, min_eq_left hvw', max_eq_right hvw'] at key
      rw [hneg w v]
      exact key.neg_left
    · rw [min_eq_right hvw, max_eq_left hvw, min_eq_right hvw', max_eq_left hvw'] at key
      rw [hneg w v, hneg w' v']
      exact key.neg_left.neg_right
  rcases hdisj with h | h
  · exact main t u t' u' h
  · exact (main t' u' t u h).symm

end Increments


/-! ### `sec:setup`: the planar return probability -/

section Return

variable {P : Measure Ω} {W : ℝ≥0 → Ω → Plane}

/-- The law of a planar Brownian increment: the two coordinates are independent centred
Gaussians of variance `|u - t|`, so the increment has the product law. -/
theorem IsPlanarBrownian.map_increment [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (t u : ℝ≥0) :
    P.map (fun ω => (W u ω 0 - W t ω 0, W u ω 1 - W t ω 1))
      = (gaussianReal 0 (nndist (u : ℝ) (t : ℝ))).prod
          (gaussianReal 0 (nndist (u : ℝ) (t : ℝ))) := by
  have hae : ∀ i : Fin 2, AEMeasurable (fun ω => W u ω i - W t ω i) P := fun i =>
    ((hW.coord i).toIsPreBrownianReal.aemeasurable u).sub
      ((hW.coord i).toIsPreBrownianReal.aemeasurable t)
  have hlaw : ∀ i : Fin 2, P.map (fun ω => W u ω i - W t ω i)
      = gaussianReal 0 (nndist (u : ℝ) (t : ℝ)) := fun i =>
    ((hW.coord i).toIsPreBrownianReal.hasLaw_sub u t).map_eq
  have hg : Measurable fun p : ℝ≥0 → ℝ => p u - p t :=
    (measurable_pi_apply u).sub (measurable_pi_apply t)
  have hindep : IndepFun (fun ω => W u ω 0 - W t ω 0) (fun ω => W u ω 1 - W t ω 1) P :=
    (hW.indep.comp (fun _ : Fin 2 => fun p : ℝ≥0 → ℝ => p u - p t) fun _ => hg).indepFun
      (show (0 : Fin 2) ≠ 1 by decide)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hae 0) (hae 1)).mp hindep, hlaw 0, hlaw 1]

/-- The planar return event of `eq:gaussian-reduction`, read through the law of the
increment: the probability that the increment lands in the open disc of radius `r` is the
mass of the disc for the product Gaussian. -/
theorem IsPlanarBrownian.return_eq_gaussian [IsProbabilityMeasure P]
    (hW : IsPlanarBrownian W P) {r : ℝ} (hr : 0 < r) (t u : ℝ≥0) :
    P {ω | dist (W u ω) (W t ω) < r}
      = ((gaussianReal 0 (nndist (u : ℝ) (t : ℝ))).prod
          (gaussianReal 0 (nndist (u : ℝ) (t : ℝ))))
          {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} := by
  have hae : ∀ i : Fin 2, AEMeasurable (fun ω => W u ω i - W t ω i) P := fun i =>
    ((hW.coord i).toIsPreBrownianReal.aemeasurable u).sub
      ((hW.coord i).toIsPreBrownianReal.aemeasurable t)
  have hlaw : HasLaw (fun ω => (W u ω 0 - W t ω 0, W u ω 1 - W t ω 1))
      ((gaussianReal 0 (nndist (u : ℝ) (t : ℝ))).prod
        (gaussianReal 0 (nndist (u : ℝ) (t : ℝ)))) P :=
    ⟨(hae 0).prodMk (hae 1), hW.map_increment t u⟩
  have hmeas : MeasurableSet {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hset : {ω | dist (W u ω) (W t ω) < r}
      = {ω | (W u ω 0 - W t ω 0) ^ 2 + (W u ω 1 - W t ω 1) ^ 2 < r ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq, EuclideanSpace.dist_eq, Real.dist_eq, Fin.sum_univ_two,
      sq_abs]
    exact Real.sqrt_lt' hr
  rw [hset]
  exact hlaw.measure_eq hmeas

/-- The radial integral behind the planar return probability of
`eq:gaussian-reduction`: `∫₀^r ρ e^{-ρ²/(2v)} dρ = v(1 - e^{-r²/(2v)})`. -/
theorem integral_radial {v : ℝ} (hv : 0 < v) {r : ℝ} (hr : 0 < r) :
    ∫ ρ in Set.Ioo (0 : ℝ) r, ρ * Real.exp (-ρ ^ 2 / (2 * v))
      = v * (1 - Real.exp (-r ^ 2 / (2 * v))) := by
  have hv' : v ≠ 0 := ne_of_gt hv
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt (fun y : ℝ => -v * Real.exp (-y ^ 2 / (2 * v)))
        (x * Real.exp (-x ^ 2 / (2 * v))) x := by
    intro x _
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * v)) (-(2 * x) / (2 * v)) x :=
      hp.neg.div_const (2 * v)
    have h3 : HasDerivAt (fun y : ℝ => -v * Real.exp (-y ^ 2 / (2 * v)))
        (-v * (Real.exp (-x ^ 2 / (2 * v)) * (-(2 * x) / (2 * v)))) x :=
      h1.exp.const_mul (-v)
    have heq : -v * (Real.exp (-x ^ 2 / (2 * v)) * (-(2 * x) / (2 * v)))
        = x * Real.exp (-x ^ 2 / (2 * v)) := by
      field_simp
    rw [← heq]
    exact h3
  have hcont : ContinuousOn (fun ρ : ℝ => ρ * Real.exp (-ρ ^ 2 / (2 * v)))
      (Set.uIcc 0 r) := by fun_prop
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp
  ring

/-- The polar identity behind the change of variables. -/
theorem sq_polar (ρ θ : ℝ) : (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 := by
  calc (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2
      = ρ ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = ρ ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- The product of the two coordinate densities of a centred planar Gaussian, in polar
coordinates. -/
theorem gaussianPDFReal_polar {v : ℝ≥0} (ρ θ : ℝ) :
    gaussianPDFReal 0 v (ρ * Real.cos θ) * gaussianPDFReal 0 v (ρ * Real.sin θ)
      = (2 * Real.pi * (v : ℝ))⁻¹ * Real.exp (-ρ ^ 2 / (2 * (v : ℝ))) := by
  have hA : (0 : ℝ) ≤ 2 * Real.pi * (v : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi * (v : ℝ)) * Real.sqrt (2 * Real.pi * (v : ℝ))
      = 2 * Real.pi * (v : ℝ) := Real.mul_self_sqrt hA
  have hexp : -(ρ * Real.cos θ - 0) ^ 2 / (2 * (v : ℝ))
      + -(ρ * Real.sin θ - 0) ^ 2 / (2 * (v : ℝ)) = -ρ ^ 2 / (2 * (v : ℝ)) := by
    rw [sub_zero, sub_zero, ← add_div]
    congr 1
    have h := sq_polar ρ θ
    linarith
  rw [gaussianPDFReal, gaussianPDFReal,
    show ∀ a b c : ℝ, c * a * (c * b) = c * c * (a * b) from fun a b c => by ring,
    ← Real.exp_add, hexp, ← mul_inv, hsqrt]

/-- The mass of the open disc of radius `r` for the centred planar Gaussian with
independent coordinates of variance `v`: the return probability `1 - e^{-r²/(2v)}` of
`eq:gaussian-reduction`, computed in polar coordinates. -/
theorem gaussian_prod_disc {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)) {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2}
      = ENNReal.ofReal (1 - Real.exp (-r ^ 2 / (2 * (v : ℝ)))) := by
  have hV : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hv)
  have hS : MeasurableSet {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hRect : MeasurableSet (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  rw [gaussianReal_of_var_ne_zero 0 hv,
    prod_withDensity (measurable_gaussianPDF 0 v) (measurable_gaussianPDF 0 v),
    withDensity_apply _ hS, ← Measure.volume_eq_prod, ← lintegral_indicator hS,
    ← lintegral_comp_polarCoord_symm,
    ← lintegral_indicator polarCoord.open_target.measurableSet]
  have hind : (fun p : ℝ × ℝ => Set.indicator polarCoord.target
        (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
          Set.indicator {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2}
            (fun z : ℝ × ℝ => gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2)
            (polarCoord.symm p)) p)
      = Set.indicator (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi)
          (fun p : ℝ × ℝ => ENNReal.ofReal ((2 * Real.pi * (v : ℝ))⁻¹ *
            (p.1 * Real.exp (-p.1 ^ 2 / (2 * (v : ℝ)))))) := by
    funext p
    by_cases hp : p ∈ polarCoord.target
    · have hp1 : (0 : ℝ) < p.1 := hp.1
      have hp2 : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
      rw [Set.indicator_of_mem hp]
      by_cases hlt : p.1 < r
      · have hmemR : p ∈ Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi := ⟨⟨hp1, hlt⟩, hp2⟩
        have hmemS : polarCoord.symm p ∈ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} := by
          simp only [polarCoord_symm_apply, Set.mem_setOf_eq, sq_polar]
          nlinarith
        rw [Set.indicator_of_mem hmemR, Set.indicator_of_mem hmemS, polarCoord_symm_apply,
          gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
          gaussianPDFReal_polar, smul_eq_mul,
          ← ENNReal.ofReal_mul hp1.le]
        congr 1
        ring
      · have hnotR : p ∉ Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi := by
          intro hmem
          exact hlt hmem.1.2
        have hnotS : polarCoord.symm p ∉ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} := by
          simp only [polarCoord_symm_apply, Set.mem_setOf_eq, sq_polar, not_lt]
          nlinarith [not_lt.mp hlt]
        rw [Set.indicator_of_notMem hnotR, Set.indicator_of_notMem hnotS]
        simp
    · have hnotR : p ∉ Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hmem
        exact hp ⟨Set.mem_Ioi.mpr hmem.1.1, hmem.2⟩
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hnotR]
  rw [hind, lintegral_indicator hRect, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop)]
  have hinner : ∀ x : ℝ, ∫⁻ _ in Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal ((2 * Real.pi * (v : ℝ))⁻¹ * (x * Real.exp (-x ^ 2 / (2 * (v : ℝ)))))
      = ENNReal.ofReal ((2 * Real.pi * (v : ℝ))⁻¹ * (x * Real.exp (-x ^ 2 / (2 * (v : ℝ)))))
        * ENNReal.ofReal (2 * Real.pi) := by
    intro x
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    congr 1
    ring_nf
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop)]
  have hint : IntegrableOn
      (fun x : ℝ => (2 * Real.pi * (v : ℝ))⁻¹ * (x * Real.exp (-x ^ 2 / (2 * (v : ℝ)))))
      (Set.Ioo (0 : ℝ) r) := by
    have hIcc : IntegrableOn
        (fun x : ℝ => (2 * Real.pi * (v : ℝ))⁻¹ * (x * Real.exp (-x ^ 2 / (2 * (v : ℝ)))))
        (Set.Icc (0 : ℝ) r) := ContinuousOn.integrableOn_Icc (by fun_prop)
    exact hIcc.mono_set Set.Ioo_subset_Icc_self
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) r)]
      fun x : ℝ => (2 * Real.pi * (v : ℝ))⁻¹ * (x * Real.exp (-x ^ 2 / (2 * (v : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    simp only [Pi.zero_apply]
    positivity
  have hneg : -r ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    have hq : (0 : ℝ) ≤ r ^ 2 / (2 * (v : ℝ)) := by positivity
    rw [neg_div]
    linarith
  have hexpnn : (0 : ℝ) ≤ 1 - Real.exp (-r ^ 2 / (2 * (v : ℝ))) := by
    have := Real.exp_le_one_iff.mpr hneg
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_radial hV hr,
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (mul_nonneg hV.le hexpnn))]
  congr 1
  field_simp

/-- `eq:gaussian-reduction`, the planar return probability: for distinct times the
probability that the Brownian increment stays within `r` is `1 - e^{-r²/(2|u-t|)}`. -/
theorem IsPlanarBrownian.return_prob [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {r : ℝ} (hr : 0 < r) {t u : ℝ≥0} (htu : t ≠ u) :
    P {ω | dist (W u ω) (W t ω) < r}
      = ENNReal.ofReal (1 - Real.exp (-(r ^ 2 / (2 * |(u : ℝ) - (t : ℝ)|)))) := by
  have hut : (u : ℝ) ≠ (t : ℝ) := fun h => htu (NNReal.coe_injective h).symm
  have hne : nndist (u : ℝ) (t : ℝ) ≠ 0 := fun h => hut (nndist_eq_zero.mp h)
  have hcoe : ((nndist (u : ℝ) (t : ℝ) : ℝ≥0) : ℝ) = |(u : ℝ) - (t : ℝ)| := by
    rw [coe_nndist, Real.dist_eq]
  rw [hW.return_eq_gaussian hr t u, gaussian_prod_disc hne hr, hcoe, neg_div]

end Return


end BrownianImages
