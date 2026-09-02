/-
`sec:concentration`: `thm:cantor-application`, the second headline result of the paper.
The middle-thirds Cantor measure separates from the natural measure of every strongly
separated non-arithmetic system of the same dimension, and in particular from the paired
measure `μ_B` under `eq:non-lattice`.

* `CantorApplication.exists_separation_of_oscillation`: a profile that oscillates by a
  fixed amount past every threshold separates, in the sense of `eq:profile-separation`,
  from a profile that converges.
* `CantorApplication.exists_profile_oscillation`: `eq:ha-asymptotic` and `eq:lattice-gap`
  put the expected profile of `μ_A` in that first class, with the explicit gap `d_A/2`.
* `cantor_application_of_endpoints`: `thm:cantor-application`, on `audit_main` and
  `audit_non_lattice_limit` as explicit hypotheses, each carrying the statement text of
  its endpoint.
* `cantor_application_pair_of_endpoints`: the named instance of its last sentence, on
  the same two hypotheses.
-/
import BrownianImages.Endpoints

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace CantorApplication

/-- `eq:profile-separation` from an oscillation and a limit: if `H₁` takes, past every
threshold, two values differing by at least `d`, and `H₂` converges, then the two
profiles separate.  Past the threshold where `H₂` has settled to within `d/8` of its
limit the triangle inequality forces a gap of `d/4` at one of the two times. -/
theorem exists_separation_of_oscillation {H₁ H₂ : ℝ → ℝ} {d L : ℝ} (hd : 0 < d)
    (hosc : ∀ V : ℝ, ∃ v₁ ≥ V, ∃ v₂ ≥ V, d ≤ H₁ v₁ - H₁ v₂)
    (hlim : Tendsto H₂ atTop (𝓝 L)) :
    ∃ ε > 0, ∀ V : ℝ, ∃ v ≥ V, ε ≤ |H₁ v - H₂ v| := by
  refine ⟨d / 4, by linarith, ?_⟩
  have hev : ∀ᶠ v in atTop, |H₂ v - L| ≤ d / 8 := by
    have hball := hlim (Metric.closedBall_mem_nhds L (by linarith : (0:ℝ) < d / 8))
    filter_upwards [hball] with v hv
    simpa [Metric.mem_closedBall, Real.dist_eq] using hv
  obtain ⟨V₀, hV₀⟩ := Filter.eventually_atTop.mp hev
  intro V
  obtain ⟨v₁, hv₁, v₂, hv₂, hdiff⟩ := hosc (max V V₀)
  have hv₁V : V ≤ v₁ := le_trans (le_max_left _ _) hv₁
  have hv₂V : V ≤ v₂ := le_trans (le_max_left _ _) hv₂
  have hb₁ := abs_le.mp (hV₀ v₁ (le_trans (le_max_right _ _) hv₁))
  have hb₂ := abs_le.mp (hV₀ v₂ (le_trans (le_max_right _ _) hv₂))
  by_cases hcase : d / 4 ≤ |H₁ v₁ - H₂ v₁|
  · exact ⟨v₁, hv₁V, hcase⟩
  · refine ⟨v₂, hv₂V, ?_⟩
    by_contra hcon
    have h₁ := abs_lt.mp (not_le.mp hcase)
    have h₂ := abs_lt.mp (not_le.mp hcon)
    linarith [h₁.1, h₁.2, h₂.1, h₂.2, hb₁.1, hb₁.2, hb₂.1, hb₂.2]

/-- `eq:ha-asymptotic` and `eq:lattice-gap`: the expected profile of the middle-thirds
measure oscillates by a fixed amount past every threshold.  The gap is half the
oscillation `d_A` of the smoothed periodic profile `T G̃_A` over a period, which
`eq:lattice-gap` makes strictly positive; the error term of `eq:ha-asymptotic` is below
`d_A/4` far out, and the extrema of `T G̃_A` recur at every period. -/
theorem exists_profile_oscillation {KA : Set ℝ} {μA : Measure ℝ}
    (hA : cantorSystem.IsNatural KA sCantor μA) :
    ∃ d > 0, ∀ V : ℝ, ∃ v₁ ≥ V, ∃ v₂ ≥ V, d ≤ H sCantor μA v₁ - H sCantor μA v₂ := by
  obtain ⟨g, hg, hper, hagree, -, hgne⟩ := exists_periodic_profile hA
  have hlog3 : (0:ℝ) < Real.log 3 := log_three_pos
  have hhalf : (0:ℝ) < Real.log 3 / 2 := by linarith
  obtain ⟨C, hC0, hCbd⟩ := profile_asymptotics_lattice hA hg hper hagree
  have hne := smoothOp_nonconstant sCantor_pos sCantor_lt_one hlog3 hg hper hgne
  obtain ⟨va, -, vb, -, hgap, -⟩ :=
    smoothOp_gap sCantor_pos sCantor_lt_one hlog3 hg hper hne
  have hTper : Function.Periodic (smoothOp sCantor g) (Real.log 3 / 2) :=
    smoothOp_periodic hper
  set d₀ : ℝ := smoothOp sCantor g va - smoothOp sCantor g vb with hd₀def
  -- far enough out the error term of `eq:ha-asymptotic` is below `d₀/4`
  have hdecay : ∀ᶠ v in atTop, C * Real.exp (-2 * (1 - sCantor) * v) ≤ d₀ / 4 := by
    have hneg : -2 * (1 - sCantor) < 0 := by
      have := sCantor_lt_one; nlinarith
    have h1 : Tendsto (fun v : ℝ => -2 * (1 - sCantor) * v) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id
    have h2 : Tendsto (fun v : ℝ => C * Real.exp (-2 * (1 - sCantor) * v)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp h1).const_mul C
      simpa using this
    exact h2.eventually_le_const (by linarith : (0:ℝ) < d₀ / 4)
  obtain ⟨V₀, hV₀⟩ := Filter.eventually_atTop.mp hdecay
  refine ⟨d₀ / 2, by linarith, ?_⟩
  intro V
  obtain ⟨n₁, hn₁⟩ := Rescaling.exists_far (v₀ := va) hhalf (max V (max 0 V₀))
  obtain ⟨n₂, hn₂⟩ := Rescaling.exists_far (v₀ := vb) hhalf (max V (max 0 V₀))
  refine ⟨va + n₁ * (Real.log 3 / 2), le_trans (le_max_left _ _) hn₁,
    vb + n₂ * (Real.log 3 / 2), le_trans (le_max_left _ _) hn₂, ?_⟩
  have hb₁ : |H sCantor μA (va + n₁ * (Real.log 3 / 2)) - smoothOp sCantor g va|
      ≤ d₀ / 4 := by
    have hz : (0:ℝ) ≤ va + n₁ * (Real.log 3 / 2) :=
      le_trans (le_trans (le_max_left 0 V₀) (le_max_right V _)) hn₁
    have hV : V₀ ≤ va + n₁ * (Real.log 3 / 2) :=
      le_trans (le_trans (le_max_right 0 V₀) (le_max_right V _)) hn₁
    have := le_trans (hCbd _ hz) (hV₀ _ hV)
    rwa [hTper.nat_mul n₁ va] at this
  have hb₂ : |H sCantor μA (vb + n₂ * (Real.log 3 / 2)) - smoothOp sCantor g vb|
      ≤ d₀ / 4 := by
    have hz : (0:ℝ) ≤ vb + n₂ * (Real.log 3 / 2) :=
      le_trans (le_trans (le_max_left 0 V₀) (le_max_right V _)) hn₂
    have hV : V₀ ≤ vb + n₂ * (Real.log 3 / 2) :=
      le_trans (le_trans (le_max_right 0 V₀) (le_max_right V _)) hn₂
    have := le_trans (hCbd _ hz) (hV₀ _ hV)
    rwa [hTper.nat_mul n₂ vb] at this
  have h₁ := abs_le.mp hb₁
  have h₂ := abs_le.mp hb₂
  linarith [h₁.1, h₂.2]

/-- The expected profile of the homogeneous measure oscillates by a fixed amount past
every threshold, uniformly for `0 < λ < 1/2`. -/
theorem homogeneous_exists_profile_oscillation {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    ∃ d > 0, ∀ V : ℝ, ∃ v₁ ≥ V, ∃ v₂ ≥ V,
      d ≤ H (homogeneousDim lam) μA v₁ - H (homogeneousDim lam) μA v₂ := by
  let s := homogeneousDim lam
  let p := Real.log lam⁻¹
  have hs0 : 0 < s := homogeneousDim_pos hlam0 hlam
  have hs1 : s < 1 := homogeneousDim_lt_one hlam0 hlam
  have hp : 0 < p := log_inv_pos hlam0 hlam
  obtain ⟨g, hg, hper, hagree, -, hgne⟩ := homogeneous_periodic_profile hlam0 hlam hA
  haveI := hA.isProbabilityMeasure
  obtain ⟨C, hC0, hCbd⟩ := exists_lattice_bound hs0 hs1 (μ := μA)
    hg hp.ne' hper hagree
  have hhalf : (0:ℝ) < p / 2 := by linarith
  have hne := smoothOp_nonconstant hs0 hs1 hp hg hper hgne
  obtain ⟨va, -, vb, -, hgap, -⟩ := smoothOp_gap hs0 hs1 hp hg hper hne
  have hTper : Function.Periodic (smoothOp s g) (p / 2) := smoothOp_periodic hper
  set d₀ : ℝ := smoothOp s g va - smoothOp s g vb with hd₀def
  have hdecay : ∀ᶠ v in atTop, C * Real.exp (-2 * (1 - s) * v) ≤ d₀ / 4 := by
    have hneg : -2 * (1 - s) < 0 := by linarith
    have h1 : Tendsto (fun v : ℝ => -2 * (1 - s) * v) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id
    have h2 : Tendsto (fun v : ℝ => C * Real.exp (-2 * (1 - s) * v)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
    exact h2.eventually_le_const (by linarith : (0:ℝ) < d₀ / 4)
  obtain ⟨V₀, hV₀⟩ := Filter.eventually_atTop.mp hdecay
  refine ⟨d₀ / 2, by linarith, ?_⟩
  intro V
  obtain ⟨n₁, hn₁⟩ := Rescaling.exists_far (v₀ := va) hhalf (max V (max 0 V₀))
  obtain ⟨n₂, hn₂⟩ := Rescaling.exists_far (v₀ := vb) hhalf (max V (max 0 V₀))
  refine ⟨va + n₁ * (p / 2), le_trans (le_max_left _ _) hn₁,
    vb + n₂ * (p / 2), le_trans (le_max_left _ _) hn₂, ?_⟩
  have hb₁ : |H s μA (va + n₁ * (p / 2)) - smoothOp s g va| ≤ d₀ / 4 := by
    have hV : V₀ ≤ va + n₁ * (p / 2) :=
      le_trans (le_trans (le_max_right 0 V₀) (le_max_right V _)) hn₁
    have := le_trans (hCbd _) (hV₀ _ hV)
    rwa [hTper.nat_mul n₁ va] at this
  have hb₂ : |H s μA (vb + n₂ * (p / 2)) - smoothOp s g vb| ≤ d₀ / 4 := by
    have hV : V₀ ≤ vb + n₂ * (p / 2) :=
      le_trans (le_trans (le_max_right 0 V₀) (le_max_right V _)) hn₂
    have := le_trans (hCbd _) (hV₀ _ hV)
    rwa [hTper.nat_mul n₂ vb] at this
  have h₁ := abs_le.mp hb₁
  have h₂ := abs_le.mp hb₂
  linarith [h₁.1, h₂.2]

end CantorApplication

set_option linter.unusedVariables false in
/-- `thm:cantor-application`.  The middle-thirds Cantor measure separates from the
natural measure of every strongly separated non-arithmetic system of the same dimension.
Strong separation of the middle-thirds system itself is not a hypothesis: it is
`cantorSystem_stronglySeparated`.  The two open endpoints `audit_non_lattice_limit` and
`audit_main` enter as explicit hypotheses, in their own statement text: the index type of
the first is the ambient one, since a second `Type*` binder would sit in a second
universe and no application could reach it. -/
theorem cantor_application_of_endpoints {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {KA : Set ℝ} {μA : Measure ℝ} (hA : cantorSystem.IsNatural KA sCantor μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hna : S.NonArithmetic)
    (hdim : S.IsDimension sCantor) {μ : Measure ℝ} (hμ : S.IsNatural K sCantor μ)
    (hlimit : ∀ (S : System ι)
      {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
      (hdim : S.IsDimension s) (hna : S.NonArithmetic)
      {μ : Measure ℝ} (hμ : S.IsNatural K s μ),
      0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
        Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)))
    (hmain : ∀ {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
      (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
      {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
      (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|),
      (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) := by
  haveI := hA.isProbabilityMeasure
  haveI := hμ.isProbabilityMeasure
  obtain ⟨AA, hFrostA⟩ := AhlforsRegular.exists_isFrostman_of_isNatural sCantor_pos
    (cantorSystem_stronglySeparated hA.attractor.2.2.1) hA
  obtain ⟨A, hFrost⟩ :=
    AhlforsRegular.exists_isFrostman_of_isNatural sCantor_pos hsep hμ
  obtain ⟨hCpos, hC⟩ := hlimit S sCantor_pos sCantor_lt_one hsep hdim hna hμ
  obtain ⟨-, hHlim⟩ :=
    profile_asymptotics_nonLattice sCantor_pos sCantor_lt_one hFrost hCpos hC
  obtain ⟨d, hd, hosc⟩ := CantorApplication.exists_profile_oscillation hA
  exact hmain hW sCantor_pos sCantor_lt_one hFrostA hFrost
    (CantorApplication.exists_separation_of_oscillation hd hosc hHlim)

set_option linter.unusedVariables false in
/-- `thm:cantor-application`, the named instance of its last sentence: under
`eq:non-lattice` the paired measure `μ_B` separates from the middle-thirds measure.  The
bridge from `eq:non-lattice` to non-arithmeticity is `pairSystem_nonArithmetic_iff`, and
the two open endpoints enter as above, the index type of the first read at `Fin 2`. -/
theorem cantor_application_pair_of_endpoints {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {KA : Set ℝ} {μA : Measure ℝ} (hA : cantorSystem.IsNatural KA sCantor μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one)).IsNatural KB sCantor μB)
    (hnl : Irrational (Real.log (pairRatio sCantor)⁻¹ / Real.log 2))
    (hlimit : ∀ (S : System (Fin 2))
      {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
      (hdim : S.IsDimension s) (hna : S.NonArithmetic)
      {μ : Measure ℝ} (hμ : S.IsNatural K s μ),
      0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
        Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)))
    (hmain : ∀ {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
      (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
      {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
      (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|),
      (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) :=
  cantor_application_of_endpoints hW hA _
    (pairSystem_stronglySeparated (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one) hB.attractor.2.2.1)
    ((pairSystem_nonArithmetic_iff sCantor_pos sCantor_lt_one).mpr hnl)
    (pairSystem_isDimension sCantor_pos sCantor_lt_one) hB hlimit hmain

set_option linter.unusedVariables false in
/-- `thm:cantor-application` in the paper's parameter-uniform form.  The homogeneous
equal-weight measure at ratio `λ` separates from every strongly separated
non-arithmetic natural measure of the same dimension. -/
theorem homogeneous_application_of_endpoints {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDim lam) μ)
    (hlimit : ∀ (S : System ι)
      {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
      (hdim : S.IsDimension s) (hna : S.NonArithmetic)
      {μ : Measure ℝ} (hμ : S.IsNatural K s μ),
      0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
        Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)))
    (hmain : ∀ {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
      (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
      {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
      (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|),
      (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) := by
  have hs0 := homogeneousDim_pos hlam0 hlam
  have hs1 := homogeneousDim_lt_one hlam0 hlam
  haveI := hA.isProbabilityMeasure
  haveI := hμ.isProbabilityMeasure
  obtain ⟨AA, hFrostA⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0
    (homogeneousSystem_stronglySeparated hlam0 hlam hA.attractor.2.2.1) hA
  obtain ⟨A, hFrost⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0 hsep hμ
  obtain ⟨hCpos, hC⟩ := hlimit S hs0 hs1 hsep hdim hna hμ
  obtain ⟨-, hHlim⟩ := profile_asymptotics_nonLattice hs0 hs1 hFrost hCpos hC
  obtain ⟨d, hd, hosc⟩ :=
    CantorApplication.homogeneous_exists_profile_oscillation hlam0 hlam hA
  exact hmain hW hs0 hs1 hFrostA hFrost
    (CantorApplication.exists_separation_of_oscillation hd hosc hHlim)

set_option linter.unusedVariables false in
/-- The paired instance of the parameter-uniform application. -/
theorem homogeneous_application_pair_of_endpoints {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2))
    (hlimit : ∀ (S : System (Fin 2))
      {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
      (hdim : S.IsDimension s) (hna : S.NonArithmetic)
      {μ : Measure ℝ} (hμ : S.IsNatural K s μ),
      0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
        Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)))
    (hmain : ∀ {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
      (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
      {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
      (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|),
      (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) :=
  homogeneous_application_of_endpoints hW hlam0 hlam hA _
    (pairSystem_stronglySeparated (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam)) hB.attractor.2.2.1)
    ((pairSystem_nonArithmetic_iff (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam)).mpr hnl)
    (pairSystem_isDimension (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam)) hB hlimit hmain

end BrownianImages
