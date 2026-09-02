/-
`sec:smoothing` of `BrownianImagesComplete.tex`: `eq:gb-limit` and
`thm:profile-asymptotics` as one statement.

`eq:gb-limit` is `thm:non-lattice-limit` read at the paired system.  The support of `ϑ`
is `{log 2, log(1/c)}`, so `eq:non-lattice` is exactly the non-arithmetic hypothesis of
that lemma: `pairSystem_nonArithmetic_iff` is the conversion, and
`pairSystem_isDimension`, `pairSystem_stronglySeparated` and the attractor sitting in
`[0,1]` are the remaining inputs.

The bundle `thm:profile-asymptotics` carries the renewal constant `C_B` of
`eq:gb-limit` through all three conclusions about `μ_B`.  `profile_asymptotics_nonLattice`
supplies `eq:hb-asymptotic` and `non_lattice_correlation_limit_const` the limit of the
normalised correlation integral, with the same constant `C_B ∫₀^∞ φ` in both; the `μ_A`
half is `exists_periodic_profile`, `profile_asymptotics_lattice` and
`lattice_correlation_oscillation`.

`thm:non-lattice-limit` itself, the endpoint `audit_non_lattice_limit`, is open, so both
results here carry its conclusion as an explicit hypothesis `hlim`, in the shape
`Challenge.lean` states it.  The alphabet of `hlim` is `Type` rather than `Type*`: a
`Type*` inside a hypothesis binds a universe parameter of the declaration, which the
concrete alphabet `Fin 2` of the paired system can then no longer meet.  Nothing is lost,
the endpoint being universe polymorphic, and `hlim` is discharged by the bare name
`audit_non_lattice_limit` once that endpoint is proved.

* `ProfileAsymptotics.exists_isFrostman_pair`: the internal Frostman regularity result
  for `μ_B`.
* `ProfileAsymptotics.non_lattice_correlation_limit_const`: the `μ_B` conclusion of
  `thm:profile-asymptotics` with the limit named, `C ∫₀^∞ φ` rather than some `L > 0`.
* `gb_limit_of_non_lattice_limit`: `eq:gb-limit`.
* `thm_profile_asymptotics_of_non_lattice_limit`: `thm:profile-asymptotics`, bundled.
-/
import BrownianImages.Endpoints

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ProfileAsymptotics

/-- The natural measure `μ_B` of the paired system is `s`-Frostman.
The paired system is strongly separated with gap `1/2 - c` on its attractor, which sits
in `[0,1]`. -/
theorem exists_isFrostman_pair {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one)).IsNatural KB sCantor μB) :
    ∃ A : ℝ, IsFrostman sCantor A μB :=
  AhlforsRegular.exists_isFrostman_of_isNatural sCantor_pos
    (pairSystem_stronglySeparated (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one) hB.attractor.2.2.1) hB

set_option linter.unusedVariables false in
/-- `thm:profile-asymptotics`, the conclusion for `μ_B` with the limit named: the
normalised expected correlation integral converges to `C ∫₀^∞ φ`, the same constant
`eq:hb-asymptotic` produces.  `audit_non_lattice_correlation_limit` asserts only that
some positive limit exists; the bundle needs the value, so it is proved here from
`eq:smoothing` and `eq:hb-asymptotic` directly. -/
theorem non_lattice_correlation_limit_const {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s C A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (hCpos : 0 < C) :
    Tendsto (fun r : ℝ => expCorr W P μ r / r ^ (2 * s)) (𝓝[>] 0)
      (𝓝 (C * ∫ η in Set.Ioi (0:ℝ), kern s η)) := by
  obtain ⟨hLpos, hLtend⟩ := profile_asymptotics_nonLattice hs0 hs1 hμ hCpos hC
  have hlog : Tendsto (fun r : ℝ => Real.log r⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  refine Filter.Tendsto.congr' ?_ (hLtend.comp hlog)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  have hrpow : (0:ℝ) < r ^ (2 * s) := Real.rpow_pos_of_pos hr0 _
  rw [Function.comp_apply, (gaussian_reduction hW hs0 hs1 hμ hr0).2,
    Rescaling.integral_ret_pairLaw hs0 hs1 hμ hr0]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hrpow)]

end ProfileAsymptotics

set_option linter.unusedVariables false in
/-- `eq:gb-limit`: under `eq:non-lattice` the normalised profile of `μ_B` converges to a
finite positive constant.  This is `thm:non-lattice-limit` at the paired system, whose
log-ratios are `log 2` and `log(1/c)`, so that `eq:non-lattice` is its non-arithmetic
hypothesis by `pairSystem_nonArithmetic_iff`.  `hlim` is the conclusion of
`audit_non_lattice_limit`, which is open. -/
theorem gb_limit_of_non_lattice_limit
    (hlim : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (S : System ι)
      {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
      (hdim : S.IsDimension s) (hna : S.NonArithmetic)
      {μ : Measure ℝ} (hμ : S.IsNatural K s μ),
      0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
        Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)))
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one)).IsNatural KB sCantor μB)
    (hnl : Irrational (Real.log (pairRatio sCantor)⁻¹ / Real.log 2)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (G sCantor μB) atTop (𝓝 C) := by
  obtain ⟨hpos, htend⟩ :=
    hlim (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
        (pairRatio_lt_half sCantor_pos sCantor_lt_one))
      sCantor_pos sCantor_lt_one
      (pairSystem_stronglySeparated (pairRatio_pos sCantor_pos)
        (pairRatio_lt_half sCantor_pos sCantor_lt_one) hB.attractor.2.2.1)
      (pairSystem_isDimension sCantor_pos sCantor_lt_one)
      ((pairSystem_nonArithmetic_iff sCantor_pos sCantor_lt_one).mpr hnl) hB
  exact ⟨_, hpos, htend⟩

set_option linter.unusedVariables false in
/-- `thm:profile-asymptotics` as one statement, on the paper's hypotheses: the natural
measures of the two systems and `eq:non-lattice`.  The renewal constant `C_B` of
`eq:gb-limit` is carried through all three conclusions about `μ_B`: it is the limit of
`G_B`, and `C_B ∫₀^∞ φ` is the limit both of `H_B` and of the normalised correlation
integral.  `hlim` is the conclusion of `audit_non_lattice_limit`, which is open; the
`μ_A` half does not use it. -/
theorem thm_profile_asymptotics_of_non_lattice_limit
    (hlim : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (S : System ι)
      {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
      (hdim : S.IsDimension s) (hna : S.NonArithmetic)
      {μ : Measure ℝ} (hμ : S.IsNatural K s μ),
      0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
        Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)))
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {KA : Set ℝ} {μA : Measure ℝ} (hA : cantorSystem.IsNatural KA sCantor μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one)).IsNatural KB sCantor μB)
    (hnl : Irrational (Real.log (pairRatio sCantor)⁻¹ / Real.log 2)) :
    (∃ CB : ℝ, 0 < CB ∧
        Tendsto (G sCantor μB) atTop (𝓝 CB) ∧
        Tendsto (H sCantor μB) atTop (𝓝 (CB * ∫ η in Set.Ioi (0:ℝ), kern sCantor η)) ∧
        0 < CB * ∫ η in Set.Ioi (0:ℝ), kern sCantor η ∧
        Tendsto (fun r : ℝ => expCorr W P μB r / r ^ (2 * sCantor)) (𝓝[>] 0)
          (𝓝 (CB * ∫ η in Set.Ioi (0:ℝ), kern sCantor η))) ∧
      (∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log 3) ∧
        (∀ w, Real.log 3 ≤ w → g w = G sCantor μA w) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 0 ≤ v →
          |H sCantor μA v - smoothOp sCantor g v|
            ≤ C * Real.exp (-2 * (1 - sCantor) * v)) ∧
      (∃ a b : ℝ, a < b ∧
        (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧ expCorr W P μA r ≤ a * r ^ (2 * sCantor)) ∧
        (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧ b * r ^ (2 * sCantor) ≤ expCorr W P μA r)) := by
  haveI := hB.isProbabilityMeasure
  obtain ⟨CB, hCBpos, hCB⟩ := gb_limit_of_non_lattice_limit hlim hB hnl
  obtain ⟨AB, hFrostB⟩ := ProfileAsymptotics.exists_isFrostman_pair hB
  obtain ⟨hposB, hHB⟩ :=
    profile_asymptotics_nonLattice sCantor_pos sCantor_lt_one hFrostB hCBpos hCB
  refine ⟨⟨CB, hCBpos, hCB, hHB, hposB,
    ProfileAsymptotics.non_lattice_correlation_limit_const hW sCantor_pos sCantor_lt_one
      hFrostB hCB hCBpos⟩, ?_, lattice_correlation_oscillation hW hA⟩
  obtain ⟨g, hg, hper, hagree, -, -⟩ := exists_periodic_profile hA
  obtain ⟨C, hC0, hCbd⟩ := profile_asymptotics_lattice hA hg hper hagree
  exact ⟨g, hg, hper, hagree, C, hC0, hCbd⟩

end BrownianImages
