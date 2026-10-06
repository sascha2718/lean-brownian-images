/-
Comparator solution file, and the formal statement of the paper: every numbered
result of `BrownianImagesComplete.tex`, together with the displayed claims that a
later result cites or that carry a hypothesis of their own, stated as `audit_*`
endpoints and proved by the library declarations.  It is not every display:
`docs/correspondence.md` says which are covered by a neighbouring endpoint instead,
and which displays are not formalised.

`Challenge.lean` restates the headline theorems, `thm:main`,
`thm:cantor-application` and `thm:two-contraction-distinction`, on Mathlib-only copies
of the definitions;
`comparator-config.json` lists those endpoint names.  Comparator checks each listed
statement against `Challenge.lean`, audits the axioms of the proofs, and replays
them through the kernel.  For the listed endpoints the statement text must stay
character-for-character identical to `Challenge.lean`.
-/
import BrownianImages
import BrownianImages.Minkowski.Profile
import BrownianImages.Minkowski.Reconstruction

-- the statement text is frozen against `Challenge.lean`, so unused binders stay
set_option linter.unusedVariables false

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics TopologicalSpace
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Expected profiles and the two named measures -/

/-- `eq:expected-profile`: the normalised expected correlation profile
`H_μ^s(t) = e^{2st} 𝔼 C_{e^{-t}}(W_*μ)`. -/
noncomputable def expectedProfile (W : ℝ≥0 → Ω → Plane) (P : Measure Ω)
    (s : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  Real.exp (2 * s * t) * ∫ ω, (corr (occupation W μ ω) (Real.exp (-t))).toReal ∂P

/-- The similarity dimension `log 2 / log (1/λ)` of the homogeneous system. -/
noncomputable def homogeneousDimension (lam : ℝ) : ℝ := Real.log 2 / Real.log lam⁻¹

/-- The contraction ratio `c` of `eq:c-definition`: the solution of `c^s = 1 - 2^{-s}`. -/
noncomputable def pairedRatio (s : ℝ) : ℝ := (1 - (2:ℝ) ^ (-s)) ^ s⁻¹

/-- `sec:introduction`: the homogeneous equal-weight probability measure `μ_A`
on `[0,1]`, invariant under `x ↦ λx` and `x ↦ λx + 1 - λ`. -/
structure IsHomogeneousMeasure (lam : ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The measure is carried by the unit interval. -/
  support : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- The invariance equation with equal weights. -/
  selfSimilar : μ = ENNReal.ofReal (1/2) • μ.map (fun x => lam * x) +
    ENNReal.ofReal (1/2) • μ.map (fun x => lam * x + (1 - lam))

/-- `sec:introduction`: the paired probability measure `μ_B` on `[0,1]`, with
maps `x ↦ x/2`, `x ↦ cx + 1 - c` and weights `2^{-s}`, `c^s`, where `c = pairedRatio s`. -/
structure IsPairMeasure (s : ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The measure is carried by the unit interval. -/
  support : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- The invariance equation with the similarity weights. -/
  selfSimilar : μ = ENNReal.ofReal ((1/2 : ℝ) ^ s) • μ.map (fun x => 1/2 * x) +
    ENNReal.ofReal (pairedRatio s ^ s) • μ.map (fun x => pairedRatio s * x + (1 - pairedRatio s))

/-- `sec:introduction`: the natural probability measure `μ_c` on `[0,1]` of the IFS
`x ↦ x/2`, `x ↦ cx + 1 - c`, with weights `2^{-s}` and `c^s`.  At the dimension `s(c)`,
where `2^{-s(c)} + c^{s(c)} = 1`, these are the `s`th powers of the contraction ratios. -/
structure IsTwoContractionMeasure (c s : ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The measure is carried by the unit interval. -/
  support : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- The invariance equation with the similarity weights. -/
  selfSimilar : μ = ENNReal.ofReal ((1/2 : ℝ) ^ s) • μ.map (fun x => 1/2 * x) +
    ENNReal.ofReal (c ^ s) • μ.map (fun x => c * x + (1 - c))

/-- `eq:smoothing` identifies the expected profile in `thm:main` with the
deterministic smoothing formula used by the library. -/
private theorem expectedProfile_eq_H {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) (t : ℝ) : expectedProfile W P s μ t = H s μ t := by
  change Real.exp (2 * s * t) * expCorr W P μ (Real.exp (-t)) = H s μ t
  rw [smoothing hW hs0 hs1 hμ (Real.exp_pos _), Real.log_inv, Real.log_exp,
    neg_neg, ← Real.exp_mul, ← mul_assoc, ← Real.exp_add,
    show 2 * s * t + -t * (2 * s) = 0 from by ring, Real.exp_zero, one_mul]

/-- Hutchinson uniqueness supplies the attractor supporting any invariant
probability measure on `[0,1]`. -/
private theorem exists_isNatural_of_selfSimilar {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : System ι) {s : ℝ} (hdim : S.IsDimension s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hself : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i))
    (hsupport : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0) : ∃ K, S.IsNatural K s μ := by
  obtain ⟨⟨K, ν⟩, hν, _⟩ := S.exists_unique_isNatural hdim
  let := hν.isProbability
  have heq := Hutchinson.eq_of_selfSimilar S hdim hself hν.selfSimilar
    hsupport hν.support_Icc
  exact ⟨K, heq ▸ hν⟩

/-- The direct definition of `μ_A` in `sec:introduction` is equivalent to the
natural measure of the bundled homogeneous system. -/
private theorem isHomogeneousMeasure_iff_exists_isNatural {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1/2) {μ : Measure ℝ} :
    IsHomogeneousMeasure lam μ ↔ ∃ K,
      (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ := by
  have hself : (μ = ∑ i, ENNReal.ofReal
      ((homogeneousSystem lam hlam0 hlam).ratio i ^ homogeneousDim lam) •
        μ.map ((homogeneousSystem lam hlam0 hlam).map i)) ↔
      μ = ENNReal.ofReal (1/2) • μ.map (fun x => lam * x) +
        ENNReal.ofReal (1/2) • μ.map (fun x => lam * x + (1 - lam)) := by
    simp only [Fin.sum_univ_two]
    rw [funext (homogeneousSystem_map_zero hlam0 hlam),
      funext (homogeneousSystem_map_one hlam0 hlam)]
    change (μ = ENNReal.ofReal (lam ^ homogeneousDim lam) • μ.map (fun x => lam * x) +
      ENNReal.ofReal (lam ^ homogeneousDim lam) • μ.map (fun x => lam * x + (1 - lam))) ↔ _
    rw [rpow_homogeneousDim hlam0 hlam]
  constructor
  · intro hμ
    let := hμ.isProbability
    exact exists_isNatural_of_selfSimilar _ (homogeneousSystem_isDimension hlam0 hlam)
      (hself.mpr hμ.selfSimilar) hμ.support
  · rintro ⟨K, hμ⟩
    exact ⟨hμ.isProbability, hμ.support_Icc, hself.mp hμ.selfSimilar⟩

/-- The direct definition of `μ_B` in `sec:introduction` is equivalent to the
natural measure of the bundled paired system; its ratio bounds follow from `0 < s < 1`. -/
private theorem isPairMeasure_iff_exists_isNatural {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {μ : Measure ℝ} :
    IsPairMeasure s μ ↔ ∃ K,
      (pairSystem (pairRatio s) (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)).IsNatural
        K s μ := by
  have hself : (μ = ∑ i, ENNReal.ofReal
      ((pairSystem (pairRatio s) (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)).ratio i ^ s) •
        μ.map ((pairSystem (pairRatio s) (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)).map i)) ↔
      μ = ENNReal.ofReal ((1/2 : ℝ) ^ s) • μ.map (fun x => 1/2 * x) +
        ENNReal.ofReal (pairRatio s ^ s) •
          μ.map (fun x => pairRatio s * x + (1 - pairRatio s)) := by
    simp only [Fin.sum_univ_two]
    rw [funext (pairSystem_map_zero (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)),
      funext (pairSystem_map_one (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1))]
    rfl
  constructor
  · intro hμ
    let := hμ.isProbability
    exact exists_isNatural_of_selfSimilar _ (pairSystem_isDimension hs0 hs1)
      (hself.mpr hμ.selfSimilar) hμ.support
  · rintro ⟨K, hμ⟩
    exact ⟨hμ.isProbability, hμ.support_Icc, hself.mp hμ.selfSimilar⟩

/-- The direct definition of `μ_c` in `sec:introduction` is equivalent to the natural
measure of the two-map system at its dimension. -/
private theorem isTwoContractionMeasure_iff_exists_isNatural {c s : ℝ} (hc0 : 0 < c)
    (hc : c < 1/2) (hs : (2:ℝ) ^ (-s) + c ^ s = 1) {μ : Measure ℝ} :
    IsTwoContractionMeasure c s μ ↔ ∃ K, (pairSystem c hc0 hc).IsNatural K s μ := by
  have hhalf : (1/2 : ℝ) ^ s = (2:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
  have hdim : (pairSystem c hc0 hc).IsDimension s := by
    simp only [System.IsDimension, Fin.sum_univ_two, pairSystem_ratio_zero,
      pairSystem_ratio_one, hhalf]
    exact hs
  have hself : (μ = ∑ i, ENNReal.ofReal ((pairSystem c hc0 hc).ratio i ^ s) •
        μ.map ((pairSystem c hc0 hc).map i)) ↔
      μ = ENNReal.ofReal ((1/2 : ℝ) ^ s) • μ.map (fun x => 1/2 * x) +
        ENNReal.ofReal (c ^ s) • μ.map (fun x => c * x + (1 - c)) := by
    simp only [Fin.sum_univ_two]
    rw [funext (pairSystem_map_zero hc0 hc), funext (pairSystem_map_one hc0 hc)]
    rfl
  constructor
  · intro hμ
    let := hμ.isProbability
    exact exists_isNatural_of_selfSimilar _ hdim (hself.mpr hμ.selfSimilar) hμ.support
  · rintro ⟨K, hμ⟩
    exact ⟨hμ.isProbability, hμ.support_Icc, hself.mp hμ.selfSimilar⟩

/-- The dimension equation `2^{-s} + c^s = 1` is the similarity dimension of the two-map
system. -/
private theorem pairSystem_isDimension_of {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hs : (2:ℝ) ^ (-s) + c ^ s = 1) : (pairSystem c hc0 hc).IsDimension s := by
  have hhalf : (1/2 : ℝ) ^ s = (2:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
  simp only [System.IsDimension, Fin.sum_univ_two, pairSystem_ratio_zero,
    pairSystem_ratio_one, hhalf]
  exact hs

/-- Along the family, the Cesàro means of the expected profile converge to the closed form
of `eq:two-contraction-mean`. -/
private theorem tendsto_avg_expectedProfile_of_isNatural {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : (pairSystem c hc0 hc).IsDimension s) {K : Set ℝ} {μ : Measure ℝ}
    (hμ : (pairSystem c hc0 hc).IsNatural K s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s μ t) atTop
      (𝓝 (twoContractionMean c s μ)) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (pairSystem_openSetCondition hc0 hc hμ.attractor).exists_isFrostman _ hs0.le hμ
  simp only [expectedProfile_eq_H hW hs0 hs1 hA]
  exact pairSystem_tendsto_avg_H hc0 hc hs0 hs1 hdim hμ

/-- Along the family the means are strictly increasing in the contraction. -/
private theorem twoContractionMean_lt_of_lt {c₁ c₂ s₁ s₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1/2) (hs₁ : (2:ℝ) ^ (-s₁) + c₁ ^ s₁ = 1)
    (hs₂ : (2:ℝ) ^ (-s₂) + c₂ ^ s₂ = 1) {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hK₁ : (pairSystem c₁ hc₁ (hc.trans hc₂)).IsNatural K₁ s₁ μ₁)
    (hK₂ : (pairSystem c₂ (hc₁.trans hc) hc₂).IsNatural K₂ s₂ μ₂) :
    twoContractionMean c₁ s₁ μ₁ < twoContractionMean c₂ s₂ μ₂ := by
  obtain ⟨hs₁0, hs₁1, hc₁eq⟩ := dimension_facts hc₁ (hc.trans hc₂) hs₁
  obtain ⟨hs₂0, hs₂1, hc₂eq⟩ := dimension_facts (hc₁.trans hc) hc₂ hs₂
  have hs12 : s₁ < s₂ := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [hc₁eq, hc₂eq, heq] at hc
      exact lt_irrefl _ hc
    · have := pairRatio_lt_pairRatio hs₂0 hlt
      rw [← hc₁eq, ← hc₂eq] at this
      linarith
  subst hc₁eq
  subst hc₂eq
  exact twoContractionMean_lt hs₁0 hs12 hs₂1 hK₁ hK₂

/-! ### `sec:reconstruction`: reconstruction from the compact image -/

/-- `thm:minkowski-reconstruction`, including its final Borel assertion, under the open
set condition; the bundled compact set is the attractor carried by the natural
measure. -/
theorem audit_minkowski_reconstruction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    MinkowskiReconstruction.TubeReconstructsOccupation
        W P hμ.compactAttractor μ ∧
      ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
        Measurable reconstruct ∧
        (fun ω ↦ reconstruct (brownianImage W hμ.compactAttractor ω)) =ᵐ[P]
          occupationProb W μ :=
  hμ.minkowskiReconstruction hW S hs0 hs1 (hosc.strongOpenSetCondition S hμ.attractor) hdim

/-- The formal Borel step in `thm:minkowski-reconstruction`: once the pathwise weak
tube limit is known, the limiting occupation probability is almost surely a Borel
function of the compact Brownian image. -/
theorem audit_borel_reconstruction_of_pathwise
    {P : Measure Ω} {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {K : NonemptyCompacts ℝ} {μ : Measure ℝ}
    (hpath : MinkowskiReconstruction.TubeReconstructsOccupation W P K μ) :
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (fun ω ↦ reconstruct (brownianImage W K ω)) =ᵐ[P]
        occupationProb W μ :=
  MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise hW hpath

/-- The formal descent used in `thm:cantor-set-application`: two pathwise tube limits
transfer mutual singularity of the occupation laws to mutual singularity of the laws
of the compact Brownian images. -/
theorem audit_brownianImageLaw_mutuallySingular_of_pathwise
    {P : Measure Ω} {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {K₁ K₂ : NonemptyCompacts ℝ} {μ₁ μ₂ : Measure ℝ}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hpath₁ : MinkowskiReconstruction.TubeReconstructsOccupation W P K₁ μ₁)
    (hpath₂ : MinkowskiReconstruction.TubeReconstructsOccupation W P K₂ μ₂)
    (hoccupation : (occupationLaw W P μ₁).MutuallySingular
      (occupationLaw W P μ₂)) :
    (brownianImageLaw W P K₁).MutuallySingular
      (brownianImageLaw W P K₂) :=
  MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction
    hW hpath₁ hpath₂ hoccupation

/-- `thm:cantor-set-application`.  The compact Brownian image of the homogeneous
attractor at any ratio `0 < λ < 1/2` and that of the attractor of every non-lattice
system of the same dimension satisfying the open set condition have mutually singular
laws on the Hausdorff hyperspace. -/
theorem audit_cantor_set_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    (hosc : S.OpenSetCondition) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDim lam) μ) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hμ.compactAttractor) :=
  MinkowskiReconstruction.homogeneous_brownianImage_application
    hW hlam0 hlam hA S (hosc.strongOpenSetCondition S hμ.attractor) hna hdim hμ

/-- The paired instance of `thm:cantor-set-application`, the last sentence of the
corollary: under `eq:non-lattice`, the compact Brownian images of the homogeneous
attractor and of `K_B` have mutually singular laws on the Hausdorff hyperspace.
Together with `audit_exceptional_parameters_countable`, this gives the
countable-exception assertion. -/
theorem audit_cantor_set_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hB.compactAttractor) :=
  MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional
    hW hlam0 hlam hA hB hnl

/-- `eq:neighbourhood-union-scaling`.  The cut-off of a finite nonempty union is the
pointwise maximum of the component cut-offs, and smoothed tube mass has the paper's
affine planar scaling. -/
theorem audit_tube_union_scaling {ι : Type*} [Fintype ι] [Nonempty ι]
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (F : ι → CompactPlane)
    (x a : Plane) (G : CompactPlane) :
    tubeCutoff r (compactUnion F) x =
        Finset.univ.sup' Finset.univ_nonempty
          (fun i ↦ tubeCutoff r (F i) x) ∧
      tubeMass r (translateCompact a (dilateCompact q G)) =
        q ^ 2 * tubeMass (r / q) G :=
  ⟨tubeCutoff_compactUnion hr F x, tubeMass_translate_dilate hr hq a G⟩

/-- `eq:neighbourhood-defect-elementary`.  The smoothed multiple-counting defect is
nonnegative and is bounded by the unordered sum of raw pairwise tube-intersection
areas. -/
theorem audit_tube_defect_elementary {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr : 0 < r) (F : ι → CompactPlane) :
    0 ≤ tubeDefect r F ∧
      tubeDefect r F ≤ pairwiseTubeOverlapAreaSum r F :=
  ⟨tubeDefect_nonneg hr F, tubeDefect_le_pairwiseTubeOverlapAreaSum hr F⟩

/-- `thm:neighbourhood-moments`, including the finiteness of every real expectation used in
the inequalities.  The compact time set is the attractor carried by the natural
measure; the open set condition enters only through the classical Ahlfors regularity
of the natural measure, cited from Falconer in the paper and proved in the library. -/
theorem audit_tube_moments {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∀ q : ℝ, 1 ≤ q → ∃ Cq : ℝ, 0 < Cq ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun ω ↦ (brownianTubeArea W hμ.compactAttractor r ω) ^ q) P ∧
        Integrable
          (fun ω ↦ (tubeMass r (brownianImage W hμ.compactAttractor ω)) ^ q) P ∧
        (∫ ω, (brownianTubeArea W hμ.compactAttractor r ω) ^ q ∂P) +
            (∫ ω, (tubeMass r (brownianImage W hμ.compactAttractor ω)) ^ q ∂P)
          ≤ Cq * r ^ (q * tubeExponent s)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
        Integrable
          (fun ω ↦ tubeMass r (brownianImage W hμ.compactAttractor ω)) P ∧
        c * r ^ tubeExponent s ≤
          ∫ ω, tubeMass r (brownianImage W hμ.compactAttractor ω) ∂P :=
  hμ.tubeMoments hW S hs0 hs1 hosc hdim

/-- `thm:neighbourhood-overlap`, including integrability of the overlap and defect random
variables.  One constant and one exponent `η > 0` control every distinct first-level
pair and the resulting multiple-counting defect, with the bound `C r^{α+2η}`; `η` is
the exponent of `thm:cross-piece-mass`, which the statement of the lemma inherits. -/
theorem audit_tube_overlap {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ i j : ι, i ≠ j →
        Integrable (fun ω ↦ tubeOverlapArea r
          (brownianImage W (hμ.compactPiece S i) ω)
          (brownianImage W (hμ.compactPiece S j) ω)) P ∧
        (∫ ω, tubeOverlapArea r
            (brownianImage W (hμ.compactPiece S i) ω)
            (brownianImage W (hμ.compactPiece S j) ω) ∂P)
          ≤ C * r ^ (tubeExponent s + 2 * η)) ∧
      Integrable (fun ω ↦ tubeDefect r
        (fun i ↦ brownianImage W (hμ.compactPiece S i) ω)) P ∧
      (∫ ω, tubeDefect r
          (fun i ↦ brownianImage W (hμ.compactPiece S i) ω) ∂P)
        ≤ C * r ^ (tubeExponent s + 2 * η) :=
  hμ.tubeOverlap hW S hs0 hs1 (hosc.strongOpenSetCondition S hμ.attractor) hdim

/-- `thm:neighbourhood-renewal`.  The real integrals defining the mean profile are required
to be integrable.  Uniform convergence in the lattice case is written directly
with its `ε`--`N` quantifiers on one period. -/
theorem audit_tube_renewal {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∀ v : ℝ, 0 ≤ v →
      Integrable (brownianTubeProfile W hμ.compactAttractor s v) P) ∧
    (∃ c C : ℝ, 0 < c ∧ ∀ v : ℝ, 0 ≤ v →
      c ≤ meanBrownianTubeProfile W P hμ.compactAttractor s v ∧
      meanBrownianTubeProfile W P hμ.compactAttractor s v ≤ C) ∧
    (S.TubeNonArithmetic →
      ∃ CK : ℝ, 0 < CK ∧ Tendsto
        (meanBrownianTubeProfile W P hμ.compactAttractor s) atTop (nhds CK)) ∧
    (∀ h : ℝ, 0 < h → S.TubeArithmetic h →
      ∃ PK : ℝ → ℝ, Function.Periodic PK h ∧
        (∃ c C : ℝ, 0 < c ∧ ∀ t : ℝ, c ≤ PK t ∧ PK t ≤ C) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ t ∈ Set.Icc (0 : ℝ) h,
            |meanBrownianTubeProfile W P hμ.compactAttractor s
                (t + (n : ℝ) * h) - PK t| ≤ ε) :=
  hμ.tubeRenewal hW S hs0 hs1 (hosc.strongOpenSetCondition S hμ.attractor) hdim

/-- `thm:neighbourhood-concentration`.  Membership in `L²` is included explicitly before
the `eLpNorm` bound, and the final assertion has the paper's quantifier order: each
fixed phase has its own almost-sure event. -/
theorem audit_tube_concentration {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∃ C : ℝ, 0 < C ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ v : ℝ, 0 ≤ v →
      MemLp (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ∧
      eLpNorm (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ≤
        ENNReal.ofReal (C * Real.exp (-γ * v))) ∧
    ∀ t : ℝ, ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ centeredBrownianTubeProfile W P hμ.compactAttractor s
        ((n : ℝ) + t) ω) atTop (nhds 0) :=
  hμ.tubeConcentration hW S hs0 hs1 (hosc.strongOpenSetCondition S hμ.attractor) hdim

/-! ### `sec:setup`: the Gaussian reduction -/

/-- Almost surely the occupation measure of a probability measure has total mass one, so
`occupationProb` reads it as a point of `𝒫(ℝ²)` and the fallback in that definition never
enters a conclusion. -/
theorem audit_isProbabilityMeasure_occupation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂P, IsProbabilityMeasure (occupation W μ ω) :=
  hW.ae_isProbabilityMeasure_occupation μ

/-- `sec:setup`: an `s`-Frostman measure with `0 < s` has no atoms.  This is the
hypothesis the paper uses to discard the diagonal in `thm:gaussian-reduction`. -/
theorem audit_measure_singleton {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ}
    (hμ : IsFrostman s A μ) (x : ℝ) : μ {x} = 0 :=
  hμ.measure_singleton hs x

/-- `eq:frostman` is written with open balls and centres in `[0,1]`, while `IsFrostman`
uses closed balls and arbitrary centres.  The two conventions agree up to the change of
constant the paper allows itself. -/
theorem audit_frostman_conventions {s A : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] :
    (IsFrostman s A μ → IsFrostmanOpen s A μ) ∧
      (IsFrostmanOpen s A μ → IsFrostman s (3 ^ s * A) μ) :=
  ⟨fun h => h.isFrostmanOpen, fun h => h.isFrostman hs⟩

/-- `sec:setup`: the pair-distance law has no atoms.  This is the Fubini step before
"Thus `Φ` is continuous". -/
theorem audit_pairLaw_noAtoms {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) (δ : ℝ) : pairLaw μ {δ} = 0 :=
  pairLaw_measure_singleton hs hμ δ

/-- `sec:setup`: the pair-distance distribution has no atoms, hence `Φ` is
continuous. -/
theorem audit_phi_continuous {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) : Continuous (Phi μ) :=
  continuous_phi hs hμ

/-- `eq:phi-frostman`.  The Frostman bound passes to the pair-distance distribution. -/
theorem audit_phi_le {s A : ℝ} (hs : 0 < s) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsFrostman s A μ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Phi μ δ ≤ A * δ ^ s :=
  phi_le hμ hδ0 hδ1

/-- The open-ball and closed-ball forms of Ahlfors regularity agree up to the
constant. -/
theorem audit_ahlfors_conventions {s A : ℝ} (hs : 0 ≤ s) {μ : Measure ℝ}
    (h : IsAhlforsClosed s A μ) : IsAhlfors s (2 ^ s * A) μ :=
  h.isAhlfors hs

/-- `sec:setup`: the smoothing kernel is integrable on `(0,∞)`, "since it decays
exponentially at `0` and as `η^{s-2}` at infinity, where `s < 1`", and its integral is
strictly positive.  The positivity is what makes the limit of `eq:hb-asymptotic`
non-zero. -/
theorem audit_kern_integrable {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn (kern s) (Set.Ioi 0) ∧ 0 < ∫ η in Set.Ioi (0:ℝ), kern s η :=
  ⟨kern_integrableOn hs0 hs1, integral_kern_pos hs0 hs1⟩

/-! ### `sec:renewal`: the pair-distance renewal profiles -/

/-- `thm:non-lattice-limit`: the two inputs the key renewal theorem consumes from the
system.  `ϑ` is a probability measure, and its first moment is the renewal mean `m`. -/
theorem audit_renewalLaw {ι : Type*} [Fintype ι] (S : System ι) {s : ℝ}
    (hdim : S.IsDimension s) :
    IsProbabilityMeasure (S.renewalLaw s) ∧ ∫ x, x ∂(S.renewalLaw s) = S.renewalMean s :=
  ⟨S.isProbabilityMeasure_renewalLaw hdim, S.integral_id_renewalLaw s⟩

/-- `thm:non-lattice-limit`: the strict exponential moment the key renewal theorem asks
of the renewal measure.  Its content is that the log-ratios are bounded away from zero,
which is what `r_i < 1` gives. -/
theorem audit_exists_expTransform_lt_one {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {s : ℝ} (hdim : S.IsDimension s) :
    ∃ θ : ℝ, 0 < θ ∧ AbsorptionCutoff.Renewal.expTransform θ (S.renewalLaw s) < 1 :=
  S.exists_expTransform_lt_one hdim

/-- `eq:c-definition`: the ratio `c` exists, lies in `(0, 1/2)`, and solves
`c^s = 1 - 2^{-s}` at the middle-thirds exponent. -/
theorem audit_pairRatio {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    ∃ c : ℝ, 0 < c ∧ c < 1/2 ∧
      c ^ homogeneousDim lam = 1 - (2:ℝ) ^ (-homogeneousDim lam) :=
  ⟨pairRatio (homogeneousDim lam), pairRatio_pos (homogeneousDim_pos hlam0 hlam),
    pairRatio_lt_half (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam),
    pairRatio_rpow (homogeneousDim_pos hlam0 hlam)⟩

/-- `sec:renewal`: the homogeneous system has similarity dimension
`log 2 / log(1/λ)` and first-level gap `1-2λ`. -/
theorem audit_homogeneousSystem_facts {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    (homogeneousSystem lam hlam0 hlam).IsDimension (homogeneousDim lam) ∧
      ∀ K : Set ℝ, K ⊆ Set.Icc 0 1 →
        (homogeneousSystem lam hlam0 hlam).StronglySeparated K (1 - 2 * lam) :=
  ⟨homogeneousSystem_isDimension hlam0 hlam,
    fun _ hK => homogeneousSystem_stronglySeparated hlam0 hlam hK⟩

/-- `sec:renewal`: the paired system has similarity dimension `s` and is strongly
separated with gap `1/2 - c` on every subset of `[0,1]`. -/
theorem audit_pairSystem_facts {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (pairSystem (pairRatio s) (pairRatio_pos hs0)
        (pairRatio_lt_half hs0 hs1)).IsDimension s ∧
      ∀ K : Set ℝ, K ⊆ Set.Icc 0 1 →
        (pairSystem (pairRatio s) (pairRatio_pos hs0)
          (pairRatio_lt_half hs0 hs1)).StronglySeparated K (1/2 - pairRatio s) :=
  ⟨pairSystem_isDimension hs0 hs1, fun _ hK => pairSystem_stronglySeparated _ _ hK⟩

/-- `eq:non-lattice` is exactly the non-lattice hypothesis of
`thm:non-lattice-limit` for the paired system, whose log-ratios are `log 2` and
`log(1/c)`. -/
theorem audit_pairSystem_nonArithmetic_iff {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (pairSystem (pairRatio s) (pairRatio_pos hs0)
        (pairRatio_lt_half hs0 hs1)).NonArithmetic
      ↔ Irrational (Real.log (pairRatio s)⁻¹ / Real.log 2) :=
  pairSystem_nonArithmetic_iff hs0 hs1

/-- `thm:homogeneous-nonconstancy`.  For every `0 < λ < 1/2`, the eventual periodic
profile of the homogeneous equal-weight measure is non-constant. -/
theorem audit_cantor_nonconstant {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {K : Set ℝ} {μ : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural K (homogeneousDim lam) μ)
    (w₀ : ℝ) :
    ∃ x, w₀ ≤ x ∧ ∃ y, w₀ ≤ y ∧
      G (homogeneousDim lam) μ x ≠ G (homogeneousDim lam) μ y :=
  HomogeneousNonconstancy.homogeneous_G_nonconstant_on_tail hlam0 hlam hA w₀

/-- `sec:renewal`: a function continuous on a closed period whose endpoint values agree
extends to a continuous periodic function on the line.  This is the construction of
`G̃_A`, stated for the shift identity `eq:g-recursion` supplies. -/
theorem audit_exists_periodic_extension {p a : ℝ} (hp : 0 < p) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici a))
    (hshift : ∀ w, a + p ≤ w → f w = f (w - p)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g p ∧ ∀ w, a ≤ w → g w = f w :=
  exists_periodic_extension_of_shift hp hcont hshift

/-! ### `sec:smoothing`: Gaussian smoothing and distributional separation -/

/-- `sec:smoothing`: the `k`-th Fourier coefficient of a `q`-periodic function, as the
paper normalises it, is Mathlib's `fourierCoeffOn` on `[0,q]`.  This is the bridge to the
`AddCircle` Fourier theory, whose Hilbert basis `fourierBasis` supplies the uniqueness
step of `thm:smoothing-injective`. -/
theorem audit_fourierCoeffP_eq_fourierCoeffOn {q : ℝ} (hq : 0 < q) (g : ℝ → ℝ) (k : ℤ) :
    fourierCoeffP q g k = fourierCoeffOn hq (fun x => (g x : ℂ)) k :=
  fourierCoeffP_eq_fourierCoeffOn hq g k

/-- `thm:smoothing-injective`, the Fourier uniqueness step: a continuous `p`-periodic
function all of whose Fourier coefficients vanish is zero. -/
theorem audit_fourier_uniqueness {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g p) (h : ∀ k : ℤ, fourierCoeffP p g k = 0) (x : ℝ) :
    g x = 0 :=
  eq_zero_of_fourierCoeffP_eq_zero hp hg hper h x

/-- `sec:smoothing`: the smoothed periodic profile is strictly positive, since `φ > 0`
and the profile is strictly positive on a period. -/
theorem audit_smoothOp_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {g : ℝ → ℝ}
    (hg : Continuous g) (hpos : ∀ x, 0 < g x) (hbdd : ∃ M, ∀ x, |g x| ≤ M) (v : ℝ) :
    0 < smoothOp s g v :=
  smoothOp_pos hs0 hs1 hg hpos hbdd.choose_spec v

/-- `eq:gamma-multiplier`.  Both factors of the closed form are non-zero: the Gamma
function has no zeros in the right half plane. -/
theorem audit_gammaMult_ne_zero {s : ℝ} (hs : s < 1) {p : ℝ} (hp : 0 < p) (k : ℤ) :
    gammaMult s p k ≠ 0 :=
  gammaMult_ne_zero hs p k

/-- `eq:periodic-smoothing`: `Tg` is `p/2`-periodic.  The factor `2t` in the argument of
`g` is what halves the period, and it is why `eq:fourier-multiplier` takes the
coefficient of `Tg` at period `p/2`. -/
theorem audit_smoothOp_periodic {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hper : Function.Periodic g p) :
    Function.Periodic (smoothOp s g) (p / 2) :=
  smoothOp_periodic hper

/-! ### `sec:variance`: the four-point variance bound -/

/-- `thm:variance`, the final assertion: each variance scale is `o(r^{4s})`. -/
theorem audit_varScale_isLittleO {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun r : ℝ => varScale s r / r ^ (4 * s)) (𝓝[>] 0) (𝓝 0) :=
  varScale_div_tendsto_zero hs0 hs1

/-! ### `sec:concentration`: uniform concentration -/

/-- `eq:monotone-fill`: on a grid interval the empirical profile is squeezed between
`e^{-2s/m}` and `e^{2s/m}` times its values at the endpoints, because `r ↦ C_r` is
non-decreasing. -/
theorem audit_monotone_fill {s : ℝ} (hs : 0 ≤ s) (ν : Measure Plane)
    [IsProbabilityMeasure ν] {a b v : ℝ} (hab : a ≤ b) (hav : a ≤ v) (hvb : v ≤ b) :
    Real.exp (-(2 * s * (b - a))) * Yprofile s ν b ≤ Yprofile s ν v ∧
      Yprofile s ν v ≤ Real.exp (2 * s * (b - a)) * Yprofile s ν a :=
  monotone_fill ν hs hav hvb

/-! ### `sec:obstruction`: the homometric obstruction -/

/-- `sec:obstruction`: the signed convolution `σ * σ̃` is the law of the difference of
two independent samples.  This is the bridge between the convolution the paper writes
and the difference law the proof of `thm:homometric-example` produces. -/
theorem audit_conv_reflect (σ : Measure ℝ) [SFinite σ] :
    σ.conv (reflect σ) = (σ.prod σ).map (fun p : ℝ × ℝ => p.1 - p.2) :=
  conv_reflect_eq_map_sub σ

/-! ### Closed in the parallel pass -/

/-- `sec:concentration`: the oscillation `d_A` of the smoothed periodic profile over a
period is attained and strictly positive. -/
theorem audit_lattice_gap {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (hne : ∃ v w, smoothOp s g v ≠ smoothOp s g w) :
    ∃ a ∈ Set.Icc (0:ℝ) (p/2), ∃ b ∈ Set.Icc (0:ℝ) (p/2),
      0 < smoothOp s g a - smoothOp s g b ∧
        ∀ v, smoothOp s g b ≤ smoothOp s g v ∧ smoothOp s g v ≤ smoothOp s g a :=
  smoothOp_gap hs0 hs1 hp hg hper hne

/-- `thm:renewal-recursion`, `eq:phi-recursion`.  At every scale the pair-distance
distribution satisfies the self-similar recursion with the cross term `Φ_×` of pairs
with different first-level addresses. -/
theorem audit_renewal_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ}
    {s : ℝ} {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (δ : ℝ) :
    Phi μ δ = ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) + S.crossPhi s μ δ :=
  phi_recursion_cross S hμ δ

/-- `thm:renewal-recursion`, `eq:g-recursion`.  The recursion in the normalised
profile, at every `w`. -/
theorem audit_g_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {s : ℝ}
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) (w : ℝ) :
    G s μ w = ∑ i, S.ratio i ^ s * G s μ (w - S.logRatio i)
      + Real.exp (s * w) * S.crossPhi s μ (Real.exp (-w)) :=
  g_recursion_cross S hμ w

/-- `thm:renewal-recursion`, the bound on the cross term: under the open set condition,
`0 ≤ Φ_×(δ) ≤ C δ^{s+η}` for `0 < δ ≤ 1`, with `η ∈ (0, 1-s)`. -/
theorem audit_crossPhi_bound {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    (hosc : S.OpenSetCondition) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 - s ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      0 ≤ S.crossPhi s μ δ ∧ S.crossPhi s μ δ ≤ C * δ ^ (s + η) := by
  obtain ⟨C, η, hC, hη, hηs, hbound⟩ :=
    (hosc.strongOpenSetCondition S hμ.attractor).exists_crossPhi_bound S hs0 hs1 hdim hμ
  exact ⟨C, η, hC, hη, hηs, fun δ hδ0 hδ1 => ⟨S.crossPhi_nonneg s μ δ, hbound δ hδ0 hδ1⟩⟩

/-- `thm:renewal-recursion`, the separated case: if the first-level pieces have mutual
distance at least `ρ`, the cross term vanishes below `ρ`. -/
theorem audit_crossPhi_separated {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < ρ) : S.crossPhi s μ δ = 0 :=
  crossPhi_eq_zero_of_stronglySeparated S hsep hμ hδ

/-- `thm:stopping-overlap`.  Under the open set condition there is an integer `M ≥ 1`
such that, at every threshold `0 < u ≤ 1`, the stopping family `𝒲(u)`, realised as the
leaves of the stopping tree at any depth past which every branch has stopped, has
multiplicity at most `M` and can be coloured with `M` colours so that intervals of one
colour have pairwise disjoint interiors. -/
theorem audit_stopping_overlap {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    (hosc : S.OpenSetCondition) :
    ∃ M : ℕ, 0 < M ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∀ n : ℕ, Hutchinson.maxRatio S ^ n ≤ u →
        (∀ x : ℝ, ∀ T : Finset (S.StoppingLeaves u n System.stoppingRoot),
          (∀ leaf ∈ T, x ∈ S.stoppingWordMap (S.stoppingLeafWord u leaf) '' Set.Icc (0:ℝ) 1) →
          T.card ≤ M) ∧
        ∃ c : S.StoppingLeaves u n System.stoppingRoot → Fin M,
          ∀ leaf₁ leaf₂, leaf₁ ≠ leaf₂ → c leaf₁ = c leaf₂ →
            Disjoint
              (interior (S.stoppingWordMap (S.stoppingLeafWord u leaf₁) '' Set.Icc (0:ℝ) 1))
              (interior (S.stoppingWordMap (S.stoppingLeafWord u leaf₂) '' Set.Icc (0:ℝ) 1)) := by
  classical
  obtain ⟨U, hU⟩ := hosc
  obtain ⟨M, hM, hmult⟩ := hU.exists_point_multiplicity_bound S
  obtain ⟨M', hM', hcol⟩ := hU.exists_stopping_coloring S
  refine ⟨max M M', lt_max_of_lt_left hM, fun u hu0 hu1 n hn => ⟨fun x T hT => ?_, ?_⟩⟩
  · refine le_trans (Finset.card_le_card fun leaf hleaf => ?_)
      (le_trans (hmult u hu0 hu1 n hn x) (le_max_left _ _))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT leaf hleaf⟩
  · obtain ⟨c, hc⟩ := hcol u hu0 hu1 n hn
    refine ⟨fun leaf => Fin.castLE (le_max_right M M') (c leaf), fun leaf₁ leaf₂ hne hceq => ?_⟩
    exact hc leaf₁ leaf₂ hne (Fin.castLE_injective _ hceq)

/-- `thm:cross-piece-mass`.  Under the open set condition there are `C > 0` and
`η ∈ (0, 1-s)` such that, for `i ≠ j` and `0 < h ≤ 1`, the mass of `μ_i = (S_i)_* μ`
within distance `h` of `K_j = S_j K` is at most `C h^η` (`eq:boundary-mass`), and
`(μ_i × μ_j){|x-y| ≤ h} ≤ C h^{s+η}` (`eq:cross-piece-mass`). -/
theorem audit_cross_piece_mass {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} (hosc : S.OpenSetCondition) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 - s ∧ ∀ i j : ι, i ≠ j → ∀ h : ℝ, 0 < h → h ≤ 1 →
      (μ.map (S.map i)) (Metric.cthickening h (S.map j '' K)) ≤ ENNReal.ofReal (C * h ^ η) ∧
      ((μ.map (S.map i)).prod (μ.map (S.map j))) {p : ℝ × ℝ | |p.1 - p.2| ≤ h}
        ≤ ENNReal.ofReal (C * h ^ (s + η)) :=
  (hosc.strongOpenSetCondition S hμ.attractor).exists_cross_piece_bound S hs0 hs1 hdim hμ

/-- Schief's theorem, cited in `sec:introduction` and in the proof of
`thm:cross-piece-mass`: for a system with attractor `K`, the open set condition is
equivalent to the existence of a feasible open set meeting `K`. -/
theorem audit_schief {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    (hK : S.IsAttractor K) :
    S.OpenSetCondition ↔ ∃ U : Set ℝ, S.IsFeasible U ∧ (U ∩ K).Nonempty :=
  S.openSetCondition_iff_strongOpenSetCondition hK

/-- `eq:gamma-multiplier`: the multiplier integral evaluates in closed form, by the
substitution `x = 1/(2η)`. -/
theorem audit_gamma_multiplier {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {p : ℝ} (hp : 0 < p)
    (k : ℤ) : multInt s p k = gammaMult s p k :=
  multInt_eq_gammaMult hs1 p k

/-- `thm:smoothing-injective`, the multiplier statement: no Fourier multiplier of the
smoothing operator vanishes. -/
theorem audit_multInt_ne_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {p : ℝ} (hp : 0 < p)
    (k : ℤ) : multInt s p k ≠ 0 :=
  multInt_ne_zero hs1 p k

/-- `eq:periodic-smoothing`: `Tg` is continuous and `p/2`-periodic. -/
theorem audit_smoothOp_continuous_periodic {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hp : 0 < p) {g : ℝ → ℝ} (hg : Continuous g) (hbdd : ∃ M, ∀ x, |g x| ≤ M)
    (hper : Function.Periodic g p) :
    Continuous (smoothOp s g) ∧ Function.Periodic (smoothOp s g) (p/2) :=
  ⟨continuous_smoothOp hs0 hs1 hg hbdd.choose_spec, smoothOp_periodic hper⟩

/-- `thm:profile-uniform-continuity`.  The expected profile is uniformly continuous. -/
theorem audit_profile_uniform_continuity {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    UniformContinuous (H s μ) :=
  profile_uniformContinuous hs0 hs1 hμ

/-- `eq:fourier-multiplier`, the Fourier identity: smoothing acts on the Fourier
coefficients as multiplication by `M_k`.  The coefficient of `g` is taken at period `p`
and that of `Tg` at period `p/2`, which is the period `Tg` has. -/
theorem audit_fourier_multiplier {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hbdd : ∃ M, ∀ x, |g x| ≤ M)
    (hper : Function.Periodic g p) (k : ℤ) :
    fourierCoeffP (p/2) (smoothOp s g) k = multInt s p k * fourierCoeffP p g k :=
  fourierCoeffP_smoothOp hs0 hs1 hp hg hbdd hper k

/-- `thm:smoothing-injective`, the kernel form the Fourier argument produces; injectivity
follows from it by linearity of `T`. -/
theorem audit_smoothing_kernel_trivial {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (h : ∀ v, smoothOp s g v = 0) : ∀ x, g x = 0 :=
  smoothOp_eq_zero hs0 hs1 hp hg hper h

/-- `thm:smoothing-injective`.  The Gaussian smoothing operator is injective on the
continuous `p`-periodic functions. -/
theorem audit_smoothing_injective {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hper₁ : Function.Periodic g₁ p) (hper₂ : Function.Periodic g₂ p)
    (h : ∀ v, smoothOp s g₁ v = smoothOp s g₂ v) : ∀ x, g₁ x = g₂ x :=
  smoothOp_injective hs0 hs1 hp hg₁ hg₂ hper₁ hper₂ h

/-- `thm:smoothing-injective`, the stated consequence: `Tg` is constant only when `g`
is, so the smoothed periodic profile of the middle-thirds measure is non-constant. -/
theorem audit_smoothing_nonconstant {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 0 < p)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g p)
    (hne : ∃ x y, g x ≠ g y) : ∃ v w, smoothOp s g v ≠ smoothOp s g w :=
  smoothOp_nonconstant hs0 hs1 hp hg hper hne

/-- `thm:profile-asymptotics`, `eq:hb-asymptotic`.  In the non-lattice case the
expected profile converges to `C ∫₀^∞ φ`, and that limit is finite and strictly
positive. -/
theorem audit_profile_asymptotics_non_lattice {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {A : ℝ} (hμ : IsFrostman s A μ)
    (hCpos : 0 < C) (hC : Tendsto (G s μ) atTop (𝓝 C)) :
    0 < C * ∫ η in Set.Ioi (0:ℝ), kern s η ∧
      Tendsto (H s μ) atTop (𝓝 (C * ∫ η in Set.Ioi (0:ℝ), kern s η)) :=
  profile_asymptotics_nonLattice hs0 hs1 hμ hCpos hC

/-- `eq:ha-asymptotic`, as the uniform bound the proof
produces for the homogeneous system. -/
theorem audit_profile_asymptotics_lattice {KA : Set ℝ} {μA : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g (Real.log lam⁻¹))
    (hagree : ∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) :
    ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      |H (homogeneousDim lam) μA v - smoothOp (homogeneousDim lam) g v|
        ≤ C * Real.exp (-2 * (1 - homogeneousDim lam) * v) := by
  have := hA.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_lattice_bound (homogeneousDim_pos hlam0 hlam)
    (homogeneousDim_lt_one hlam0 hlam) hg (log_inv_pos hlam0 hlam).ne' hper hagree
  exact ⟨C, hC0, fun v _ => hC v⟩

/-- `eq:ha-asymptotic` in the asymptotic shape the paper writes it. -/
theorem audit_profile_asymptotics_lattice_bigO {KA : Set ℝ} {μA : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g (Real.log lam⁻¹))
    (hagree : ∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) :
    (fun v => H (homogeneousDim lam) μA v - smoothOp (homogeneousDim lam) g v)
      =O[atTop] fun v => Real.exp (-2 * (1 - homogeneousDim lam) * v) := by
  have := hA.isProbabilityMeasure
  obtain ⟨C, _, hC⟩ := exists_lattice_bound (homogeneousDim_pos hlam0 hlam)
    (homogeneousDim_lt_one hlam0 hlam) hg (log_inv_pos hlam0 hlam).ne' hper hagree
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun v => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hC v

/-- The law of the occupation measure lives on `𝒫(ℝ²)`, and the paper equips that space
with the Borel σ-algebra of the weak topology.  Mathlib's `ProbabilityMeasure` carries
the Giry σ-algebra, generated by the evaluations; on the Polish space `ℝ²` the two
agree. -/
theorem audit_borel_eq_giry :
    borel (ProbabilityMeasure Plane)
      = (inferInstance : MeasurableSpace (ProbabilityMeasure Plane)) :=
  borel_probabilityMeasure_eq_giry

/-- `thm:gaussian-four-point`, first assertion: increments over intervals with disjoint
interiors are independent.  The endpoints are unoriented, as in the paper. -/
theorem audit_disjoint_increments_indep {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {t u t' u' : ℝ≥0}
    (hdisj : max t u ≤ min t' u' ∨ max t' u' ≤ min t u) :
    IndepFun (fun ω => W u ω - W t ω) (fun ω => W u' ω - W t' ω) P :=
  disjoint_increments_indep hW hdisj

/-- The law of the occupation measure is a probability measure, so the object the paper
calls `Law(W_*μ)` has total mass one. -/
theorem audit_isProbabilityMeasure_occupationLaw {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (occupationLaw W P μ) :=
  isProbabilityMeasure_occupationLaw μ

/-- The law of the compact Brownian image is a probability measure, so the compact-image
laws compared in `thm:cantor-set-application` have total mass one and their mutual
singularity is not the vacuous statement about two zero measures. -/
theorem audit_isProbabilityMeasure_brownianImageLaw {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (K : NonemptyCompacts ℝ) :
    IsProbabilityMeasure (brownianImageLaw W P K) :=
  isProbabilityMeasure_brownianImageLaw K

/-- The occupation measure is a measurable function of the sample path, so
`occupationLaw` is the law of `W_*μ` and not the junk value `Measure.map` returns on a
non-measurable map.  Almost sure continuity of the paths, carried by
`IsPlanarBrownian`, is what supplies this. -/
theorem audit_aemeasurable_occupation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    AEMeasurable (occupationProb W μ) P :=
  hW.aemeasurable_occupationProb μ

/-- Internal Ahlfors-regularity endpoint for the natural measure of a system satisfying
the open set condition, cited from Falconer in the paper. Support points are those
charging every ball. -/
theorem audit_ahlfors {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    {s : ℝ} (hs : 0 < s) (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ A : ℝ, IsAhlforsClosed s A μ :=
  System.OpenSetCondition.exists_isAhlforsClosed S hosc hs.le hμ

/-- Internal Ahlfors-regularity endpoint for the two named measures `μ_A` and `μ_B`.
The general endpoint above is the same statement for every strongly separated system. -/
theorem audit_ahlfors_named {KA : Set ℝ} {μA : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB) :
    ∃ A : ℝ, IsAhlfors (homogeneousDim lam) A μA ∧
      IsAhlfors (homogeneousDim lam) A μB :=
  exists_isAhlfors_homogeneous_pair hlam0 hlam hA hB

/-- `thm:gaussian-reduction`, `eq:gaussian-reduction`.  The expected correlation
integral is the Gaussian transform of the pair-distance law, in both the `μ × μ` form
and the Stieltjes form against `dΦ`.  The Frostman hypothesis is what makes `μ`
atomless, so that the diagonal, where the exponent is undefined, is null. -/
theorem audit_gaussian_reduction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    expCorr W P μ r
        = ∫ p : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 / (2 * |p.1 - p.2|)))) ∂(μ.prod μ) ∧
      expCorr W P μ r
        = ∫ δ : ℝ, (1 - Real.exp (-(r ^ 2 / (2 * δ)))) ∂(pairLaw μ) :=
  gaussian_reduction hW hs0 hs1 hμ hr

/-- `eq:smoothing`.  The exact rescaling `S_μ(r) = r^{2s} H_μ^s(log(1/r))`, for every
`r > 0`. -/
theorem audit_smoothing {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ}
    (hr0 : 0 < r) :
    expCorr W P μ r = r ^ (2 * s) * H s μ (Real.log r⁻¹) :=
  smoothing hW hs0 hs1 hμ hr0

/-- `sec:renewal`: the homogeneous attractor and its natural measure exist and are
unique.  This is Hutchinson's theorem for `homogeneousSystem`. -/
theorem audit_exists_cantor_measure {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    ∃! p : Set ℝ × Measure ℝ,
      (homogeneousSystem lam hlam0 hlam).IsNatural p.1 (homogeneousDim lam) p.2 :=
  exists_unique_isNatural_homogeneousSystem hlam0 hlam

/-- `sec:renewal`: the paired attractor and its natural measure exist and are unique. -/
theorem audit_exists_pair_measure {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃! p : Set ℝ × Measure ℝ,
      (pairSystem (pairRatio s) (pairRatio_pos hs0)
        (pairRatio_lt_half hs0 hs1)).IsNatural p.1 s p.2 :=
  exists_unique_isNatural_pairSystem hs0 hs1

/-- `sec:renewal`: the positive non-constant periodic extension of the homogeneous
profile on the full parameter range. -/
theorem audit_exists_periodic_profile {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
      (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) ∧
      (∀ x, 0 < g x) ∧ ∃ x y, g x ≠ g y :=
  homogeneous_periodic_profile hlam0 hlam hA

/-- `thm:smoothing-injective` as one statement: injectivity of `T` on the continuous
`p`-periodic functions, together with the named conclusion that `T G̃_A` is
non-constant. -/
theorem audit_thm_smoothing_injective {KA : Set ℝ} {μA : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    (∀ g₁ g₂ : ℝ → ℝ, Continuous g₁ → Continuous g₂ →
        Function.Periodic g₁ (Real.log lam⁻¹) → Function.Periodic g₂ (Real.log lam⁻¹) →
        (∀ v, smoothOp (homogeneousDim lam) g₁ v = smoothOp (homogeneousDim lam) g₂ v) →
        ∀ x, g₁ x = g₂ x) ∧
      (∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
        (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) ∧
        ∃ v w, smoothOp (homogeneousDim lam) g v ≠
          smoothOp (homogeneousDim lam) g w) :=
  thm_smoothing_injective_homogeneous hlam0 hlam hA

/-- `eq:hb-asymptotic`, the consequence for `μ_B`: the normalised expected
correlation integral has a finite positive limit. -/
theorem audit_non_lattice_correlation_limit {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s C A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (hCpos : 0 < C) :
    ∃ L > 0, Tendsto (fun r : ℝ => expCorr W P μ r / r ^ (2 * s)) (𝓝[>] 0) (𝓝 L) :=
  non_lattice_correlation_limit hW hs0 hs1 hμ hC hCpos

/-- `eq:ha-asymptotic`, the consequence for `μ_A`: the normalised expected
correlation integral oscillates, its lower limit strictly below its upper limit. -/
theorem audit_lattice_correlation_oscillation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {KA : Set ℝ} {μA : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA) :
    ∃ a b : ℝ, a < b ∧
      (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧
        expCorr W P μA r ≤ a * r ^ (2 * homogeneousDim lam)) ∧
      (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧
        b * r ^ (2 * homogeneousDim lam) ≤ expCorr W P μA r) :=
  homogeneous_lattice_correlation_oscillation hW hlam0 hlam hA

/-- `thm:gaussian-four-point`, `eq:joint-return-bound`.  The joint return probability of
two overlapping Brownian increments.  The times are non-negative by type. -/
theorem audit_gaussian_four_point {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {r : ℝ} {t u t' u' : ℝ≥0}
    (hr : 0 < r)
    (hΔ : 0 < |(u:ℝ) - t| * |(u':ℝ) - t'| - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2) :
    (jointReturn W P r t u t' u').toReal
      ≤ min 1 (min (r ^ 2 / (2 * max |(u:ℝ) - t| |(u':ℝ) - t'|))
          (r ^ 4 / (4 * (|(u:ℝ) - t| * |(u':ℝ) - t'|
            - overlap (t:ℝ) (u:ℝ) (t':ℝ) (u':ℝ) ^ 2)))) :=
  gaussian_four_point hW hr hΔ

/-- `thm:gaussian-four-point`, `eq:joint-return-bound` as the paper states it: outside a
`μ⁴`-null set the determinant is positive, and the bound holds whenever the two intervals
overlap.  The positivity carries no overlap hypothesis, as in the paper: `Δ = 0` forces
either a degenerate interval or the two unoriented intervals to agree, and both are null
for a Frostman measure. -/
theorem audit_gaussian_four_point_ae {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))),
      0 < |q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
          - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2 ∧
        (0 < overlap q.1 q.2.1 q.2.2.1 q.2.2.2 →
          (jointReturn W P r q.1.toNNReal q.2.1.toNNReal q.2.2.1.toNNReal
              q.2.2.2.toNNReal).toReal
            ≤ min 1 (min (r ^ 2 / (2 * max |q.2.1 - q.1| |q.2.2.2 - q.2.2.1|))
                (r ^ 4 / (4 * (|q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
                  - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2))))) :=
  gaussian_four_point_ae hW hs0 hs1 hμ hr

/-- `thm:gaussian-four-point` as one statement: independence off the overlap, and the
almost everywhere return bound on it. -/
theorem audit_thm_gaussian_four_point {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {r : ℝ} (hr : 0 < r) :
    (∀ t u t' u' : ℝ≥0, (max t u ≤ min t' u' ∨ max t' u' ≤ min t u) →
        IndepFun (fun ω => W u ω - W t ω) (fun ω => W u' ω - W t' ω) P) ∧
      ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(μ.prod (μ.prod (μ.prod μ))),
        0 < |q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
            - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2 ∧
          (0 < overlap q.1 q.2.1 q.2.2.1 q.2.2.2 →
            (jointReturn W P r q.1.toNNReal q.2.1.toNNReal q.2.2.1.toNNReal
                q.2.2.2.toNNReal).toReal
              ≤ min 1 (min (r ^ 2 / (2 * max |q.2.1 - q.1| |q.2.2.2 - q.2.2.1|))
                  (r ^ 4 / (4 * (|q.2.1 - q.1| * |q.2.2.2 - q.2.2.1|
                    - overlap q.1 q.2.1 q.2.2.1 q.2.2.2 ^ 2))))) :=
  gaussian_four_point_bundled hW hs0 hs1 hμ hr

/-- `thm:endpoint-block-mass`, both halves.
The `μ⁴`-mass of a dyadic block of ordered quadruples, and the joint return probability
on that block.  `μ` sits on `[0,1]`, so reading the times through `Real.toNNReal` is the
identity `μ⁴`-almost everywhere. -/
theorem audit_endpoint_block_mass {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs : 0 < s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ β η : ℝ, 0 < β → β ≤ 1 → 0 < η → η ≤ 1 →
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          β / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ β ∧
          η / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ η}
        ≤ ENNReal.ofReal (C * β ^ s * η ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        β / 2 < x₃ - x₂ → x₃ - x₂ ≤ β →
        η / 2 < (x₂ - x₁) + (x₄ - x₃) → (x₂ - x₁) + (x₄ - x₃) ≤ η →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (β + η)) (r ^ 4 / (β * η))) :=
  endpoint_block_mass hW hs hμ

/-- `thm:endpoint-block-mass` at the dyadic values `β, η ∈ 𝒟` the paper uses, with both
halves of the lemma. -/
theorem audit_endpoint_block_mass_dyadic {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs : 0 < s)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ j l : ℕ,
      (μ.prod (μ.prod (μ.prod μ)))
        {p : ℝ × ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
          ((1:ℝ)/2) ^ j / 2 < p.2.2.1 - p.2.1 ∧ p.2.2.1 - p.2.1 ≤ ((1:ℝ)/2) ^ j ∧
          ((1:ℝ)/2) ^ l / 2 < (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ∧
          (p.2.1 - p.1) + (p.2.2.2 - p.2.2.1) ≤ ((1:ℝ)/2) ^ l}
        ≤ ENNReal.ofReal (C * (((1:ℝ)/2) ^ j) ^ s * (((1:ℝ)/2) ^ l) ^ (2 * s)) ∧
      ∀ r : ℝ, 0 < r → ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
        ((1:ℝ)/2) ^ j / 2 < x₃ - x₂ → x₃ - x₂ ≤ ((1:ℝ)/2) ^ j →
        ((1:ℝ)/2) ^ l / 2 < (x₂ - x₁) + (x₄ - x₃) →
        (x₂ - x₁) + (x₄ - x₃) ≤ ((1:ℝ)/2) ^ l →
        (jointReturn W P r x₁.toNNReal x₃.toNNReal x₂.toNNReal x₄.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) ∧
          (jointReturn W P r x₁.toNNReal x₄.toNNReal x₂.toNNReal x₃.toNNReal).toReal
            ≤ C * min 1 (min (r ^ 2 / (((1:ℝ)/2) ^ j + ((1:ℝ)/2) ^ l))
                (r ^ 4 / (((1:ℝ)/2) ^ j * ((1:ℝ)/2) ^ l))) :=
  endpoint_block_mass_dyadic hW hs hμ

/-- `thm:four-point-integral`, `eq:four-point-integral`.  The four dyadic sums, summed:
the joint return probability integrates over the overlap set to `O(V_s(r))`. -/
theorem audit_four_point_integral {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ p : ℝ × ℝ × ℝ × ℝ in {p | 0 < overlap p.1 p.2.1 p.2.2.1 p.2.2.2},
        jointReturn W P r p.1.toNNReal p.2.1.toNNReal p.2.2.1.toNNReal p.2.2.2.toNNReal
        ∂(μ.prod (μ.prod (μ.prod μ)))
      ≤ ENNReal.ofReal (C * varScale s r) :=
  four_point_integral hW hs0 hs1 hμ

/-- `thm:main`.  Two `s`-Frostman measures whose expected profiles do not converge to
one another have mutually singular Brownian occupation laws, as laws on `𝒫(ℝ²)`.  The
hypothesis is `eq:profile-separation`, `limsup |H₁ - H₂| > 0`, written out for a
non-negative function; `IsFrostman` carries the paper's standing assumption that the
measures live on `[0,1]`. -/
theorem audit_main {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V,
      ε ≤ |expectedProfile W P s μ₁ t - expectedProfile W P s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  apply main hW hs0 hs1 h₁ h₂
  simpa only [expectedProfile_eq_H hW hs0 hs1 h₁,
    expectedProfile_eq_H hW hs0 hs1 h₂] using hsep

/-- `thm:variance`.  The four-point variance bound. -/
theorem audit_variance {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
      variance (fun ω => (corr (occupation W μ ω) r).toReal) P
        ≤ C * varScale s r :=
  variance_four_point hW hs0 hs1 hμ

/-- `thm:variance` as one statement: the bound together with the `o(r^{4s})`
consequence. -/
theorem audit_thm_variance {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    (∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 →
        variance (fun ω => (corr (occupation W μ ω) r).toReal) P ≤ C * varScale s r) ∧
      Tendsto (fun r : ℝ => varScale s r / r ^ (4 * s)) (𝓝[>] 0) (𝓝 0) :=
  variance_bundled hW hs0 hs1 hμ

/-- `eq:y-variance`: the variance bound of `thm:variance` in the exponential
coordinate. -/
theorem audit_y_variance {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      variance (fun ω => Yprofile s (occupation W μ ω) v) P
        ≤ C * (if s < 2⁻¹ then Real.exp (-(2 * s) * v)
               else if s = 2⁻¹ then (1 + v) * Real.exp (-v)
               else Real.exp (-(2 * (1 - s)) * v)) :=
  y_variance hW hs0 hs1 hμ

/-- `eq:grid-convergence`: along each grid `v_{j,m} = j/m` the empirical profile
converges to the expected profile almost surely, by Chebyshev and Borel--Cantelli. -/
theorem audit_grid_convergence {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ ω ∂P, Tendsto
      (fun j : ℕ => Yprofile s (occupation W μ ω) ((j : ℝ)/m) - H s μ ((j : ℝ)/m))
      atTop (𝓝 0) :=
  grid_convergence hW hs0 hs1 hμ hm

/-- `thm:uniform-concentration`, `eq:uniform-concentration`.  Almost surely the
empirical profile converges to the expected profile, uniformly on tails. -/
theorem audit_uniform_concentration {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ V : ℝ, ∀ v ≥ V,
      |Yprofile s (occupation W μ ω) v - H s μ v| ≤ ε :=
  uniform_concentration hW hs0 hs1 hμ

/-- `thm:base-five-profiles`.  For the natural measures of the two base-five systems with
digit sets `{0,1,4}` and `{0,2,4}`, the pair-distance distributions take the values
`eq:base-five-distances` at every scale `5⁻ⁿ`, and the expected profiles stay a fixed
distance apart along a sequence tending to infinity, the form of
`limsup |H_{μ₁}^s - H_{μ₂}^s| > 0` that `thm:main` consumes. -/
theorem audit_base_five_profiles {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K₁ baseFiveDim μ₁)
    (hμ₂ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K₂ baseFiveDim μ₂) :
    (∀ n : ℕ, Phi μ₁ ((1 / 5 : ℝ) ^ n) = 3 / 2 * (1 / 3 : ℝ) ^ n - 1 / 2 * (1 / 9 : ℝ) ^ n ∧
      Phi μ₂ ((1 / 5 : ℝ) ^ n) = (1 / 3 : ℝ) ^ n) ∧
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H baseFiveDim μ₁ t - H baseFiveDim μ₂ t| :=
  baseFive_profiles hμ₁ hμ₂

/-- The first display after `thm:base-five-profiles`: the occupation laws of the two
base-five natural measures are mutually singular, by `thm:main`. -/
theorem audit_base_five_occupation_laws {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K₁ baseFiveDim μ₁)
    (hμ₂ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K₂ baseFiveDim μ₂) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) :=
  MinkowskiReconstruction.baseFive_occupationLaw_mutuallySingular hW hμ₁ hμ₂

/-- The second display after `thm:base-five-profiles`: the laws of the compact Brownian
images of the two base-five attractors are mutually singular, by
`thm:minkowski-reconstruction`. -/
theorem audit_base_five_image_laws {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (baseFiveSystem baseFiveDigitsA baseFiveDigitsA_le).IsNatural K₁ baseFiveDim μ₁)
    (hμ₂ : (baseFiveSystem baseFiveDigitsB baseFiveDigitsB_le).IsNatural K₂ baseFiveDim μ₂) :
    (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
      (brownianImageLaw W P hμ₂.compactAttractor) :=
  MinkowskiReconstruction.baseFive_brownianImageLaw_mutuallySingular hW hμ₁ hμ₂

/-- `thm:homometric-example`.  Two distinct strongly separated self-similar measures,
Ahlfors regular of the same dimension `t = log 6 / log 30 ∈ (1/2,1)`, whose attractors are
not isometric, with equal signed convolutions `σ * σ̃`, hence identical pair-distance
distributions and identical expected profiles. -/
theorem audit_homometric_example :
    ∃ (KA KB : Set ℝ) (σA σB : Measure ℝ) (A : ℝ),
      (homSystem digitFunA digitFunA_nonneg digitFunA_le).IsNatural KA tHom σA ∧
      (homSystem digitFunB digitFunB_nonneg digitFunB_le).IsNatural KB tHom σB ∧
      σA ≠ σB ∧
      (homSystem digitFunA digitFunA_nonneg digitFunA_le).StronglySeparated KA (1/45) ∧
      (homSystem digitFunB digitFunB_nonneg digitFunB_le).StronglySeparated KB (1/45) ∧
      tHom ∈ Set.Ioo (1/2 : ℝ) 1 ∧
      IsAhlfors tHom A σA ∧ IsAhlfors tHom A σB ∧
      IsEmpty (KA ≃ᵢ KB) ∧
      σA.conv (reflect σA) = σB.conv (reflect σB) ∧
      (∀ δ : ℝ, Phi σA δ = Phi σB δ) ∧
      (∀ v : ℝ, H tHom σA v = H tHom σB v) :=
  homometric_example

/-- `thm:cantor-application`.  The homogeneous equal-weight measure at any ratio
`0 < λ < 1/2` separates from the natural measure of every non-lattice system of the
same dimension satisfying the open set condition. -/
theorem audit_cantor_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {μA : Measure ℝ} (hA : IsHomogeneousMeasure lam μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    (hosc : S.OpenSetCondition) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDimension lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDimension lam) μ) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) := by
  obtain ⟨KA, hA'⟩ := (isHomogeneousMeasure_iff_exists_isNatural hlam0 hlam).mp hA
  exact homogeneous_application hW hlam0 hlam hA' S
    (hosc.strongOpenSetCondition S hμ.attractor) hna hdim hμ

/-- The paired instance of `thm:cantor-application`, at a parameter satisfying
`eq:non-lattice`. -/
theorem audit_cantor_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {μA : Measure ℝ} (hA : IsHomogeneousMeasure lam μA)
    {μB : Measure ℝ} (hB : IsPairMeasure (homogeneousDimension lam) μB)
    (hnl : Irrational (Real.log (pairedRatio (homogeneousDimension lam))⁻¹ / Real.log 2)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) := by
  obtain ⟨KA, hA'⟩ := (isHomogeneousMeasure_iff_exists_isNatural hlam0 hlam).mp hA
  obtain ⟨KB, hB'⟩ := (isPairMeasure_iff_exists_isNatural
    (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam)).mp hB
  exact homogeneous_application_pair hW hlam0 hlam hA' hB' hnl

/-- The exceptional parameters in the last sentence of `thm:cantor-application` form
a countable set. -/
theorem audit_exceptional_parameters_countable :
    {lam : ℝ | 0 < lam ∧ lam < 1/2 ∧
      ¬ Irrational (Real.log (pairedRatio (homogeneousDimension lam))⁻¹ / Real.log 2)}.Countable :=
  exceptionalParameters_countable

/-- `thm:non-lattice-limit`, `eq:g-non-lattice-limit`.  In the non-lattice case the
normalised profile converges to `m⁻¹ ∫ z`, which is finite and strictly positive, where
`m = ∑ p_i a_i` is the renewal mean and `z = G - F * G` the renewal defect. -/
theorem audit_non_lattice_limit {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hosc : S.OpenSetCondition)
    (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) :=
  non_lattice_limit S hs0 hs1 (hosc.strongOpenSetCondition S hμ.attractor) hdim hna hμ

/-- `eq:gb-limit`: under `eq:non-lattice` the normalised profile of `μ_B` converges to a
finite positive constant. -/
theorem audit_gb_limit {KB : Set ℝ} {μB : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (G (homogeneousDim lam) μB) atTop (𝓝 C) :=
  homogeneous_gb_limit hlam0 hlam hB hnl

/-- `thm:profile-asymptotics`: the natural measure at the similarity dimension
has an asymptotically periodic profile in the lattice case and a positive constant
limit in the non-lattice case. The lattice span is for the full log-ratios. -/
theorem audit_thm_profile_asymptotics
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∀ h : ℝ, 0 < h →
      AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h →
      ∃ Q : ℝ → ℝ, Continuous Q ∧ Function.Periodic Q (h / 2) ∧
        (∀ t, 0 < Q t) ∧ Tendsto (fun t ↦ H s μ t - Q t) atTop (𝓝 0)) ∧
    (S.NonArithmetic → ∃ C : ℝ, 0 < C ∧ Tendsto (H s μ) atTop (𝓝 C)) := by
  have := hμ.isProbabilityMeasure
  constructor
  · intro h hh hlat
    exact lattice_profile_asymptotics S hs0 hs1 hosc hdim hh hlat hμ
  · intro hnl
    obtain ⟨A, hA⟩ := hosc.exists_isFrostman S hs0.le hμ
    obtain ⟨hCpos, hC⟩ := non_lattice_limit S hs0 hs1
      (hosc.strongOpenSetCondition S hμ.attractor) hdim hnl hμ
    exact ⟨_, profile_asymptotics_nonLattice hs0 hs1 hA hCpos hC⟩

/-- The specialised two-map asymptotics in `sec:smoothing`: the natural
measures of the two systems and `eq:non-lattice`.  The renewal constant `C_B` of
`eq:gb-limit` is carried through all three conclusions about `μ_B`: it is the limit of
`G_B`, and `C_B ∫₀^∞ φ` is the limit both of `H_B^s` and of the normalised correlation
integral. -/
theorem audit_homogeneous_profile_asymptotics {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    (∃ CB : ℝ, 0 < CB ∧
        Tendsto (G (homogeneousDim lam) μB) atTop (𝓝 CB) ∧
        Tendsto (H (homogeneousDim lam) μB) atTop
          (𝓝 (CB * ∫ η in Set.Ioi (0:ℝ), kern (homogeneousDim lam) η)) ∧
        0 < CB * ∫ η in Set.Ioi (0:ℝ), kern (homogeneousDim lam) η ∧
        Tendsto (fun r : ℝ => expCorr W P μB r / r ^ (2 * homogeneousDim lam))
          (𝓝[>] 0) (𝓝 (CB * ∫ η in Set.Ioi (0:ℝ), kern (homogeneousDim lam) η))) ∧
      (∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g (Real.log lam⁻¹) ∧
        (∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
          |H (homogeneousDim lam) μA v - smoothOp (homogeneousDim lam) g v|
            ≤ C * Real.exp (-2 * (1 - homogeneousDim lam) * v)) ∧
      (∃ a b : ℝ, a < b ∧
        (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧
          expCorr W P μA r ≤ a * r ^ (2 * homogeneousDim lam)) ∧
        (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧
          b * r ^ (2 * homogeneousDim lam) ≤ expCorr W P μA r)) :=
  homogeneous_thm_profile_asymptotics hW hlam0 hlam hA hB hnl

/-- `thm:non-lattice-separation`.  Two non-lattice systems whose renewal constants
`eq:g-non-lattice-limit` differ have mutually singular Brownian occupation laws. -/
theorem audit_non_lattice_separation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (S₁ : System ι₁) (S₂ : System ι₂) {K₁ K₂ : Set ℝ}
    (hosc₁ : S₁.OpenSetCondition) (hosc₂ : S₂.OpenSetCondition)
    (hdim₁ : S₁.IsDimension s) (hdim₂ : S₂.IsDimension s)
    (hna₁ : S₁.NonArithmetic) (hna₂ : S₂.NonArithmetic)
    {μ₁ μ₂ : Measure ℝ} (hμ₁ : S₁.IsNatural K₁ s μ₁) (hμ₂ : S₂.IsNatural K₂ s μ₂)
    (hne : (S₁.renewalMean s)⁻¹ * ∫ x : ℝ, S₁.renewalDefect s μ₁ x
        ≠ (S₂.renewalMean s)⁻¹ * ∫ x : ℝ, S₂.renewalDefect s μ₂ x) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) :=
  non_lattice_separation hW hs0 hs1 S₁ S₂ (hosc₁.strongOpenSetCondition S₁ hμ₁.attractor)
    (hosc₂.strongOpenSetCondition S₂ hμ₂.attractor) hdim₁ hdim₂ hna₁ hna₂ hμ₁ hμ₂ hne


/-! ### `sec:two-contraction-formula`: the two-contraction family -/

/-- `thm:two-contraction-distinction`.  Along the family `x ↦ x/2`, `x ↦ cx + 1 - c`,
`0 < c < 1/2`, normalise the natural measure `μ_c` at its own dimension `s(c)`, where
`2^{-s(c)} + c^{s(c)} = 1`.  The mean `H̄(c) = lim_{T→∞} T⁻¹ ∫₀ᵀ H_{μ_c}^{s(c)}(t) dt`
exists and is strictly increasing in `c`. -/
theorem audit_two_contraction_distinction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c₁ c₂ s₁ s₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1/2)
    (hs₁ : (2:ℝ) ^ (-s₁) + c₁ ^ s₁ = 1) (hs₂ : (2:ℝ) ^ (-s₂) + c₂ ^ s₂ = 1)
    {μ₁ μ₂ : Measure ℝ} (h₁ : IsTwoContractionMeasure c₁ s₁ μ₁)
    (h₂ : IsTwoContractionMeasure c₂ s₂ μ₂) :
    ∃ H₁ H₂ : ℝ, H₁ < H₂ ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s₁ μ₁ t)
        atTop (𝓝 H₁) ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s₂ μ₂ t)
        atTop (𝓝 H₂) := by
  obtain ⟨hs₁0, hs₁1, -⟩ := dimension_facts hc₁ (hc.trans hc₂) hs₁
  obtain ⟨hs₂0, hs₂1, -⟩ := dimension_facts (hc₁.trans hc) hc₂ hs₂
  obtain ⟨K₁, hK₁⟩ :=
    (isTwoContractionMeasure_iff_exists_isNatural hc₁ (hc.trans hc₂) hs₁).1 h₁
  obtain ⟨K₂, hK₂⟩ :=
    (isTwoContractionMeasure_iff_exists_isNatural (hc₁.trans hc) hc₂ hs₂).1 h₂
  exact ⟨_, _, twoContractionMean_lt_of_lt hc₁ hc hc₂ hs₁ hs₂ hK₁ hK₂,
    tendsto_avg_expectedProfile_of_isNatural hW hc₁ (hc.trans hc₂) hs₁0 hs₁1
      (pairSystem_isDimension_of _ _ hs₁) hK₁,
    tendsto_avg_expectedProfile_of_isNatural hW (hc₁.trans hc) hc₂ hs₂0 hs₂1
      (pairSystem_isDimension_of _ _ hs₂) hK₂⟩

/-- The family of `sec:introduction`: for every `0 < c < 1/2` the dimension `s(c)`, with
`2^{-s(c)} + c^{s(c)} = 1`, exists and is unique, and so does the natural measure `μ_c` at
that dimension.  The statements about the family quantify over these, and are therefore
not vacuous. -/
theorem audit_two_contraction_family {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    ∃! s : ℝ, (2:ℝ) ^ (-s) + c ^ s = 1 ∧
      ∃! μ : Measure ℝ, IsTwoContractionMeasure c s μ := by
  obtain ⟨s, hs, huniq⟩ := exists_unique_twoContractionDim hc0 hc
  refine ⟨s, ⟨hs, ?_⟩, fun s' hs' => huniq s' hs'.1⟩
  have hdim := pairSystem_isDimension_of hc0 hc hs
  obtain ⟨⟨K, ν⟩, hν, -⟩ := (pairSystem c hc0 hc).exists_unique_isNatural hdim
  refine ⟨ν, (isTwoContractionMeasure_iff_exists_isNatural hc0 hc hs).2 ⟨K, hν⟩,
    fun μ hμ => ?_⟩
  obtain ⟨K', hK'⟩ := (isTwoContractionMeasure_iff_exists_isNatural hc0 hc hs).1 hμ
  have := hK'.isProbabilityMeasure
  have := hν.isProbabilityMeasure
  exact Hutchinson.eq_of_selfSimilar _ hdim hK'.selfSimilar hν.selfSimilar hK'.support_Icc
    hν.support_Icc

/-- The final assertion of `thm:two-contraction-distinction`: for distinct parameters,
`limsup_{t→∞} |H_{μ_{c₁}}^{s(c₁)}(t) - H_{μ_{c₂}}^{s(c₂)}(t)| > 0`, written out as in
`eq:profile-separation`. -/
theorem audit_two_contraction_separation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c₁ c₂ s₁ s₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ < 1/2) (hc₂ : 0 < c₂) (hc₂' : c₂ < 1/2)
    (hne : c₁ ≠ c₂)
    (hs₁ : (2:ℝ) ^ (-s₁) + c₁ ^ s₁ = 1) (hs₂ : (2:ℝ) ^ (-s₂) + c₂ ^ s₂ = 1)
    {μ₁ μ₂ : Measure ℝ} (h₁ : IsTwoContractionMeasure c₁ s₁ μ₁)
    (h₂ : IsTwoContractionMeasure c₂ s₂ μ₂) :
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V,
      ε ≤ |expectedProfile W P s₁ μ₁ t - expectedProfile W P s₂ μ₂ t| := by
  obtain ⟨hs₁0, hs₁1, -⟩ := dimension_facts hc₁ hc₁' hs₁
  obtain ⟨hs₂0, hs₂1, -⟩ := dimension_facts hc₂ hc₂' hs₂
  obtain ⟨K₁, hK₁⟩ := (isTwoContractionMeasure_iff_exists_isNatural hc₁ hc₁' hs₁).1 h₁
  obtain ⟨K₂, hK₂⟩ := (isTwoContractionMeasure_iff_exists_isNatural hc₂ hc₂' hs₂).1 h₂
  have := hK₁.isProbabilityMeasure
  have := hK₂.isProbabilityMeasure
  obtain ⟨A₁, hA₁⟩ :=
    (pairSystem_openSetCondition hc₁ hc₁' hK₁.attractor).exists_isFrostman _ hs₁0.le hK₁
  obtain ⟨A₂, hA₂⟩ :=
    (pairSystem_openSetCondition hc₂ hc₂' hK₂.attractor).exists_isFrostman _ hs₂0.le hK₂
  have hcont₁ : Continuous (expectedProfile W P s₁ μ₁) := by
    rw [funext (expectedProfile_eq_H hW hs₁0 hs₁1 hA₁)]
    exact (profile_uniformContinuous hs₁0 hs₁1 hA₁).continuous
  have hcont₂ : Continuous (expectedProfile W P s₂ μ₂) := by
    rw [funext (expectedProfile_eq_H hW hs₂0 hs₂1 hA₂)]
    exact (profile_uniformContinuous hs₂0 hs₂1 hA₂).continuous
  have hmeanne : twoContractionMean c₁ s₁ μ₁ ≠ twoContractionMean c₂ s₂ μ₂ := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (twoContractionMean_lt_of_lt hc₁ hlt hc₂' hs₁ hs₂ hK₁ hK₂).ne
    · exact (twoContractionMean_lt_of_lt hc₂ hgt hc₁' hs₂ hs₁ hK₂ hK₁).ne'
  exact exists_ge_abs_sub_of_tendsto_avg hcont₁ hcont₂ hmeanne
    (tendsto_avg_expectedProfile_of_isNatural hW hc₁ hc₁' hs₁0 hs₁1
      (pairSystem_isDimension_of _ _ hs₁) hK₁)
    (tendsto_avg_expectedProfile_of_isNatural hW hc₂ hc₂' hs₂0 hs₂1
      (pairSystem_isDimension_of _ _ hs₂) hK₂)

/-- The display before `thm:two-contraction-distinction`, with `eq:two-contraction-mean`:
for every `0 < c < 1/2` the mean `H̄(c) = lim_{T→∞} T⁻¹ ∫₀ᵀ H_{μ_c}^{s(c)}` exists, and it
equals `2pq 2^{-s} Γ(1-s) M_c(s)/(sm)` with `p = 2^{-s}`, `q = c^s`,
`m = p log 2 + q log(1/c)` and `M_c(s) = 𝔼 Z_c^{-s}`, `Z_c = 1 - c + cY - X/2`, in the
lattice and the non-lattice case alike. -/
theorem audit_two_contraction_mean {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (hs : (2:ℝ) ^ (-s) + c ^ s = 1)
    {μ : Measure ℝ} (hμ : IsTwoContractionMeasure c s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s μ t) atTop
      (𝓝 (2 * (2:ℝ) ^ (-s) * c ^ s * (2:ℝ) ^ (-s) * Real.Gamma (1 - s) * crossMoment c μ s /
        (s * ((2:ℝ) ^ (-s) * Real.log 2 + c ^ s * Real.log c⁻¹)))) := by
  obtain ⟨hs0, hs1, -⟩ := dimension_facts hc0 hc hs
  obtain ⟨K, hK⟩ := (isTwoContractionMeasure_iff_exists_isNatural hc0 hc hs).1 hμ
  have hhalf : (1/2 : ℝ) ^ s = (2:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
  have h := tendsto_avg_expectedProfile_of_isNatural hW hc0 hc hs0 hs1
    (pairSystem_isDimension_of _ _ hs) hK
  rw [twoContractionMean, hhalf] at h
  convert h using 2
  ring

/-- `eq:two-contraction-constant`: if `log(1/c)/log 2` is irrational, the expected profile
itself converges to `2pq 2^{-s} Γ(1-s) M_c(s)/(sm)`. -/
theorem audit_two_contraction_constant {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (hs : (2:ℝ) ^ (-s) + c ^ s = 1)
    {μ : Measure ℝ} (hμ : IsTwoContractionMeasure c s μ)
    (hirr : Irrational (Real.log c⁻¹ / Real.log 2)) :
    Tendsto (expectedProfile W P s μ) atTop
      (𝓝 (2 * (2:ℝ) ^ (-s) * c ^ s * (2:ℝ) ^ (-s) * Real.Gamma (1 - s) * crossMoment c μ s /
        (s * ((2:ℝ) ^ (-s) * Real.log 2 + c ^ s * Real.log c⁻¹)))) := by
  obtain ⟨hs0, hs1, hceq⟩ := dimension_facts hc0 hc hs
  obtain ⟨K, hK⟩ := (isTwoContractionMeasure_iff_exists_isNatural hc0 hc hs).1 hμ
  have := hK.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (pairSystem_openSetCondition hc0 hc hK.attractor).exists_isFrostman _ hs0.le hK
  have hhalf : (1/2 : ℝ) ^ s = (2:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
  have hna : (pairSystem c hc0 hc).NonArithmetic := by
    subst hceq
    exact (pairSystem_nonArithmetic_iff hs0 hs1).2 hirr
  have h := pairSystem_tendsto_H_nonLattice hc0 hc hs0 hs1
    (pairSystem_isDimension_of _ _ hs) hK hna
  rw [twoContractionMean, hhalf] at h
  rw [funext (expectedProfile_eq_H hW hs0 hs1 hA)]
  convert h using 2
  ring


/-- `thm:renewal-average`.  For the natural measure of a system under the open set
condition, and every frequency `ξ` with `e^{iξ a_i} = 1` for all log-ratios, the averages
of `G(w) e^{-iξw}` over `[0, T]` converge to `m⁻¹ ∫ z(w) e^{-iξw} dw`
(`eq:renewal-average`), and the averages of `H_μ^s` converge to `(∫₀^∞ φ) m⁻¹ ∫ z`
(`eq:mean-profile`), with no case split between lattice and non-lattice systems. -/
theorem audit_renewal_average {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hosc : S.OpenSetCondition)
    (hdim : S.IsDimension s) {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∀ ξ : ℝ, (∀ i, Complex.exp (Complex.I * ξ * S.logRatio i) = 1) →
      Tendsto (fun T : ℝ => T⁻¹ • ∫ u in (0:ℝ)..T,
          (G s μ u : ℂ) * Complex.exp (-(Complex.I * ξ * u))) atTop
        (𝓝 ((S.renewalMean s)⁻¹ • ∫ w, (S.renewalDefect s μ w : ℂ) *
          Complex.exp (-(Complex.I * ξ * w))))) ∧
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, H s μ t) atTop
      (𝓝 ((∫ η in Set.Ioi (0:ℝ), kern s η) *
        ((S.renewalMean s)⁻¹ * ∫ w, S.renewalDefect s μ w))) :=
  ⟨fun _ hξ => hμ.tendsto_avg_G_char S hs0 hs1 hosc hdim hξ,
    hμ.tendsto_avg_H S hs0 hs1 hosc hdim⟩

/-- The coding of `sec:two-contraction-formula`: at the natural parameters
`b = c(s)`, `v = q(s) = 1 - 2^{-s}`, the moment `M_{c(s)}(s)` of the natural measure is
`J(s, c(s), q(s))`, the mean of `Z^{-s}` over two independent Bernoulli codings. -/
theorem audit_moment_coding {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {K : Set ℝ}
    {μ : Measure ℝ} (hμ : (pairSystem (pairRatio s) (pairRatio_pos hs0)
      (pairRatio_lt_half hs0 hs1)).IsNatural K s μ) :
    crossMoment (pairRatio s) μ s = crossJ s (pairRatio s) (1 - (2:ℝ) ^ (-s)) :=
  crossMoment_eq_momentM hs0 hs1 hμ

/-- `thm:parameter-steps`: the three one-sided bounds on `J(α, b, v) = 𝔼 Z^{-α}`, in the
exponent (`eq:exponent-step`), in the contraction where `v(3 - 2b) ≤ 1`
(`eq:contraction-step`), and in the weight (`eq:weight-step`). -/
theorem audit_parameter_steps :
    (∀ {α α' b v : ℝ}, 0 ≤ α → α ≤ α' → 0 < b → b < 1/2 → 0 ≤ v → v ≤ 1 →
      crossJ α b v ≤ crossJ α' b v) ∧
    (∀ {α b b' v : ℝ}, 0 ≤ α → 0 < b → b ≤ b' → b' < 1/2 → 0 ≤ v → v ≤ 1 →
      v * (3 - 2 * b) ≤ 1 → crossJ α b v ≤ crossJ α b' v) ∧
    (∀ {α b v v' : ℝ}, 0 ≤ α → 0 < b → b < 1/2 → 0 ≤ v → v ≤ v' → v' ≤ 1 → v < 1 →
      crossJ α b v * (1 - (v' - v) * (2 * α * b * (1 - b) / ((1/2 - b) * (1 - v))))
        ≤ crossJ α b v') :=
  ⟨crossJ_mono_exponent, crossJ_mono_contraction, crossJ_weight_ge⟩

/-- `thm:local-monotonicity`: a function that, at every point of an interval, is larger
slightly to the right and smaller slightly to the left is strictly increasing on the
interval.  No continuity is assumed. -/
theorem audit_local_monotonicity {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hloc : ∀ x ∈ I, (∀ᶠ y in 𝓝[>] x, f x < f y) ∧ (∀ᶠ y in 𝓝[<] x, f y < f x)) :
    StrictMonoOn f I :=
  strictMonoOn_of_local hI hloc

/-- `eq:two-contraction-periodic`: in the lattice case, with `h > 0` the span of the group
generated by `log 2` and `log(1/c)` and `ζ_k = s - 2πik/h`, the coefficients
`c_k = (2pq/m) 2^{-ζ_k} Γ(1-ζ_k) M_c(ζ_k)/ζ_k` of `twoContractionCoeff` are absolutely
summable, and `H_{μ_c}^s(t) - ∑_k c_k e^{4πikt/h} → 0`. -/
theorem audit_two_contraction_periodic {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (hs : (2:ℝ) ^ (-s) + c ^ s = 1)
    {μ : Measure ℝ} (hμ : IsTwoContractionMeasure c s μ) {h : ℝ} (hh : 0 < h)
    (hspan : AddSubgroup.closure ({Real.log 2, Real.log c⁻¹} : Set ℝ)
      = AddSubgroup.zmultiples h) :
    Summable (fun k : ℤ => ‖twoContractionCoeff c s μ h k‖) ∧
      Tendsto (fun t : ℝ => (expectedProfile W P s μ t : ℂ) - ∑' k : ℤ,
        twoContractionCoeff c s μ h k * Complex.exp (4 * Real.pi * Complex.I * k * t / h))
        atTop (𝓝 0) := by
  obtain ⟨hs0, hs1, -⟩ := dimension_facts hc0 hc hs
  obtain ⟨K, hK⟩ := (isTwoContractionMeasure_iff_exists_isNatural hc0 hc hs).1 hμ
  have := hK.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (pairSystem_openSetCondition hc0 hc hK.attractor).exists_isFrostman _ hs0.le hK
  have hlat : AddSubgroup.closure (Set.range (pairSystem c hc0 hc).logRatio)
      = AddSubgroup.zmultiples h := by
    rw [pairSystem_range_logRatio, Set.pair_comm]; exact hspan
  rw [funext (expectedProfile_eq_H hW hs0 hs1 hA)]
  exact pairSystem_periodic hc0 hc hs0 hs1 (pairSystem_isDimension_of _ _ hs) hh hlat hK

/-- `thm:two-contraction-formula`, bundled.  With `p = 2^{-s}`, `q = c^s`,
`m = p log 2 + q log(1/c)` and `M_c(s) = 𝔼 Z_c^{-s}`: if `log(1/c)/log 2` is irrational,
`H_{μ_c}^s` converges to `2pq 2^{-s} Γ(1-s) M_c(s)/(sm)` (`eq:two-contraction-constant`);
if it is rational, the group generated by `log 2` and `log(1/c)` has a span `h > 0`, the
coefficients of `eq:two-contraction-periodic` are absolutely summable and `H_{μ_c}^s` is
asymptotic to their Fourier series; in both cases the mean is
`2pq 2^{-s} Γ(1-s) M_c(s)/(sm)` (`eq:two-contraction-mean`). -/
theorem audit_thm_two_contraction_formula {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c s : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (hs : (2:ℝ) ^ (-s) + c ^ s = 1)
    {μ : Measure ℝ} (hμ : IsTwoContractionMeasure c s μ) :
    (Irrational (Real.log c⁻¹ / Real.log 2) →
      Tendsto (expectedProfile W P s μ) atTop
        (𝓝 (2 * (2:ℝ) ^ (-s) * c ^ s * (2:ℝ) ^ (-s) * Real.Gamma (1 - s) *
          crossMoment c μ s / (s * ((2:ℝ) ^ (-s) * Real.log 2 + c ^ s * Real.log c⁻¹))))) ∧
    (¬ Irrational (Real.log c⁻¹ / Real.log 2) →
      ∃ h : ℝ, 0 < h ∧ AddSubgroup.closure ({Real.log 2, Real.log c⁻¹} : Set ℝ)
          = AddSubgroup.zmultiples h ∧
        Summable (fun k : ℤ => ‖twoContractionCoeff c s μ h k‖) ∧
        Tendsto (fun t : ℝ => (expectedProfile W P s μ t : ℂ) - ∑' k : ℤ,
          twoContractionCoeff c s μ h k * Complex.exp (4 * Real.pi * Complex.I * k * t / h))
          atTop (𝓝 0)) ∧
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s μ t) atTop
      (𝓝 (2 * (2:ℝ) ^ (-s) * c ^ s * (2:ℝ) ^ (-s) * Real.Gamma (1 - s) * crossMoment c μ s /
        (s * ((2:ℝ) ^ (-s) * Real.log 2 + c ^ s * Real.log c⁻¹)))) := by
  refine ⟨audit_two_contraction_constant hW hc0 hc hs hμ, fun hrat => ?_,
    audit_two_contraction_mean hW hc0 hc hs hμ⟩
  obtain ⟨hs0, hs1, hceq⟩ := dimension_facts hc0 hc hs
  have hna : ¬ (pairSystem c hc0 hc).NonArithmetic := by
    subst hceq
    rw [pairSystem_nonArithmetic_iff hs0 hs1]
    exact hrat
  rcases (pairSystem c hc0 hc).nonArithmetic_or_exists_lattice with hd | ⟨h, hh, hlat⟩
  · exact absurd hd hna
  · have hspan : AddSubgroup.closure ({Real.log 2, Real.log c⁻¹} : Set ℝ)
        = AddSubgroup.zmultiples h := by
      rw [Set.pair_comm, ← pairSystem_range_logRatio hc0 hc]; exact hlat
    exact ⟨h, hh, hspan, audit_two_contraction_periodic hW hc0 hc hs hμ hh hspan⟩

/-! ### `sec:small-dimension`: monotonicity for small dimension

The family of `sec:fixed-dimension-family` with `a = p^{1/s}`, `b = q^{1/s}`, `q = 1 - p`:
`fixedMoment s p` is `M_p(s) = 𝔼 Z_p^{-s}` through the Bernoulli coding of `μ_p`,
`entropy p` is `E(p)`, `fixedMean s p` is the right-hand side of `eq:fixed-dimension-mean`,
and `kappa p` the logarithmic derivative `κ` of the entropy factor. -/

/-- `sec:fixed-dimension-family`: the attractor `K_p` and the natural measure `μ_p` of the
system `x ↦ ax`, `x ↦ bx + 1 - b` with `a = p^{1/s}`, `b = (1-p)^{1/s}` exist and are
unique. -/
theorem audit_exists_fixed_dimension_measure {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∃! m : Set ℝ × Measure ℝ, (fixedSystem s p hs hp0 hp1).IsNatural m.1 s m.2 :=
  (fixedSystem s p hs hp0 hp1).exists_unique_isNatural (fixedSystem_isDimension hs hp0 hp1)

/-- `sec:small-dimension`, the moment `M_p(s) = 𝔼 Z_p^{-s}`: `fixedMoment s p` is the
integral of `Z_p^{-s} = (1 - b + bY - aX)^{-s}` against `μ_p ⊗ μ_p` for the natural measure
`μ_p` of the system. -/
theorem audit_fixed_moment_natural {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    fixedMoment s p = ∫ y, ∫ x,
      (1 - (1 - p) ^ s⁻¹ + (1 - p) ^ s⁻¹ * y - p ^ s⁻¹ * x) ^ (-s) ∂μ ∂μ :=
  fixedMoment_eq_natural hs hp0 hp1 hμ

/-- `sec:small-dimension`, `M_p ≥ 1`, since `Z_p ≤ 1`. -/
theorem audit_fixed_moment_ge_one {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) : 1 ≤ fixedMoment s p :=
  one_le_fixedMoment hs hs1 hp0 hp1

/-- `eq:log-derivative-mean`: `κ` is the logarithmic derivative of the entropy factor
`pq/E(p)`, and wherever `M_p` is differentiable the mean `H̄_s = C_s (pq/E) M_p` has
derivative `C_s (pq/E) (κ M_p + M_p')`, with `C_s = 2^{1-s} Γ(1-s)`. -/
theorem audit_log_derivative_mean {s p D : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hM : HasDerivAt (fixedMoment s) D p) :
    HasDerivAt (fun x => x * (1 - x) / entropy x) (p * (1 - p) / entropy p * kappa p) p ∧
    HasDerivAt (fixedMean s)
      ((2:ℝ) ^ (1 - s) * Real.Gamma (1 - s) * (p * (1 - p) / entropy p) *
        (kappa p * fixedMoment s p + D)) p :=
  ⟨hasDerivAt_entropyFactor hp0 hp1, hasDerivAt_fixedMean hp0 hp1 hM⟩

/-- `thm:entropy-factor`: `κ > 0` on `(0, 1/2)`, `κ(p) ≥ 0.88/(p log(e/p))` for
`p ≤ 1/50`, and `κ(p) ≥ c (1/2 - p)` on `[p₁, 1/2)` for some `c > 0`. -/
theorem audit_entropy_factor :
    (∀ p ∈ Set.Ioo (0:ℝ) (1/2), 0 < kappa p) ∧
    (∀ p ∈ Set.Ioc (0:ℝ) (1/50), 0.88 / (p * (1 - Real.log p)) ≤ kappa p) ∧
    (∀ p₁ ∈ Set.Ioo (0:ℝ) (1/2), ∃ c > 0, ∀ p ∈ Set.Ico p₁ (1/2),
      c * (1/2 - p) ≤ kappa p) :=
  ⟨fun p hp => kappa_pos hp.1 hp.2, fun p hp => kappa_ge_of_le hp.1 hp.2,
    fun p₁ hp₁ => kappa_ge_of_ge hp₁.1 hp₁.2⟩

/-- `eq:leading-ones`: `M_p = ∑_{n ≥ 0} p qⁿ 𝔼[(1 - b^{n+1} - a(X - b^{n+1} Y''))^{-s}]`,
with `X`, `Y''` independent of law `μ_p`. -/
theorem audit_leading_ones {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) :
    HasSum (fun n : ℕ => p * (1 - p) ^ n * leadingTerm s p n) (fixedMoment s p) :=
  hasSum_leadingTerm hs hs1 hp0 hp1

/-- `eq:main-term`: `Σ(p) = (e^{sT} - 1) ∑_{m ≥ 1} (e^{mT} - 1)^{-s}` with
`T = log(1/b) = log(1/q)/s`. -/
theorem audit_main_term {s p : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    mainTerm s p = (Real.exp (s * fixedT s p) - 1) *
      ∑' m : ℕ, (Real.exp (((m:ℝ) + 1) * fixedT s p) - 1) ^ (-s) :=
  mainTerm_eq hs hp0 hp1

/-- `thm:main-term-derivative`: for `0 < s ≤ 1/2` and `0 < p ≤ 1/50`, `Σ` is
differentiable at `p` with `|Σ'(p)| ≤ 6 p^{-s}`. -/
theorem audit_main_term_derivative {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) : ∃ D, HasDerivAt (mainTerm s) D p ∧ |D| ≤ 6 * p ^ (-s) :=
  exists_hasDerivAt_mainTerm hs hs1 hp0 hp

/-- `thm:remainder-derivative`: for `0 < s ≤ 1/2` and `0 < p ≤ 1/50`, `M_p` and `Σ` are
differentiable at `p` with `|M_p' - Σ'(p)| ≤ 3000 s (3p/2)^{1/s} p^{-2-s}`. -/
theorem audit_remainder_derivative {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) (hp0 : 0 < p)
    (hp : p ≤ 1/50) :
    ∃ D D', HasDerivAt (fixedMoment s) D p ∧ HasDerivAt (mainTerm s) D' p ∧
      |D - D'| ≤ 3000 * s * (3 * p / 2) ^ s⁻¹ * p ^ (-2 - s) :=
  exists_hasDerivAt_fixedMoment hs hs1 hp0 hp

/-- `thm:second-derivative-small-s`: for `0 < s ≤ 2·10⁻⁵` and `10⁻⁴ ≤ p ≤ 1/2`, `M` is
differentiable on `(p - 5·10⁻⁵, p + 5·10⁻⁵)`, and `M'` is differentiable at `p` with
`|M_p''| ≤ 10¹¹ s γ`, `γ = (1 - 5·10⁻⁵)^{1/s}`. -/
theorem audit_second_derivative_small_s {s p : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000)
    (hp0 : 1 / 10000 ≤ p) (hp1 : p ≤ 1/2) :
    (∀ x ∈ Set.Ioo (p - 5 / 100000) (p + 5 / 100000),
      HasDerivAt (fixedMoment s) (deriv (fixedMoment s) x) x) ∧
    ∃ D, HasDerivAt (deriv (fixedMoment s)) D p ∧
      |D| ≤ 10 ^ 11 * s * (1 - 5 / 100000) ^ s⁻¹ :=
  fixedMoment_second_derivative hs hsQ hp0 hp1

/-- The symmetry `M_p = M_{1-p}` in the proof of `thm:small-dimension-monotone`, in the
form the proof uses: `M` is differentiable at `1/2` with `M_{1/2}' = 0`. -/
theorem audit_moment_symmetric_derivative {s : ℝ} (hs : 0 < s) (hsQ : s ≤ 2 / 100000) :
    HasDerivAt (fixedMoment s) 0 (1/2) := by
  have h := hasDerivAt_fixedMoment_of_le_half hs hsQ (by norm_num) le_rfl
  rwa [deriv_fixedMoment_half hs hsQ] at h

/-- `thm:small-dimension-monotone`: there is `s₀ ∈ (0, 1)` such that for every
`s ∈ (0, s₀]` the mean `p ↦ H̄_s(p)` is strictly increasing on `(0, 1/2]`. -/
theorem audit_small_dimension_monotone :
    ∃ s₀ ∈ Set.Ioo (0:ℝ) 1, ∀ s ∈ Set.Ioc (0:ℝ) s₀,
      StrictMonoOn (fixedMean s) (Set.Ioc 0 (1/2)) :=
  exists_strictMonoOn_fixedMean

/-- `thm:critical-set-finite`, the strict increase on `(0, p₀]`: for every `s ∈ (0, 1/2]`
there is `p₀ ∈ (0, 1/2)` with `H̄_s` strictly increasing on `(0, p₀]`. -/
theorem audit_critical_set_finite {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) :
    ∃ p₀ ∈ Set.Ioo (0:ℝ) (1/2), StrictMonoOn (fixedMean s) (Set.Ioc 0 p₀) :=
  exists_strictMonoOn_fixedMean_small hs hs1

/-! ### `sec:fixed-dimension-family` and `sec:fixed-dimension-separation`

The objects are those of `sec:small-dimension` above; `criticalSet s` is the critical set
`D_s` of `H̄_s` in `(0, 1/2)` and `levelSet s p₁` the level set of `H̄_s` through `p₁` in
`(0, 1/2]`. -/

/-- The display before `thm:fixed-dimension-analyticity`: `M_p = M_{1-p}` and
`H̄_s(p) = H̄_s(1-p)` on `(0,1)`. -/
theorem audit_fixed_dimension_symmetry {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p)
    (hp1 : p < 1) :
    fixedMoment s (1 - p) = fixedMoment s p ∧ fixedMean s (1 - p) = fixedMean s p :=
  ⟨fixedMoment_symm hs hs1 hp0 hp1, fixedMean_symm hs hs1 hp0 hp1⟩

/-- `thm:fixed-dimension-analyticity`: `p ↦ M_p(s)` and `p ↦ H̄_s(p)` are real analytic on
`(0,1)`. -/
theorem audit_fixed_dimension_analyticity {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    AnalyticOnNhd ℝ (fixedMoment s) (Set.Ioo 0 1) ∧
      AnalyticOnNhd ℝ (fixedMean s) (Set.Ioo 0 1) :=
  ⟨analyticOnNhd_fixedMoment hs hs1, analyticOnNhd_fixedMean hs hs1⟩

/-- The singularity consequences of `thm:fixed-dimension-range`,
`thm:fixed-dimension-separation` and `thm:small-dimension-monotone`: two parameters of the
family with distinct means have mutually singular image-measure laws, by `thm:main`, and
mutually singular compact-image laws, by `thm:minkowski-reconstruction`. -/
theorem audit_fixed_dimension_laws {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p₁ p₂ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
    {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : (fixedSystem s p₁ hs hp₁0 hp₁1).IsNatural K₁ s μ₁)
    (hμ₂ : (fixedSystem s p₂ hs hp₂0 hp₂1).IsNatural K₂ s μ₂)
    (hne : fixedMean s p₁ ≠ fixedMean s p₂) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) ∧
      (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
        (brownianImageLaw W P hμ₂.compactAttractor) :=
  ⟨MinkowskiReconstruction.fixedSystem_occupationLaw_mutuallySingular hW hs hs1 hp₁0 hp₁1 hp₂0
      hp₂1 hμ₁ hμ₂ hne,
    MinkowskiReconstruction.fixedSystem_brownianImageLaw_mutuallySingular hW hs hs1 hp₁0 hp₁1
      hp₂0 hp₂1 hμ₁ hμ₂ hne⟩

/-- `thm:fixed-dimension-range`: `p ↦ H̄_s(p)` is continuous and strictly positive on
`(0, 1/2]`, `H̄_s(p) → 0` as `p ↓ 0`, and there is an uncountable `S ⊆ (0, 1/2)` on which the
mean is injective, so that by `audit_fixed_dimension_laws` the parameters of `S` have pairwise
mutually singular image-measure and compact-image laws. -/
theorem audit_fixed_dimension_range {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ContinuousOn (fixedMean s) (Set.Ioc 0 (1/2)) ∧
    (∀ p ∈ Set.Ioc (0:ℝ) (1/2), 0 < fixedMean s p) ∧
    Tendsto (fixedMean s) (𝓝[>] 0) (𝓝 0) ∧
    ∃ S : Set ℝ, S ⊆ Set.Ioo 0 (1/2) ∧ ¬ S.Countable ∧ S.InjOn (fixedMean s) :=
  ⟨(continuousOn_fixedMean hs hs1).mono fun p hp => ⟨hp.1, by linarith [hp.2]⟩,
    fun p hp => fixedMean_pos hs hs1 hp.1 (by linarith [hp.2]),
    tendsto_fixedMean_zero hs hs1, exists_uncountable_injOn_fixedMean hs hs1⟩

/-- `thm:fixed-dimension-range`, bundled with its consequence: the uncountable subfamily
has pairwise mutually singular image-measure and compact-image laws. -/
theorem audit_thm_fixed_dimension_range {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ContinuousOn (fixedMean s) (Set.Ioc 0 (1/2)) ∧
    (∀ p ∈ Set.Ioc (0:ℝ) (1/2), 0 < fixedMean s p) ∧
    Tendsto (fixedMean s) (𝓝[>] 0) (𝓝 0) ∧
    ∃ S : Set ℝ, S ⊆ Set.Ioo 0 (1/2) ∧ ¬ S.Countable ∧
      ∀ p₁ ∈ S, ∀ p₂ ∈ S, p₁ ≠ p₂ →
        ∀ (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
          {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
          (hμ₁ : (fixedSystem s p₁ hs hp₁0 hp₁1).IsNatural K₁ s μ₁)
          (hμ₂ : (fixedSystem s p₂ hs hp₂0 hp₂1).IsNatural K₂ s μ₂),
          (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) ∧
            (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
              (brownianImageLaw W P hμ₂.compactAttractor) := by
  obtain ⟨hc, hpos, hlim, S, hS, hSc, hinj⟩ := audit_fixed_dimension_range hs hs1
  refine ⟨hc, hpos, hlim, S, hS, hSc, fun p₁ hp₁ p₂ hp₂ hne hp₁0 hp₁1 hp₂0 hp₂1 K₁ K₂ μ₁ μ₂
    hμ₁ hμ₂ => ?_⟩
  exact audit_fixed_dimension_laws hW hs hs1 hp₁0 hp₁1 hp₂0 hp₂1 hμ₁ hμ₂ (hinj.ne hp₁ hp₂ hne)

/-- `thm:fixed-dimension-separation`, the analytic assertions: `D_s` has no accumulation
point in `(0, 1/2]`; on every interval of `(0, 1/2)` free of critical points the mean is
strictly monotone; some `(1/2 - ε_s, 1/2)` is such an interval; and for every `p₁ ∈ (0, 1/2]`
the level set through `p₁` has no accumulation point in `(0, 1/2]` and is countable. -/
theorem audit_fixed_dimension_separation {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (∀ p ∈ Set.Ioc (0:ℝ) (1/2), ¬ AccPt p (𝓟 (criticalSet s))) ∧
    (∀ α β : ℝ, Set.Ioo α β ⊆ Set.Ioo 0 (1/2) →
      (∀ q ∈ Set.Ioo α β, deriv (fixedMean s) q ≠ 0) →
      StrictMonoOn (fixedMean s) (Set.Ioo α β) ∨ StrictAntiOn (fixedMean s) (Set.Ioo α β)) ∧
    (∃ ε ∈ Set.Ioo (0:ℝ) (1/2), (∀ q ∈ Set.Ioo (1/2 - ε) (1/2), deriv (fixedMean s) q ≠ 0) ∧
      (StrictMonoOn (fixedMean s) (Set.Ioo (1/2 - ε) (1/2)) ∨
        StrictAntiOn (fixedMean s) (Set.Ioo (1/2 - ε) (1/2)))) ∧
    (∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2),
      (∀ p ∈ Set.Ioc (0:ℝ) (1/2), ¬ AccPt p (𝓟 (levelSet s p₁))) ∧ (levelSet s p₁).Countable) :=
  ⟨fun p hp => not_accPt_criticalSet hs hs1 hp,
    fun _ _ hsub hne => strictMono_or_anti_of_ne_zero hs hs1 hsub hne,
    exists_eps_strictMono hs hs1,
    fun p₁ _ => ⟨fun p hp => not_accPt_levelSet hs hs1 p₁ hp, levelSet_countable hs hs1 p₁⟩⟩

/-- `thm:fixed-dimension-separation`, bundled: the analytic assertions together with the
mutual singularity of the laws for all `p₁, p₂ ∈ (0, 1/2]` with distinct means. -/
theorem audit_thm_fixed_dimension_separation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (∀ p ∈ Set.Ioc (0:ℝ) (1/2), ¬ AccPt p (𝓟 (criticalSet s))) ∧
    (∀ α β : ℝ, Set.Ioo α β ⊆ Set.Ioo 0 (1/2) →
      (∀ q ∈ Set.Ioo α β, deriv (fixedMean s) q ≠ 0) →
      StrictMonoOn (fixedMean s) (Set.Ioo α β) ∨ StrictAntiOn (fixedMean s) (Set.Ioo α β)) ∧
    (∃ ε ∈ Set.Ioo (0:ℝ) (1/2), (∀ q ∈ Set.Ioo (1/2 - ε) (1/2), deriv (fixedMean s) q ≠ 0) ∧
      (StrictMonoOn (fixedMean s) (Set.Ioo (1/2 - ε) (1/2)) ∨
        StrictAntiOn (fixedMean s) (Set.Ioo (1/2 - ε) (1/2)))) ∧
    (∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2),
      (∀ p ∈ Set.Ioc (0:ℝ) (1/2), ¬ AccPt p (𝓟 (levelSet s p₁))) ∧ (levelSet s p₁).Countable) ∧
    (∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2), ∀ p₂ ∈ Set.Ioc (0:ℝ) (1/2),
      fixedMean s p₁ ≠ fixedMean s p₂ →
      ∀ (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
        {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
        (hμ₁ : (fixedSystem s p₁ hs hp₁0 hp₁1).IsNatural K₁ s μ₁)
        (hμ₂ : (fixedSystem s p₂ hs hp₂0 hp₂1).IsNatural K₂ s μ₂),
        (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) ∧
          (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
            (brownianImageLaw W P hμ₂.compactAttractor)) := by
  obtain ⟨h1, h2, h3, h4⟩ := audit_fixed_dimension_separation hs hs1
  exact ⟨h1, h2, h3, h4, fun p₁ _ p₂ _ hne hp₁0 hp₁1 hp₂0 hp₂1 K₁ K₂ μ₁ μ₂ hμ₁ hμ₂ =>
    audit_fixed_dimension_laws hW hs hs1 hp₁0 hp₁1 hp₂0 hp₂1 hμ₁ hμ₂ hne⟩

/-- `thm:small-dimension-monotone`, bundled with its second sentence: for `s ≤ s₀` the mean
is strictly increasing on `(0, 1/2]`, and distinct `p₁, p₂ ∈ (0, 1/2]` have mutually singular
image-measure and compact-image laws. -/
theorem audit_thm_small_dimension_monotone {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) :
    ∃ s₀ ∈ Set.Ioo (0:ℝ) 1, ∀ s, ∀ hs : s ∈ Set.Ioc (0:ℝ) s₀,
      StrictMonoOn (fixedMean s) (Set.Ioc 0 (1/2)) ∧
      ∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2), ∀ p₂ ∈ Set.Ioc (0:ℝ) (1/2), p₁ ≠ p₂ →
        ∀ (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1)
          {K₁ K₂ : Set ℝ} {μ₁ μ₂ : Measure ℝ}
          (hμ₁ : (fixedSystem s p₁ hs.1 hp₁0 hp₁1).IsNatural K₁ s μ₁)
          (hμ₂ : (fixedSystem s p₂ hs.1 hp₂0 hp₂1).IsNatural K₂ s μ₂),
          (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) ∧
            (brownianImageLaw W P hμ₁.compactAttractor).MutuallySingular
              (brownianImageLaw W P hμ₂.compactAttractor) := by
  obtain ⟨s₀, hs₀, hmono⟩ := exists_strictMonoOn_fixedMean
  refine ⟨s₀, hs₀, fun s hs => ⟨hmono s hs, fun p₁ hp₁ p₂ hp₂ hne hp₁0 hp₁1 hp₂0 hp₂1 K₁ K₂ μ₁ μ₂
    hμ₁ hμ₂ => ?_⟩⟩
  exact audit_fixed_dimension_laws hW hs.1 (by linarith [hs.2, hs₀.2]) hp₁0 hp₁1 hp₂0 hp₂1 hμ₁ hμ₂
    ((hmono s hs).injOn.ne hp₁ hp₂ hne)

/-- `thm:critical-set-finite`, bundled: the strict increase on some `(0, p₀]` and the
finiteness of `D_s`, for every `s ∈ (0, 1/2]`. -/
theorem audit_thm_critical_set_finite {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) :
    (∃ p₀ ∈ Set.Ioo (0:ℝ) (1/2), StrictMonoOn (fixedMean s) (Set.Ioc 0 p₀)) ∧
      (criticalSet s).Finite :=
  ⟨exists_strictMonoOn_fixedMean_small hs hs1, criticalSet_finite hs hs1⟩

/-! ### `thm:fixed-dimension-profiles` -/

/-- `eq:fixed-dimension-mean` of `thm:fixed-dimension-profiles`: the mean profile of the
natural measure `μ_p` exists and equals `H̄_s(p) = 2^{1-s} Γ(1-s) pq M_p(s)/E(p)`, which is
`fixedMean s p` by definition. -/
theorem audit_fixed_dimension_mean {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s μ t) atTop
      (𝓝 (fixedMean s p)) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor).exists_isFrostman _ hs.le hμ
  simp only [expectedProfile_eq_H hW hs hs1 hA]
  exact fixedSystem_tendsto_avg_H hs hs1 hp0 hp1 hμ

/-- `thm:fixed-dimension-profiles`, the non-lattice case: if `log a / log b ∉ ℚ`,
`H_{μ_p}^s(t) → H̄_s(p)`. -/
theorem audit_fixed_dimension_non_lattice {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
    (hirr : Irrational (Real.log (fixedA s p) / Real.log (fixedB s p))) :
    Tendsto (expectedProfile W P s μ) atTop (𝓝 (fixedMean s p)) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor).exists_isFrostman _ hs.le hμ
  rw [funext (expectedProfile_eq_H hW hs hs1 hA)]
  exact fixedSystem_tendsto_H_nonLattice hs hs1 hp0 hp1 hμ
    ((fixedSystem_nonArithmetic_iff hs hp0 hp1).2 hirr)

/-- `eq:fixed-dimension-periodic`: in the lattice case, with `h > 0` the span of the group
generated by `log(1/a)` and `log(1/b)` and `ζ_k = s - 2πik/h`, the coefficients
`c_k = (2spq/E(p)) 2^{-ζ_k} Γ(1-ζ_k) M_p(ζ_k)/ζ_k` of `fixedDimCoeff` are absolutely summable
and `H_{μ_p}^s(t) - ∑_k c_k e^{4πikt/h} → 0`. -/
theorem audit_fixed_dimension_periodic {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
    {h : ℝ} (hh : 0 < h)
    (hspan : AddSubgroup.closure ({Real.log (fixedA s p)⁻¹, Real.log (fixedB s p)⁻¹} : Set ℝ)
      = AddSubgroup.zmultiples h) :
    Summable (fun k : ℤ => ‖fixedDimCoeff s p μ h k‖) ∧
      Tendsto (fun t : ℝ => (expectedProfile W P s μ t : ℂ) - ∑' k : ℤ,
        fixedDimCoeff s p μ h k * Complex.exp (4 * Real.pi * Complex.I * k * t / h))
        atTop (𝓝 0) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor).exists_isFrostman _ hs.le hμ
  have hlat : AddSubgroup.closure (Set.range (fixedSystem s p hs hp0 hp1).logRatio)
      = AddSubgroup.zmultiples h := by
    rw [fixedSystem_range_logRatio hs hp0 hp1]; exact hspan
  rw [funext (expectedProfile_eq_H hW hs hs1 hA)]
  exact fixedSystem_periodic hs hs1 hp0 hp1 hh hlat hμ

/-- `eq:fixed-dimension-correlation`: for every `r > 0`,
`S_{μ_p}(r) = 2pq ∑_{j,k≥0} C(j+k, j) p^{2j} q^{2k} 𝔼[1 - exp(-r²/(2 a^j b^k Z_p))]`, with
`X`, `Y` independent of law `μ_p` in `Z_p`, and the series converges uniformly in `r`: the
remainder after the terms with `j + k < m` is at most `(p² + q²)^m`. -/
theorem audit_fixed_dimension_correlation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ)
    {r : ℝ} (hr : 0 < r) :
    HasSum (fun jk : ℕ × ℕ => 2 * (p * (1 - p)) *
        (((jk.1 + jk.2).choose jk.1 : ℝ) * p ^ (2 * jk.1) * (1 - p) ^ (2 * jk.2)) *
        ∫ q : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 /
          (2 * (fixedA s p ^ jk.1 * fixedB s p ^ jk.2 * fixedCross s p q.1 q.2))))) ∂(μ.prod μ))
      (expCorr W P μ r) ∧
    ∀ m : ℕ, |expCorr W P μ r -
        ∑ jk ∈ (Finset.range m).biUnion Finset.HasAntidiagonal.antidiagonal,
          2 * (p * (1 - p)) *
            (((jk.1 + jk.2).choose jk.1 : ℝ) * p ^ (2 * jk.1) * (1 - p) ^ (2 * jk.2)) *
            ∫ q : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 /
              (2 * (fixedA s p ^ jk.1 * fixedB s p ^ jk.2 * fixedCross s p q.1 q.2)))))
              ∂(μ.prod μ)|
      ≤ (p ^ 2 + (1 - p) ^ 2) ^ m := by
  have := hμ.isProbabilityMeasure
  obtain ⟨A, hA⟩ :=
    (fixedSystem_openSetCondition hs hs1 hp0 hp1 hμ.attractor).exists_isFrostman _ hs.le hμ
  have hS : expCorr W P μ r = corrScale μ r 1 := by
    rw [expCorr_eq_integral_prod hW hs hA hr]
    unfold corrScale retKernel
    simp only [one_mul]
  rw [hS]
  exact fixedSystem_correlation hs hs1 hp0 hp1 hμ r

/-- `thm:fixed-dimension-profiles`, bundled: `eq:fixed-dimension-correlation` with its
uniform convergence; the mean profile exists and equals `eq:fixed-dimension-mean`; if
`log a / log b` is irrational the profile converges to it; if it is rational the group
generated by `log(1/a)` and `log(1/b)` has a span `h > 0`, the coefficients of
`eq:fixed-dimension-periodic` are absolutely summable and the profile is asymptotic to
their Fourier series. -/
theorem audit_thm_fixed_dimension_profiles {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s p : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {K : Set ℝ} {μ : Measure ℝ} (hμ : (fixedSystem s p hs hp0 hp1).IsNatural K s μ) :
    (∀ r : ℝ, 0 < r →
      HasSum (fun jk : ℕ × ℕ => 2 * (p * (1 - p)) *
          (((jk.1 + jk.2).choose jk.1 : ℝ) * p ^ (2 * jk.1) * (1 - p) ^ (2 * jk.2)) *
          ∫ q : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 /
            (2 * (fixedA s p ^ jk.1 * fixedB s p ^ jk.2 * fixedCross s p q.1 q.2)))))
            ∂(μ.prod μ))
        (expCorr W P μ r) ∧
      ∀ m : ℕ, |expCorr W P μ r -
          ∑ jk ∈ (Finset.range m).biUnion Finset.HasAntidiagonal.antidiagonal,
            2 * (p * (1 - p)) *
              (((jk.1 + jk.2).choose jk.1 : ℝ) * p ^ (2 * jk.1) * (1 - p) ^ (2 * jk.2)) *
              ∫ q : ℝ × ℝ, (1 - Real.exp (-(r ^ 2 /
                (2 * (fixedA s p ^ jk.1 * fixedB s p ^ jk.2 * fixedCross s p q.1 q.2)))))
                ∂(μ.prod μ)|
        ≤ (p ^ 2 + (1 - p) ^ 2) ^ m) ∧
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s μ t) atTop
      (𝓝 (fixedMean s p)) ∧
    (Irrational (Real.log (fixedA s p) / Real.log (fixedB s p)) →
      Tendsto (expectedProfile W P s μ) atTop (𝓝 (fixedMean s p))) ∧
    (¬ Irrational (Real.log (fixedA s p) / Real.log (fixedB s p)) →
      ∃ h : ℝ, 0 < h ∧
        AddSubgroup.closure ({Real.log (fixedA s p)⁻¹, Real.log (fixedB s p)⁻¹} : Set ℝ)
          = AddSubgroup.zmultiples h ∧
        Summable (fun k : ℤ => ‖fixedDimCoeff s p μ h k‖) ∧
        Tendsto (fun t : ℝ => (expectedProfile W P s μ t : ℂ) - ∑' k : ℤ,
          fixedDimCoeff s p μ h k * Complex.exp (4 * Real.pi * Complex.I * k * t / h))
          atTop (𝓝 0)) := by
  refine ⟨fun r hr => audit_fixed_dimension_correlation hW hs hs1 hp0 hp1 hμ hr,
    audit_fixed_dimension_mean hW hs hs1 hp0 hp1 hμ,
    audit_fixed_dimension_non_lattice hW hs hs1 hp0 hp1 hμ, fun hrat => ?_⟩
  have hna : ¬ (fixedSystem s p hs hp0 hp1).NonArithmetic := by
    rw [fixedSystem_nonArithmetic_iff hs hp0 hp1]; exact hrat
  rcases (fixedSystem s p hs hp0 hp1).nonArithmetic_or_exists_lattice with hd | ⟨h, hh, hlat⟩
  · exact absurd hd hna
  · have hspan : AddSubgroup.closure ({Real.log (fixedA s p)⁻¹, Real.log (fixedB s p)⁻¹} : Set ℝ)
        = AddSubgroup.zmultiples h := by
      rw [← fixedSystem_range_logRatio hs hp0 hp1]; exact hlat
    exact ⟨h, hh, hspan, audit_fixed_dimension_periodic hW hs hs1 hp0 hp1 hμ hh hspan⟩

end BrownianImages
