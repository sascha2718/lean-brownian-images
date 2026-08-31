/-
The results of `BrownianImagesComplete.tex` that rest on `thm:non-lattice-limit`, closed
now that `TailHarmonic.nonLatticeLimit` supplies it.

* `gb_limit`, `thm_profile_asymptotics`: `eq:gb-limit` and `thm:profile-asymptotics`.
* `non_lattice_separation`: `thm:non-lattice-separation`.
* `cantor_application`, `cantor_application_pair`: `thm:cantor-application`, in general
  and for the paired measure `μ_B`.
-/
import BrownianImages.TailHarmonic
import BrownianImages.ProfileAsymptotics
import BrownianImages.Separation
import BrownianImages.CantorApplication
import BrownianImages.MainTheorem
import BrownianImages.ExceptionalParameters

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

set_option linter.unusedVariables false in
/-- `eq:gb-limit`: under `eq:non-lattice` the normalised profile of `μ_B` converges to a
finite positive constant. -/
theorem gb_limit {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one)).IsNatural KB sCantor μB)
    (hnl : Irrational (Real.log (pairRatio sCantor)⁻¹ / Real.log 2)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (G sCantor μB) atTop (𝓝 C) :=
  gb_limit_of_non_lattice_limit nonLatticeLimit hB hnl

set_option linter.unusedVariables false in
/-- `thm:profile-asymptotics` as one statement, on the paper's hypotheses: the natural
measures of the two systems and `eq:non-lattice`.  The renewal constant `C_B` of
`eq:gb-limit` is carried through all three conclusions about `μ_B`: it is the limit of
`G_B`, and `C_B ∫₀^∞ K` is the limit both of `H_B` and of the normalised correlation
integral. -/
theorem thm_profile_asymptotics {P : Measure Ω} [IsProbabilityMeasure P]
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
        (∀ R > 0, ∃ r, 0 < r ∧ r < R ∧ b * r ^ (2 * sCantor) ≤ expCorr W P μA r)) :=
  thm_profile_asymptotics_of_non_lattice_limit nonLatticeLimit hW hA hB hnl

set_option linter.unusedVariables false in
/-- `thm:non-lattice-separation`.  Two non-arithmetic systems whose renewal constants
`eq:g-non-lattice-limit` differ have mutually singular Brownian occupation laws. -/
theorem non_lattice_separation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (S₁ : System ι₁) (S₂ : System ι₂) {K₁ K₂ : Set ℝ} {ρ₁ ρ₂ : ℝ}
    (hsep₁ : S₁.StronglySeparated K₁ ρ₁) (hsep₂ : S₂.StronglySeparated K₂ ρ₂)
    (hdim₁ : S₁.IsDimension s) (hdim₂ : S₂.IsDimension s)
    (hna₁ : S₁.NonArithmetic) (hna₂ : S₂.NonArithmetic)
    {μ₁ μ₂ : Measure ℝ} (hμ₁ : S₁.IsNatural K₁ s μ₁) (hμ₂ : S₂.IsNatural K₂ s μ₂)
    (hne : (S₁.renewalMean s)⁻¹ * ∫ x : ℝ, S₁.renewalDefect s μ₁ x
        ≠ (S₂.renewalMean s)⁻¹ * ∫ x : ℝ, S₂.renewalDefect s μ₂ x) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) :=
  non_lattice_separation_of_main_of_limit hW hs0 hs1 S₁ S₂ hsep₁ hsep₂ hdim₁ hdim₂
    hna₁ hna₂ hμ₁ hμ₂ hne
    (nonLatticeLimit S₁ hs0 hs1 hsep₁ hdim₁ hna₁ hμ₁)
    (nonLatticeLimit S₂ hs0 hs1 hsep₂ hdim₂ hna₂ hμ₂)
    (fun h₁ h₂ hsep => main hW hs0 hs1 h₁ h₂ hsep)

set_option linter.unusedVariables false in
/-- `thm:cantor-application`.  The middle-thirds Cantor measure separates from the
natural measure of every strongly separated non-arithmetic system of the same dimension.
Strong separation of the middle-thirds system itself is not a hypothesis: it is
`cantorSystem_stronglySeparated`. -/
theorem cantor_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {KA : Set ℝ} {μA : Measure ℝ} (hA : cantorSystem.IsNatural KA sCantor μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hna : S.NonArithmetic)
    (hdim : S.IsDimension sCantor) {μ : Measure ℝ} (hμ : S.IsNatural K sCantor μ) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) :=
  cantor_application_of_endpoints hW hA S hsep hna hdim hμ nonLatticeLimit main

set_option linter.unusedVariables false in
/-- `thm:cantor-application`, the named instance of its last sentence: under
`eq:non-lattice` the paired measure `μ_B` separates from the middle-thirds measure. -/
theorem cantor_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {KA : Set ℝ} {μA : Measure ℝ} (hA : cantorSystem.IsNatural KA sCantor μA)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio sCantor) (pairRatio_pos sCantor_pos)
      (pairRatio_lt_half sCantor_pos sCantor_lt_one)).IsNatural KB sCantor μB)
    (hnl : Irrational (Real.log (pairRatio sCantor)⁻¹ / Real.log 2)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) :=
  cantor_application_pair_of_endpoints hW hA hB hnl nonLatticeLimit main

set_option linter.unusedVariables false in
/-- `eq:gb-limit` for the paired system associated with an arbitrary
`0 < λ < 1/2`. -/
theorem homogeneous_gb_limit {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (G (homogeneousDim lam) μB) atTop (𝓝 C) := by
  let s := homogeneousDim lam
  let S := pairSystem (pairRatio s) (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
    (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam))
  obtain ⟨hpos, htend⟩ := nonLatticeLimit S
    (homogeneousDim_pos hlam0 hlam) (homogeneousDim_lt_one hlam0 hlam)
    (pairSystem_stronglySeparated (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam)) hB.attractor.2.2.1)
    (pairSystem_isDimension (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam))
    ((pairSystem_nonArithmetic_iff (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam)).mpr hnl) hB
  exact ⟨_, hpos, htend⟩

set_option linter.unusedVariables false in
/-- `thm:profile-asymptotics` with the homogeneous measure at an arbitrary
`0 < λ < 1/2`. -/
theorem homogeneous_thm_profile_asymptotics {P : Measure Ω} [IsProbabilityMeasure P]
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
          b * r ^ (2 * homogeneousDim lam) ≤ expCorr W P μA r)) := by
  have hs0 := homogeneousDim_pos hlam0 hlam
  have hs1 := homogeneousDim_lt_one hlam0 hlam
  haveI := hB.isProbabilityMeasure
  obtain ⟨CB, hCBpos, hCB⟩ := homogeneous_gb_limit hlam0 hlam hB hnl
  obtain ⟨AB, hFrostB⟩ := AhlforsRegular.exists_isFrostman_of_isNatural hs0
    (pairSystem_stronglySeparated (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)
      hB.attractor.2.2.1) hB
  obtain ⟨hposB, hHB⟩ := profile_asymptotics_nonLattice hs0 hs1 hFrostB hCBpos hCB
  refine ⟨⟨CB, hCBpos, hCB, hHB, hposB,
    ProfileAsymptotics.non_lattice_correlation_limit_const hW hs0 hs1
      hFrostB hCB hCBpos⟩,
    homogeneous_profile_asymptotics_lattice hlam0 hlam hA,
    homogeneous_lattice_correlation_oscillation hW hlam0 hlam hA⟩

set_option linter.unusedVariables false in
/-- `thm:cantor-application` in its actual parameter-uniform form. -/
theorem homogeneous_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDim lam) μ) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) :=
  homogeneous_application_of_endpoints hW hlam0 hlam hA S hsep hna hdim hμ
    nonLatticeLimit main

set_option linter.unusedVariables false in
/-- The paired instance of the parameter-uniform corollary. -/
theorem homogeneous_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
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
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) :=
  homogeneous_application_pair_of_endpoints hW hlam0 hlam hA hB hnl nonLatticeLimit main

end BrownianImages
