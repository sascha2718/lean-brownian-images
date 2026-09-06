/-
Comparator solution file, and the formal statement of the paper: every numbered
result of `BrownianImagesComplete.tex`, together with the displayed claims that a
later result cites or that carry a hypothesis of their own, stated as `audit_*`
endpoints and proved by the library declarations.  It is not every display:
`docs/correspondence.md` says which are covered by a neighbouring endpoint instead.

`Challenge.lean` restates the headline theorems, `thm:main` and
`thm:cantor-application`, on Mathlib-only copies of the definitions;
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

/-! ### `sec:reconstruction`: reconstruction from the compact image -/

/-- `thm:minkowski-reconstruction`, including its final Borel assertion.  Pairwise
disjoint first-level intervals are encoded by `System.IntervalSeparated`; the bundled
compact set is the attractor carried by the natural measure. -/
theorem audit_minkowski_reconstruction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    MinkowskiReconstruction.TubeReconstructsOccupation
        W P hμ.compactAttractor μ ∧
      ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
        Measurable reconstruct ∧
        (fun ω ↦ reconstruct (brownianImage W hμ.compactAttractor ω)) =ᵐ[P]
          occupationProb W μ :=
  hμ.minkowskiReconstruction hW S hs0 hs1 hsep hdim

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
attractor at any ratio `0 < λ < 1/2` and that of the attractor of every non-arithmetic
system of the same dimension with pairwise disjoint first-level intervals have mutually
singular laws on the Hausdorff hyperspace.  Pairwise disjoint first-level intervals are
encoded by `System.IntervalSeparated`, which implies the strong separation that
`thm:cantor-application` asks for. -/
theorem audit_cantor_set_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    (hsep : S.IntervalSeparated) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDim lam) μ) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hμ.compactAttractor) :=
  MinkowskiReconstruction.homogeneous_brownianImage_application
    hW hlam0 hlam hA S hsep hna hdim hμ

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
measure. -/
theorem audit_tube_moments {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
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
  hμ.tubeMoments hW S hs0 hs1 hsep hdim

/-- `thm:neighbourhood-overlap`, including integrability of the overlap and defect random
variables.  One constant controls every distinct first-level pair and the resulting
multiple-counting defect. -/
theorem audit_tube_overlap {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ i j : ι, i ≠ j →
        Integrable (fun ω ↦ tubeOverlapArea r
          (brownianImage W (hμ.compactPiece S i) ω)
          (brownianImage W (hμ.compactPiece S j) ω)) P ∧
        (∫ ω, tubeOverlapArea r
            (brownianImage W (hμ.compactPiece S i) ω)
            (brownianImage W (hμ.compactPiece S j) ω) ∂P)
          ≤ C * r ^ (2 * tubeExponent s)) ∧
      Integrable (fun ω ↦ tubeDefect r
        (fun i ↦ brownianImage W (hμ.compactPiece S i) ω)) P ∧
      (∫ ω, tubeDefect r
          (fun i ↦ brownianImage W (hμ.compactPiece S i) ω) ∂P)
        ≤ C * r ^ (2 * tubeExponent s) :=
  hμ.tubeOverlap hW S hs0 hs1 hsep hdim

/-- `thm:neighbourhood-renewal`.  The real integrals defining the mean profile are required
to be integrable.  Uniform convergence in the arithmetic case is written directly
with its `ε`--`N` quantifiers on one period. -/
theorem audit_tube_renewal {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
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
  hμ.tubeRenewal hW S hs0 hs1 hsep hdim

/-- `thm:neighbourhood-concentration`.  Membership in `L²` is included explicitly before
the `eLpNorm` bound, and the final assertion has the paper's quantifier order: each
fixed phase has its own almost-sure event. -/
theorem audit_tube_concentration {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∃ C : ℝ, 0 < C ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ v : ℝ, 0 ≤ v →
      MemLp (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ∧
      eLpNorm (centeredBrownianTubeProfile W P hμ.compactAttractor s v) 2 P ≤
        ENNReal.ofReal (C * Real.exp (-γ * v))) ∧
    ∀ t : ℝ, ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ centeredBrownianTubeProfile W P hμ.compactAttractor s
        ((n : ℝ) + t) ω) atTop (nhds 0) :=
  hμ.tubeConcentration hW S hs0 hs1 hsep hdim

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

/-- `eq:non-lattice` is exactly the non-arithmetic hypothesis of
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

/-- `thm:renewal-recursion`, `eq:phi-recursion`.  Below the separation gap the
pair-distance distribution satisfies the self-similar recursion. -/
theorem audit_renewal_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ}
    {ρ s : ℝ} (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < ρ) :
    Phi μ δ = ∑ i, S.ratio i ^ (2 * s) * Phi μ (δ / S.ratio i) :=
  phi_recursion S hsep hμ hδ0 hδ

/-- `thm:renewal-recursion`, `eq:g-recursion`.  The recursion in the normalised
profile. -/
theorem audit_g_recursion {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hsep : S.StronglySeparated K ρ) {μ : Measure ℝ} (hμ : S.IsNatural K s μ)
    {w : ℝ} (hw : Real.log ρ⁻¹ < w) :
    G s μ w = ∑ i, S.ratio i ^ s * G s μ (w - S.logRatio i) :=
  g_recursion S hsep hμ hw

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

/-- `thm:profile-asymptotics`, `eq:hb-asymptotic`.  In the non-arithmetic case the
expected profile converges to `C ∫₀^∞ φ`, and that limit is finite and strictly
positive. -/
theorem audit_profile_asymptotics_non_lattice {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {A : ℝ} (hμ : IsFrostman s A μ)
    (hCpos : 0 < C) (hC : Tendsto (G s μ) atTop (𝓝 C)) :
    0 < C * ∫ η in Set.Ioi (0:ℝ), kern s η ∧
      Tendsto (H s μ) atTop (𝓝 (C * ∫ η in Set.Ioi (0:ℝ), kern s η)) :=
  profile_asymptotics_nonLattice hs0 hs1 hμ hCpos hC

/-- `thm:profile-asymptotics`, `eq:ha-asymptotic`, as the uniform bound the proof
produces for the homogeneous system. -/
theorem audit_profile_asymptotics_lattice {KA : Set ℝ} {μA : Measure ℝ}
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g (Real.log lam⁻¹))
    (hagree : ∀ w, homogeneousStart lam ≤ w → g w = G (homogeneousDim lam) μA w) :
    ∃ C > 0, ∀ v : ℝ, 0 ≤ v →
      |H (homogeneousDim lam) μA v - smoothOp (homogeneousDim lam) g v|
        ≤ C * Real.exp (-2 * (1 - homogeneousDim lam) * v) := by
  haveI := hA.isProbabilityMeasure
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
  haveI := hA.isProbabilityMeasure
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
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (occupationLaw W P μ) :=
  hW.isProbabilityMeasure_occupationLaw μ

/-- The law of the compact Brownian image is a probability measure, so the compact-image
laws compared in `thm:cantor-set-application` have total mass one and their mutual
singularity is not the vacuous statement about two zero measures. -/
theorem audit_isProbabilityMeasure_brownianImageLaw {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) (K : NonemptyCompacts ℝ) :
    IsProbabilityMeasure (brownianImageLaw W P K) :=
  hW.isProbabilityMeasure_brownianImageLaw K

/-- The occupation measure is a measurable function of the sample path, so
`occupationLaw` is the law of `W_*μ` and not the junk value `Measure.map` returns on a
non-measurable map.  Almost sure continuity of the paths, carried by
`IsPlanarBrownian`, is what supplies this. -/
theorem audit_aemeasurable_occupation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    AEMeasurable (occupationProb W μ) P :=
  hW.aemeasurable_occupationProb μ

/-- Internal Ahlfors-regularity endpoint for a strongly separated natural measure.
Support points are those charging every ball. -/
theorem audit_ahlfors {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hs : 0 < s) (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ A : ℝ, IsAhlforsClosed s A μ :=
  exists_isAhlforsClosed S hs hsep hdim hμ

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

/-- `eq:smoothing`.  The exact rescaling `S_μ(r) = r^{2s} H_μ(log(1/r))`, for every
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

/-- `thm:profile-asymptotics`, the conclusion for `μ_B`: the normalised expected
correlation integral has a finite positive limit. -/
theorem audit_non_lattice_correlation_limit {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) {s C A : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsFrostman s A μ)
    (hC : Tendsto (G s μ) atTop (𝓝 C)) (hCpos : 0 < C) :
    ∃ L > 0, Tendsto (fun r : ℝ => expCorr W P μ r / r ^ (2 * s)) (𝓝[>] 0) (𝓝 L) :=
  non_lattice_correlation_limit hW hs0 hs1 hμ hC hCpos

/-- `thm:profile-asymptotics`, the conclusion for `μ_A`: the normalised expected
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
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) :=
  main hW hs0 hs1 h₁ h₂ hsep

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
`0 < λ < 1/2` separates from the natural measure of every strongly separated
non-arithmetic system of the same dimension. -/
theorem audit_cantor_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDim lam) μ) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) :=
  homogeneous_application hW hlam0 hlam hA S hsep hna hdim hμ

/-- The paired instance of `thm:cantor-application`, the last sentence of the theorem,
at a parameter satisfying `eq:non-lattice`.  The ratio bounds `0 < c < 1/2` of
`eq:c-definition` enter as hypotheses. -/
theorem audit_cantor_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    (hc0 : 0 < pairRatio (homogeneousDim lam))
    (hc : pairRatio (homogeneousDim lam) < 1/2)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam)) hc0 hc).IsNatural
      KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) :=
  homogeneous_application_pair hW hlam0 hlam hA hB hnl

/-- The exceptional parameters in the last sentence of `thm:cantor-application` form
a countable set. -/
theorem audit_exceptional_parameters_countable :
    {lam : ℝ | 0 < lam ∧ lam < 1/2 ∧
      ¬ Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)}.Countable :=
  exceptionalParameters_countable

/-- `thm:non-lattice-limit`, `eq:g-non-lattice-limit`.  In the non-arithmetic case the
normalised profile converges to `m⁻¹ ∫ z`, which is finite and strictly positive, where
`m = ∑ p_i a_i` is the renewal mean and `z = G - F * G` the renewal defect. -/
theorem audit_non_lattice_limit {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {ρ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsep : S.StronglySeparated K ρ)
    (hdim : S.IsDimension s) (hna : S.NonArithmetic)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    0 < (S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x ∧
      Tendsto (G s μ) atTop (𝓝 ((S.renewalMean s)⁻¹ * ∫ x : ℝ, S.renewalDefect s μ x)) :=
  non_lattice_limit S hs0 hs1 hsep hdim hna hμ

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

/-- `thm:profile-asymptotics` as one statement, on the paper's hypotheses: the natural
measures of the two systems and `eq:non-lattice`.  The renewal constant `C_B` of
`eq:gb-limit` is carried through all three conclusions about `μ_B`: it is the limit of
`G_B`, and `C_B ∫₀^∞ φ` is the limit both of `H_B` and of the normalised correlation
integral. -/
theorem audit_thm_profile_asymptotics {P : Measure Ω} [IsProbabilityMeasure P]
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

/-- `thm:non-lattice-separation`.  Two non-arithmetic systems whose renewal constants
`eq:g-non-lattice-limit` differ have mutually singular Brownian occupation laws. -/
theorem audit_non_lattice_separation {P : Measure Ω} [IsProbabilityMeasure P]
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
  non_lattice_separation hW hs0 hs1 S₁ S₂ hsep₁ hsep₂ hdim₁ hdim₂ hna₁ hna₂ hμ₁ hμ₂ hne

end BrownianImages
