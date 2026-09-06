/-
`thm:cantor-set-application`: almost-sure distinguishability of the compact Brownian
image of the homogeneous attractor from that of any non-arithmetic attractor of the same
dimension with pairwise disjoint first-level intervals, and its paired instance.

The homogeneous source is reconstructed by its one-delay renewal equation.  The other
source is non-arithmetic, so the general reconstruction theorem applies to it.  The
occupation-law singularity of `thm:cantor-application` then descends through the two
Borel reconstruction maps to singularity of the compact-image laws themselves.

* `homogeneous_brownianImage_application`: `thm:cantor-set-application`, the endpoint
  `audit_cantor_set_application`.
* `homogeneous_brownianImage_application_pair_unconditional`: its paired instance under
  `eq:non-lattice`, the endpoint `audit_cantor_set_application_pair`.
-/
import BrownianImages.Minkowski.HomogeneousReconstruction
import BrownianImages.Minkowski.ReconstructionAssembly
import BrownianImages.Minkowski.FullEndpointAssembly
import BrownianImages.NonLattice

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace MinkowskiReconstruction

variable {Omega : Type*} [MeasurableSpace Omega]

/-- `thm:cantor-set-application`: the compact Brownian image of the homogeneous
attractor at any ratio `0 < λ < 1/2` and that of the attractor of a non-arithmetic
system of the same dimension with pairwise disjoint first-level intervals have mutually
singular laws on the Hausdorff hyperspace.  The homogeneous source is reconstructed from
its one-delay renewal equation, the non-arithmetic source by the general reconstruction
theorem, and the occupation-law singularity of `thm:cantor-application` descends through
the common Borel reconstruction map.  Interval separation implies the strong separation
that `thm:cantor-application` asks for. -/
theorem homogeneous_brownianImage_application
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {KA : Set ℝ} {muA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) muA)
    {iota : Type*} [Fintype iota] [Nonempty iota] (S : System iota) {K : Set ℝ}
    (hsep : S.IntervalSeparated) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {mu : Measure ℝ}
    (hmu : S.IsNatural K (homogeneousDim lam) mu) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hmu.compactAttractor) := by
  haveI := hA.isProbability
  haveI := hmu.isProbability
  obtain ⟨rho, hrho⟩ := hsep
  have hoccupation : (occupationLaw W P muA).MutuallySingular (occupationLaw W P mu) :=
    homogeneous_application hW hlam0 hlam hA S
      (System.StronglySeparated.mono S hmu.attractor.2.2.1 hrho) hna hdim hmu
  have hpathA := hA.tubeReconstructsOccupation_homogeneousSystem hW hlam0 hlam
  have hpathK := hmu.tubeReconstructsOccupation hW S (homogeneousDim_pos hlam0 hlam)
    (homogeneousDim_lt_one hlam0 hlam) ⟨rho, hrho⟩ hdim
  exact brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction
    hW hpathA hpathK hoccupation

/-- The paired instance of `thm:cantor-set-application`: under `eq:non-lattice` the
compact Brownian images of the homogeneous attractor and of `K_B` have mutually singular
laws.  A generic compact Brownian image therefore determines which of the two source
sets was used. -/
theorem homogeneous_brownianImage_application_pair_unconditional
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {KA : Set ℝ} {muA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural
      KA (homogeneousDim lam) muA)
    {KB : Set ℝ} {muB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam))
      (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
      (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
        (homogeneousDim_lt_one hlam0 hlam))).IsNatural
          KB (homogeneousDim lam) muB)
    (hnl : Irrational
      (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    (brownianImageLaw W P hA.compactAttractor).MutuallySingular
      (brownianImageLaw W P hB.compactAttractor) := by
  let s : ℝ := homogeneousDim lam
  let c : ℝ := pairRatio s
  let S : System (Fin 2) := pairSystem c
    (pairRatio_pos (homogeneousDim_pos hlam0 hlam))
    (pairRatio_lt_half (homogeneousDim_pos hlam0 hlam)
      (homogeneousDim_lt_one hlam0 hlam))
  have hs0 : 0 < s := homogeneousDim_pos hlam0 hlam
  have hs1 : s < 1 := homogeneousDim_lt_one hlam0 hlam
  have hsep : S.IntervalSeparated := by
    simpa only [S, c, s] using pairSystem_intervalSeparated
      (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)
  have hdim : S.IsDimension s := by
    simpa only [S, c] using pairSystem_isDimension hs0 hs1
  have hnaturalB : S.IsNatural KB s muB := by
    simpa only [S, c, s] using hB
  have hna : S.TubeNonArithmetic := by
    apply (S.tubeNonArithmetic_iff_nonArithmetic).2
    simpa only [S, c] using
      ((pairSystem_nonArithmetic_iff hs0 hs1).2 (by simpa only [s] using hnl))
  have hpathA := hA.tubeReconstructsOccupation_homogeneousSystem
    hW hlam0 hlam
  have hpathB := hnaturalB.tubeReconstructsOccupation_of_tubeNonArithmetic
    hW S hs0 hs1 hsep hdim hna
  exact homogeneous_brownianImage_application_pair_of_pathwise
    hW hlam0 hlam hA hB hnl hpathA hpathB

end MinkowskiReconstruction

end

end BrownianImages
