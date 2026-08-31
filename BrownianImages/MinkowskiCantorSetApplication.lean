/-
Almost-sure distinguishability of the two compact Brownian images in the
homogeneous-versus-paired application.

The homogeneous source is reconstructed by its one-delay renewal equation.  The
paired source is non-arithmetic under the logarithmic incommensurability
hypothesis, so the general non-arithmetic reconstruction theorem applies.  The
previous occupation-law singularity then descends through the two Borel
reconstruction maps to singularity of the compact-image laws themselves.
-/
import BrownianImages.MinkowskiHomogeneousReconstruction
import BrownianImages.MinkowskiReconstructionAssembly

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace MinkowskiReconstruction

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Unconditional compact-set version of the homogeneous-versus-paired
application.  A generic compact Brownian image therefore determines which of the
two source sets was used. -/
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
