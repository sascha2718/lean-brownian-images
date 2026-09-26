/-
The non-arithmetic mean-renewal conclusion assembled from the tube moments and
the overlap estimate of `thm:neighbourhood-overlap`.

The only remaining hypothesis is the unit-interval Brownian maximal-moment
input.  The cutoff, direct Riemann integrability, renewal equation, positivity,
and exponential defect tail are all discharged by the imported modules.
-/
import BrownianImages.Minkowski.TubeMomentAssembly
import BrownianImages.Minkowski.StoppingOverlap
import BrownianImages.Minkowski.TubeRenewalLimit

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]

/-- Complete non-arithmetic mean-profile limit, conditional only on moments of
the unit Brownian radius. -/
theorem IsNatural.meanBrownianTubeProfile_tendsto_of_standardRadiusMoments
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hna : S.TubeNonArithmetic)
    (hunit : ∀ p : Real, 1 ≤ p → Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ p) P) :
    ∃ CK : Real, 0 < CK ∧
      Tendsto (meanBrownianTubeProfile W P hmu.compactAttractor s)
        atTop (nhds CK) := by
  obtain ⟨hall, hcont, c, A, hc, hbounds⟩ :=
    hmu.meanTubeProfile_data_of_standardRadiusMoments
      S hs0 hs1 (hsosc.openSetCondition S) hdim hW hunit
  have hmom := hmu.tubeMoments_of_standardRadiusMoments
    S hs0 hs1 (hsosc.openSetCondition S) hdim hW hunit
  obtain ⟨C, η, hC, hη, hoverlap⟩ :=
    hmu.tubeOverlap_of_sosc_of_tubeMoments S hW hs0 hs1 hsosc hdim hmom.1
  apply hmu.meanBrownianTubeProfile_tendsto_of_pairwise_overlap
    hW S hdim hs1 hna hcont hc hC.le (by positivity : 0 < 2 * η)
  · intro v _hv
    exact hall v
  · exact hbounds
  · intro v hv i j hij
    have hr1 : tubeRadiusReal v ≤ 1 := by
      unfold tubeRadiusReal
      exact (Real.exp_le_one_iff).mpr (by linarith)
    have hpair := (hoverlap (tubeRadiusReal v) (tubeRadiusReal_pos v) hr1).1
      i j hij
    simpa only [IsNatural.brownianFirstLevelPiece] using hpair

end System

end

end BrownianImages
