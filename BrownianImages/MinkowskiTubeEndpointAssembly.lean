/-
Unconditional endpoint assembly for the Brownian tube estimates.

The unit-interval Brownian radius moments are proved in
`MinkowskiBrownianMaximalMoment`.  This file feeds that input into the existing
moment, overlap, renewal, and concentration assemblies and exposes the final
statements without an additional maximal-moment hypothesis.
-/
import BrownianImages.MinkowskiBrownianMaximalMoment
import BrownianImages.MinkowskiTubeMomentAssembly
import BrownianImages.MinkowskiTubeRenewalAssembly
import BrownianImages.MinkowskiTubeConcentrationAssembly

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {Omega : Type*} [MeasurableSpace Omega]
variable {iota : Type*}
variable [Fintype iota] [Nonempty iota]

/-- `thm:neighbourhood-moments`, with the Brownian maximal-moment input discharged. -/
theorem IsNatural.tubeMoments
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    (∀ q : Real, 1 ≤ q → ∃ Cq : Real, 0 < Cq ∧
      ∀ r : Real, 0 < r → r ≤ 1 →
        Integrable
          (fun omega => (brownianTubeArea W hmu.compactAttractor r omega) ^ q) P ∧
        Integrable
          (fun omega =>
            (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q) P ∧
        (∫ omega, (brownianTubeArea W hmu.compactAttractor r omega) ^ q ∂P) +
            (∫ omega,
              (tubeMass r (brownianImage W hmu.compactAttractor omega)) ^ q ∂P) ≤
          Cq * r ^ (q * tubeExponent s)) ∧
      ∃ c : Real, 0 < c ∧ ∀ r : Real, 0 < r → r ≤ 1 →
        Integrable
          (fun omega => tubeMass r
            (brownianImage W hmu.compactAttractor omega)) P ∧
        c * r ^ tubeExponent s ≤
          ∫ omega, tubeMass r
            (brownianImage W hmu.compactAttractor omega) ∂P := by
  apply hmu.tubeMoments_of_standardRadiusMoments
    S hs0 hs1 hsep hdim hW
  intro p hp
  exact BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    hW hp

/-- `thm:neighbourhood-overlap`, with both the tube moments and Brownian maximal input
discharged. -/
theorem IsNatural.tubeOverlap
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    ∃ C : Real, 0 < C ∧ ∀ r : Real, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
            (brownianImage W (hmu.compactPiece S i) omega)
            (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
          C * r ^ (2 * tubeExponent s)) ∧
      Integrable (fun omega => tubeDefect r
        (fun i => brownianImage W (hmu.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect r
          (fun i => brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
        C * r ^ (2 * tubeExponent s) := by
  have hmom := hmu.tubeMoments hW S hs0 hs1 hsep hdim
  exact hmu.tubeOverlap_of_tubeMomentsUpper
    hW S hs0 hs1 hsep hdim hmom.1

/-- The non-arithmetic branch of `thm:neighbourhood-renewal`, with the unit Brownian
radius moments discharged. -/
theorem IsNatural.meanBrownianTubeProfile_tendsto
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hna : S.TubeNonArithmetic) :
    ∃ CK : Real, 0 < CK ∧
      Tendsto (meanBrownianTubeProfile W P hmu.compactAttractor s)
        atTop (nhds CK) := by
  apply hmu.meanBrownianTubeProfile_tendsto_of_standardRadiusMoments
    hW S hs0 hs1 hsep hdim hna
  intro p hp
  exact BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    hW hp

section Concentration

universe u v

variable {OmegaC : Type u} {iotaC : Type v} [MeasurableSpace OmegaC]
variable [Fintype iotaC] [Nonempty iotaC]

/-- `thm:neighbourhood-concentration`, with the unit Brownian radius moments
discharged. -/
theorem IsNatural.tubeConcentration
    {P : Measure OmegaC} [IsProbabilityMeasure P]
    {W : NNReal → OmegaC → Plane} (hW : IsPlanarBrownian W P)
    (S : System iotaC) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    (∃ C : Real, 0 < C ∧ ∃ gamma : Real, 0 < gamma ∧
      ∀ v : Real, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v))) ∧
    ∀ t : Real, ∀ᵐ omega ∂P, Tendsto
      (fun n : Nat => centeredBrownianTubeProfile W P hmu.compactAttractor s
        ((n : Real) + t) omega) atTop (nhds 0) := by
  apply hmu.tubeConcentration_of_standardRadiusMoments
    hW S hs0 hs1 hsep hdim
  intro p hp
  exact BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    hW hp

end Concentration

end System

end

end BrownianImages
