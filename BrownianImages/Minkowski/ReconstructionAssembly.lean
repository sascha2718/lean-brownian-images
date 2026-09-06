/-
End-to-end assembly of Minkowski reconstruction from the unconditional Brownian
tube estimates, renewal limits, and generation-cylinder quotient argument.

The non-arithmetic branch is unconditional.  The arithmetic wrapper consumes the
uniform periodic conclusion of the arithmetic renewal theorem; the separate
discrete-renewal module is responsible for constructing that conclusion.
-/
import BrownianImages.Minkowski.GenerationRatio
import BrownianImages.Minkowski.TubeEndpointAssembly

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {Omega : Type*} [MeasurableSpace Omega]
variable {iota : Type*}
variable [Fintype iota] [Nonempty iota]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {W : NNReal → Omega → Plane}

/-- The full reconstruction theorem in the non-arithmetic case. -/
theorem IsNatural.tubeReconstructsOccupation_of_tubeNonArithmetic
    (hW : IsPlanarBrownian W P) (S : System iota)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (hna : S.TubeNonArithmetic) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  have hunit : ∀ p : ℝ, 1 ≤ p → Integrable
      (fun omega => (1 + standardBrownianRadius W omega) ^ p) P :=
    fun p hp => hW.integrable_one_add_standardBrownianRadius_rpow hp
  obtain ⟨_hall, _hcontinuous, c, _A, hc, hbounds⟩ :=
    hmu.meanTubeProfile_data_of_standardRadiusMoments
      S hs0 hs1 hsep hdim hW hunit
  obtain ⟨L, _hL, hlimit⟩ :=
    hmu.meanBrownianTubeProfile_tendsto hW S hs0 hs1 hsep hdim hna
  have hconcentration := hmu.tubeConcentration
    hW S hs0 hs1 hsep hdim
  exact hmu.tubeReconstructsOccupation_of_nonArithmetic_mean_limit
    S hdim hW hconcentration.1 hc
      (fun n => (hbounds (n : ℝ) (Nat.cast_nonneg n)).1) hlimit

/-- Arithmetic reconstruction from the uniform periodic mean-profile conclusion.
All moment and concentration inputs are discharged here. -/
theorem IsNatural.tubeReconstructsOccupation_of_tubeArithmetic
    (hW : IsPlanarBrownian W P) (S : System iota)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    {h : ℝ} (hh : 0 < h) (harith : S.TubeArithmetic h)
    {periodicProfile : ℝ → ℝ}
    (hperiodic : Function.Periodic periodicProfile h)
    (huniform : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
        |meanBrownianTubeProfile W P hmu.compactAttractor s
            (t + (n : ℝ) * h) - periodicProfile t| ≤ epsilon) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  have hunit : ∀ p : ℝ, 1 ≤ p → Integrable
      (fun omega => (1 + standardBrownianRadius W omega) ^ p) P :=
    fun p hp => hW.integrable_one_add_standardBrownianRadius_rpow hp
  obtain ⟨_hall, _hcontinuous, c, _A, hc, hbounds⟩ :=
    hmu.meanTubeProfile_data_of_standardRadiusMoments
      S hs0 hs1 hsep hdim hW hunit
  have hconcentration := hmu.tubeConcentration
    hW S hs0 hs1 hsep hdim
  exact hmu.tubeReconstructsOccupation_of_arithmetic_periodic_limit
    S hdim hW hconcentration.1 hc hh
      (fun n => (hbounds (n : ℝ) (Nat.cast_nonneg n)).1)
      harith hperiodic huniform

/-- The two renewal alternatives together imply reconstruction for an arbitrary
finite separated system. -/
theorem IsNatural.tubeReconstructsOccupation_of_renewal_alternatives
    (hW : IsPlanarBrownian W P) (S : System iota)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (harithmetic : ∀ h : ℝ, 0 < h → S.TubeArithmetic h →
      ∃ periodicProfile : ℝ → ℝ,
        Function.Periodic periodicProfile h ∧
        ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
            |meanBrownianTubeProfile W P hmu.compactAttractor s
                (t + (n : ℝ) * h) - periodicProfile t| ≤ epsilon) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  rcases S.tubeNonArithmetic_or_exists_tubeArithmetic_pos with hna | ⟨h, hh, ha⟩
  · exact hmu.tubeReconstructsOccupation_of_tubeNonArithmetic
      hW S hs0 hs1 hsep hdim hna
  · obtain ⟨periodicProfile, hperiodic, huniform⟩ := harithmetic h hh ha
    exact hmu.tubeReconstructsOccupation_of_tubeArithmetic
      hW S hs0 hs1 hsep hdim hh ha hperiodic huniform

omit [Nonempty iota] in
omit [IsProbabilityMeasure P] in
/-- Once pathwise tube reconstruction has been obtained, its Borel realization is
formal and uses no additional analytic input. -/
theorem IsNatural.minkowskiReconstruction_of_pathwise
    (hW : IsPlanarBrownian W P) (S : System iota)
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu)
    (hpath : MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu) :
    MinkowskiReconstruction.TubeReconstructsOccupation
        W P hmu.compactAttractor mu ∧
      ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
        Measurable reconstruct ∧
        (fun omega => reconstruct (brownianImage W hmu.compactAttractor omega)) =ᵐ[P]
          occupationProb W mu := by
  exact ⟨hpath,
    MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise hW hpath⟩

end System

end

end BrownianImages
