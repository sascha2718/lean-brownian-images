/-
Final unconditional assembly of the renewal alternatives and Minkowski
reconstruction for a finite interval-separated self-similar system.

The arithmetic branch uses the finite-delay lattice renewal theorem, while the
non-arithmetic branch uses the continuous key renewal theorem.  The Brownian
moment, overlap, and concentration inputs are discharged by the endpoint
assemblies imported below.
-/
import BrownianImages.MinkowskiTubeDiscreteRenewal
import BrownianImages.MinkowskiReconstructionAssembly

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

universe u v

variable {Omega : Type u} [MeasurableSpace Omega]
variable {iota : Type v} [Fintype iota] [Nonempty iota]

/-- The arithmetic branch of the mean tube-profile renewal theorem, with the
Brownian moment and first-level overlap estimates discharged. -/
theorem IsNatural.meanBrownianTubeProfile_periodic_limit
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s h : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hh : 0 < h) (harith : S.TubeArithmetic h) :
    ∃ PK : Real → Real, Function.Periodic PK h ∧
      (∃ c C : Real, 0 < c ∧ ∀ t : Real, c ≤ PK t ∧ PK t ≤ C) ∧
      ∀ epsilon : Real, 0 < epsilon → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ t ∈ Set.Icc (0 : Real) h,
          |meanBrownianTubeProfile W P hmu.compactAttractor s
              (t + (n : Real) * h) - PK t| ≤ epsilon := by
  have hunit : ∀ p : Real, 1 ≤ p → Integrable
      (fun omega => (1 + standardBrownianRadius W omega) ^ p) P :=
    fun p hp => hW.integrable_one_add_standardBrownianRadius_rpow hp
  obtain ⟨hall, hcontinuous, c, A, hc, hbounds⟩ :=
    hmu.meanTubeProfile_data_of_standardRadiusMoments
      S hs0 hs1 hsep hdim hW hunit
  have hmom := hmu.tubeMoments_of_standardRadiusMoments
    S hs0 hs1 hsep hdim hW hunit
  obtain ⟨C, hC, hoverlap⟩ := hmu.tubeOverlap_of_tubeMomentsUpper
    hW S hs0 hs1 hsep hdim hmom.1
  let D : Real := ((Fintype.card iota : Real) ^ 2 / 2) * C
  have hD : 0 ≤ D := mul_nonneg (by positivity) hC.le
  have hgamma : 0 < tubeExponent s := tubeExponent_pos hs1
  have hrenewal : ∀ x : Real,
      (∀ i : iota, S.halfLogRatio i ≤ x) →
      meanBrownianTubeProfile W P hmu.compactAttractor s x =
          S.tubeRenewalConv s
            (meanBrownianTubeProfile W P hmu.compactAttractor s) x -
            hmu.meanBrownianTubeDefectProfile S W P x ∧
        0 ≤ hmu.meanBrownianTubeDefectProfile S W P x ∧
        hmu.meanBrownianTubeDefectProfile S W P x ≤
          D * Real.exp (-tubeExponent s * x) := by
    intro x hxsteps
    obtain ⟨i0⟩ := ‹Nonempty iota›
    have hx0 : 0 ≤ x := (S.halfLogRatio_pos i0).le.trans (hxsteps i0)
    have hr1 : tubeRadiusReal x ≤ 1 := by
      unfold tubeRadiusReal
      exact (Real.exp_le_one_iff).mpr (by linarith)
    have hpair : ∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea (tubeRadiusReal x)
          (hmu.brownianFirstLevelPiece S W omega i)
          (hmu.brownianFirstLevelPiece S W omega j)) P ∧
        (∫ omega, tubeOverlapArea (tubeRadiusReal x)
          (hmu.brownianFirstLevelPiece S W omega i)
          (hmu.brownianFirstLevelPiece S W omega j) ∂P) ≤
            C * tubeRadiusReal x ^ (2 * tubeExponent s) := by
      intro i j hij
      simpa only [IsNatural.brownianFirstLevelPiece] using
        (hoverlap (tubeRadiusReal x) (tubeRadiusReal_pos x) hr1).1 i j hij
    have hrec := hW.mean_tube_renewal_of_pairwise_overlap
      S hmu x C hC.le (fun i => hall (x - S.halfLogRatio i)) hpair
    exact ⟨hrec.2.1, hrec.2.2.1, by simpa only [D] using hrec.2.2.2⟩
  obtain ⟨PK, _hPKcontinuous, hPKperiodic, hPKbounds, hPKuniform⟩ :=
    hmu.meanBrownianTubeProfile_periodic_limit_of_tubeArithmetic
      S hdim hh harith hcontinuous hc hD hgamma hbounds
        (fun x hx => (hrenewal x hx).1)
        (fun x hx => (hrenewal x hx).2)
  exact ⟨PK, hPKperiodic, hPKbounds, hPKuniform⟩

/-- `thm:tube-renewal`, including both the non-arithmetic and arithmetic
alternatives, with all Brownian moment and overlap inputs discharged. -/
theorem IsNatural.tubeRenewal
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    (∀ x : Real, 0 ≤ x →
      Integrable (brownianTubeProfile W hmu.compactAttractor s x) P) ∧
    (∃ c C : Real, 0 < c ∧ ∀ x : Real, 0 ≤ x →
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s x ∧
      meanBrownianTubeProfile W P hmu.compactAttractor s x ≤ C) ∧
    (S.TubeNonArithmetic →
      ∃ CK : Real, 0 < CK ∧ Tendsto
        (meanBrownianTubeProfile W P hmu.compactAttractor s) atTop (nhds CK)) ∧
    (∀ h : Real, 0 < h → S.TubeArithmetic h →
      ∃ PK : Real → Real, Function.Periodic PK h ∧
        (∃ c C : Real, 0 < c ∧ ∀ t : Real, c ≤ PK t ∧ PK t ≤ C) ∧
        ∀ epsilon : Real, 0 < epsilon → ∃ N : Nat, ∀ n : Nat, N ≤ n →
          ∀ t ∈ Set.Icc (0 : Real) h,
            |meanBrownianTubeProfile W P hmu.compactAttractor s
                (t + (n : Real) * h) - PK t| ≤ epsilon) := by
  have hunit : ∀ p : Real, 1 ≤ p → Integrable
      (fun omega => (1 + standardBrownianRadius W omega) ^ p) P :=
    fun p hp => hW.integrable_one_add_standardBrownianRadius_rpow hp
  obtain ⟨hall, _hcontinuous, c, C, hc, hbounds⟩ :=
    hmu.meanTubeProfile_data_of_standardRadiusMoments
      S hs0 hs1 hsep hdim hW hunit
  refine ⟨fun x _hx => hall x, ⟨c, C, hc, hbounds⟩, ?_, ?_⟩
  · intro hna
    exact hmu.meanBrownianTubeProfile_tendsto
      hW S hs0 hs1 hsep hdim hna
  · intro h hh harith
    exact hmu.meanBrownianTubeProfile_periodic_limit
      hW S hs0 hs1 hsep hdim hh harith

/-- Unconditional pathwise recovery of the natural measure from the compact
Brownian image for an arbitrary finite interval-separated system. -/
theorem IsNatural.tubeReconstructsOccupation
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  apply hmu.tubeReconstructsOccupation_of_renewal_alternatives
    hW S hs0 hs1 hsep hdim
  intro h hh harith
  obtain ⟨PK, hperiodic, _hbounds, huniform⟩ :=
    hmu.meanBrownianTubeProfile_periodic_limit
      hW S hs0 hs1 hsep hdim hh harith
  exact ⟨PK, hperiodic, huniform⟩

/-- `thm:minkowski-reconstruction`: pathwise tube reconstruction together with
its measurable realization as a function of the compact Brownian image. -/
theorem IsNatural.minkowskiReconstruction
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    MinkowskiReconstruction.TubeReconstructsOccupation
        W P hmu.compactAttractor mu ∧
      ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
        Measurable reconstruct ∧
        (fun omega => reconstruct (brownianImage W hmu.compactAttractor omega)) =ᵐ[P]
          occupationProb W mu := by
  exact hmu.minkowskiReconstruction_of_pathwise hW S
    (hmu.tubeReconstructsOccupation hW S hs0 hs1 hsep hdim)

end System

end

end BrownianImages
