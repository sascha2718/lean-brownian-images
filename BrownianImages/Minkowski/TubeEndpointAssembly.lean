module

/-
Unconditional endpoint assembly for the Brownian tube estimates.

The unit-interval Brownian radius moments are proved in
`Minkowski.BrownianMaximalMoment`.  This file feeds that input into the existing
moment, overlap, renewal, and concentration assemblies and exposes the final
statements without an additional maximal-moment hypothesis.
`IsNatural.tubeOverlap_of_crossPhi_bound` preserves the prescribed exponent of
`thm:cross-piece-mass` in the pairwise overlap and multiple-counting defect bounds
of `thm:neighbourhood-overlap`.
-/
public import BrownianImages.Minkowski.TubeRenewalAssembly
public import BrownianImages.Minkowski.StoppingConcentration

@[expose] public section

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
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
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
    S hs0 hs1 hosc hdim hW
  intro p hp
  exact BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    hW hp

/-- `thm:neighbourhood-overlap` for any prescribed exponent in the cross-piece
product bound, with the tube moments and Brownian maximal input discharged. -/
theorem IsNatural.tubeOverlap_of_cross_piece_bound
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    {Cc η : Real} (hCc : 0 < Cc) (hη : 0 < η) (hηs : η < 1 - s)
    (hcross : ∀ i j : iota, i ≠ j → ∀ h : Real, 0 < h → h ≤ 1 →
      ((mu.map (S.map i)).prod (mu.map (S.map j))) {p : Real × Real | |p.1 - p.2| ≤ h}
        ≤ ENNReal.ofReal (Cc * h ^ (s + η))) :
    ∃ C : Real, 0 < C ∧ ∀ r : Real, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
            (brownianImage W (hmu.compactPiece S i) omega)
            (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
          C * r ^ (tubeExponent s + 2 * η)) ∧
      Integrable (fun omega => tubeDefect r
        (fun i => brownianImage W (hmu.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect r
          (fun i => brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
        C * r ^ (tubeExponent s + 2 * η) := by
  have hmom := hmu.tubeMoments hW S hs0 hs1 hosc hdim
  exact hmu.tubeOverlap_of_cross_piece_bound_of_mean_bound S hW hs0 hCc hη hηs hcross
    (hmu.exists_tubeArea_mean_bound_of_tubeMoments S hmom.1)

/-- `thm:neighbourhood-overlap` with exactly the exponent prescribed by the total
cross-correlation bound of `thm:cross-piece-mass`. The positive natural cylinder weights
convert the total bound to a bound on each pair without changing that exponent. -/
theorem IsNatural.tubeOverlap_of_crossPhi_bound
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    {Cc η : Real} (hCc : 0 < Cc) (hη : 0 < η) (hηs : η < 1 - s)
    (hcross : ∀ h : Real, 0 < h → h ≤ 1 → S.crossPhi s mu h ≤ Cc * h ^ (s + η)) :
    ∃ C : Real, 0 < C ∧ ∀ r : Real, 0 < r → r ≤ 1 →
      (∀ i j : iota, i ≠ j →
        Integrable (fun omega => tubeOverlapArea r
          (brownianImage W (hmu.compactPiece S i) omega)
          (brownianImage W (hmu.compactPiece S j) omega)) P ∧
        (∫ omega, tubeOverlapArea r
            (brownianImage W (hmu.compactPiece S i) omega)
            (brownianImage W (hmu.compactPiece S j) omega) ∂P) ≤
          C * r ^ (tubeExponent s + 2 * η)) ∧
      Integrable (fun omega => tubeDefect r
        (fun i => brownianImage W (hmu.compactPiece S i) omega)) P ∧
      (∫ omega, tubeDefect r
          (fun i => brownianImage W (hmu.compactPiece S i) omega) ∂P) ≤
        C * r ^ (tubeExponent s + 2 * η) := by
  obtain ⟨Cpair, hCpair, hpair⟩ := hmu.exists_cross_piece_bound_of_crossPhi_bound S hs0 hCc hcross
  exact hmu.tubeOverlap_of_cross_piece_bound hW S hs0 hs1 hosc hdim hCpair hη hηs hpair

/-- The internal non-arithmetic limit giving the shift relation in
`thm:neighbourhood-renewal`, with the unit Brownian radius moments discharged. -/
theorem IsNatural.meanBrownianTubeProfile_tendsto
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    (hna : S.TubeNonArithmetic) :
    ∃ CK : Real, 0 < CK ∧
      Tendsto (meanBrownianTubeProfile W P hmu.compactAttractor s)
        atTop (nhds CK) := by
  apply hmu.meanBrownianTubeProfile_tendsto_of_standardRadiusMoments
    hW S hs0 hs1 hsosc hdim hna
  intro p hp
  exact BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    hW hp

section Concentration

universe u v

variable {OmegaC : Type u} {iotaC : Type v} [MeasurableSpace OmegaC]
variable [Fintype iotaC] [Nonempty iotaC]

/-- Internal centred-norm form of `thm:neighbourhood-concentration`, with the unit
Brownian radius moments discharged. The paper states its square as a variance bound. -/
theorem IsNatural.tubeConcentration
    {P : Measure OmegaC} [IsProbabilityMeasure P]
    {W : NNReal → OmegaC → Plane} (hW : IsPlanarBrownian W P)
    (S : System iotaC) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    (∃ C : Real, 0 < C ∧ ∃ gamma : Real, 0 < gamma ∧
      ∀ v : Real, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v))) ∧
    ∀ t : Real, ∀ᵐ omega ∂P, Tendsto
      (fun n : Nat => centeredBrownianTubeProfile W P hmu.compactAttractor s
        ((n : Real) + t) omega) atTop (nhds 0) := by
  apply hmu.tubeConcentration_of_sosc S hW hs0 hs1 hsosc hdim
  intro p hp
  exact BrownianImages.IsPlanarBrownian.integrable_one_add_standardBrownianRadius_rpow
    hW hp

/-- `thm:neighbourhood-concentration`: exponential decay of the variance and
almost-sure convergence along each fixed shifted integer grid. -/
theorem IsNatural.tubeVarianceConcentration
    {P : Measure OmegaC} [IsProbabilityMeasure P]
    {W : NNReal → OmegaC → Plane} (hW : IsPlanarBrownian W P)
    (S : System iotaC) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsosc : S.StrongOpenSetCondition K) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu) :
    (∃ C : Real, 0 < C ∧ ∃ gamma : Real, 0 < gamma ∧
      ∀ t : Real, 0 ≤ t →
        MemLp (brownianTubeProfile W hmu.compactAttractor s t) 2 P ∧
        variance (brownianTubeProfile W hmu.compactAttractor s t) P ≤
          C * Real.exp (-gamma * t)) ∧
    ∀ t : Real, ∀ᵐ omega ∂P, Tendsto
      (fun n : Nat => centeredBrownianTubeProfile W P hmu.compactAttractor s
        ((n : Real) + t) omega) atTop (nhds 0) := by
  obtain ⟨⟨C, hC, gamma, hgamma, hbound⟩, hgrid⟩ :=
    hmu.tubeConcentration hW S hs0 hs1 hsosc hdim
  refine ⟨⟨C ^ 2, sq_pos_of_pos hC, 2 * gamma, by positivity, ?_⟩, hgrid⟩
  intro t ht
  obtain ⟨hmem, hnorm⟩ := hbound t ht
  have hraw : MemLp (brownianTubeProfile W hmu.compactAttractor s t) 2 P := by
    convert hmem.add
      (memLp_const (meanBrownianTubeProfile W P hmu.compactAttractor s t)) using 1
    ext omega
    simp [centeredBrownianTubeProfile]
  refine ⟨hraw, ?_⟩
  have hreal : lpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s t) 2 P ≤
      C * Real.exp (-gamma * t) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal
      (mul_nonneg hC.le (Real.exp_pos _).le)] using h
  have hcenter : MinkowskiL2Recurrence.centeredL2Norm
      (brownianTubeProfile W hmu.compactAttractor s t) P ≤
        C * Real.exp (-gamma * t) := hreal
  calc
    variance (brownianTubeProfile W hmu.compactAttractor s t) P =
        MinkowskiL2Recurrence.centeredL2Norm
          (brownianTubeProfile W hmu.compactAttractor s t) P ^ 2 :=
      (MinkowskiL2Recurrence.centeredL2Norm_sq hraw).symm
    _ ≤ (C * Real.exp (-gamma * t)) ^ 2 :=
      (sq_le_sq₀ (MinkowskiL2Recurrence.centeredL2Norm_nonneg _ _)
        (mul_nonneg hC.le (Real.exp_pos _).le)).mpr hcenter
    _ = C ^ 2 * Real.exp (-(2 * gamma) * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring

end Concentration

end System

end

end BrownianImages
