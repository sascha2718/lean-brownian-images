/-
Endpoint-facing assembly of the Brownian tube moments and the elementary
consequences for the mean normalized tube profile.

All geometric covering, stopping-tree, and lower-correlation arguments have
already been discharged.  The only hypothesis left here is the classical
fact that the unit-interval Brownian maximum has moments of every positive
order.
-/
import BrownianImages.Minkowski.StoppingTubeUpper
import BrownianImages.Minkowski.TubeMeanContinuity

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [Nonempty iota]
variable {P : Measure Omega} {W : NNReal → Omega → Plane}

/-- The logarithmic normalization exactly cancels the tube-radius power. -/
theorem exp_tubeExponent_mul_tubeRadiusReal_rpow (s v : Real) :
    Real.exp (tubeExponent s * v) *
      tubeRadiusReal v ^ tubeExponent s = 1 := by
  rw [Real.rpow_def_of_pos (tubeRadiusReal_pos v)]
  unfold tubeRadiusReal
  rw [Real.log_exp, ← Real.exp_add]
  ring_nf
  simp

/-- The exact tube-moment endpoint, conditional only on the unit Brownian
radius moments. -/
theorem IsNatural.tubeMoments_of_standardRadiusMoments
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hunit : ∀ p : Real, 1 ≤ p → Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ p) P) :
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
  exact hmu.tubeMoments_of_upper S hsep hdim hs0 hs1 hW
    (hmu.tubeMomentUpper_of_standardRadiusMoments S hdim hs0 hW hunit)

/-- Unit Brownian radius moments give all-scale integrability, continuity, and
uniform positive lower and finite upper bounds for the mean normalized tube
profile.  These are the first two conclusions of `thm:neighbourhood-renewal`. -/
theorem IsNatural.meanTubeProfile_data_of_standardRadiusMoments
    (S : System iota) {K : Set Real} {s : Real}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsep : S.IntervalSeparated) (hdim : S.IsDimension s)
    {mu : Measure Real} (hmu : S.IsNatural K s mu)
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    (hunit : ∀ p : Real, 1 ≤ p → Integrable (fun omega =>
      (1 + standardBrownianRadius W omega) ^ p) P) :
    (∀ v : Real,
      Integrable (brownianTubeProfile W hmu.compactAttractor s v) P) ∧
    Continuous (meanBrownianTubeProfile W P hmu.compactAttractor s) ∧
    ∃ c C : Real, 0 < c ∧ ∀ v : Real, 0 ≤ v →
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s v ∧
      meanBrownianTubeProfile W P hmu.compactAttractor s v ≤ C := by
  have hall : ∀ v : Real,
      Integrable (brownianTubeProfile W hmu.compactAttractor s v) P :=
    hmu.integrable_brownianTubeProfile_of_standardRadiusMoments
      S hdim hW hunit
  have hcont := hW.continuous_meanBrownianTubeProfile_of_integrable
    hmu.compactAttractor hs1 hall
  have hmom := hmu.tubeMoments_of_standardRadiusMoments
    S hs0 hs1 hsep hdim hW hunit
  obtain ⟨C, hC, hupper⟩ := hmom.1 1 le_rfl
  obtain ⟨c, hc, hlower⟩ := hmom.2
  refine ⟨hall, hcont, c, C, hc, ?_⟩
  intro v hv
  let r : Real := tubeRadiusReal v
  have hr : 0 < r := tubeRadiusReal_pos v
  have hr1 : r ≤ 1 := by
    dsimp only [r, tubeRadiusReal]
    exact (Real.exp_le_one_iff).mpr (by linarith)
  obtain ⟨_hmassInt, hlowerR⟩ := hlower r hr hr1
  obtain ⟨_hareaInt, _hmassPowInt, hupperR⟩ := hupper r hr hr1
  have hmassNonneg : 0 ≤ ∫ omega,
      tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P :=
    integral_nonneg fun omega => tubeMass_nonneg r _
  have hareaNonneg : 0 ≤ ∫ omega,
      brownianTubeArea W hmu.compactAttractor r omega ∂P :=
    integral_nonneg fun omega => tubeArea_nonneg r _
  have hmassUpper : (∫ omega,
      tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P) ≤
        C * r ^ tubeExponent s := by
    calc
      (∫ omega,
        tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P) ≤
          (∫ omega,
            brownianTubeArea W hmu.compactAttractor r omega ∂P) +
          ∫ omega,
            tubeMass r (brownianImage W hmu.compactAttractor omega) ∂P :=
        le_add_of_nonneg_left hareaNonneg
      _ ≤ C * r ^ ((1 : Real) * tubeExponent s) := by
        simpa using hupperR
      _ = C * r ^ tubeExponent s := by rw [one_mul]
  have hmean : meanBrownianTubeProfile W P hmu.compactAttractor s v =
      Real.exp (tubeExponent s * v) *
        ∫ omega, tubeMass r
          (brownianImage W hmu.compactAttractor omega) ∂P := by
    unfold meanBrownianTubeProfile brownianTubeProfile normalizedTubeMass
    rw [integral_const_mul]
  rw [hmean]
  constructor
  · calc
      c = Real.exp (tubeExponent s * v) *
          (c * r ^ tubeExponent s) := by
        calc
          c = c * 1 := (mul_one c).symm
          _ = c * (Real.exp (tubeExponent s * v) *
              r ^ tubeExponent s) := by
            rw [exp_tubeExponent_mul_tubeRadiusReal_rpow]
          _ = Real.exp (tubeExponent s * v) *
              (c * r ^ tubeExponent s) := by ring
      _ ≤ Real.exp (tubeExponent s * v) *
          ∫ omega, tubeMass r
            (brownianImage W hmu.compactAttractor omega) ∂P :=
        mul_le_mul_of_nonneg_left hlowerR (Real.exp_pos _).le
  · calc
      Real.exp (tubeExponent s * v) *
          (∫ omega, tubeMass r
            (brownianImage W hmu.compactAttractor omega) ∂P) ≤
          Real.exp (tubeExponent s * v) *
            (C * r ^ tubeExponent s) :=
        mul_le_mul_of_nonneg_left hmassUpper (Real.exp_pos _).le
      _ = C := by
        calc
          Real.exp (tubeExponent s * v) *
              (C * r ^ tubeExponent s) =
              C * (Real.exp (tubeExponent s * v) *
                r ^ tubeExponent s) := by ring
          _ = C * 1 := by
            rw [exp_tubeExponent_mul_tubeRadiusReal_rpow]
          _ = C := mul_one C

end System

end

end BrownianImages
