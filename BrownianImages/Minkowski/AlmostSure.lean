/-
`sec:reconstruction`: the Borel--Cantelli passage used at the end of the
Minkowski tube-concentration argument.

The analytic part of that argument produces summable deviation probabilities
for the centred tube profile along every fixed grid phase.  This file records
the exact probability-theoretic conclusion independently of how those bounds
are obtained.
-/
import BrownianImages.Minkowski.Profile
import Mathlib.Probability.BorelCantelli
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Topology

namespace MinkowskiAlmostSure

/-- If the probabilities of every fixed positive deviation are summable, then
the random variables converge to zero almost surely. -/
theorem ae_tendsto_zero_of_summable_deviations
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : Nat -> Omega -> Real)
    (hsum : forall epsilon : Real, 0 < epsilon ->
      (∑' n : Nat, P {omega | epsilon <= |X n omega|}) ≠ ∞) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => X n omega) atTop (nhds 0) := by
  have hthreshold : forall k : Nat, ∀ᵐ omega ∂P,
      ∀ᶠ n : Nat in atTop, |X n omega| < 1 / ((k : Real) + 1) := by
    intro k
    have hepsilon : (0 : Real) < 1 / ((k : Real) + 1) := by positivity
    let E : Nat -> Set Omega := fun n =>
      {omega | 1 / ((k : Real) + 1) <= |X n omega|}
    have hne : (∑' n : Nat, P (E n)) ≠ ∞ := by
      simpa only [E] using hsum _ hepsilon
    filter_upwards [ae_eventually_notMem hne] with omega homega
    exact homega.mono fun n hn => by simpa only [E, Set.mem_setOf_eq, not_le] using hn
  filter_upwards [ae_all_iff.mpr hthreshold] with omega homega
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.mp (homega k)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hN n hn).trans hk

/-- An exponentially summable bound for each fixed deviation implies almost-sure
convergence to zero.  The constant may depend on the deviation threshold, as it
does after applying Chebyshev's inequality. -/
theorem ae_tendsto_zero_of_exponential_deviation_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : Nat -> Omega -> Real) {gamma : Real} (hgamma : 0 < gamma)
    (hbound : forall epsilon : Real, 0 < epsilon -> exists Cepsilon : Real,
      0 <= Cepsilon ∧ forall n : Nat,
        P {omega | epsilon <= |X n omega|} <=
          ENNReal.ofReal (Cepsilon * Real.exp (-gamma * (n : Real)))) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => X n omega) atTop (nhds 0) := by
  apply ae_tendsto_zero_of_summable_deviations X
  intro epsilon hepsilon
  obtain ⟨Cepsilon, hCepsilon, hdeviation⟩ := hbound epsilon hepsilon
  have hsummable : Summable
      (fun n : Nat => Cepsilon * Real.exp (-gamma * (n : Real))) := by
    have hexp : Summable (fun n : Nat => Real.exp ((n : Real) * (-gamma))) :=
      Real.summable_exp_nat_mul_iff.mpr (by linarith)
    simpa only [mul_neg, neg_mul, mul_comm] using hexp.mul_left Cepsilon
  have hfinite : (∑' n : Nat,
      ENNReal.ofReal (Cepsilon * Real.exp (-gamma * (n : Real)))) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hCepsilon (Real.exp_pos _).le) hsummable]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfinite (ENNReal.tsum_le_tsum hdeviation)

/-- A squared `L²` bound with exponential decay gives the summable deviation
bound required by Borel--Cantelli.  This is the norm-to-almost-sure part of
`thm:neighbourhood-concentration`; the separate analytic recurrence is responsible for
producing `hsq` for the centred tube profile. -/
theorem ae_tendsto_zero_of_exponential_eLpNorm_sq_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : Nat -> Omega -> Real) {C gamma : Real}
    (hC : 0 <= C) (hgamma : 0 < gamma)
    (hmem : forall n : Nat, MemLp (X n) 2 P)
    (hsq : forall n : Nat,
      eLpNorm (X n) 2 P ^ (2 : Real) <=
        ENNReal.ofReal (C * Real.exp (-gamma * (n : Real)))) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => X n omega) atTop (nhds 0) := by
  apply ae_tendsto_zero_of_exponential_deviation_bound X hgamma
  intro epsilon hepsilon
  refine ⟨C / epsilon ^ 2, div_nonneg hC (sq_nonneg epsilon), fun n => ?_⟩
  have hepsilonENN : ENNReal.ofReal epsilon ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, hepsilon]
  have hchebyshev := meas_ge_le_mul_pow_eLpNorm_enorm
    (p := (2 : ENNReal)) P two_ne_zero ENNReal.ofNat_ne_top
    (hmem n).aestronglyMeasurable hepsilonENN (by simp)
  have hsets : {omega | epsilon <= |X n omega|} =
      {omega | ENNReal.ofReal epsilon <= ‖X n omega‖ₑ} := by
    ext omega
    change epsilon <= |X n omega| ↔
      ENNReal.ofReal epsilon <= ‖X n omega‖ₑ
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  rw [hsets]
  refine hchebyshev.trans ?_
  refine (mul_le_mul_right (hsq n) _).trans_eq ?_
  rw [ENNReal.toReal_ofNat, ENNReal.rpow_two,
    ← ENNReal.ofReal_inv_of_pos hepsilon,
    ← ENNReal.ofReal_pow (inv_nonneg.mpr hepsilon.le),
    ← ENNReal.ofReal_mul (sq_nonneg epsilon⁻¹)]
  congr 1
  field_simp [hepsilon.ne']

/-- The paper's unsquared exponential `L²` estimate directly implies almost-sure
convergence along the integer grid. -/
theorem ae_tendsto_zero_of_exponential_eLpNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : Nat -> Omega -> Real) {C gamma : Real}
    (hC : 0 <= C) (hgamma : 0 < gamma)
    (hmem : forall n : Nat, MemLp (X n) 2 P)
    (hnorm : forall n : Nat,
      eLpNorm (X n) 2 P <=
        ENNReal.ofReal (C * Real.exp (-gamma * (n : Real)))) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => X n omega) atTop (nhds 0) := by
  apply ae_tendsto_zero_of_exponential_eLpNorm_sq_bound X
    (sq_nonneg C) (mul_pos zero_lt_two hgamma) hmem
  intro n
  calc
    eLpNorm (X n) 2 P ^ (2 : Real) <=
        ENNReal.ofReal (C * Real.exp (-gamma * (n : Real))) ^ (2 : Real) := by
      exact ENNReal.rpow_le_rpow (hnorm n) (by positivity)
    _ = ENNReal.ofReal
        (C ^ 2 * Real.exp (-(2 * gamma) * (n : Real))) := by
      rw [ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (mul_nonneg hC (Real.exp_pos _).le)]
      congr 1
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      ring_nf

/-- A scale-uniform exponential `L²` estimate on the nonnegative half-line gives
the paper's almost-sure convergence along every fixed phase `n + t`.  A finite
initial segment is discarded when the phase is negative. -/
theorem ae_tendsto_zero_along_phase_of_exponential_eLpNorm_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : Real -> Omega -> Real) {C gamma : Real}
    (hC : 0 <= C) (hgamma : 0 < gamma)
    (hmem : forall v : Real, 0 <= v -> MemLp (X v) 2 P)
    (hnorm : forall v : Real, 0 <= v ->
      eLpNorm (X v) 2 P <= ENNReal.ofReal (C * Real.exp (-gamma * v)))
    (t : Real) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => X ((n : Real) + t) omega)
      atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-t)
  have hNt : 0 <= (N : Real) + t := by linarith
  let Cphase : Real := C * Real.exp (-gamma * ((N : Real) + t))
  have hCphase : 0 <= Cphase :=
    mul_nonneg hC (Real.exp_pos _).le
  have hshift : ∀ᵐ omega ∂P, Tendsto
      (fun n : Nat => X (((n + N : Nat) : Real) + t) omega)
      atTop (nhds 0) := by
    apply ae_tendsto_zero_of_exponential_eLpNorm_bound
      (fun n : Nat => X (((n + N : Nat) : Real) + t))
      hCphase hgamma
    · intro n
      apply hmem
      simpa only [Nat.cast_add, add_assoc] using
        add_nonneg (Nat.cast_nonneg n) hNt
    · intro n
      have hv : 0 <= ((n + N : Nat) : Real) + t := by
        simpa only [Nat.cast_add, add_assoc] using
          add_nonneg (Nat.cast_nonneg n) hNt
      refine (hnorm _ hv).trans_eq ?_
      congr 1
      dsimp only [Cphase]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring
  filter_upwards [hshift] with omega homega
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n : Nat => X ((n : Real) + t) omega) N]
  simpa only [Nat.cast_add] using homega

/-- Paper-shaped form of the consequence in `thm:neighbourhood-concentration`: the stated
exponential `L²` estimate for the centred Brownian tube profile already implies
the almost-sure fixed-phase conclusion. -/
theorem tubeGridConcentration_of_exponential_eLpNorm
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {W : ℝ≥0 → Omega → Plane} {K : NonemptyCompacts ℝ} {s : Real}
    (hbound : exists C : Real, 0 < C ∧ exists gamma : Real, 0 < gamma ∧
      forall v : Real, 0 <= v ->
        MemLp (centeredBrownianTubeProfile W P K s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P K s v) 2 P <=
          ENNReal.ofReal (C * Real.exp (-gamma * v))) :
    forall t : Real, ∀ᵐ omega ∂P, Tendsto
      (fun n : Nat => centeredBrownianTubeProfile W P K s
        ((n : Real) + t) omega) atTop (nhds 0) := by
  obtain ⟨C, hC, gamma, hgamma, hbound⟩ := hbound
  intro t
  apply ae_tendsto_zero_along_phase_of_exponential_eLpNorm_bound
    (fun v => centeredBrownianTubeProfile W P K s v)
    hC.le hgamma
  · intro v hv
    exact (hbound v hv).1
  · intro v hv
    exact (hbound v hv).2

end MinkowskiAlmostSure

end BrownianImages
