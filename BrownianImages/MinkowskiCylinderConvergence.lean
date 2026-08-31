/-
`sec:reconstruction`: the abstract final passage from finite cylinder estimates to weak
convergence of normalized tube probabilities.

The stochastic part of the reconstruction argument supplies the hypotheses of the theorem below:
fixed-generation tube-mass ratios, shrinking weighted cylinder diameters, and weak convergence of
the corresponding weighted atomic approximations.  This file contains only the deterministic
two-scale limit argument.
-/
import BrownianImages.MinkowskiCylinder
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace BrownianImages

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators BoundedContinuousFunction ENNReal NNReal Topology

/-- Abstract cylinder-to-weak-convergence theorem for normalized tube probabilities.  The index
type of the finite cylinder family may depend on the generation. -/
theorem tendsto_tubeProbability_of_cylinder_approximation
    (rho : Nat -> Real) (hrho : ∀ n, 0 < rho n)
    (hrho0 : Tendsto rho atTop (nhds 0))
    (I : Nat -> Type*) [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    (R : CompactPlane) (F : (k : Nat) -> I k -> CompactPlane)
    (x0 : (k : Nat) -> I k -> Plane) (p : (k : Nat) -> I k -> Real)
    (hunion : ∀ k, compactUnion (F k) = R)
    (hanchor : ∀ k i, x0 k i ∈ F k i)
    (hp : ∀ k i, 0 ≤ p k i) (hpsum : ∀ k, ∑ i, p k i = 1)
    (hratio : ∀ k i,
      Tendsto (fun n => tubeMassRatio (rho n) (F k) i) atTop (nhds (p k i)))
    (hdiam : Tendsto
      (fun k => ∑ i, p k i * Metric.diam (F k i : Set Plane)) atTop (nhds 0))
    (target : ProbabilityMeasure Plane)
    (hatomic : ∀ (f : Plane →ᵇ Real) {K : NNReal}, LipschitzWith K f ->
      Tendsto (fun k => ∑ i, p k i * f (x0 k i)) atTop
        (nhds (∫ x, f x ∂(target : Measure Plane)))) :
    Tendsto (fun n => tubeProbability (rho n) (hrho n) R) atTop (nhds target) := by
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f hfbounded hflip
  let K : NNReal := hflip.choose
  have hfK : LipschitzWith K f := hflip.choose_spec
  let fb : Plane →ᵇ Real :=
    { toFun := f
      continuous_toFun := hfK.continuous
      map_bounded' := hfbounded }
  let D : Nat -> Real := fun k => ∑ i, p k i * Metric.diam (F k i : Set Plane)
  let A : Nat -> Real := fun k => ∑ i, p k i * f (x0 k i)
  let T : Real := ∫ x, f x ∂(target : Measure Plane)
  have hD : Tendsto D atTop (nhds 0) := hdiam
  have hA : Tendsto A atTop (nhds T) := by
    simpa [A, T, fb] using hatomic fb hfK
  have hDnonneg : ∀ k, 0 ≤ D k := by
    intro k
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hp k i) Metric.diam_nonneg
  have hKD : Tendsto (fun k => (K : Real) * D k) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hD :
      Tendsto (fun k => (K : Real) * D k) atTop (nhds ((K : Real) * 0)))
  refine Metric.tendsto_atTop.2 fun epsilon hepsilon => ?_
  obtain ⟨kD, hkD⟩ := Metric.tendsto_atTop.1 hKD (epsilon / 4) (by positivity)
  obtain ⟨kA, hkA⟩ := Metric.tendsto_atTop.1 hA (epsilon / 4) (by positivity)
  let k := max kD kA
  have hkD' : kD ≤ k := le_max_left _ _
  have hkA' : kA ≤ k := le_max_right _ _
  have hKDsmall : (K : Real) * D k < epsilon / 4 := by
    have h := hkD k hkD'
    have hnonneg : 0 ≤ (K : Real) * D k :=
      mul_nonneg (NNReal.coe_nonneg K) (hDnonneg k)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using h
  have hAsmall : |A k - T| < epsilon / 4 := by
    simpa only [Real.dist_eq] using hkA k hkA'
  have herr := tendsto_cylinderErrorBound hrho hrho0 (F k) (p k)
    (hpsum k) (hratio k) (K : Real) ‖fb‖
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 herr (epsilon / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have herrorClose := hN n hn
  have herrorSmall :
      cylinderErrorBound (K : Real) ‖fb‖ (rho n) (F k) (p k) < epsilon / 2 := by
    rw [Real.dist_eq] at herrorClose
    have habs := le_abs_self
      (cylinderErrorBound (K : Real) ‖fb‖ (rho n) (F k) (p k) -
        (K : Real) * D k)
    linarith
  have hcylinder := integral_tubeProbability_sub_weighted_anchors_le
    fb hfK (hrho n) (F k) (x0 k) (hanchor k) (p k)
  have hcylinder' :
      |(∫ x, f x ∂(tubeProbability (rho n) (hrho n) R : Measure Plane)) - A k| ≤
        cylinderErrorBound (K : Real) ‖fb‖ (rho n) (F k) (p k) := by
    simpa [A, fb, cylinderErrorBound, hunion k] using hcylinder
  change dist (∫ x, f x ∂(tubeProbability (rho n) (hrho n) R : Measure Plane)) T < epsilon
  rw [Real.dist_eq]
  calc
    |(∫ x, f x ∂(tubeProbability (rho n) (hrho n) R : Measure Plane)) - T| =
        |((∫ x, f x ∂(tubeProbability (rho n) (hrho n) R : Measure Plane)) - A k) +
          (A k - T)| := by ring_nf
    _ ≤ |(∫ x, f x ∂(tubeProbability (rho n) (hrho n) R : Measure Plane)) - A k| +
        |A k - T| := abs_add_le _ _
    _ ≤ cylinderErrorBound (K : Real) ‖fb‖ (rho n) (F k) (p k) +
        |A k - T| := add_le_add hcylinder' le_rfl
    _ < epsilon := by linarith

end BrownianImages
