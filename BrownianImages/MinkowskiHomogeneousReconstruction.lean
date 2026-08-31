/-
Minkowski reconstruction for the homogeneous two-map system without invoking the
general arithmetic renewal theorem.

Both similarities have the same half-logarithmic Brownian scaling delay.  The exact
mean tube-renewal equation therefore says that the mean profile changes across one
period by precisely the nonnegative multiple-counting defect.  The overlap estimate
makes that defect exponentially small.  Telescoping over a fixed generation gives
the delayed-mean comparison required by the generation-cylinder quotient theorem.
-/
import BrownianImages.MinkowskiBrownianMaximalMoment
import BrownianImages.MinkowskiGenerationRatio
import BrownianImages.MinkowskiOverlapSystem
import BrownianImages.MinkowskiTubeConcentrationAssembly
import BrownianImages.MinkowskiTubeMomentAssembly

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

/-- Every letter of the homogeneous system has the same half-logarithmic Brownian
scaling delay. -/
theorem homogeneousSystem_halfLogRatio {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (i : Fin 2) :
    (homogeneousSystem lam hlam0 hlam).halfLogRatio i =
      (1 / 2 : ℝ) * Real.log lam⁻¹ := by
  rfl

/-- For the homogeneous system the renewal convolution is a single translate: the
two equal natural weights sum to one. -/
theorem homogeneousSystem_tubeRenewalConv {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (m : ℝ → ℝ) (v : ℝ) :
    (homogeneousSystem lam hlam0 hlam).tubeRenewalConv
        (homogeneousDim lam) m v =
      m (v - (1 / 2 : ℝ) * Real.log lam⁻¹) := by
  rw [System.tubeRenewalConv, Fin.sum_univ_two,
    homogeneousSystem_halfLogRatio hlam0 hlam 0,
    homogeneousSystem_halfLogRatio hlam0 hlam 1]
  change lam ^ homogeneousDim lam * m (v - (1 / 2 : ℝ) * Real.log lam⁻¹) +
      lam ^ homogeneousDim lam * m (v - (1 / 2 : ℝ) * Real.log lam⁻¹) = _
  rw [rpow_homogeneousDim hlam0 hlam]
  ring

/-- A generation-`k` cylinder in the homogeneous system has delay `k beta`, where
`beta = (1/2) log(1/lam)`. -/
theorem homogeneousSystem_generationHalfLogRatio {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    ∀ (k : ℕ) (w : GenerationWord (Fin 2) k),
      (homogeneousSystem lam hlam0 hlam).generationHalfLogRatio k w =
        (k : ℝ) * ((1 / 2 : ℝ) * Real.log lam⁻¹)
  | 0, _ => by simp
  | Nat.succ k, w => by
      rw [System.generationHalfLogRatio_succ,
        homogeneousSystem_generationHalfLogRatio hlam0 hlam k w.1,
        homogeneousSystem_halfLogRatio hlam0 hlam w.2]
      push_cast
      ring

/-- If a function changes negligibly across one fixed delay at infinity, it also
changes negligibly across every fixed natural multiple of that delay along the
integer reconstruction grid. -/
theorem tendsto_natCast_sub_nat_mul_sub_of_oneStep
    (m : ℝ → ℝ) (beta : ℝ)
    (hone : Tendsto (fun v : ℝ => m (v - beta) - m v) atTop (nhds 0)) :
    ∀ k : ℕ, Tendsto
      (fun n : ℕ => m ((n : ℝ) - (k : ℝ) * beta) - m (n : ℝ))
      atTop (nhds 0)
  | 0 => by simp
  | Nat.succ k => by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have hshift : Tendsto
          (fun n : ℕ => (n : ℝ) - (k : ℝ) * beta) atTop atTop := by
        simpa only [sub_eq_add_neg] using
          (Filter.atTop.tendsto_atTop_add_const_right
            (-((k : ℝ) * beta)) hnat)
      have h := (hone.comp hshift).add
        (tendsto_natCast_sub_nat_mul_sub_of_oneStep m beta hone k)
      convert h using 1
      · funext n
        simp only [Function.comp_apply]
        push_cast
        ring_nf
      · simp

namespace System

universe u

variable {Omega : Type u} [MeasurableSpace Omega]

/-- Unconditional pathwise Minkowski reconstruction for the homogeneous two-map
natural measure.  The proof uses only Brownian maximal moments, the separated-piece
overlap estimate, the one-step homogeneous renewal equation, and exponential `L²`
concentration; no arithmetic renewal theorem is needed. -/
theorem IsNatural.tubeReconstructsOccupation_homogeneousSystem
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {K : Set ℝ} {mu : Measure ℝ}
    (hmu : (homogeneousSystem lam hlam0 hlam).IsNatural
      K (homogeneousDim lam) mu) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  let S : System (Fin 2) := homogeneousSystem lam hlam0 hlam
  let s : ℝ := homogeneousDim lam
  let beta : ℝ := (1 / 2 : ℝ) * Real.log lam⁻¹
  let m : ℝ → ℝ :=
    meanBrownianTubeProfile W P hmu.compactAttractor s
  let d : ℝ → ℝ := hmu.meanBrownianTubeDefectProfile S W P
  have hs0 : 0 < s := homogeneousDim_pos hlam0 hlam
  have hs1 : s < 1 := homogeneousDim_lt_one hlam0 hlam
  have hdim : S.IsDimension s := homogeneousSystem_isDimension hlam0 hlam
  have hsep : S.IntervalSeparated := homogeneousSystem_intervalSeparated hlam0 hlam
  have hunit : ∀ p : ℝ, 1 ≤ p → Integrable
      (fun omega => (1 + standardBrownianRadius W omega) ^ p) P := by
    intro p hp
    exact hW.integrable_one_add_standardBrownianRadius_rpow hp
  obtain ⟨hall, _hcontinuous, c, _A, hc, hbounds⟩ :=
    hmu.meanTubeProfile_data_of_standardRadiusMoments
      S hs0 hs1 hsep hdim hW hunit
  have hmom := hmu.tubeMoments_of_standardRadiusMoments
    S hs0 hs1 hsep hdim hW hunit
  obtain ⟨C, hC, hoverlap⟩ := hmu.tubeOverlap_of_tubeMomentsUpper
    hW S hs0 hs1 hsep hdim hmom.1
  let D : ℝ := ((Fintype.card (Fin 2) : ℝ) ^ 2 / 2) * C
  have hD : 0 ≤ D := mul_nonneg (by positivity) hC.le
  have halpha : 0 < tubeExponent s := tubeExponent_pos hs1
  have hrenewal : ∀ v : ℝ, 0 ≤ v →
      m v = m (v - beta) - d v ∧
      0 ≤ d v ∧
      d v ≤ D * Real.exp (-tubeExponent s * v) := by
    intro v hv
    have hr1 : tubeRadiusReal v ≤ 1 := by
      unfold tubeRadiusReal
      exact (Real.exp_le_one_iff).mpr (by linarith)
    have hpair : ∀ i j : Fin 2, i ≠ j →
        Integrable (fun omega => tubeOverlapArea (tubeRadiusReal v)
          (hmu.brownianFirstLevelPiece S W omega i)
          (hmu.brownianFirstLevelPiece S W omega j)) P ∧
        (∫ omega, tubeOverlapArea (tubeRadiusReal v)
          (hmu.brownianFirstLevelPiece S W omega i)
          (hmu.brownianFirstLevelPiece S W omega j) ∂P) ≤
            C * tubeRadiusReal v ^ (2 * tubeExponent s) := by
      intro i j hij
      simpa only [IsNatural.brownianFirstLevelPiece] using
        (hoverlap (tubeRadiusReal v) (tubeRadiusReal_pos v) hr1).1 i j hij
    have hrec := hW.mean_tube_renewal_of_pairwise_overlap
      S hmu v C hC.le (fun i => hall (v - S.halfLogRatio i)) hpair
    have hconv : S.tubeRenewalConv s m v = m (v - beta) := by
      simpa only [S, s, m, beta] using
        homogeneousSystem_tubeRenewalConv hlam0 hlam m v
    refine ⟨?_, hrec.2.2.1, ?_⟩
    · have hrecEq := hrec.2.1
      change m v = S.tubeRenewalConv s m v - d v at hrecEq
      rw [hconv] at hrecEq
      exact hrecEq
    · simpa only [d, D] using hrec.2.2.2
  have hdecay : Tendsto
      (fun v : ℝ => D * Real.exp (-tubeExponent s * v))
      atTop (nhds 0) := by
    have hneg : -tubeExponent s < 0 := by linarith
    have harg : Tendsto (fun v : ℝ => -tubeExponent s * v)
        atTop atBot :=
      (tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp harg).const_mul D
  have hd : Tendsto d atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
      exact (hrenewal v hv).2.1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
      exact (hrenewal v hv).2.2
    · exact hdecay
  have hone : Tendsto (fun v : ℝ => m (v - beta) - m v)
      atTop (nhds 0) := by
    apply hd.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    linarith [(hrenewal v hv).1]
  have hmean : ∀ k (w : GenerationWord (Fin 2) k), Tendsto
      (fun n : ℕ =>
        meanBrownianTubeProfile W P hmu.compactAttractor s
            ((n : ℝ) - S.generationHalfLogRatio k w) -
          meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
      atTop (nhds 0) := by
    intro k w
    have hk := tendsto_natCast_sub_nat_mul_sub_of_oneStep m beta hone k
    simpa only [m, S, s, beta,
      homogeneousSystem_generationHalfLogRatio hlam0 hlam k w] using hk
  have hlower : ∀ n : ℕ,
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ) := by
    intro n
    exact (hbounds n (Nat.cast_nonneg n)).1
  have hbound := (hmu.tubeConcentration_of_standardRadiusMoments
    hW S hs0 hs1 hsep hdim hunit).1
  exact hmu.tubeReconstructsOccupation_of_generation_tubeMassRatio S hdim hW
    (hmu.ae_generation_tubeMassRatio_of_exponential_concentration
      S hW hbound hc hmean hlower)

/-- The corresponding Borel reconstruction map is obtained formally from the
homogeneous pathwise tube limit. -/
theorem IsNatural.exists_borel_reconstruction_homogeneousSystem
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : NNReal → Omega → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {K : Set ℝ} {mu : Measure ℝ}
    (hmu : (homogeneousSystem lam hlam0 hlam).IsNatural
      K (homogeneousDim lam) mu) :
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (fun omega ↦ reconstruct (brownianImage W hmu.compactAttractor omega)) =ᵐ[P]
        occupationProb W mu := by
  exact MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise hW
    (hmu.tubeReconstructsOccupation_homogeneousSystem hW hlam0 hlam)

end System

end

end BrownianImages
