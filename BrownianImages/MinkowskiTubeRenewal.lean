/-
`sec:reconstruction`, `thm:tube-renewal`: the expectation-level renewal identity for
the normalised Brownian tube profile.

This file contains only the exact algebraic and probabilistic reduction.  The analytic
inputs remain explicit: integrability of the delayed profiles and of the normalised
multiple-counting defect, together with a bound for the latter.  In particular, no
renewal limit is asserted without the moment, overlap, and renewal-theorem hypotheses
which supply it in the paper.
-/
import BrownianImages.MinkowskiBrownianCompactPieces
import BrownianImages.MinkowskiDefectExpectation
import BrownianImages.MinkowskiProfile

namespace BrownianImages

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The translation part of every similarity is nonnegative, since the similarity
maps the left endpoint of the unit interval back into that interval. -/
theorem shift_nonneg (i : ι) : 0 ≤ S.shift i := by
  have h := S.mapsTo i (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa using h.1

/-- The renewal convolution for Brownian tube profiles, with half-logarithmic
steps `beta_i` and natural weights `p_i`. -/
noncomputable def tubeRenewalConv (s : ℝ) (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ i, S.tubeWeight s i * g (v - S.halfLogRatio i)

/-- The first-level attractor piece is the affine time copy to which Brownian scaling
for compact time sets applies. -/
theorem IsNatural.compactPiece_eq_affineTimeCompact
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ} (hmu : S.IsNatural K s mu)
    (i : ι) :
    hmu.compactPiece S i =
      affineTimeCompact (S.shift i).toNNReal (S.ratio i).toNNReal
        hmu.compactAttractor := by
  apply NonemptyCompacts.ext
  rw [IsNatural.coe_compactPiece, coe_affineTimeCompact]
  apply Set.image_congr
  intro t _ht
  rw [System.map, Real.coe_toNNReal _ (S.shift_nonneg i),
    Real.coe_toNNReal _ (S.ratio_pos i).le]
  ring

end System

/-- Shifting logarithmic scale by the Brownian half-logarithmic time step divides
the physical tube radius by the corresponding square-root dilation. -/
theorem tubeRadiusReal_sub_halfLogRatio
    {ι : Type*} [Fintype ι] (S : System ι) (v : ℝ) (i : ι) :
    tubeRadiusReal (v - S.halfLogRatio i) =
      tubeRadiusReal v / Real.sqrt (S.ratio i) := by
  have hratio : 0 < S.ratio i := S.ratio_pos i
  have hsqrt : Real.exp ((1 / 2 : ℝ) * Real.log (S.ratio i)) =
      Real.sqrt (S.ratio i) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hratio]
    congr 1
    ring
  rw [tubeRadiusReal, tubeRadiusReal, System.halfLogRatio,
    System.logRatio, Real.log_inv]
  rw [show -(v - (1 / 2 : ℝ) * -Real.log (S.ratio i)) =
      -v - (1 / 2 : ℝ) * Real.log (S.ratio i) by ring]
  rw [Real.exp_sub, hsqrt]

/-- The planar Brownian Jacobian and logarithmic normalisation combine to the
natural cylinder weight: `r_i exp(alpha beta_i) = r_i^s`. -/
theorem exp_tubeExponent_mul_ratio
    {ι : Type*} [Fintype ι] (S : System ι) (s v : ℝ) (i : ι) :
    Real.exp (tubeExponent s * v) * S.ratio i =
      S.tubeWeight s i *
        Real.exp (tubeExponent s * (v - S.halfLogRatio i)) := by
  have hratio : 0 < S.ratio i := S.ratio_pos i
  calc
    Real.exp (tubeExponent s * v) * S.ratio i =
        Real.exp (tubeExponent s * v) * Real.exp (Real.log (S.ratio i)) := by
      rw [Real.exp_log hratio]
    _ = Real.exp (tubeExponent s * v + Real.log (S.ratio i)) := by
      rw [Real.exp_add]
    _ = Real.exp (Real.log (S.ratio i) * s) *
        Real.exp (tubeExponent s * (v - S.halfLogRatio i)) := by
      rw [← Real.exp_add]
      congr 1
      rw [System.halfLogRatio, System.logRatio, Real.log_inv]
      unfold tubeExponent
      ring
    _ = S.tubeWeight s i *
        Real.exp (tubeExponent s * (v - S.halfLogRatio i)) := by
      rw [System.tubeWeight, Real.rpow_def_of_pos hratio]

/-- The normalised multiple-counting defect in the first-level tube decomposition. -/
noncomputable def normalizedTubeDefect {ι : Type*} [Fintype ι] [Nonempty ι]
    (s v : ℝ) (F : ι → CompactPlane) : ℝ :=
  Real.exp (tubeExponent s * v) * tubeDefect (tubeRadiusReal v) F

theorem normalizedTubeDefect_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (s v : ℝ) (F : ι → CompactPlane) :
    0 ≤ normalizedTubeDefect s v F :=
  mul_nonneg (Real.exp_pos _).le
    (tubeDefect_nonneg (tubeRadiusReal_pos v) F)

/-- Multiplying the elementary tube-defect estimate by the profile normalisation
gives its exact profile-scale form. -/
theorem normalizedTubeDefect_le_pairwiseTubeOverlapAreaSum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (s v : ℝ) (F : ι → CompactPlane) :
    normalizedTubeDefect s v F ≤
      Real.exp (tubeExponent s * v) *
        pairwiseTubeOverlapAreaSum (tubeRadiusReal v) F := by
  exact mul_le_mul_of_nonneg_left
    (tubeDefect_le_pairwiseTubeOverlapAreaSum (tubeRadiusReal_pos v) F)
    (Real.exp_pos _).le

/-- Exact pointwise decomposition of the normalised tube mass of a finite union
into the normalised masses of its pieces minus the normalised defect. -/
theorem normalizedTubeMass_compactUnion_eq_sum_sub_defect
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (s v : ℝ) (F : ι → CompactPlane) :
    normalizedTubeMass s v (compactUnion F) =
      (∑ i, normalizedTubeMass s v (F i)) - normalizedTubeDefect s v F := by
  unfold normalizedTubeMass normalizedTubeDefect tubeDefect
  rw [← Finset.mul_sum]
  ring

/-! ### First-level Brownian cylinders -/

/-- The compact Brownian image of the `i`th first-level attractor piece. -/
noncomputable def System.IsNatural.brownianFirstLevelPiece
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (W : ℝ≥0 → Omega → Plane)
    (omega : Omega) (i : ι) : CompactPlane :=
  brownianImage W (hmu.compactPiece S i) omega

/-- On a continuous sample path, the first-level Brownian cylinders cover exactly
the Brownian image of the full attractor. -/
theorem System.IsNatural.compactUnion_brownianFirstLevelPiece_eq
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) {W : ℝ≥0 → Omega → Plane}
    {omega : Omega} (homega : Continuous (fun t => W t omega)) :
    compactUnion (fun i => hmu.brownianFirstLevelPiece S W omega i) =
      brownianImage W hmu.compactAttractor omega := by
  apply le_antisymm
  · unfold compactUnion
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro i _ x hx
    change x ∈ (brownianImage W (hmu.compactPiece S i) omega : Set Plane) at hx
    change x ∈ (brownianImage W hmu.compactAttractor omega : Set Plane)
    rw [coe_brownianImage_of_continuous _ homega] at hx
    rw [coe_brownianImage_of_continuous _ homega]
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨t, ?_, rfl⟩
    rw [System.IsNatural.coe_compactPiece] at ht
    change t ∈ K
    rw [hmu.attractor.2.2.2]
    exact Set.mem_iUnion.mpr ⟨i, ht⟩
  · intro x hx
    change x ∈ (brownianImage W hmu.compactAttractor omega : Set Plane) at hx
    rw [coe_brownianImage_of_continuous _ homega] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    change t ∈ K at ht
    rw [hmu.attractor.2.2.2] at ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    apply Finset.le_sup'
      (fun i => hmu.brownianFirstLevelPiece S W omega i) (Finset.mem_univ i)
    change W t.toNNReal omega ∈
      (brownianImage W (hmu.compactPiece S i) omega : Set Plane)
    rw [coe_brownianImage_of_continuous _ homega,
      System.IsNatural.coe_compactPiece]
    exact ⟨t, hi, rfl⟩

/-- The first-level Brownian cylinders cover the full compact image almost surely. -/
theorem IsPlanarBrownian.ae_compactUnion_brownianFirstLevelPiece_eq
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    {P : Measure Omega} {W : ℝ≥0 → Omega → Plane}
    (hW : IsPlanarBrownian W P) (S : System ι)
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) :
    ∀ᵐ omega ∂P,
      compactUnion (fun i => hmu.brownianFirstLevelPiece S W omega i) =
        brownianImage W hmu.compactAttractor omega := by
  filter_upwards [hW.ae_continuous] with omega homega
  exact hmu.compactUnion_brownianFirstLevelPiece_eq S homega

/-- Exact tube-mass law of a first-level Brownian cylinder.  The right-hand side
is the full-attractor tube mass at the delayed logarithmic scale, multiplied by
the temporal Jacobian `r_i`. -/
theorem IsPlanarBrownian.map_tubeMass_brownianFirstLevelPiece_eq
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v : ℝ) (i : ι) :
    P.map (fun omega => tubeMass (tubeRadiusReal v)
        (hmu.brownianFirstLevelPiece S W omega i)) =
      P.map (fun omega => S.ratio i *
        tubeMass (tubeRadiusReal (v - S.halfLogRatio i))
          (brownianImage W hmu.compactAttractor omega)) := by
  have hrne : (S.ratio i).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (S.ratio_pos i))
  have hlaw := hW.map_tubeMass_affineBrownianCompactPiece_eq
    (tubeRadiusReal_pos v) (S.shift i).toNNReal hrne hmu.compactAttractor
    hmu.attractor.2.2.1
  simpa only [System.IsNatural.brownianFirstLevelPiece,
    hmu.compactPiece_eq_affineTimeCompact S i, affineBrownianCompactPiece,
    Real.coe_toNNReal _ (S.ratio_pos i).le,
    ← tubeRadiusReal_sub_halfLogRatio S v i] using hlaw

/-- The profile-scale form of Brownian cylinder scaling: the normalised first-level
piece has the same law as the delayed full profile multiplied by `p_i = r_i^s`. -/
theorem IsPlanarBrownian.identDistrib_normalizedTubeMass_brownianFirstLevelPiece
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v : ℝ) (i : ι) :
    IdentDistrib
      (fun omega => normalizedTubeMass s v
        (hmu.brownianFirstLevelPiece S W omega i))
      (fun omega => S.tubeWeight s i *
        brownianTubeProfile W hmu.compactAttractor s
          (v - S.halfLogRatio i) omega) P P := by
  let X : Omega → ℝ := fun omega =>
    tubeMass (tubeRadiusReal v) (hmu.brownianFirstLevelPiece S W omega i)
  let Y : Omega → ℝ := fun omega => S.ratio i *
    tubeMass (tubeRadiusReal (v - S.halfLogRatio i))
      (brownianImage W hmu.compactAttractor omega)
  have hX : AEMeasurable X P :=
    (continuous_tubeMass (tubeRadiusReal_pos v)).measurable.comp_aemeasurable
      (hW.aemeasurable_brownianImage (hmu.compactPiece S i))
  have hY : AEMeasurable Y P :=
    (continuous_const.mul
      (continuous_tubeMass (tubeRadiusReal_pos (v - S.halfLogRatio i)))).measurable
      |>.comp_aemeasurable
        (hW.aemeasurable_brownianImage hmu.compactAttractor)
  have hmass : IdentDistrib X Y P P :=
    ⟨hX, hY, hW.map_tubeMass_brownianFirstLevelPiece_eq S hmu v i⟩
  have hscaled := hmass.const_mul (Real.exp (tubeExponent s * v))
  simpa only [X, Y, normalizedTubeMass, brownianTubeProfile, ← mul_assoc,
    exp_tubeExponent_mul_ratio S s v i] using hscaled

/-- Integrability transfers exactly from the delayed full profile to a normalised
first-level cylinder. -/
theorem IsPlanarBrownian.integrable_normalizedTubeMass_brownianFirstLevelPiece_iff
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v : ℝ) (i : ι) :
    Integrable (fun omega => normalizedTubeMass s v
      (hmu.brownianFirstLevelPiece S W omega i)) P ↔
      Integrable (fun omega => S.tubeWeight s i *
        brownianTubeProfile W hmu.compactAttractor s
          (v - S.halfLogRatio i) omega) P :=
  (hW.identDistrib_normalizedTubeMass_brownianFirstLevelPiece S hmu v i).integrable_iff

/-- The expectation of a normalised first-level cylinder is the natural cylinder
weight times the delayed mean profile, whenever the delayed profile is integrable. -/
theorem IsPlanarBrownian.integral_normalizedTubeMass_brownianFirstLevelPiece
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v : ℝ) (i : ι) :
    (∫ omega, normalizedTubeMass s v
      (hmu.brownianFirstLevelPiece S W omega i) ∂P) =
      S.tubeWeight s i *
        meanBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.halfLogRatio i) := by
  rw [(hW.identDistrib_normalizedTubeMass_brownianFirstLevelPiece
    S hmu v i).integral_eq]
  exact integral_const_mul _ _

/-! ### Expectation-level renewal equation -/

/-- The expected profile-scale multiple-counting defect `d(v)` from the tube
renewal equation. -/
noncomputable def System.IsNatural.meanBrownianTubeDefectProfile
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (W : ℝ≥0 → Omega → Plane)
    (P : Measure Omega) (v : ℝ) : ℝ :=
  ∫ omega, normalizedTubeDefect s v
    (fun i => hmu.brownianFirstLevelPiece S W omega i) ∂P

/-- The expected normalised tube defect is nonnegative. -/
theorem System.IsNatural.meanBrownianTubeDefectProfile_nonneg
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (W : ℝ≥0 → Omega → Plane)
    (P : Measure Omega) (v : ℝ) :
    0 ≤ hmu.meanBrownianTubeDefectProfile S W P v := by
  apply integral_nonneg
  intro omega
  exact normalizedTubeDefect_nonneg s v
    (fun i => hmu.brownianFirstLevelPiece S W omega i)

/-- **Expectation-level tube renewal equation.**  Integrability of the delayed
full profiles and of the raw first-level defect implies integrability at the
current scale and gives the exact equation

`m(v) = sum_i p_i m(v - beta_i) - d(v)`.

Thus the remaining analytic input is precisely an integrable exponentially
decaying defect (plus the renewal-theorem passage), rather than any further
Brownian scaling or finite-union algebra. -/
theorem IsPlanarBrownian.integrable_brownianTubeProfile_and_mean_renewal_eq
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v : ℝ)
    (hdelayed : ∀ i,
      Integrable (brownianTubeProfile W hmu.compactAttractor s
        (v - S.halfLogRatio i)) P)
    (hdefect : Integrable (fun omega =>
      tubeDefect (tubeRadiusReal v)
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) P) :
    Integrable (brownianTubeProfile W hmu.compactAttractor s v) P ∧
      meanBrownianTubeProfile W P hmu.compactAttractor s v =
        S.tubeRenewalConv s
          (meanBrownianTubeProfile W P hmu.compactAttractor s) v -
          hmu.meanBrownianTubeDefectProfile S W P v := by
  let F : ι → Omega → CompactPlane := fun i omega =>
    hmu.brownianFirstLevelPiece S W omega i
  have hpiece : ∀ i,
      Integrable (fun omega => normalizedTubeMass s v (F i omega)) P := by
    intro i
    apply (hW.integrable_normalizedTubeMass_brownianFirstLevelPiece_iff
      S hmu v i).2
    exact (hdelayed i).const_mul (S.tubeWeight s i)
  have hsum : Integrable
      (fun omega => ∑ i, normalizedTubeMass s v (F i omega)) P :=
    integrable_finsetSum Finset.univ fun i _ => hpiece i
  have hdefectNorm : Integrable
      (fun omega => normalizedTubeDefect s v (fun i => F i omega)) P := by
    simpa only [normalizedTubeDefect] using
      hdefect.const_mul (Real.exp (tubeExponent s * v))
  have hrec : brownianTubeProfile W hmu.compactAttractor s v =ᵐ[P]
      fun omega => (∑ i, normalizedTubeMass s v (F i omega)) -
        normalizedTubeDefect s v (fun i => F i omega) := by
    filter_upwards [hW.ae_compactUnion_brownianFirstLevelPiece_eq S hmu]
      with omega hunion
    unfold brownianTubeProfile
    rw [← hunion]
    exact normalizedTubeMass_compactUnion_eq_sum_sub_defect s v
      (fun i => F i omega)
  have hfull : Integrable
      (brownianTubeProfile W hmu.compactAttractor s v) P :=
    (hsum.sub hdefectNorm).congr hrec.symm
  refine ⟨hfull, ?_⟩
  unfold meanBrownianTubeProfile System.tubeRenewalConv
  rw [integral_congr_ae hrec, integral_sub hsum hdefectNorm,
    integral_finsetSum]
  · apply congrArg₂ (· - ·)
    · apply Finset.sum_congr rfl
      intro i _
      exact hW.integral_normalizedTubeMass_brownianFirstLevelPiece S hmu v i
    · rfl
  · intro i _
    exact hpiece i

/-- A raw defect expectation of order `r^(2 alpha)` becomes an exponentially
decaying forcing of order `exp(-alpha v)` in the normalised renewal equation. -/
theorem System.IsNatural.meanBrownianTubeDefectProfile_le_of_tubeDefect_mean_le
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (W : ℝ≥0 → Omega → Plane)
    (P : Measure Omega) (v C : ℝ)
    (hbound : (∫ omega, tubeDefect (tubeRadiusReal v)
      (fun i => hmu.brownianFirstLevelPiece S W omega i) ∂P) ≤
        C * tubeRadiusReal v ^ (2 * tubeExponent s)) :
    hmu.meanBrownianTubeDefectProfile S W P v ≤
      C * Real.exp (-tubeExponent s * v) := by
  unfold System.IsNatural.meanBrownianTubeDefectProfile normalizedTubeDefect
  rw [integral_const_mul]
  calc
    Real.exp (tubeExponent s * v) *
        (∫ omega, tubeDefect (tubeRadiusReal v)
          (fun i => hmu.brownianFirstLevelPiece S W omega i) ∂P) ≤
        Real.exp (tubeExponent s * v) *
          (C * tubeRadiusReal v ^ (2 * tubeExponent s)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = C * Real.exp (-tubeExponent s * v) := by
      rw [tubeRadiusReal, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      calc
        Real.exp (tubeExponent s * v) *
            (C * Real.exp (-v * (2 * tubeExponent s))) =
            C * (Real.exp (tubeExponent s * v) *
              Real.exp (-v * (2 * tubeExponent s))) := by ring
        _ = C * Real.exp
            (tubeExponent s * v + -v * (2 * tubeExponent s)) := by
          rw [Real.exp_add]
        _ = C * Real.exp (-tubeExponent s * v) := by
          congr 2
          ring

/-- A uniform finite-pair overlap estimate gives exactly the integrable,
exponentially decaying forcing required by the expectation-level renewal equation.
The only loss is the deterministic finite-family factor `card(iota)^2 / 2`. -/
theorem IsPlanarBrownian.integrable_normalizedTubeDefect_and_mean_le_of_pairwise_overlap
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ i j : ι, i ≠ j →
      Integrable (fun omega => tubeOverlapArea (tubeRadiusReal v)
        (hmu.brownianFirstLevelPiece S W omega i)
        (hmu.brownianFirstLevelPiece S W omega j)) P ∧
      (∫ omega, tubeOverlapArea (tubeRadiusReal v)
        (hmu.brownianFirstLevelPiece S W omega i)
        (hmu.brownianFirstLevelPiece S W omega j) ∂P) ≤
          C * tubeRadiusReal v ^ (2 * tubeExponent s)) :
    Integrable (fun omega => normalizedTubeDefect s v
      (fun i => hmu.brownianFirstLevelPiece S W omega i)) P ∧
    0 ≤ hmu.meanBrownianTubeDefectProfile S W P v ∧
    hmu.meanBrownianTubeDefectProfile S W P v ≤
      (((Fintype.card ι : ℝ) ^ 2 / 2) * C) *
        Real.exp (-tubeExponent s * v) := by
  let F : ι → Omega → CompactPlane := fun i omega =>
    hmu.brownianFirstLevelPiece S W omega i
  have hF : ∀ i, AEMeasurable (F i) P := fun i =>
    hW.aemeasurable_brownianImage (hmu.compactPiece S i)
  have hoverlap : ∀ i j : ι, i ≠ j →
      Integrable (fun omega => tubeOverlapArea (tubeRadiusReal v)
        (F i omega) (F j omega)) P :=
    fun i j hij => (hpair i j hij).1
  have hscale : 0 ≤ C * tubeRadiusReal v ^ (2 * tubeExponent s) :=
    mul_nonneg hC (Real.rpow_nonneg (tubeRadiusReal_pos v).le _)
  have hrawInt : Integrable (fun omega =>
      tubeDefect (tubeRadiusReal v) (fun i => F i omega)) P :=
    integrable_tubeDefect_of_pairwise_overlap (tubeRadiusReal_pos v) hF hoverlap
  have hrawBound : (∫ omega,
      tubeDefect (tubeRadiusReal v) (fun i => F i omega) ∂P) ≤
      ((Fintype.card ι : ℝ) ^ 2 / 2) *
        (C * tubeRadiusReal v ^ (2 * tubeExponent s)) :=
    integral_tubeDefect_le_card_sq_mul (tubeRadiusReal_pos v) hscale hF
      hoverlap (fun i j hij => (hpair i j hij).2)
  have hnormInt : Integrable (fun omega => normalizedTubeDefect s v
      (fun i => F i omega)) P := by
    simpa only [normalizedTubeDefect] using
      hrawInt.const_mul (Real.exp (tubeExponent s * v))
  refine ⟨hnormInt,
    hmu.meanBrownianTubeDefectProfile_nonneg S W P v, ?_⟩
  apply hmu.meanBrownianTubeDefectProfile_le_of_tubeDefect_mean_le
    S W P v (((Fintype.card ι : ℝ) ^ 2 / 2) * C)
  change (∫ omega, tubeDefect (tubeRadiusReal v) (fun i => F i omega) ∂P) ≤ _
  calc
    (∫ omega, tubeDefect (tubeRadiusReal v) (fun i => F i omega) ∂P) ≤
        ((Fintype.card ι : ℝ) ^ 2 / 2) *
          (C * tubeRadiusReal v ^ (2 * tubeExponent s)) := hrawBound
    _ = (((Fintype.card ι : ℝ) ^ 2 / 2) * C) *
          tubeRadiusReal v ^ (2 * tubeExponent s) := by ring

/-- Combined finite-overlap-to-renewal reduction at one logarithmic scale.  Pairwise
overlap estimates and delayed-profile integrability yield the current integrability,
the exact mean renewal equation, and the exponentially decaying nonnegative forcing. -/
theorem IsPlanarBrownian.mean_tube_renewal_of_pairwise_overlap
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Omega → Plane} (hW : IsPlanarBrownian W P)
    (S : System ι) {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (v C : ℝ) (hC : 0 ≤ C)
    (hdelayed : ∀ i,
      Integrable (brownianTubeProfile W hmu.compactAttractor s
        (v - S.halfLogRatio i)) P)
    (hpair : ∀ i j : ι, i ≠ j →
      Integrable (fun omega => tubeOverlapArea (tubeRadiusReal v)
        (hmu.brownianFirstLevelPiece S W omega i)
        (hmu.brownianFirstLevelPiece S W omega j)) P ∧
      (∫ omega, tubeOverlapArea (tubeRadiusReal v)
        (hmu.brownianFirstLevelPiece S W omega i)
        (hmu.brownianFirstLevelPiece S W omega j) ∂P) ≤
          C * tubeRadiusReal v ^ (2 * tubeExponent s)) :
    Integrable (brownianTubeProfile W hmu.compactAttractor s v) P ∧
    meanBrownianTubeProfile W P hmu.compactAttractor s v =
      S.tubeRenewalConv s
        (meanBrownianTubeProfile W P hmu.compactAttractor s) v -
        hmu.meanBrownianTubeDefectProfile S W P v ∧
    0 ≤ hmu.meanBrownianTubeDefectProfile S W P v ∧
    hmu.meanBrownianTubeDefectProfile S W P v ≤
      (((Fintype.card ι : ℝ) ^ 2 / 2) * C) *
        Real.exp (-tubeExponent s * v) := by
  have hforcing :=
    hW.integrable_normalizedTubeDefect_and_mean_le_of_pairwise_overlap
      S hmu v C hC hpair
  have hrawInt : Integrable (fun omega =>
      tubeDefect (tubeRadiusReal v)
        (fun i => hmu.brownianFirstLevelPiece S W omega i)) P := by
    have hscale : 0 ≤ C * tubeRadiusReal v ^ (2 * tubeExponent s) :=
      mul_nonneg hC (Real.rpow_nonneg (tubeRadiusReal_pos v).le _)
    exact integrable_tubeDefect_of_pairwise_overlap (tubeRadiusReal_pos v)
      (fun i => hW.aemeasurable_brownianImage (hmu.compactPiece S i))
      (fun i j hij => (hpair i j hij).1)
  have hrenewal := hW.integrable_brownianTubeProfile_and_mean_renewal_eq
    S hmu v hdelayed hrawInt
  exact ⟨hrenewal.1, hrenewal.2, hforcing.2.1, hforcing.2.2⟩

end

end BrownianImages
