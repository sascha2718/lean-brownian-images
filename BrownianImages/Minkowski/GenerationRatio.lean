/-
The fixed-generation tube-mass ratio argument used by Minkowski reconstruction.

This module separates the last deterministic/probabilistic quotient calculation
from the renewal and concentration theorems which provide its hypotheses.  The
full normalized profile and every fixed generation-cylinder profile are centered,
their deterministic means differ only by the cylinder weight and a fixed renewal
delay, and the full mean stays uniformly positive.  The quotient therefore tends
to the natural cylinder weight.
-/
import BrownianImages.Minkowski.AlmostSure
import BrownianImages.Minkowski.GenerationScaling
import BrownianImages.Minkowski.Ratio
import BrownianImages.Periodic

namespace BrownianImages

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace System

variable {iota : Type*} [Fintype iota] [Nonempty iota] (S : System iota)
variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} {W : ℝ≥0 → Omega → Plane}

/-- The centered normalized profile of one fixed generation cylinder.  Its
deterministic mean is written in the scaling form supplied by
`integral_normalizedTubeMass_brownianGenerationCylinder`. -/
def IsNatural.centeredBrownianGenerationTubeProfile
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (W : ℝ≥0 → Omega → Plane)
    (P : Measure Omega) (k : ℕ) (w : GenerationWord iota k)
    (v : ℝ) (omega : Omega) : ℝ :=
  normalizedTubeMass s v
      (hmu.attractor.brownianGenerationCylinder S W omega k w) -
    S.generationWeight s k w *
      meanBrownianTubeProfile W P hmu.compactAttractor s
        (v - S.generationHalfLogRatio k w)

end System

variable {iota : Type*} [Fintype iota] [Nonempty iota] (S : System iota)
variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} {W : ℝ≥0 → Omega → Plane}

omit [Nonempty iota] in
/-- Centering the generation-cylinder scaling identity preserves equality in
distribution. -/
theorem IsPlanarBrownian.identDistrib_centeredBrownianGenerationTubeProfile
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (k : ℕ)
    (w : GenerationWord iota k) (v : ℝ) :
    IdentDistrib
      (hmu.centeredBrownianGenerationTubeProfile S W P k w v)
      (fun omega => S.generationWeight s k w *
        centeredBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w) omega) P P := by
  have h := (hW.identDistrib_normalizedTubeMass_brownianGenerationCylinder
    S hmu k w v).sub_const
      (S.generationWeight s k w *
        meanBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w))
  have hright : IdentDistrib
      (fun omega =>
        S.generationWeight s k w *
            brownianTubeProfile W hmu.compactAttractor s
              (v - S.generationHalfLogRatio k w) omega -
          S.generationWeight s k w *
            meanBrownianTubeProfile W P hmu.compactAttractor s
              (v - S.generationHalfLogRatio k w))
      (fun omega => S.generationWeight s k w *
        centeredBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w) omega) P P :=
    IdentDistrib.of_ae_eq h.aemeasurable_snd
      (Filter.Eventually.of_forall fun omega => by
        simp only [centeredBrownianTubeProfile]
        ring)
  change IdentDistrib
    (fun omega =>
      normalizedTubeMass s v
          (hmu.attractor.brownianGenerationCylinder S W omega k w) -
        S.generationWeight s k w *
          meanBrownianTubeProfile W P hmu.compactAttractor s
            (v - S.generationHalfLogRatio k w))
    (fun omega => S.generationWeight s k w *
      centeredBrownianTubeProfile W P hmu.compactAttractor s
        (v - S.generationHalfLogRatio k w) omega) P P
  exact h.trans hright

omit [Nonempty iota] in
/-- `L²` membership transfers from the delayed full profile to a generation
cylinder. -/
theorem IsPlanarBrownian.memLp_centeredBrownianGenerationTubeProfile
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (k : ℕ)
    (w : GenerationWord iota k) (v : ℝ)
    (hmem : MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s
      (v - S.generationHalfLogRatio k w)) 2 P) :
    MemLp (hmu.centeredBrownianGenerationTubeProfile S W P k w v) 2 P := by
  have hright : MemLp
      (fun omega => S.generationWeight s k w *
        centeredBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w) omega) 2 P := by
    change MemLp
      (S.generationWeight s k w •
        centeredBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w)) 2 P
    exact hmem.const_smul (S.generationWeight s k w)
  exact (hW.identDistrib_centeredBrownianGenerationTubeProfile
    S hmu k w v).memLp_iff.mpr hright

omit [Nonempty iota] in
/-- The generation-cylinder `L²` norm is the natural weight times the norm of
the delayed full centered profile. -/
theorem IsPlanarBrownian.eLpNorm_centeredBrownianGenerationTubeProfile
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (k : ℕ)
    (w : GenerationWord iota k) (v : ℝ) :
    eLpNorm (hmu.centeredBrownianGenerationTubeProfile S W P k w v) 2 P =
      ENNReal.ofReal (S.generationWeight s k w) *
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w)) 2 P := by
  rw [(hW.identDistrib_centeredBrownianGenerationTubeProfile
    S hmu k w v).eLpNorm_eq]
  have hscale := eLpNorm_const_smul
    (S.generationWeight s k w)
    (centeredBrownianTubeProfile W P hmu.compactAttractor s
      (v - S.generationHalfLogRatio k w)) 2 P
  change eLpNorm
      (S.generationWeight s k w •
        centeredBrownianTubeProfile W P hmu.compactAttractor s
          (v - S.generationHalfLogRatio k w)) 2 P = _
  simpa only [Real.enorm_eq_ofReal_abs,
    abs_of_pos (S.generationWeight_pos s k w)] using hscale

set_option maxHeartbeats 2000000

omit [Nonempty iota] in
/-- An exponential `L²` bound for the full centered profile yields almost-sure
convergence of every fixed generation-cylinder centered profile along the
reconstruction radii. -/
theorem IsPlanarBrownian.ae_tendsto_centeredBrownianGenerationTubeProfile
    [IsProbabilityMeasure P] (hW : IsPlanarBrownian W P)
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu)
    {C gamma : ℝ} (hC : 0 ≤ C) (hgamma : 0 < gamma)
    (hmem : ∀ v : ℝ, 0 ≤ v →
      MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P)
    (hnorm : ∀ v : ℝ, 0 ≤ v →
      eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
        ENNReal.ofReal (C * Real.exp (-gamma * v)))
    (k : ℕ) (w : GenerationWord iota k) :
    ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
        S W P k w (n : ℝ) omega) atTop (nhds 0) := by
  let p : ℝ := S.generationWeight s k w
  let beta : ℝ := S.generationHalfLogRatio k w
  have hp : 0 < p := S.generationWeight_pos s k w
  have hmemShift : ∀ u : ℝ, 0 ≤ u → MemLp
      (fun omega => hmu.centeredBrownianGenerationTubeProfile
        S W P k w (u + beta) omega) 2 P := by
    intro u hu
    apply hW.memLp_centeredBrownianGenerationTubeProfile S hmu
    simpa only [beta, add_sub_cancel_right] using hmem u hu
  have hnormShift : ∀ u : ℝ, 0 ≤ u →
      eLpNorm (fun omega => hmu.centeredBrownianGenerationTubeProfile
        S W P k w (u + beta) omega) 2 P ≤
          ENNReal.ofReal ((p * C) * Real.exp (-gamma * u)) := by
    intro u hu
    rw [hW.eLpNorm_centeredBrownianGenerationTubeProfile S hmu]
    have hb := hnorm u hu
    change ENNReal.ofReal p *
      eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s
        ((u + beta) - beta)) 2 P ≤ _
    rw [add_sub_cancel_right]
    calc
      ENNReal.ofReal p *
          eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s u) 2 P ≤
          ENNReal.ofReal p *
            ENNReal.ofReal (C * Real.exp (-gamma * u)) :=
        mul_le_mul_right hb _
      _ = ENNReal.ofReal ((p * C) * Real.exp (-gamma * u)) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
  have hshift : ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
        S W P k w (n : ℝ) omega) atTop (nhds 0) := by
    simpa only [add_assoc, neg_add_cancel, add_zero] using
      (MinkowskiAlmostSure.ae_tendsto_zero_along_phase_of_exponential_eLpNorm_bound
        (P := P)
        (fun u omega => hmu.centeredBrownianGenerationTubeProfile
          S W P k w (u + beta) omega)
        (C := p * C) (gamma := gamma) (mul_nonneg hp.le hC) hgamma
        hmemShift hnormShift (-beta))
  exact hshift

/-- The raw tube-mass quotient equals the quotient of normalized profiles. -/
theorem tubeMassRatio_eq_normalizedTubeMass
    {F : iota → CompactPlane} (s v : ℝ) (w : iota) :
    tubeMassRatio (tubeRadiusReal v) F w =
      normalizedTubeMass s v (F w) /
        normalizedTubeMass s v (compactUnion F) := by
  unfold tubeMassRatio normalizedTubeMass
  field_simp [Real.exp_ne_zero]

/-- Pathwise quotient lemma for one generation cylinder. -/
theorem System.IsNatural.tendsto_generation_tubeMassRatio_of_centered
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) {omega : Omega}
    (homega : Continuous (fun t => W t omega))
    (k : ℕ) (w : GenerationWord iota k) {c : ℝ} (hc : 0 < c)
    (hfull : Tendsto
      (fun n : ℕ => centeredBrownianTubeProfile W P hmu.compactAttractor s
        (n : ℝ) omega) atTop (nhds 0))
    (hcylinder : Tendsto
      (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
        S W P k w (n : ℝ) omega) atTop (nhds 0))
    (hmean : Tendsto
      (fun n : ℕ =>
        meanBrownianTubeProfile W P hmu.compactAttractor s
            ((n : ℝ) - S.generationHalfLogRatio k w) -
          meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
      atTop (nhds 0))
    (hlower : ∀ᶠ n : ℕ in atTop,
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ)) :
    Tendsto
      (fun n => tubeMassRatio (tubeRadius n)
        (hmu.attractor.brownianGenerationCylinder S W omega k) w)
      atTop (nhds (S.generationWeight s k w)) := by
  let x : ℕ → ℝ := fun n =>
    brownianTubeProfile W hmu.compactAttractor s (n : ℝ) omega
  let y : ℕ → ℝ := fun n => normalizedTubeMass s (n : ℝ)
    (hmu.attractor.brownianGenerationCylinder S W omega k w)
  let mx : ℕ → ℝ := fun n =>
    meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ)
  let my : ℕ → ℝ := fun n =>
    meanBrownianTubeProfile W P hmu.compactAttractor s
      ((n : ℝ) - S.generationHalfLogRatio k w)
  let p : ℝ := S.generationWeight s k w
  have hquotient := MinkowskiRatio.tendsto_div_of_weighted_centered_errors
    x y mx my p hc (ne_of_gt (S.generationWeight_pos s k w))
    (by simpa only [x, mx, centeredBrownianTubeProfile] using hfull)
    (by simpa only [y, my, p,
      System.IsNatural.centeredBrownianGenerationTubeProfile] using hcylinder)
    (by simpa only [my, mx] using hmean)
    (by simpa only [mx] using hlower)
  convert hquotient using 1
  funext n
  have hunion := hmu.attractor.compactUnion_brownianGenerationCylinder_eq
    S homega k
  have hunion' :
      compactUnion (hmu.attractor.brownianGenerationCylinder S W omega k) =
        brownianImage W hmu.compactAttractor omega := by
    simpa only [System.IsNatural.compactAttractor] using hunion
  rw [tubeRadius, show Real.exp (-(n : ℝ)) = tubeRadiusReal (n : ℝ) by rfl,
    tubeMassRatio_eq_normalizedTubeMass s (n : ℝ) w, hunion']
  simp only [x, y, brownianTubeProfile]

/-- Almost-sure system-level assembly of the fixed-generation quotient argument. -/
theorem System.IsNatural.ae_generation_tubeMassRatio_of_centered
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hW : IsPlanarBrownian W P)
    {c : ℝ} (hc : 0 < c)
    (hfull : ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => centeredBrownianTubeProfile W P hmu.compactAttractor s
        (n : ℝ) omega) atTop (nhds 0))
    (hcylinder : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota k),
      Tendsto
        (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
          S W P k w (n : ℝ) omega) atTop (nhds 0))
    (hmean : ∀ k (w : GenerationWord iota k), Tendsto
      (fun n : ℕ =>
        meanBrownianTubeProfile W P hmu.compactAttractor s
            ((n : ℝ) - S.generationHalfLogRatio k w) -
          meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
      atTop (nhds 0))
    (hlower : ∀ n : ℕ,
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ)) :
    ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hmu.attractor.brownianGenerationCylinder S W omega k) w)
        atTop (nhds (S.generationWeight s k w)) := by
  filter_upwards [hW.ae_continuous, hfull, hcylinder] with
    omega homega hfullOmega hcylinderOmega
  intro k w
  exact hmu.tendsto_generation_tubeMassRatio_of_centered S homega k w hc
    hfullOmega (hcylinderOmega k w) (hmean k w)
    (Filter.Eventually.of_forall hlower)

/-- Endpoint-facing ratio assembly.  Exponential `L²` concentration supplies
both the full-profile and all countably many fixed-cylinder centered limits; the
only additional analytic input is the deterministic delayed-mean comparison. -/
theorem System.IsNatural.ae_generation_tubeMassRatio_of_exponential_concentration
    [IsProbabilityMeasure P]
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hW : IsPlanarBrownian W P)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v)))
    {c : ℝ} (hc : 0 < c)
    (hmean : ∀ k (w : GenerationWord iota k), Tendsto
      (fun n : ℕ =>
        meanBrownianTubeProfile W P hmu.compactAttractor s
            ((n : ℝ) - S.generationHalfLogRatio k w) -
          meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
      atTop (nhds 0))
    (hlower : ∀ n : ℕ,
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ)) :
    ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota k),
      Tendsto
        (fun n => tubeMassRatio (tubeRadius n)
          (hmu.attractor.brownianGenerationCylinder S W omega k) w)
        atTop (nhds (S.generationWeight s k w)) := by
  obtain ⟨C, hC, gamma, hgamma, hbound⟩ := hbound
  have hfull : ∀ᵐ omega ∂P, Tendsto
      (fun n : ℕ => centeredBrownianTubeProfile W P hmu.compactAttractor s
        (n : ℝ) omega) atTop (nhds 0) := by
    simpa only [add_zero] using
      (MinkowskiAlmostSure.tubeGridConcentration_of_exponential_eLpNorm
        (W := W) (P := P) (K := hmu.compactAttractor) (s := s)
        ⟨C, hC, gamma, hgamma, hbound⟩ 0)
  have hcylinderAt (k : ℕ) (w : GenerationWord iota k) :
      ∀ᵐ omega ∂P, Tendsto
        (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
          S W P k w (n : ℝ) omega) atTop (nhds 0) :=
    hW.ae_tendsto_centeredBrownianGenerationTubeProfile S hmu
      hC.le hgamma (fun v hv => (hbound v hv).1)
      (fun v hv => (hbound v hv).2) k w
  have hcylinderK (k : ℕ) : ∀ᵐ omega ∂P,
      ∀ w : GenerationWord iota k, Tendsto
        (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
          S W P k w (n : ℝ) omega) atTop (nhds 0) :=
    ae_all_iff.mpr (hcylinderAt k)
  have hcylinder : ∀ᵐ omega ∂P, ∀ k (w : GenerationWord iota k),
      Tendsto
        (fun n : ℕ => hmu.centeredBrownianGenerationTubeProfile
          S W P k w (n : ℝ) omega) atTop (nhds 0) :=
    ae_all_iff.mpr hcylinderK
  exact hmu.ae_generation_tubeMassRatio_of_centered S hW hc
    hfull hcylinder hmean hlower

/-- A convergent mean profile is asymptotically unchanged by every fixed
generation delay. -/
theorem tendsto_natCast_sub_shift_sub_of_tendsto_atTop
    (m : ℝ → ℝ) {L beta : ℝ} (hm : Tendsto m atTop (nhds L)) :
    Tendsto (fun n : ℕ => m ((n : ℝ) - beta) - m (n : ℝ))
      atTop (nhds 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) - beta) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (Filter.atTop.tendsto_atTop_add_const_right (-beta) hnat)
  have h := (hm.comp hshift).sub (hm.comp hnat)
  simpa only [Function.comp_apply, sub_self] using h

/-- Uniform convergence on the lattice sections of one period is equivalent to
ordinary convergence to the periodic profile on the whole positive half-line. -/
theorem tendsto_sub_periodic_of_uniform_lattice
    {m periodicProfile : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hperiodic : Function.Periodic periodicProfile h)
    (huniform : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
        |m (t + (n : ℝ) * h) - periodicProfile t| ≤ epsilon) :
    Tendsto (fun v : ℝ => m v - periodicProfile v) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := huniform (epsilon / 2) (by linarith)
  refine ⟨(N : ℝ) * h, fun v hv => ?_⟩
  have hv0 : 0 ≤ v := by
    have hNh : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg N) hh.le
    exact hNh.trans hv
  obtain ⟨n, hn⟩ := exists_nat_sub_mem_Ico (p := h) (a := 0) hh hv0
  let t : ℝ := v - (n : ℝ) * h
  have ht0 : 0 ≤ t := by simpa only [t, zero_add] using hn.1
  have hth : t < h := by simpa only [t, zero_add] using hn.2
  have htIcc : t ∈ Set.Icc (0 : ℝ) h := ⟨ht0, hth.le⟩
  have hv_eq : v = t + (n : ℝ) * h := by
    dsimp only [t]
    ring
  have hNn : N ≤ n := by
    by_contra hnot
    have hnN : n < N := Nat.lt_of_not_ge hnot
    have hcast : (n : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnN)
    have hvlt : v < ((n : ℝ) + 1) * h := by
      have htlt : t < h := hth
      rw [hv_eq]
      nlinarith
    have hmul : ((n : ℝ) + 1) * h ≤ (N : ℝ) * h :=
      mul_le_mul_of_nonneg_right hcast hh.le
    linarith
  have hbound := hN n hNn t htIcc
  have hper : periodicProfile v = periodicProfile t := by
    rw [hv_eq]
    exact hperiodic.nat_mul n t
  change dist (m v - periodicProfile v) 0 < epsilon
  rw [Real.dist_eq, sub_zero, hper, hv_eq]
  exact hbound.trans_lt (by linarith)

/-- If a delay is an integral multiple of the period, a mean profile converging
uniformly to that periodic profile is asymptotically unchanged by the delay. -/
theorem tendsto_natCast_sub_period_sub_of_uniform_lattice
    {m periodicProfile : ℝ → ℝ} {h beta : ℝ} (hh : 0 < h)
    (hperiodic : Function.Periodic periodicProfile h)
    (hbeta : beta ∈ AddSubgroup.zmultiples h)
    (huniform : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
        |m (t + (n : ℝ) * h) - periodicProfile t| ≤ epsilon) :
    Tendsto (fun n : ℕ => m ((n : ℝ) - beta) - m (n : ℝ))
      atTop (nhds 0) := by
  have hglobal := tendsto_sub_periodic_of_uniform_lattice hh hperiodic huniform
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) - beta) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (Filter.atTop.tendsto_atTop_add_const_right (-beta) hnat)
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hbeta
  have hperShift : ∀ n : ℕ,
      periodicProfile ((n : ℝ) - beta) = periodicProfile (n : ℝ) := by
    intro n
    have hpz := hperiodic.int_mul z ((n : ℝ) - beta)
    have hz' : (z : ℝ) * h = beta := by
      simpa only [zsmul_eq_mul] using hz
    rw [hz'] at hpz
    simpa only [sub_add_cancel] using hpz.symm
  have h := (hglobal.comp hshift).sub (hglobal.comp hnat)
  convert h using 1
  · funext n
    rw [Function.comp_apply, Function.comp_apply, hperShift]
    ring
  · simp

omit [Nonempty iota] in
/-- Arithmeticity places every generation delay in the corresponding lattice. -/
theorem System.generationHalfLogRatio_mem_zmultiples
    (h : ℝ) (harith : S.TubeArithmetic h)
    (k : ℕ) (w : GenerationWord iota k) :
    S.generationHalfLogRatio k w ∈ AddSubgroup.zmultiples h := by
  rw [← harith]
  exact S.generationHalfLogRatio_mem_closure k w

/-- The closed subgroup generated by finitely many positive tube-renewal steps is
either dense or a lattice with a strictly positive span. -/
theorem System.tubeNonArithmetic_or_exists_tubeArithmetic_pos :
    S.TubeNonArithmetic ∨ ∃ h : ℝ, 0 < h ∧ S.TubeArithmetic h := by
  let H : AddSubgroup ℝ := AddSubgroup.closure (Set.range S.halfLogRatio)
  rcases AddSubgroup.dense_or_cyclic H with hdense | ⟨a, ha⟩
  · exact Or.inl hdense
  · right
    have ha0 : a ≠ 0 := by
      intro hazero
      obtain ⟨i⟩ := ‹Nonempty iota›
      have hi : S.halfLogRatio i ∈ H :=
        AddSubgroup.subset_closure (Set.mem_range_self i)
      have hzero : H = ⊥ := by
        rw [ha, hazero, ← AddSubgroup.zmultiples_eq_closure]
        simp
      rw [hzero] at hi
      have : S.halfLogRatio i = 0 := by simpa using hi
      exact (S.halfLogRatio_pos i).ne' this
    refine ⟨|a|, abs_pos.mpr ha0, ?_⟩
    have hcyclic : H = AddSubgroup.zmultiples a := by
      rw [ha, AddSubgroup.zmultiples_eq_closure]
    change H = AddSubgroup.zmultiples |a|
    rw [hcyclic]
    rcases lt_or_gt_of_ne ha0 with hneg | hpos
    · rw [abs_of_neg hneg]
      exact AddSubgroup.zmultiples_neg.symm
    · rw [abs_of_pos hpos]

/-- In the non-arithmetic case, the renewal limit and exponential concentration
give all fixed-generation ratios needed for reconstruction. -/
theorem System.IsNatural.tubeReconstructsOccupation_of_nonArithmetic_mean_limit
    [IsProbabilityMeasure P]
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hdim : S.IsDimension s)
    (hW : IsPlanarBrownian W P)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v)))
    {c L : ℝ} (hc : 0 < c)
    (hlower : ∀ n : ℕ,
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
    (hlimit : Tendsto
      (meanBrownianTubeProfile W P hmu.compactAttractor s)
      atTop (nhds L)) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  have hmean : ∀ k (w : GenerationWord iota k), Tendsto
      (fun n : ℕ =>
        meanBrownianTubeProfile W P hmu.compactAttractor s
            ((n : ℝ) - S.generationHalfLogRatio k w) -
          meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
      atTop (nhds 0) := by
    intro k w
    exact tendsto_natCast_sub_shift_sub_of_tendsto_atTop _ hlimit
  exact hmu.tubeReconstructsOccupation_of_generation_tubeMassRatio S hdim hW
    (hmu.ae_generation_tubeMassRatio_of_exponential_concentration
      S hW hbound hc hmean hlower)

/-- In the arithmetic case, uniform convergence to the periodic renewal profile
and exponential concentration give the same fixed-generation reconstruction.
Every generation delay is an integral multiple of the lattice span, so the
periodic phases cancel in the cylinder/full quotient. -/
theorem System.IsNatural.tubeReconstructsOccupation_of_arithmetic_periodic_limit
    [IsProbabilityMeasure P]
    {K : Set ℝ} {s : ℝ} {mu : Measure ℝ}
    (hmu : S.IsNatural K s mu) (hdim : S.IsDimension s)
    (hW : IsPlanarBrownian W P)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ v : ℝ, 0 ≤ v →
        MemLp (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ∧
        eLpNorm (centeredBrownianTubeProfile W P hmu.compactAttractor s v) 2 P ≤
          ENNReal.ofReal (C * Real.exp (-gamma * v)))
    {c h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hlower : ∀ n : ℕ,
      c ≤ meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
    (harith : S.TubeArithmetic h)
    {periodicProfile : ℝ → ℝ}
    (hperiodic : Function.Periodic periodicProfile h)
    (huniform : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) h,
        |meanBrownianTubeProfile W P hmu.compactAttractor s
            (t + (n : ℝ) * h) - periodicProfile t| ≤ epsilon) :
    MinkowskiReconstruction.TubeReconstructsOccupation
      W P hmu.compactAttractor mu := by
  have hmean : ∀ k (w : GenerationWord iota k), Tendsto
      (fun n : ℕ =>
        meanBrownianTubeProfile W P hmu.compactAttractor s
            ((n : ℝ) - S.generationHalfLogRatio k w) -
          meanBrownianTubeProfile W P hmu.compactAttractor s (n : ℝ))
      atTop (nhds 0) := by
    intro k w
    exact tendsto_natCast_sub_period_sub_of_uniform_lattice hh hperiodic
      (S.generationHalfLogRatio_mem_zmultiples h harith k w) huniform
  exact hmu.tubeReconstructsOccupation_of_generation_tubeMassRatio S hdim hW
    (hmu.ae_generation_tubeMassRatio_of_exponential_concentration
      S hW hbound hc hmean hlower)

end

end BrownianImages
