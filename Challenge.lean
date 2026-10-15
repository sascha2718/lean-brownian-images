module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# Distinguishing sets and measures from their planar Brownian images

The nine results of Section 1 of arXiv:2610.16339v2. Expected correlation
profiles distinguish Brownian occupation laws, and the compact image determines its
occupation measure. The two-contraction family has finitely many possible exceptions
to separation, with no exceptions for sufficiently small dimension.
-/

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

/-! ### Brownian occupation measures and their correlation profiles -/

/-- The plane `ℝ²`, carrying the Euclidean metric. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `eq:correlation-integral`: the correlation integral
`C_r(ν) = (ν × ν){(x,y) : |x - y| < r}`. -/
noncomputable def corr (ν : Measure Plane) (r : ℝ) : ℝ≥0∞ :=
  (ν.prod ν) {p : Plane × Plane | dist p.1 p.2 < r}

/-- `eq:frostman`: `μ` is `s`-Frostman with constant `A`, that is a measure on `[0,1]`
with `μ(B̄(x,ρ)) ≤ A ρ^s` for every `x` and every `0 < ρ ≤ 1`. -/
structure IsFrostman (s A : ℝ) (μ : Measure ℝ) : Prop where
  one_le_const : 1 ≤ A
  support : μ (Set.Icc (0:ℝ) 1)ᶜ = 0
  measure_closedBall_le :
    ∀ x : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ s)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Planar Brownian motion: independent real Brownian
motions in two dimensions with almost surely continuous paths. -/
structure IsPlanarBrownian (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) : Prop where
  /-- Each coordinate is a real Brownian motion, paths included. -/
  coord : ∀ i : Fin 2, IsBrownianReal (fun t ω => W t ω i) P
  /-- The two coordinate processes are independent. -/
  indep : iIndepFun (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 => W t ω i) P

/-- The occupation measure `ν = W_*μ` of the Brownian path, a random measure on the
plane. The time parameter is read through `Real.toNNReal`, which is the identity on the
support `[0,1]` of `μ`. -/
noncomputable def occupation (W : ℝ≥0 → Ω → Plane) (μ : Measure ℝ) (ω : Ω) : Measure Plane :=
  μ.map (fun t : ℝ => W t.toNNReal ω)

/-- `eq:expected-profile`: the normalised expected correlation profile
`H_μ^s(t) = e^{2st} 𝔼 C_{e^{-t}}(W_*μ)`. -/
noncomputable def expectedProfile (W : ℝ≥0 → Ω → Plane) (P : Measure Ω)
    (s : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  Real.exp (2 * s * t) * ∫ ω, (corr (occupation W μ ω) (Real.exp (-t))).toReal ∂P

/-- The occupation measure read as a point of `𝒫(ℝ²)`, the space the paper takes laws
on, with the Dirac mass at the origin as the value when the total mass is not one. -/
noncomputable def occupationProb (W : ℝ≥0 → Ω → Plane) (μ : Measure ℝ) (ω : Ω) :
    ProbabilityMeasure Plane :=
  open scoped Classical in
  if h : IsProbabilityMeasure (occupation W μ ω) then ⟨occupation W μ ω, h⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- `Law(W_*μ)`, a measure on `𝒫(ℝ²)`. -/
noncomputable def occupationLaw (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (μ : Measure ℝ) :
    Measure (ProbabilityMeasure Plane) :=
  P.map (occupationProb W μ)

/-! ### Self-similar iterated function systems and their natural measures -/

/-- A self-similar iterated function system (IFS) on `[0,1]`: finitely many similarities
`S_i(x) = ε_i r_i x + b_i` with contraction ratios `r_i ∈ (0,1)` and orientations
`ε_i ∈ {1, -1}`, each mapping `[0,1]` into itself. -/
structure System (ι : Type*) [Fintype ι] where
  /-- The contraction ratios. -/
  ratio : ι → ℝ
  /-- The orientations, `1` for an orientation-preserving similarity and `-1` for an
  orientation-reversing one. -/
  sign : ι → ℝ
  /-- The translation parts. -/
  shift : ι → ℝ
  /-- Each ratio is positive. -/
  ratio_pos : ∀ i, 0 < ratio i
  /-- Each ratio is a contraction. -/
  ratio_lt_one : ∀ i, ratio i < 1
  /-- Each orientation is `1` or `-1`. -/
  sign_eq : ∀ i, sign i = 1 ∨ sign i = -1
  /-- Each similarity maps the unit interval into itself. -/
  mapsTo : ∀ i,
    Set.MapsTo (fun x => sign i * ratio i * x + shift i) (Set.Icc 0 1) (Set.Icc 0 1)

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The similarity attached to a letter, `S_i(x) = ε_i r_i x + b_i`. -/
def map (i : ι) (x : ℝ) : ℝ := S.sign i * S.ratio i * x + S.shift i

/-- An attractor of the system: a non-empty compact subset of `[0,1]` with
`K = ⋃ i S_i K`. -/
def IsAttractor (K : Set ℝ) : Prop :=
  IsCompact K ∧ K.Nonempty ∧ K ⊆ Set.Icc 0 1 ∧ K = ⋃ i, S.map i '' K

/-- A feasible open set for the system, as in `sec:introduction`: a non-empty bounded
open set `U ⊂ ℝ` with `S_i(U) ⊆ U` for every `i` and the images `S_i(U)` pairwise
disjoint.  The set need not be an interval, and the first-level intervals `S_i([0,1])`
may overlap. -/
structure IsFeasible (U : Set ℝ) : Prop where
  /-- The set is open. -/
  isOpen : IsOpen U
  /-- The set is non-empty. -/
  nonempty : U.Nonempty
  /-- The set is bounded. -/
  isBounded : Bornology.IsBounded U
  /-- Each similarity maps the set into itself. -/
  mapsTo : ∀ i, Set.MapsTo (S.map i) U U
  /-- The first-level images are pairwise disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (S.map i '' U) (S.map j '' U)

/-- The open set condition of `sec:introduction`: some feasible open set exists. -/
def OpenSetCondition : Prop := ∃ U : Set ℝ, S.IsFeasible U

/-- The similarity dimension equation `∑ r_i^s = 1`. -/
def IsDimension (s : ℝ) : Prop := ∑ i, S.ratio i ^ s = 1

/-- The natural `s`-dimensional measure of the system: the self-similar probability
measure carried by the attractor, with weights `p_i = r_i^s`. -/
structure IsNatural (K : Set ℝ) (s : ℝ) (μ : Measure ℝ) : Prop where
  /-- It is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- `K` is an attractor of the system. -/
  attractor : S.IsAttractor K
  /-- The measure is carried by the attractor. -/
  support : μ Kᶜ = 0
  /-- Hutchinson's identity with weights `p_i = r_i^s`. -/
  selfSimilar : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i)

/-- The log-ratios `a_i = log(1/r_i)`. -/
noncomputable def logRatio (i : ι) : ℝ := Real.log (S.ratio i)⁻¹

/-- The system is non-lattice: the additive group generated by the log-ratios is
dense in `ℝ`. -/
def NonArithmetic : Prop :=
  Dense ((AddSubgroup.closure (Set.range S.logRatio) : AddSubgroup ℝ) : Set ℝ)

end System

/-! ### Compact Brownian images -/

/-- The Hausdorff space of nonempty compact subsets of the plane. -/
abbrev CompactPlane := NonemptyCompacts Plane

/-- The Borel σ-algebra of the Hausdorff hyperspace. -/
noncomputable instance measurableSpace_nonemptyCompacts_plane :
    MeasurableSpace (NonemptyCompacts Plane) := borel (NonemptyCompacts Plane)

/-- The image `W(K)`, with singleton `{0}` as the value when the path restricted to
`K` is not continuous. Under the Brownian hypothesis this fallback is almost surely
irrelevant. -/
noncomputable def brownianImage (W : ℝ≥0 → Ω → Plane)
    (K : NonemptyCompacts ℝ) (ω : Ω) : NonemptyCompacts Plane :=
  let f := ContinuousMap.mkD (fun t : K ↦ W t.1.toNNReal ω) (ContinuousMap.const K 0)
  (⊤ : NonemptyCompacts K).map f f.continuous

/-- Its law on the Hausdorff hyperspace. -/
noncomputable def brownianImageLaw (W : ℝ≥0 → Ω → Plane) (P : Measure Ω)
    (K : NonemptyCompacts ℝ) : Measure (NonemptyCompacts Plane) :=
  P.map (brownianImage W K)

/-- The cut-off probability `ν_{F,r}` in Section 1, with an irrelevant fallback
when the normalised density is not a probability measure. -/
noncomputable def cutoffProbability (r : ℝ) (F : CompactPlane) : ProbabilityMeasure Plane :=
  open scoped Classical in
  let μ := volume.withDensity (fun x : Plane =>
    ENNReal.ofReal (max (1 - Metric.infDist x F / r) 0))
  let ν := (μ Set.univ)⁻¹ • μ
  if h : IsProbabilityMeasure ν then ⟨ν, h⟩ else default


/-! ### The two-contraction family -/

/-- The natural measure and attractor of the two-contraction family in Section 1. -/
structure IsTwoContractionNatural (s p : ℝ) (K : NonemptyCompacts ℝ)
    (μ : Measure ℝ) : Prop where
  isProbability : IsProbabilityMeasure μ
  unitInterval : (K : Set ℝ) ⊆ Set.Icc 0 1
  invariant : (K : Set ℝ) =
    (fun x => p ^ s⁻¹ * x) '' (K : Set ℝ) ∪
    (fun x => (1 - p) ^ s⁻¹ * x + (1 - (1 - p) ^ s⁻¹)) '' (K : Set ℝ)
  support : μ (K : Set ℝ)ᶜ = 0
  selfSimilar : μ = ENNReal.ofReal p • μ.map (fun x => p ^ s⁻¹ * x) +
    ENNReal.ofReal (1 - p) •
      μ.map (fun x => (1 - p) ^ s⁻¹ * x + (1 - (1 - p) ^ s⁻¹))

/-- The pair `(K_p, μ_p)` specified by its invariance equations. -/
noncomputable def twoContractionData (s p : ℝ) : NonemptyCompacts ℝ × Measure ℝ :=
  Classical.epsilon fun a => IsTwoContractionNatural s p a.1 a.2

/-- The Cesàro mean of the expected Brownian correlation profile. Its existence
on the parameter range is part of `audit_finite_exceptions`. -/
noncomputable def meanProfile (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (s p : ℝ) : ℝ :=
  limUnder atTop (fun R : ℝ => R⁻¹ * ∫ t in (0:ℝ)..R,
    expectedProfile W P s (twoContractionData s p).2 t)

/-- The critical parameters in `(0,1/2)`. -/
noncomputable def meanCriticalSet (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (s : ℝ) : Set ℝ :=
  {p | p ∈ Set.Ioo 0 (1/2) ∧ deriv (meanProfile W P s) p = 0}


/-! ### The headline results, in manuscript order -/

/-- Theorem 1.1 (`thm:main`). Two `s`-Frostman measures whose expected profiles do not
converge to one another have mutually singular Brownian occupation laws on `𝒫(ℝ²)`. The
hypothesis is `eq:profile-separation`, `limsup |H₁ - H₂| > 0`, written out for a
non-negative function; `IsFrostman` carries the paper's standing assumption that the
measures live on `[0,1]`. -/
theorem audit_main {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V,
      ε ≤ |expectedProfile W P s μ₁ t - expectedProfile W P s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  sorry

/-- Theorem 1.2 (`thm:profile-asymptotics`). Under the open set condition, a lattice
system of span `h` has a positive, nonconstant limiting profile of period `h/2`.
A non-lattice system has a positive constant limit. -/
theorem audit_profile_asymptotics {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    (∀ h : ℝ, 0 < h →
      AddSubgroup.closure (Set.range S.logRatio) = AddSubgroup.zmultiples h →
      ∃ Q : ℝ → ℝ, Continuous Q ∧ Function.Periodic Q (h / 2) ∧
        (∀ t, 0 < Q t) ∧ (∃ v w, Q v ≠ Q w) ∧
        Tendsto (fun t => expectedProfile W P s μ t - Q t) atTop (𝓝 0)) ∧
    (S.NonArithmetic → ∃ C : ℝ, 0 < C ∧
      Tendsto (expectedProfile W P s μ) atTop (𝓝 C)) := by
  sorry

/-- Corollary 1.3 (`thm:cantor-application`). Natural measures of a lattice and a
non-lattice IFS of the same dimension have mutually singular Brownian occupation
laws, under the open set condition. -/
theorem audit_lattice_nonlattice_measures {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (S₁ : System ι₁) (S₂ : System ι₂) {K₁ K₂ : Set ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hosc₁ : S₁.OpenSetCondition) (hosc₂ : S₂.OpenSetCondition)
    (hdim₁ : S₁.IsDimension s) (hdim₂ : S₂.IsDimension s)
    (hlat : ∃ h > 0, AddSubgroup.closure (Set.range S₁.logRatio) = AddSubgroup.zmultiples h)
    (hnl : S₂.NonArithmetic) {μ₁ μ₂ : Measure ℝ}
    (hμ₁ : S₁.IsNatural K₁ s μ₁) (hμ₂ : S₂.IsNatural K₂ s μ₂) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := by
  sorry

/-- Theorem 1.4 (`thm:fixed-dimension-separation`). The mean profile exists and has
finite level sets on `(0,1/2]`. Distinct means give mutually singular occupation laws.
Critical parameters do not accumulate in `(0,1/2]`, and the mean is strictly monotone
on every open interval without critical parameters. -/
theorem audit_finite_exceptions {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (∀ p ∈ Set.Ioo (0:ℝ) 1, Tendsto
      (fun R : ℝ => R⁻¹ * ∫ t in (0:ℝ)..R,
        expectedProfile W P s (twoContractionData s p).2 t)
      atTop (𝓝 (meanProfile W P s p))) ∧
    (∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2),
      {p₂ | p₂ ∈ Set.Ioc (0:ℝ) (1/2) ∧
        meanProfile W P s p₂ = meanProfile W P s p₁}.Finite) ∧
    (∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2), ∀ p₂ ∈ Set.Ioc (0:ℝ) (1/2),
      meanProfile W P s p₁ ≠ meanProfile W P s p₂ →
      (occupationLaw W P (twoContractionData s p₁).2).MutuallySingular
        (occupationLaw W P (twoContractionData s p₂).2)) ∧
    (∀ p ∈ Set.Ioc (0:ℝ) (1/2), ¬ AccPt p (𝓟 (meanCriticalSet W P s))) ∧
    (∀ α β : ℝ, Set.Ioo α β ⊆ Set.Ioo 0 (1/2) →
      (∀ q ∈ Set.Ioo α β, deriv (meanProfile W P s) q ≠ 0) →
      StrictMonoOn (meanProfile W P s) (Set.Ioo α β) ∨
        StrictAntiOn (meanProfile W P s) (Set.Ioo α β)) := by
  sorry

/-- Theorem 1.5 (`thm:small-dimension-monotone`). For every sufficiently small
positive dimension, the mean is strictly increasing on `(0,1/2]` and distinct
parameters give mutually singular occupation laws. -/
theorem audit_small_dimension {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) :
    ∃ s₀ ∈ Set.Ioo (0:ℝ) 1, ∀ s ∈ Set.Ioc (0:ℝ) s₀,
      StrictMonoOn (meanProfile W P s) (Set.Ioc 0 (1/2)) ∧
      ∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2), ∀ p₂ ∈ Set.Ioc (0:ℝ) (1/2), p₁ ≠ p₂ →
        (occupationLaw W P (twoContractionData s p₁).2).MutuallySingular
          (occupationLaw W P (twoContractionData s p₂).2) := by
  sorry

/-- Corollary 1.6 (`thm:critical-set-finite`). For `0 < s ≤ 1/2`, the mean is
strictly increasing near zero and has only finitely many critical parameters. -/
theorem audit_finite_critical_set {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/2) :
    (∃ p₀ ∈ Set.Ioo (0:ℝ) (1/2),
      StrictMonoOn (meanProfile W P s) (Set.Ioc 0 p₀)) ∧
    (meanCriticalSet W P s).Finite := by
  sorry

/-- Theorem 1.7 (`thm:minkowski-reconstruction`). Normalised triangular neighbourhood
measures at radii `exp(-n)` converge weakly almost surely to the occupation measure.
Consequently, the occupation measure is a Borel function of the compact Brownian image. -/
theorem audit_reconstruction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {K : NonemptyCompacts ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hosc : S.OpenSetCondition) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural (K : Set ℝ) s μ) :
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => cutoffProbability (Real.exp (-(n:ℝ))) (brownianImage W K ω))
      atTop (𝓝 (occupationProb W μ ω))) ∧
    ∃ reconstruct : CompactPlane → ProbabilityMeasure Plane,
      Measurable reconstruct ∧
      (fun ω => reconstruct (brownianImage W K ω)) =ᵐ[P] occupationProb W μ := by
  sorry

/-- Corollary 1.8 (`thm:cantor-set-application`). Lattice and non-lattice attractors
of the same dimension have mutually singular compact Brownian image laws, under the
open set condition. -/
theorem audit_lattice_nonlattice_sets {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (S₁ : System ι₁) (S₂ : System ι₂) {K₁ K₂ : NonemptyCompacts ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hosc₁ : S₁.OpenSetCondition) (hosc₂ : S₂.OpenSetCondition)
    (hdim₁ : S₁.IsDimension s) (hdim₂ : S₂.IsDimension s)
    (hlat : ∃ h > 0, AddSubgroup.closure (Set.range S₁.logRatio) = AddSubgroup.zmultiples h)
    (hnl : S₂.NonArithmetic) (hK₁ : S₁.IsAttractor (K₁ : Set ℝ))
    (hK₂ : S₂.IsAttractor (K₂ : Set ℝ)) :
    (brownianImageLaw W P K₁).MutuallySingular (brownianImageLaw W P K₂) := by
  sorry

/-- Corollary 1.9. Distinct means give mutually singular compact-image laws, with
finitely many possible exceptions for each parameter. For sufficiently small dimension,
every pair of distinct parameters is separated; the same threshold gives monotonicity. -/
theorem audit_two_contraction_sets {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P) :
    (∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2),
      ∀ p₂ ∈ Set.Ioc (0:ℝ) (1/2), meanProfile W P s p₁ ≠ meanProfile W P s p₂ →
        (brownianImageLaw W P (twoContractionData s p₁).1).MutuallySingular
          (brownianImageLaw W P (twoContractionData s p₂).1)) ∧
    (∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2),
      {p₂ | p₂ ∈ Set.Ioc (0:ℝ) (1/2) ∧
        ¬ (brownianImageLaw W P (twoContractionData s p₁).1).MutuallySingular
          (brownianImageLaw W P (twoContractionData s p₂).1)}.Finite) ∧
    ∃ s₀ ∈ Set.Ioo (0:ℝ) 1, ∀ s ∈ Set.Ioc (0:ℝ) s₀,
      StrictMonoOn (meanProfile W P s) (Set.Ioc 0 (1/2)) ∧
      ∀ p₁ ∈ Set.Ioc (0:ℝ) (1/2), ∀ p₂ ∈ Set.Ioc (0:ℝ) (1/2), p₁ ≠ p₂ →
        (brownianImageLaw W P (twoContractionData s p₁).1).MutuallySingular
          (brownianImageLaw W P (twoContractionData s p₂).1) := by
  sorry

end BrownianImages
