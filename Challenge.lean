/-
The headline results `thm:main`, `thm:cantor-application` and
`thm:two-contraction-distinction` of `BrownianImagesComplete.tex`, including the paired
example and its countable exceptional set.
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.NumberTheory.Real.Irrational

namespace BrownianImages

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-! ### Brownian occupation measures and their correlation profiles -/

/-- The plane `ℝ²`, carrying the Euclidean metric. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `eq:correlation-functional`: the correlation functional
`C_r(ν) = (ν × ν){(x,y) : |x - y| < r}`. -/
noncomputable def corr (ν : Measure Plane) (r : ℝ) : ℝ≥0∞ :=
  (ν.prod ν) {p : Plane × Plane | dist p.1 p.2 < r}

/-- `eq:frostman`: `μ` is `s`-Frostman with constant `A`, that is a measure on `[0,1]`
with `μ(B̄(x,ρ)) ≤ A ρ^s` for every `x` and every `0 < ρ ≤ 1`. -/
structure IsFrostman (s A : ℝ) (μ : Measure ℝ) : Prop where
  /-- The constant is at least one. -/
  one_le_const : 1 ≤ A
  /-- The measure sits on the unit interval. -/
  support : μ (Set.Icc (0:ℝ) 1)ᶜ = 0
  /-- The Frostman bound on closed balls of radius at most one. -/
  measure_closedBall_le :
    ∀ x : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ s)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Planar Brownian motion: the two coordinate processes are independent real Brownian
motions with almost surely continuous paths. -/
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

/-- The similarity dimension `log 2 / log (1/λ)` of the homogeneous system. -/
noncomputable def homogeneousDimension (lam : ℝ) : ℝ := Real.log 2 / Real.log lam⁻¹

/-- The contraction ratio `c` of `eq:c-definition`: the solution of `c^s = 1 - 2^{-s}`. -/
noncomputable def pairedRatio (s : ℝ) : ℝ := (1 - (2:ℝ) ^ (-s)) ^ s⁻¹

/-- `sec:introduction`: the homogeneous equal-weight probability measure `μ_A`
on `[0,1]`, invariant under `x ↦ λx` and `x ↦ λx + 1 - λ`. -/
structure IsHomogeneousMeasure (lam : ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The measure is carried by the unit interval. -/
  support : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- The invariance equation with equal weights. -/
  selfSimilar : μ = ENNReal.ofReal (1/2) • μ.map (fun x => lam * x) +
    ENNReal.ofReal (1/2) • μ.map (fun x => lam * x + (1 - lam))

/-- `sec:introduction`: the paired probability measure `μ_B` on `[0,1]`, with
maps `x ↦ x/2`, `x ↦ cx + 1 - c` and weights `2^{-s}`, `c^s`, where `c = pairedRatio s`. -/
structure IsPairMeasure (s : ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The measure is carried by the unit interval. -/
  support : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- The invariance equation with the similarity weights. -/
  selfSimilar : μ = ENNReal.ofReal ((1/2 : ℝ) ^ s) • μ.map (fun x => 1/2 * x) +
    ENNReal.ofReal (pairedRatio s ^ s) • μ.map (fun x => pairedRatio s * x + (1 - pairedRatio s))

/-- `sec:introduction`: the natural probability measure `μ_c` on `[0,1]` of the IFS
`x ↦ x/2`, `x ↦ cx + 1 - c`, with weights `2^{-s}` and `c^s`.  At the dimension `s(c)`,
where `2^{-s(c)} + c^{s(c)} = 1`, these are the `s`th powers of the contraction ratios. -/
structure IsTwoContractionMeasure (c s : ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- The measure is carried by the unit interval. -/
  support : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0
  /-- The invariance equation with the similarity weights. -/
  selfSimilar : μ = ENNReal.ofReal ((1/2 : ℝ) ^ s) • μ.map (fun x => 1/2 * x) +
    ENNReal.ofReal (c ^ s) • μ.map (fun x => c * x + (1 - c))

/-! ### The headline theorems -/

/-- `thm:main`.  Two `s`-Frostman measures whose expected profiles do not converge to
one another have mutually singular Brownian occupation laws, as laws on `𝒫(ℝ²)`.  The
hypothesis is `eq:profile-separation`, `limsup |H₁ - H₂| > 0`, written out for a
non-negative function; `IsFrostman` carries the paper's standing assumption that the
measures live on `[0,1]`. -/
theorem audit_main {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → Plane}
    (hW : IsPlanarBrownian W P) {s A₁ A₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsFrostman s A₁ μ₁) (h₂ : IsFrostman s A₂ μ₂)
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V,
      ε ≤ |expectedProfile W P s μ₁ t - expectedProfile W P s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := sorry

/-- `thm:cantor-application`.  The homogeneous equal-weight measure at any ratio
`0 < λ < 1/2` separates from the natural measure of every non-lattice system of the
same dimension satisfying the open set condition. -/
theorem audit_cantor_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {μA : Measure ℝ} (hA : IsHomogeneousMeasure lam μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ}
    (hosc : S.OpenSetCondition) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDimension lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDimension lam) μ) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) := sorry

/-- The paired instance of `thm:cantor-application`, at a parameter satisfying
`eq:non-lattice`. -/
theorem audit_cantor_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {μA : Measure ℝ} (hA : IsHomogeneousMeasure lam μA)
    {μB : Measure ℝ} (hB : IsPairMeasure (homogeneousDimension lam) μB)
    (hnl : Irrational (Real.log (pairedRatio (homogeneousDimension lam))⁻¹ / Real.log 2)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) := sorry

/-- The exceptional parameters in the last sentence of `thm:cantor-application` form
a countable set. -/
theorem audit_exceptional_parameters_countable :
    {lam : ℝ | 0 < lam ∧ lam < 1/2 ∧
      ¬ Irrational (Real.log (pairedRatio (homogeneousDimension lam))⁻¹ / Real.log 2)}.Countable := sorry

/-- `thm:two-contraction-distinction`.  Along the family `x ↦ x/2`, `x ↦ cx + 1 - c`,
`0 < c < 1/2`, normalise the natural measure `μ_c` at its own dimension `s(c)`, where
`2^{-s(c)} + c^{s(c)} = 1`.  The mean `H̄(c) = lim_{T→∞} T⁻¹ ∫₀ᵀ H_{μ_c}^{s(c)}(t) dt`
exists and is strictly increasing in `c`. -/
theorem audit_two_contraction_distinction {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c₁ c₂ s₁ s₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1/2)
    (hs₁ : (2:ℝ) ^ (-s₁) + c₁ ^ s₁ = 1) (hs₂ : (2:ℝ) ^ (-s₂) + c₂ ^ s₂ = 1)
    {μ₁ μ₂ : Measure ℝ} (h₁ : IsTwoContractionMeasure c₁ s₁ μ₁)
    (h₂ : IsTwoContractionMeasure c₂ s₂ μ₂) :
    ∃ H₁ H₂ : ℝ, H₁ < H₂ ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s₁ μ₁ t)
        atTop (𝓝 H₁) ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0:ℝ)..T, expectedProfile W P s₂ μ₂ t)
        atTop (𝓝 H₂) := sorry

/-- The final assertion of `thm:two-contraction-distinction`: for distinct parameters,
`limsup_{t→∞} |H_{μ_{c₁}}^{s(c₁)}(t) - H_{μ_{c₂}}^{s(c₂)}(t)| > 0`, written out as in
`eq:profile-separation`. -/
theorem audit_two_contraction_separation {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {c₁ c₂ s₁ s₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ < 1/2) (hc₂ : 0 < c₂) (hc₂' : c₂ < 1/2)
    (hne : c₁ ≠ c₂)
    (hs₁ : (2:ℝ) ^ (-s₁) + c₁ ^ s₁ = 1) (hs₂ : (2:ℝ) ^ (-s₂) + c₂ ^ s₂ = 1)
    {μ₁ μ₂ : Measure ℝ} (h₁ : IsTwoContractionMeasure c₁ s₁ μ₁)
    (h₂ : IsTwoContractionMeasure c₂ s₂ μ₂) :
    ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V,
      ε ≤ |expectedProfile W P s₁ μ₁ t - expectedProfile W P s₂ μ₂ t| := sorry

end BrownianImages
