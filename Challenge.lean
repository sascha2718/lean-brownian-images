/-
Comparator challenge file: the headline theorems of `BrownianImagesComplete.tex`,
`thm:main` and `thm:cantor-application`, restated with `sorry` in place of their
proofs, together with the definitions their statements need and nothing else.  The
file imports only Mathlib, so the audit trusts this file and Mathlib alone.

The definitions are copies of the library's own.  Comparator compares the transitive
closure of every constant a statement uses between this file and `Solution.lean`,
whose closure contains the library originals, so any drift between a copy here and
the library fails the audit.

Comparator compares these statements against the identically named declarations of
`Solution.lean`, audits the axioms of the solution proofs, and replays them through
the kernel.  The statement text must stay character-for-character identical to
`Solution.lean`.  Comparator never compares against the tex: the correspondence with
the document is a human obligation, and `PLAN.md` is where it is argued.

Run from `lean/` with
`lake env <comparator binary> comparator-config.json`.
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.NumberTheory.Real.Irrational

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ### The objects of `thm:main`, copied from `BrownianImages.Defs` -/

/-- The plane `ℝ²`, carrying the Euclidean metric. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `eq:frostman`: `μ` is `s`-Frostman with constant `A`, that is a measure on `[0,1]`
with `μ(B(x,ρ)) ≤ A ρ^s` for every `x` and every `0 < ρ ≤ 1`.  The paper states the
condition for measures on `[0,1]` throughout, and the support condition is part of the
definition: every consumer of `IsFrostman` needs it. -/
structure IsFrostman (s A : ℝ) (μ : Measure ℝ) : Prop where
  /-- The constant is at least one. -/
  one_le_const : 1 ≤ A
  /-- The measure sits on the unit interval. -/
  support : μ (Set.Icc (0:ℝ) 1)ᶜ = 0
  /-- The Frostman bound on closed balls of radius at most one. -/
  measure_closedBall_le :
    ∀ x : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ s)

/-- `eq:phi-definition`: the pair-distance distribution `Φ(δ) = P(|X - Y| ≤ δ)` for
independent `X, Y` with law `μ`. -/
noncomputable def Phi (μ : Measure ℝ) (δ : ℝ) : ℝ :=
  ((μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal

/-- `eq:g-definition`: the normalised pair-distance profile `G(w) = e^{sw} Φ(e^{-w})`. -/
noncomputable def G (s : ℝ) (μ : Measure ℝ) (w : ℝ) : ℝ :=
  Real.exp (s * w) * Phi μ (Real.exp (-w))

/-- `eq:h-definition`: the smoothing kernel `φ(η) = ½ η^{s-2} exp(-1/(2η))`. -/
noncomputable def kern (s η : ℝ) : ℝ :=
  2⁻¹ * η ^ (s - 2) * Real.exp (-(2 * η)⁻¹)

/-- `eq:h-definition`: the expected profile `H_μ(t) = ∫₀^∞ φ(η) G(2t - log η) dη`.
`eq:smoothing` identifies it with `eq:expected-profile`. -/
noncomputable def H (s : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ η in Set.Ioi (0 : ℝ), kern s η * G s μ (2 * t - Real.log η)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Planar Brownian motion: the two coordinate processes are independent real Brownian
motions.  `IsBrownianReal`, rather than `IsPreBrownianReal`, is what the paper means by
standard Brownian motion: it carries almost surely continuous paths, and without them
`t ↦ W t ω` need not be measurable and the occupation measure below degenerates. -/
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

/-- The occupation measure read as a point of `𝒫(ℝ²)`, the space the paper takes laws
on.  Off the event where the total mass is one the value is the Dirac mass at the
origin; `audit_isProbabilityMeasure_occupation` in `Solution.lean` says that event has
full probability, so the choice of fallback never enters a conclusion. -/
noncomputable def occupationProb (W : ℝ≥0 → Ω → Plane) (μ : Measure ℝ) (ω : Ω) :
    ProbabilityMeasure Plane :=
  open scoped Classical in
  if h : IsProbabilityMeasure (occupation W μ ω) then ⟨occupation W μ ω, h⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- `Law(W_*μ)`, a measure on `𝒫(ℝ²)`. -/
noncomputable def occupationLaw (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (μ : Measure ℝ) :
    Measure (ProbabilityMeasure Plane) :=
  P.map (occupationProb W μ)

/-! ### The objects of `thm:cantor-application`, copied from
`BrownianImages.SelfSimilar` -/

/-- A self-similar system on `[0,1]`: finitely many similarities
`S_i(x) = r_i x + b_i` with ratios in `(0,1)`, each mapping `[0,1]` into itself. -/
structure System (ι : Type*) [Fintype ι] where
  /-- The contraction ratios. -/
  ratio : ι → ℝ
  /-- The translation parts. -/
  shift : ι → ℝ
  /-- Each ratio is positive. -/
  ratio_pos : ∀ i, 0 < ratio i
  /-- Each ratio is a contraction. -/
  ratio_lt_one : ∀ i, ratio i < 1
  /-- Each similarity maps the unit interval into itself. -/
  mapsTo : ∀ i, Set.MapsTo (fun x => ratio i * x + shift i) (Set.Icc 0 1) (Set.Icc 0 1)

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The similarity attached to a letter, `S_i(x) = r_i x + b_i`. -/
def map (i : ι) (x : ℝ) : ℝ := S.ratio i * x + S.shift i

/-- An attractor of the system: a non-empty compact subset of `[0,1]` with
`K = ⋃ i S_i K`.  Hutchinson's existence and uniqueness theorem is
`audit_exists_cantor_measure` and `audit_exists_pair_measure` in `Solution.lean`. -/
def IsAttractor (K : Set ℝ) : Prop :=
  IsCompact K ∧ K.Nonempty ∧ K ⊆ Set.Icc 0 1 ∧ K = ⋃ i, S.map i '' K

/-- Strong separation with gap `ρ`: the pieces `S_i K` and `S_j K` of the attractor stay
`ρ` apart for `i ≠ j`.  This is the constant `ρ = min_{i≠j} dist(S_iK, S_jK)` of
`sec:renewal`: a condition on the pieces of the attractor, not on the first-level
intervals `S_i([0,1])`, which would be strictly stronger. -/
def StronglySeparated (K : Set ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ i j, i ≠ j → ∀ x ∈ K, ∀ y ∈ K, ρ ≤ |S.map i x - S.map j y|

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

/-- The log-ratios `a_i = log(1/r_i)`, the atoms of the renewal measure `ϑ`. -/
noncomputable def logRatio (i : ι) : ℝ := Real.log (S.ratio i)⁻¹

/-- The system is non-arithmetic: the additive group generated by the log-ratios is
dense in `ℝ`.  This is the hypothesis of `thm:non-lattice-limit`. -/
def NonArithmetic : Prop :=
  Dense ((AddSubgroup.closure (Set.range S.logRatio) : AddSubgroup ℝ) : Set ℝ)

end System

/-- The homogeneous two-map system
`S^A_0(x) = λx`, `S^A_1(x) = λx + 1 - λ` of `μ_A`, for `0 < λ < 1/2`. -/
noncomputable def homogeneousSystem (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    System (Fin 2) where
  ratio _ := lam
  shift i := if i = 0 then 0 else 1 - lam
  ratio_pos _ := hlam0
  ratio_lt_one _ := by linarith
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    fin_cases i <;> constructor <;> simp <;> nlinarith

/-- The similarity dimension `log 2 / log (1/λ)` of the homogeneous system. -/
noncomputable def homogeneousDim (lam : ℝ) : ℝ := Real.log 2 / Real.log lam⁻¹

/-- The system `S^B_0(x) = x/2`, `S^B_1(x) = cx + 1 - c` of `μ_B`, at a ratio
`0 < c < 1/2`. -/
noncomputable def pairSystem (c : ℝ) (hc0 : 0 < c) (hc : c < 1/2) : System (Fin 2) where
  ratio i := if i = 0 then 1/2 else c
  shift i := if i = 0 then 0 else 1 - c
  ratio_pos i := by
    fin_cases i
    · norm_num
    · simpa using hc0
  ratio_lt_one i := by
    fin_cases i
    · norm_num
    · simpa using by linarith
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    fin_cases i <;> constructor <;> simp <;> nlinarith

/-- The contraction ratio `c` of `eq:c-definition`: the solution of `c^s = 1 - 2^{-s}`. -/
noncomputable def pairRatio (s : ℝ) : ℝ := (1 - (2:ℝ) ^ (-s)) ^ s⁻¹

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
    (hsep : ∃ ε > 0, ∀ V : ℝ, ∃ t ≥ V, ε ≤ |H s μ₁ t - H s μ₂ t|) :
    (occupationLaw W P μ₁).MutuallySingular (occupationLaw W P μ₂) := sorry

/-- `thm:cantor-application`.  The homogeneous equal-weight measure at any ratio
`0 < λ < 1/2` separates from the natural measure of every strongly separated
non-arithmetic system of the same dimension. -/
theorem audit_cantor_application {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι) {K : Set ℝ} {ρ : ℝ}
    (hsep : S.StronglySeparated K ρ) (hna : S.NonArithmetic)
    (hdim : S.IsDimension (homogeneousDim lam)) {μ : Measure ℝ}
    (hμ : S.IsNatural K (homogeneousDim lam) μ) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μ) := sorry

/-- The paired instance of `thm:cantor-application`, the last sentence of the theorem,
at a parameter satisfying `eq:non-lattice`.  The ratio bounds `0 < c < 1/2` of
`eq:c-definition` enter as hypotheses. -/
theorem audit_cantor_application_pair {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → Plane} (hW : IsPlanarBrownian W P)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    {KA : Set ℝ} {μA : Measure ℝ}
    (hA : (homogeneousSystem lam hlam0 hlam).IsNatural KA (homogeneousDim lam) μA)
    (hc0 : 0 < pairRatio (homogeneousDim lam))
    (hc : pairRatio (homogeneousDim lam) < 1/2)
    {KB : Set ℝ} {μB : Measure ℝ}
    (hB : (pairSystem (pairRatio (homogeneousDim lam)) hc0 hc).IsNatural
      KB (homogeneousDim lam) μB)
    (hnl : Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)) :
    (occupationLaw W P μA).MutuallySingular (occupationLaw W P μB) := sorry

/-- The exceptional parameters in the last sentence of `thm:cantor-application` form
a countable set. -/
theorem audit_exceptional_parameters_countable :
    {lam : ℝ | 0 < lam ∧ lam < 1/2 ∧
      ¬ Irrational (Real.log (pairRatio (homogeneousDim lam))⁻¹ / Real.log 2)}.Countable := sorry

end BrownianImages
