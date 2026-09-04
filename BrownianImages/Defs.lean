/-
`sec:introduction` and `sec:setup` of `BrownianImagesComplete.tex`: the objects the
paper is phrased in, collected so that every later module speaks the same language.

* `Plane`: the plane `ℝ²`, carrying the Euclidean metric.
* `corr`: the correlation functional `C_r(ν)` of `eq:correlation-functional`.
* `IsFrostman`: the Frostman condition `eq:frostman`.
* `Phi`, `pairLaw`: the pair-distance distribution `Φ` of `eq:phi-definition` and the
  law `dΦ` it is the distribution function of.
* `G`: the normalised pair-distance profile of `eq:g-definition`.
* `kern`, `logKern`: the smoothing kernel `φ` of `eq:h-definition` and the function
  `x ↦ e^x φ(e^x)` used after passing to logarithmic coordinates.
* `H`: the expected profile `H_μ` of `eq:expected-profile`, in the integral form
  `eq:h-definition` the proofs use.
* `IsFrostmanOpen`: the same condition in the shape `eq:frostman` writes it, open
  balls centred in `[0,1]`; `Frostman.lean` compares the two.
* `IsAhlfors`, `IsAhlforsClosed`: two-sided regularity on open and on closed balls.
* `IsPlanarBrownian`, `occupation`, `occupationProb`: planar Brownian motion as a pair
  of independent real Brownian motions with continuous paths, the occupation measure
  `ν = W_*μ`, and its reading as a point of `𝒫(ℝ²)`.
* `fourierCoeffP`: the Fourier coefficient of a periodic function, normalised as in
  `sec:smoothing`.
* `overlap`, `jointReturn`, `expCorr`: the overlap length, the joint return
  probability of `sec:variance`, and `S_μ(r) = 𝔼 C_r(ν)`.
* `Yprofile`: the empirical profile `Y_ν` of `sec:concentration`.
* `varScale`: the variance scale `V_s` of `eq:variance-scale`.
* `System`, with `IsAttractor`, `StronglySeparated`, `IsDimension`, `IsNatural`,
  `logRatio`, `NonArithmetic`: self-similar systems on `[0,1]` and their natural
  measures, the objects of `sec:renewal`; the theory lives in `SelfSimilar.lean`.
* `homogeneousSystem`, `homogeneousDim`, `pairSystem`, `pairRatio`: the two systems of
  `thm:cantor-application` and the ratio `c` of `eq:c-definition`.

`Challenge.lean` restates the headline theorems on Mathlib-only copies of these
definitions, and the comparator requires the copies to export identically.  Auxiliary
`_proof` constants are deduplicated per module, so every definition copied there must
be declared in this one module, in the order `Challenge.lean` declares it; that is why
the `System` block sits here rather than in `SelfSimilar.lean`.
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.NumberTheory.Real.Irrational

namespace BrownianImages

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-! ### The plane and the correlation functional -/

/-- The plane `ℝ²`, carrying the Euclidean metric. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `eq:correlation-functional`: the correlation functional
`C_r(ν) = (ν × ν){(x,y) : |x - y| < r}`. -/
noncomputable def corr (ν : Measure Plane) (r : ℝ) : ℝ≥0∞ :=
  (ν.prod ν) {p : Plane × Plane | dist p.1 p.2 < r}

/-- The defining set of `corr` is open, hence measurable. -/
theorem measurableSet_corrSet (r : ℝ) :
    MeasurableSet {p : Plane × Plane | dist p.1 p.2 < r} :=
  (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-! ### Frostman measures and the pair-distance distribution -/

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

/-- `eq:frostman` in the shape the paper writes it: open balls, centres in `[0,1]`.
`IsFrostman` uses closed balls and arbitrary centres, which is what the Fubini step of
`eq:phi-frostman` consumes; `isFrostman_of_open` and `isFrostmanOpen` compare the two,
at the cost of a change of the constant the paper also allows itself. -/
structure IsFrostmanOpen (s A : ℝ) (μ : Measure ℝ) : Prop where
  /-- The constant is at least one. -/
  one_le_const : 1 ≤ A
  /-- The measure sits on the unit interval. -/
  support : μ (Set.Icc (0:ℝ) 1)ᶜ = 0
  /-- The Frostman bound on open balls centred in `[0,1]`, of radius at most one. -/
  measure_ball_le :
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.ball x ρ) ≤ ENNReal.ofReal (A * ρ ^ s)

/-- Two-sided Ahlfors regularity on open balls centred in the support.  Support points
are those charging every ball. -/
def IsAhlfors (s A : ℝ) (μ : Measure ℝ) : Prop :=
  1 ≤ A ∧ ∀ x : ℝ, (∀ ε > 0, μ (Metric.ball x ε) ≠ 0) → ∀ r : ℝ, 0 < r → r ≤ 1 →
    ENNReal.ofReal (A⁻¹ * r ^ s) ≤ μ (Metric.ball x r) ∧
      μ (Metric.ball x r) ≤ ENNReal.ofReal (A * r ^ s)

/-- The same two-sided bound on closed balls; `IsAhlforsClosed.isAhlfors` compares the
two conventions. -/
def IsAhlforsClosed (s A : ℝ) (μ : Measure ℝ) : Prop :=
  1 ≤ A ∧ ∀ x : ℝ, (∀ ε > 0, μ (Metric.ball x ε) ≠ 0) → ∀ r : ℝ, 0 < r → r ≤ 1 →
    ENNReal.ofReal (A⁻¹ * r ^ s) ≤ μ (Metric.closedBall x r) ∧
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (A * r ^ s)

/-- `eq:phi-definition`: the pair-distance distribution `Φ(δ) = P(|X - Y| ≤ δ)` for
independent `X, Y` with law `μ`. -/
noncomputable def Phi (μ : Measure ℝ) (δ : ℝ) : ℝ :=
  ((μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal

/-- The defining set of `Phi` is closed, hence measurable. -/
theorem measurableSet_phiSet (δ : ℝ) :
    MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- The pair-distance law: the law of `|X - Y|` for independent `X, Y ∼ μ`.  It is the
Stieltjes measure `dΦ` of `eq:gaussian-reduction`, and `Φ` of `eq:phi-definition` is its
distribution function. -/
noncomputable def pairLaw (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun p : ℝ × ℝ => |p.1 - p.2|)

/-- `eq:g-definition`: the normalised pair-distance profile `G(w) = e^{sw} Φ(e^{-w})`. -/
noncomputable def G (s : ℝ) (μ : Measure ℝ) (w : ℝ) : ℝ :=
  Real.exp (s * w) * Phi μ (Real.exp (-w))

/-! ### The smoothing kernel and the expected profile -/

/-- `eq:h-definition`: the smoothing kernel `φ(η) = ½ η^{s-2} exp(-1/(2η))`. -/
noncomputable def kern (s η : ℝ) : ℝ :=
  2⁻¹ * η ^ (s - 2) * Real.exp (-(2 * η)⁻¹)

/-- The logarithmic form `e^x φ(e^x) = ½ e^{(s-1)x} exp(-e^{-x}/2)` of the
smoothing kernel, used in the proof of `thm:profile-uniform-continuity`. -/
noncomputable def logKern (s x : ℝ) : ℝ :=
  2⁻¹ * Real.exp ((s - 1) * x) * Real.exp (-(2 * Real.exp x)⁻¹)

/-- `eq:periodic-smoothing`: the Gaussian smoothing operator
`Tg(t) = ∫₀^∞ φ(η) g(2t - log η) dη`. -/
noncomputable def smoothOp (s : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ η in Set.Ioi (0 : ℝ), kern s η * g (2 * t - Real.log η)

/-- `eq:h-definition`: the expected profile `H_μ(t) = ∫₀^∞ φ(η) G(2t - log η) dη`.
`eq:smoothing` identifies it with `eq:expected-profile`. -/
noncomputable def H (s : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ η in Set.Ioi (0 : ℝ), kern s η * G s μ (2 * t - Real.log η)

/-- The expected profile in logarithmic coordinates,
`H_μ(t) = ∫_ℝ e^x φ(e^x) G(2t - x) dx`. -/
noncomputable def Hlog (s : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, logKern s x * G s μ (2 * t - x)

/-! ### Planar Brownian motion and the occupation measure -/

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
origin; `audit_isProbabilityMeasure_occupation` says that event has full probability, so
the choice of fallback never enters a conclusion. -/
noncomputable def occupationProb (W : ℝ≥0 → Ω → Plane) (μ : Measure ℝ) (ω : Ω) :
    ProbabilityMeasure Plane :=
  open scoped Classical in
  if h : IsProbabilityMeasure (occupation W μ ω) then ⟨occupation W μ ω, h⟩
  else ⟨Measure.dirac 0, inferInstance⟩

omit [MeasurableSpace Ω] in
/-- On the event of full mass, `occupationProb` is `occupation`. -/
theorem occupationProb_toMeasure (W : ℝ≥0 → Ω → Plane) (μ : Measure ℝ) {ω : Ω}
    (h : IsProbabilityMeasure (occupation W μ ω)) :
    (occupationProb W μ ω).toMeasure = occupation W μ ω := by
  classical
  rw [occupationProb, dif_pos h]
  rfl

/-- `Law(W_*μ)`, a measure on `𝒫(ℝ²)`. -/
noncomputable def occupationLaw (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (μ : Measure ℝ) :
    Measure (ProbabilityMeasure Plane) :=
  P.map (occupationProb W μ)

/-- `O = |I ∩ I'|`: the length of the overlap of the two unoriented time intervals
with endpoints `{t,u}` and `{t',u'}`. -/
noncomputable def overlap (t u t' u' : ℝ) : ℝ :=
  max 0 (min (max t u) (max t' u') - max (min t u) (min t' u'))

/-- The joint return probability `P(|Z| < r, |Z'| < r)` of `sec:variance`, for the two
Brownian increments over the time pairs `(t,u)` and `(t',u')`.  The times are
non-negative by type, so no clipping is hidden in the statement. -/
noncomputable def jointReturn (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (r : ℝ) (t u t' u' : ℝ≥0) :
    ℝ≥0∞ :=
  P {ω | dist (W u ω) (W t ω) < r ∧ dist (W u' ω) (W t' ω) < r}

/-- `S_μ(r) = 𝔼 C_r(W_*μ)`, the expected correlation integral of `sec:setup`. -/
noncomputable def expCorr (W : ℝ≥0 → Ω → Plane) (P : Measure Ω) (μ : Measure ℝ) (r : ℝ) : ℝ :=
  ∫ ω, (corr (occupation W μ ω) r).toReal ∂P

/-! ### The empirical profile and the variance scale -/

/-- `sec:concentration`: the empirical profile `Y_ν(t) = e^{2st} C_{e^{-t}}(ν)`. -/
noncomputable def Yprofile (s : ℝ) (ν : Measure Plane) (t : ℝ) : ℝ :=
  Real.exp (2 * s * t) * (corr ν (Real.exp (-t))).toReal

/-- The `k`-th Fourier coefficient of a `q`-periodic function, normalised as in the
proof of `thm:smoothing-injective`: `ĝ(k) = q⁻¹ ∫₀^q e^{-2πikx/q} g(x) dx`. -/
noncomputable def fourierCoeffP (q : ℝ) (g : ℝ → ℝ) (k : ℤ) : ℂ :=
  (q : ℂ)⁻¹ *
    ∫ x in (0:ℝ)..q, Complex.exp (-(2 * Real.pi * Complex.I * k * x / q)) * (g x : ℂ)

/-- `eq:variance-scale`: the variance scale `V_s(r)`. -/
noncomputable def varScale (s r : ℝ) : ℝ :=
  if s < 2⁻¹ then r ^ (6 * s)
  else if s = 2⁻¹ then r ^ (3 : ℝ) * (1 + Real.log r⁻¹)
  else r ^ (2 * s + 2)

/-! ### Self-similar systems and their natural measures -/

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
`K = ⋃ i S_i K`.  Hutchinson's existence and uniqueness theorem is the endpoint pair
`audit_exists_cantor_measure` and `audit_exists_pair_measure`. -/
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

end BrownianImages
