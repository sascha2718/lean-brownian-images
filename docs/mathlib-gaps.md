# What Mathlib does not have

Each item is a piece of the paper that the library builds itself. Labels such as
`sec:renewal` and `thm:non-lattice-limit` are the labels of the LaTeX source.

- **Iterated function systems and self-similar measures.** Mathlib has no iterated
  function systems, no Hutchinson theorem and no self-similar measures.
  `System.IsNatural` takes Hutchinson's identity `μ = ∑ r_i^s (S_i)_*μ` as the
  definition, together with an attractor `K` carrying the measure, and
  `System.exists_unique_isNatural` is Hutchinson's theorem for it: the pair `(K, μ)`
  exists and is unique. `Hutchinson.lean` builds it off the code space `ℕ → ι`, not off
  a metric on measures, since Mathlib carries no completeness for Lévy-Prokhorov: the
  attractor is the range of the coding map, the measure is the pushforward of the
  Bernoulli law with weights `r_i^s`, and uniqueness of the measure needs only uniform
  continuity, through the adjoint `T f = ∑ p_i f ∘ S_i` on `ℝ →ᵇ ℝ` and Heine-Cantor on
  `[0,1]`. Strong separation is a condition on the pieces `S_i K` of the attractor, as
  in `sec:renewal`, not on the first-level intervals `S_i([0,1])`, which would be
  strictly stronger; `homSystem_stronglySeparated` derives the attractor version from
  the interval version for the homometric systems.
- **The open set condition.** Mathlib has no open set condition and no Schief theorem.
  `System.IsFeasible`, `System.OpenSetCondition` and `System.StrongOpenSetCondition`
  are the paper's definitions, and `Schief.lean` proves Schief's theorem, that the open
  set condition yields a feasible open set meeting the attractor, in the form Käenmäki
  and Vilppolainen give it: words are lists, the neighbours of a word are the stopping
  words at its scale within three lengths of its interval, a word `h` with the most
  neighbours has `N(ih) = i N(h)` for every prefix `i`, and the union of the balls
  `S_w(B(x, r_h))` around the images of a point `x ∈ S_h K` is the feasible set. The
  library's own proofs take the strong form as their hypothesis and the endpoints derive
  it. What the library builds on top of a feasible open set is `sec:renewal` under the
  open set condition: the stopping family below a node, its multiplicity bound and its partition
  into `M` families with disjoint interiors, through the greedy interval colouring of
  `IntervalColoring`, the Ahlfors regularity of the natural measure at every centre
  (`StoppingGeometry`, `thm:stopping-overlap`), and the boundary and cross-piece mass
  estimates through the iterated Hutchinson identity (`CrossPiece`,
  `thm:cross-piece-mass`).
- **Renewal theory.** Mathlib has none. The key renewal theorem is vendored from an
  external Lean project, see [the vendored library](renewal-library.md).
  `thm:non-lattice-limit` goes through it: `KeyRenewalFourier` verifies Feller's
  non-lattice condition from `eq:non-lattice` and the exponential tail of the renewal
  defect `z`, which under the open set condition is the cross-term bound of
  `thm:renewal-recursion`.
- **The planar return probability.** `IsPlanarBrownian.return_prob` proves
  `P(|W_u - W_t| < r) = 1 - exp(-r²/(2|u-t|))`. Mathlib has no chi-squared distribution
  and no result on the squared norm of a Gaussian vector, so the proof goes through polar
  coordinates: `lintegral_comp_polarCoord_symm`, `prod_withDensity`, Tonelli and the
  fundamental theorem of calculus.
- **Joint measurability of the process.** Mathlib's `IsPreBrownianReal` gives only
  `AEMeasurable (B t) P` at a fixed time, so `W` itself is not jointly measurable. What
  is available is a modification: `IsPlanarBrownian.exists_jointlyMeasurable` and
  `Reduction.exists_modification` produce a `V` with every path continuous, every `V t`
  measurable, and `V = W` off one measurable null set; joint measurability is then
  `measurable_uncurry_of_continuous_of_measurable`. The statements expose the null set,
  since transporting a fixed-time identity such as `return_prob` across it needs
  `measure_congr` on a set that is only outer measurable.
  `audit_aemeasurable_occupation`, `audit_gaussian_reduction` and the variance expansion
  of `audit_variance` rest on this.
- **The Gamma multiplier.** `eq:gamma-multiplier` goes through Mathlib's Mellin
  transform (`mellin_comp_mul_left`, `mellin_comp_inv`,
  `Complex.GammaIntegral_eq_mellin`) rather than a hand-rolled change of variables; the
  paper's substitution `x = 1/(2η)` is exactly that composite, and no integrability side
  condition arises because each step is an unconditional identity.
- **Fourier uniqueness on the line.** Mathlib has no uniqueness theorem for Fourier
  coefficients of periodic functions on the line, but it has `fourierBasis`, a Hilbert
  basis of `L²(AddCircle T)`. `eq_zero_of_fourierCoeffP_eq_zero` builds the bridge: lift
  `g` to `AddCircle q` by `Function.Periodic.lift`, match the coefficients through
  `fourierCoeff_eq_intervalIntegral`, apply the injectivity of `fourierBasis.repr`, and
  come back from almost-everywhere-zero by continuity.
- **The dense-or-cyclic dichotomy.** Mathlib's `AddSubgroup.dense_or_cyclic` and
  `AddSubgroup.mem_closure_singleton` are the raw material; `pairSystem_nonArithmetic_iff`
  turns them into "the group generated by `log 2` and `log(1/c)` is dense iff their ratio
  is irrational", which makes `eq:non-lattice` exactly the hypothesis of
  `thm:non-lattice-limit`.
- **The Borel σ-algebra of the weak topology on `𝒫(ℝ²)`.** Mathlib has neither a
  `BorelSpace (ProbabilityMeasure Ω)` instance nor a `borel (ProbabilityMeasure Ω) = _`
  lemma. `borel_probabilityMeasure_eq_giry` identifies the weak Borel σ-algebra with the
  Giry one, needing only second countability, pseudo metrisability and `BorelSpace`, so
  nothing in it is special to `ℝ²`.
- **Minkowski reconstruction.** Compact Brownian images are measurable in the Hausdorff
  hyperspace; their affine cylinder laws and finite-family independence, the cut-off,
  union, scaling, defect, localization, finite-cylinder and translation-overlap algebra,
  the Brownian stopping-cover moments, the Gaussian-gap overlaps of the stopping
  cylinders at temporal scale `r²`, the telescoping of the multiple-counting defect over
  the stopping tree, the class-wise independence behind the variance of `Y_{r,u}`, and
  fixed-generation almost-sure quotient limits are all built in
  `BrownianImages/Minkowski/`. Mathlib has no
  continuous-time Brownian maximal-moment theorem; `Minkowski.BrownianMaximalReduction`
  and `Minkowski.BrownianMaximalMoment` supply the unit-interval radius moments from
  discrete martingale maximal estimates and Brownian scaling.
