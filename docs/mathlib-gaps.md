# What Mathlib does not have

Each item is a piece of the paper that the library builds itself. Labels such as
`sec:renewal` and `thm:non-lattice-limit` are the labels of the LaTeX source.

- **Iterated function systems and self-similar measures.** Mathlib has no iterated
  function systems, no Hutchinson theorem and no self-similar measures. `System` is a
  finite family of similarities `S_i(x) = ε_i r_i x + b_i` of `[0,1]`, with `ε_i = ±1`
  the orientation and `r_i ∈ (0,1)` the ratio, and `SelfSimilar.lean` carries the
  elementary geometry of an affine map of non-zero slope that every composition of
  similarities uses: images of intervals and balls, preimages of balls, the left
  endpoint `min(f(0), f(1))` of `f([0,1])`.
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
  (`StoppingGeometry`, with the geometric part in `thm:stopping-overlap` and Ahlfors
  regularity cited from Falconer in the paper), and the boundary and cross-piece mass
  estimates through the iterated Hutchinson identity (`CrossPiece`,
  `thm:cross-piece-mass`).
- **Renewal theory.** Mathlib has none. The key renewal theorem is vendored from an
  external Lean project, see [the vendored library](renewal-library.md).
  `thm:non-lattice-limit` goes through it: `KeyRenewalFourier` verifies Feller's
  non-lattice condition from `eq:non-lattice` and the exponential tail of the renewal
  defect `z`, which under the open set condition is the cross-term bound of
  `thm:renewal-recursion`.
- **Time reversal of Brownian motion.** Mathlib's `IsPreBrownianReal` has the shift,
  scaling, negation and time-inversion invariances but no time reversal.
  `reverseReal B b` is `t ↦ B(b - t) - B(b)` up to time `b`, continued past `b` by the
  increments after `b`, and `IsPreBrownianReal.reverse` proves it pre-Brownian through
  `IsGaussianProcess.isPreBrownianReal_of_covariance`: every value is a linear
  combination of four values of `B`, the process is centred, and its covariance is
  `min s t` in each of the three orderings of `s`, `t` and `b`. `IsBrownianReal.reverse`
  adds the continuity of the paths and `IsPlanarBrownian.timeReversal` is the planar
  version. `brownianImage_reflectCompact_of_continuous` reads the Brownian image of the
  reflected time set `1 - K` as the translate by `W(1)` of the image of `K` under the
  reversed motion, which is the time reversal of the increments that `sec:reconstruction`
  invokes for an orientation-reversing similarity.
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
- **The lattice correlation-profile limit.** `LatticeProfile.lean` reuses the
  finite-delay renewal theorem from `Minkowski/TubeDiscreteRenewal.lean` for the
  general lattice branch of `thm:profile-asymptotics`. Applying it to
  `A + 1 - G(2v)` puts the defect in the required sign convention. Uniform phase
  convergence gives a continuous periodic limit for `G`, the lower regularity
  estimate makes it positive, and dominated convergence transfers the vanishing
  error through Gaussian smoothing. The period for `H_μ^s` is half the span of the
  logarithmic contraction ratios.
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
- **Cesàro means and the renewal equation.** Mathlib has Cesàro means of sequences but
  none of functions on the line. `TwoContraction.Cesaro` proves that a convergent function
  has convergent averages (`tendsto_avg_of_tendsto`), and the renewal average
  `tendsto_avg_of_renewal`: for a bounded continuous `g` with integrable renewal defect
  `z = g - ∑ p_i g(· - a_i)`, `T⁻¹ ∫₀ᵀ g → (∫ z)/m`, with no lattice or non-lattice
  hypothesis.  Integrating the defect over `(-∞, T]` and averaging once more is the whole
  proof.  With a character `e^{-iξw}` that is trivial on the delays, the same lemma gives
  the Fourier coefficients of the lattice limit (`TwoContraction.Periodic`), and
  `tendsto_avg_of_periodic` is the periodic case.
- **Bernoulli codings with general weights.** Mathlib has `Measure.infinitePi` but no
  splitting off of the first coordinate; `infinitePi_eq_sum_map_cons` proves it for any
  probability measure on a finite alphabet, generalising the library's natural-weight
  version, and `integral_infinitePi_cons` is its integral form.  The monotone coupling of
  two Bernoulli measures through a three-letter alphabet (`triBern`, `lowWord`,
  `highWord`) is built from `Measure.infinitePi_map_pi`.
- **Inequalities for `Γ` and `ψ`.** Mathlib has the digamma function but not its series
  `ψ(1 + z) = -γ + ∑ z/(n(n + z))`, and no bound on `|Γ|` off the real axis.  `TwoContraction.Digamma` derives
  `-ψ(1-s) ≥ γ + s/(1-s) + s(π²/6 - 1)` from the convexity of `log Γ`
  (`Real.convexOn_log_Gamma`): the functional equation gives
  `ψ(x) = ψ(x+N) - ∑_{k<N} 1/(x+k)`, convexity gives `ψ(y) ≤ log y`, and Mathlib's limits
  `H_N - log(N+1) → γ` and `∑ 1/n² = π²/6` finish.  `norm_Gamma_le` is `|Γ(z)| ≤ Γ(Re z)`,
  from the Euler integral.
- **Chebyshev's integral inequality.** `integral_mul_le_of_similar`: two similarly
  ordered bounded measurable functions are non-negatively correlated, through the double
  integral of `(f(a) - f(b))(g(a) - g(b))`.
- **Fourier inversion on the line.** Mathlib's `has_pointwise_sum_fourier_series_of_summable`
  lives on `AddCircle`; `hasSum_fourierCoeffP` transports it to continuous periodic
  functions on the line with summable coefficients, through the same lift as the
  uniqueness theorem.
- **Local to global monotonicity.** `strictMonoOn_of_local`: a function that is locally
  strictly increasing on both sides at every point of an open interval is strictly
  increasing, with no continuity hypothesis.  It is what lets
  `thm:two-contraction-distinction` use one-sided finite differences of the moment `M(s)`
  in place of its derivative.
