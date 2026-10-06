/-
A Lean formalisation of "Pair-distance profiles and Minkowski reconstruction of planar
Brownian images" (`BrownianImagesComplete.tex`).

The library is organised along the paper.  `Solution.lean` carries the formal statement
of every numbered result of the document, and `Challenge.lean` restates the headline
theorems for the comparator audit; the modules below carry what is proved.  `README.md`
gives the build and audit instructions, and `docs/` the correspondence with the paper.

The objects, and `sec:setup`:

* `Defs`: the objects the paper is phrased in, from `eq:correlation-functional` to
  `eq:variance-scale`, together with self-similar systems, orientation-preserving or
  orientation-reversing, their natural measures, and the two systems of the
  application, placed here so `Challenge.lean` can copy them from one module.
* `Occupation`: the occupation measure as a random point of `𝒫(ℝ²)`, and the almost
  sure facts that make it one.
* `Empirical`: the empirical profile `Y_ν` of `sec:concentration` and the grid monotonicity
  `eq:monotone-fill`.
* `Frostman`: the Frostman condition, the two ball conventions, atomlessness, and the
  pair-distance bound `eq:phi-frostman`.
* `Kernel`: the smoothing kernel `φ` of `eq:h-definition`, its logarithmic form, and
  the two-sided domination that puts it in `L¹(ℝ)`.
* `WeakBorel`: the Borel σ-algebra of the weak topology on `𝒫(ℝ²)` is the Giry one.
* `Profile`: elementary bounds on `G`, and its measurability without regularity.
* `JointMeasurability`: joint measurability of the process, and the measurability of
  the occupation law that follows from it.
* `Reduction`: `thm:gaussian-reduction`, the Fubini interchange and the Gaussian
  transform of the pair-distance law.
* `Rescaling`: `eq:smoothing`, the layer cake identity and the substitution `δ = r²η`,
  and the correlation-integral consequences of the paired profile asymptotics.
* `UniformContinuity`: `thm:profile-uniform-continuity`, on the substitution `η = e^x`
  and the `L¹` continuity of translation for the kernel.

`sec:renewal`:

* `SelfSimilar`: the elementary geometry of an affine map of the line with non-zero
  slope, the orientation and the first-level interval of a similarity, strongly
  separated self-similar systems, the dimensions and gaps of the two named systems, the
  ratio `c` of `eq:c-definition`, and the renewal data of `thm:non-lattice-limit`.
* `Hutchinson`: the coding map on `ℕ → ι`, Hutchinson's theorem for a general system,
  and the two natural measures of `sec:renewal`.
* `AhlforsRegular`: Ahlfors regularity of the natural measure of a strongly separated
  system, and the cylinder-mass identities behind it.
* `OpenSet`: the geometry of a feasible open set, and the passage from strong
  separation to the strong open set condition.
* `Schief`: Schief's theorem, cited in `sec:introduction`: the open set condition gives
  a feasible open set meeting the attractor, through the word with the most neighbours
  at its own scale.
* `IntervalColoring`: intervals of bounded multiplicity are coloured with that many
  colours so that intervals of one colour have disjoint interiors.
* `StoppingGeometry`: `thm:stopping-overlap`, the stopping words below a node, the
  multiplicity bound and the partition into `M` families. It also proves the classical
  Ahlfors regularity under the open set condition, cited from Falconer in the paper.
* `CrossPiece`: `thm:cross-piece-mass`, the boundary mass and the cross-piece mass
  estimates, and the bound on the cross term of `thm:renewal-recursion`.
* `Periodic`: the continuous periodic extension `G̃_A`, through `AddCircle`.
* `Recursion`: `thm:renewal-recursion`, the self-similar recursion of `Φ` and of `G`
  with its cross term, and the vanishing of the cross term under strong separation.
* `PairDifference`: the difference mass `(μ × μ){x - y ∈ T}` and its Fubini form.
* `HomogeneousNonconstancy`: `thm:homogeneous-nonconstancy` for every `0 < λ < 1/2`.
* `ExceptionalParameters`: the countable exceptional set of `thm:cantor-application`.
* `Renewal`: the key renewal theorem, vendored from Benny Avelin's `AbsorptionCutoff`
  under the Apache License 2.0; see `BrownianImages/Renewal.lean` for provenance.
* `RenewalBridge`: the hypotheses of that theorem that are properties of the renewal
  measure `ϑ = ∑ p_i δ_{a_i}` alone, and the refutation of its upstream `Nonlattice`
  hypothesis for `ϑ`.
* `KeyRenewalFourier`: `thm:non-lattice-limit`: the renewal defect `z = G - F*G`, its
  exponential tail from `thm:cross-piece-mass`, and Feller's non-lattice condition
  `FellerNonlattice`, which `eq:non-lattice` supplies, fed to the vendored key renewal
  theorem.

`sec:smoothing`:

* `Multiplier`: the Fourier multipliers `eq:gamma-multiplier` and their non-vanishing,
  the engine of `thm:smoothing-injective`.
* `FourierMultiplier`: `eq:fourier-multiplier` and, with it, `thm:smoothing-injective`
  unconditionally.
* `Smoothing`: the extrema of a continuous periodic function, the continuity and
  linearity of the smoothing operator, the strict positivity of `Φ`, the oscillation
  `d_A`, and `thm:smoothing-injective` reduced to the two multiplier facts.
* `Asymptotics`: the smoothing limit and the homogeneous bound `eq:ha-asymptotic`.
* `LatticeProfile`: the general lattice branch of `thm:profile-asymptotics`, via
  finite-delay renewal and smoothing of the vanishing error.
* `ProfileAsymptotics`: the `μ_B` consequence of `eq:hb-asymptotic` with its
  constant named.

`sec:variance`:

* `FourPoint`: the covariance determinants of the two overlapping pairings,
  `eq:crossing-determinant` and `eq:nested-determinant`, with their dyadic block bounds.
* `GaussianFourPoint`: the mass half of `thm:endpoint-block-mass`, the independence of
  disjoint planar increments, and the planar return probability of
  `eq:gaussian-reduction`.
* `FourPointBound`: `eq:joint-return-bound`, through the regression decomposition of the
  second increment and the disc bound for a planar Gaussian.
* `BlockMass`: `thm:endpoint-block-mass`, both halves, on the two overlapping pairings.
* `FourPointIntegral`: `thm:four-point-integral`, the dyadic summation and the
  permutation invariance of `μ⁴`, and `thm:variance` on the block bound.
* `VarianceCovariance`: the variance expansion of `thm:variance`, the second moment of
  the correlation functional as a `μ⁴`-mass, and the covariance killed off the overlap
  set.

`sec:concentration`:

* `Concentration`: `sec:concentration`, from `eq:y-variance` through
  `thm:uniform-concentration`.
* `MainTheorem`: `thm:main`, the end of `sec:concentration`.
* `Separation`, `CantorApplication`: the conditional forms of
  `thm:non-lattice-separation` and `thm:cantor-application`.
* `NonLattice`: those two, `eq:gb-limit` and the paired profile asymptotics, discharged
  through `thm:non-lattice-limit`.
* `Endpoints`: the results that no single module proves, each a composition of two or
  more of the modules above in the shape `Challenge.lean` states it.

`sec:reconstruction`, in `Minkowski/`:

* `CompactImage`: compact Brownian images as measurable random variables in the
  Hausdorff hyperspace, and the law of the compact image.
* `Minkowski.System`: the attractor and its pieces as points of the hyperspace, and
  the parameters `β_i`, `p_i`, `α` of the tube analysis.
* `Minkowski.Tube`, `Minkowski.TubeAlgebra`, `Minkowski.Profile`: the smoothed tube
  probability, its continuity, and the deterministic union, scaling, and overlap
  algebra.
* `Minkowski.CorrelationLower`: the ball-mass/Fubini argument bounding tube area below
  in terms of the correlation integral.
* `Minkowski.BrownianScaling`, `Minkowski.BrownianPieces`,
  `Minkowski.BrownianCompactPieces`: Brownian rescaling and time reversal, the law and
  independence of compact images of disjoint time pieces, in the arbitrary
  compact-cylinder form, and the oriented copies `orientCompact` through which an
  orientation-reversing similarity enters Brownian scaling by time reversal of the
  increments.
* `Minkowski.Localization`, `Minkowski.Cylinder`, `Minkowski.CylinderConvergence`:
  bounded-Lipschitz localization, the finite-cylinder approximation estimates, and the
  passage from cylinder ratios to weak convergence.
* `Minkowski.OverlapTranslation`, `Minkowski.GaussianIncrement`,
  `Minkowski.OverlapProbability`, `Minkowski.BrownianOverlapGeometry`: the
  convolution/Fubini identity behind the Gaussian-gap overlap estimate for two time
  intervals, the planar Gaussian density of an increment and its uniform bound, the
  probabilistic form of the overlap identity, and the centring that matches it to
  actual Brownian cylinders.
* `Minkowski.DefectExpectation`, `Minkowski.StoppingOverlap`: pairwise overlap
  integrability and the passage to the defect, and `thm:neighbourhood-overlap` under
  the strong open set condition, through the stopping cylinders at temporal scale
  `r²` and `eq:stopping-close-pairs`.
* `Minkowski.TubeUpper`, `Minkowski.TubeMeanLower`, `Minkowski.TubeMeanContinuity`:
  the deterministic disc-cover half of `thm:neighbourhood-moments`, its lower-bound
  half, and the continuity of the mean tube profile.
* `Minkowski.BrownianMaximalReduction`, `Minkowski.BrownianMaximalMoment`,
  `Minkowski.Stopping`, `Minkowski.StoppingTubeUpper`, `Minkowski.TubeMomentAssembly`:
  the Brownian scaling reduction, every Brownian maximal moment, stopping-antichain
  covers, and all tube moments with the positive lower mean, `thm:neighbourhood-moments`.
* `Minkowski.TubeRenewal`, `Minkowski.TubeRenewalLimit`,
  `Minkowski.TubeRenewalAssembly`, `Minkowski.TubeArithmeticRenewal`,
  `Minkowski.TubeDiscreteRenewal`: the exact mean renewal recurrence, the non-arithmetic
  limit by the key renewal theorem, its assembly, and the arithmetic periodic limit by
  finite-delay renewal convergence, `thm:neighbourhood-renewal`.
* `Minkowski.L2Recurrence`, `Minkowski.DefectL2`, `Minkowski.ProfileL2`,
  `Minkowski.AlmostSure`, `Minkowski.StoppingConcentration`,
  `Minkowski.TubeEndpointAssembly`: the centred `L²` norm and its square-sum bound
  for independent summands, the first/third moment interpolation, the uniform `L²`
  bound of the profile, Borel--Cantelli along a fixed phase, and
  `thm:neighbourhood-concentration` through the stopping tree, with the unconditional
  endpoint forms.
* `Minkowski.Ratio`: the scalar passage from profile convergence and a positive renewal
  mean to the limiting cylinder-mass ratios.
* `Minkowski.Limit`, `Minkowski.LimitClassifier`, `Minkowski.TubeConvergence`:
  measurable weak limits of the tube sequence and Borel classifiers read directly from
  that sequence.
* `Minkowski.Reconstruction`: the passage from pathwise tube reconstruction to Borel
  recovery of the occupation measure and to mutual singularity of the compact-image laws.
* `Minkowski.Generation`, `Minkowski.GenerationScaling`, `Minkowski.GenerationRatio`:
  finite self-similar generations, their exact Brownian tube scaling, and the
  almost-sure fixed-generation quotient argument.
* `Minkowski.ReconstructionAssembly`, `Minkowski.HomogeneousReconstruction`,
  `Minkowski.FullEndpointAssembly`, `Minkowski.CantorSetApplication`: reconstruction
  in both renewal regimes, direct homogeneous reconstruction from the one-delay
  recurrence, `thm:minkowski-reconstruction`, and `thm:cantor-set-application` with its
  paired instance.

`sec:base-five`:

* `BaseFive`: `thm:base-five-profiles`, the two base-five systems, the recursions
  `eq:base-five-recursion`, the values `eq:base-five-distances`, and the separation of
  the expected profiles through the continuous periodic limits of the two profiles.
* `Minkowski.BaseFiveApplication`: the two displays after `thm:base-five-profiles`, the
  mutual singularity of the occupation laws and of the compact-image laws.

`sec:obstruction`:

* `Homometric`: the finite content of `thm:homometric-example`, the two systems, their
  strong separation and the common dimension `log 6 / log 30`.
* `HomometricMeasures`: `thm:homometric-example`, the two natural measures, the
  non-isometry of their attractors, and the equality of their signed convolutions,
  through the difference system.

`sec:two-contraction-formula`, in `TwoContraction/`:

* `TwoContraction.Cesaro`: `thm:renewal-average` at zero frequency, the Cesàro mean of
  `G` and of `H_μ^s` for the natural measure of any system under the open set condition,
  from the renewal equation, lattice or not; this is the existence of `H̄(c)` before
  `thm:two-contraction-distinction`.
* `TwoContraction.Formula`: the cross-distance `Z_c`, `Φ_× = 2pq ℙ(Z_c ≤ δ)`, the forcing
  transform at zero frequency, `∫ φ = 2^{-s} Γ(1-s)`, and `eq:two-contraction-mean` and
  `eq:two-contraction-constant` of `thm:two-contraction-formula`.
* `TwoContraction.Coding`: Bernoulli codings with general weights, the first-letter
  splitting, and the word-by-word comparisons in the word and in the contraction.
* `TwoContraction.Moment`: `thm:parameter-steps`, `J(α, b, v) = 𝔼 Z^{-α}` and its three
  one-sided steps, in the exponent, the contraction and the weight, the last through a
  monotone coupling.
* `TwoContraction.Parameter`: the parametrisation `c(s)`, `eq:natural-weight-bound`, and
  the moment-loss bound `eq:loss-rate-bound`.
* `TwoContraction.Digamma`: the digamma bound, from the convexity of `log Γ`.
* `TwoContraction.Prefactor`: the prefactor `F(s)` and its logarithmic derivative,
  `eq:rate-comparison`.
* `TwoContraction.Local`: `thm:local-monotonicity`, local strict increase on both sides
  gives strict monotonicity.
* `TwoContraction.Distinction`: `thm:two-contraction-distinction`, the one-sided bounds
  `eq:moment-above` and `eq:moment-below`, the strict monotonicity of the mean and the
  separation of the profiles.
* `TwoContraction.Periodic`: `eq:two-contraction-periodic`, the forcing transform
  `eq:two-contraction-forcing-transform`, the Fourier coefficients of the lattice limit
  from the renewal average with a character, and their `O(k⁻²)` decay.

`sec:small-dimension`, in `FixedDimension/`, on the family of `sec:fixed-dimension-family`
with `a = p^{1/s}`, `b = q^{1/s}` and `s` fixed:

* `FixedDimension.System`: the two maps, their coding, the cross distance `Z_p`, the
  moment `M_p(s) = 𝔼 Z_p^{-s}` through the Bernoulli coding, `M_p ≥ 1`, the entropy
  `E(p)`, the mean `H̄_s(p)` of `eq:fixed-dimension-mean`, and `κ`.
* `FixedDimension.Natural`: the law of the coded point is the natural measure `μ_p`, so
  `M_p(s)` is the integral of `Z_p^{-s}` against `μ_p ⊗ μ_p`.
* `FixedDimension.Entropy`: `thm:entropy-factor`, and the derivative of the entropy factor
  `pq/E(p)` in `eq:log-derivative-mean`.
* `FixedDimension.RiemannSum`: the comparison of a sum with an integral through the
  total variation, and the comparison for a decreasing integrand.
* `FixedDimension.MainTermF`, `FixedDimension.MainTermIntegrals`: `f(x) = (eˣ - 1)^{-s}`,
  `g = x f'`, their derivatives, limits and bounds, the integrals of `f'`, `x f''`, `g`
  and `g'` on `(T, ∞)`, and `s ∫_T^∞ f ≤ 2.3`.
* `FixedDimension.MainTerm`: `eq:main-term` and `thm:main-term-derivative`.
* `FixedDimension.ComplexCoding`: the coded points `x_u(z)` and weights `P_u(z)` of finite
  words for complex contractions, with their bounds.
* `FixedDimension.LevelSums`: the level sums `Λ^{(m)}`, the telescoping increment bound,
  their uniform limit, holomorphic on the open disc and continuous on the closed one, and
  the identification of a level sum with a double Bernoulli integral.
* `FixedDimension.Kernel`: the kernels `φ_n` of `thm:remainder-derivative` on the disc
  `|z - p| ≤ p/2`, `eq:alpha-beta` and `eq:phi-bounds`.
* `FixedDimension.Decomposition`: `eq:leading-ones`, `M_p = ∑ p qⁿ Λ_n(p)`.
* `FixedDimension.RemainderBound`, `FixedDimension.RemainderSup`,
  `FixedDimension.Remainder`: `eq:contraction-disc` and `eq:lambda-bound`, the
  holomorphic remainder `Δ = M - Σ` on the disc, `sup_U |Δ| ≤ 1296 s α p^{-1-s}` and the
  Cauchy estimate for `Δ'`, the identification `Δ(x) = M_x - Σ(x)` at real parameters by
  dominated convergence of the level sums, and `thm:remainder-derivative`.
* `FixedDimension.SecondDerivative`: `thm:second-derivative-small-s`.
* `FixedDimension.Symmetry`: the symmetry `M_{1-z} = M_z` on the disc around `1/2`, through
  the flipped-letter level sums, and `M_{1/2}' = 0`.
* `FixedDimension.Monotone`: `thm:small-dimension-monotone` and the strict increase on
  `(0, p₀]` of `thm:critical-set-finite`.

`sec:fixed-dimension-family` and `sec:fixed-dimension-separation`, in `FixedDimension/`:

* `FixedDimension.Profiles`, `FixedDimension.ProfilesLattice`:
  `thm:fixed-dimension-profiles`, the strong separation and the open set condition of the
  system, `Φ_× = 2pq ℙ(Z_p ≤ δ)`, the renewal mean `E(p)/s`, the forcing transform
  `eq:fixed-dimension-forcing`, `eq:fixed-dimension-mean` as the Cesàro mean of the
  expected profile, the non-lattice limit, and `eq:fixed-dimension-periodic` with the
  `O(k⁻²)` decay of its coefficients.
* `FixedDimension.Correlation`: `eq:fixed-dimension-correlation`, through Hutchinson's
  identity in both coordinates and the Pascal step on the antidiagonals, with the uniform
  remainder `(p² + q²)^m`.
* `FixedDimension.RealLevelSums`: the level sums at every real parameter, as double
  Bernoulli integrals, and their convergence to `M_p(s)`.
* `FixedDimension.SymmetryAll`: `M_p = M_{1-p}` and `H̄_s(p) = H̄_s(1-p)` on `(0,1)`.
* `FixedDimension.LevelSumsDomain`, `FixedDimension.ParameterLipschitz`,
  `FixedDimension.Analyticity`: `thm:fixed-dimension-analyticity`, through the telescoping
  bound with the kernel Lipschitz on a neighbourhood of `[0,1]`, the Lipschitz dependence
  of the branches and of the coded points on the parameter, the holomorphic extension on a
  disc of radius depending on `p₀` and `s`, and the restriction to the real line.
* `FixedDimension.Range`: `thm:fixed-dimension-range`, continuity and positivity of the
  mean, its limit `0` as `p ↓ 0` from the bound `M_p ≤ 2^s Σ(p)`, and the uncountable
  subfamily with distinct means.
* `FixedDimension.Separation`: `thm:fixed-dimension-separation`, the critical set and the
  level sets without accumulation points, strict monotonicity on intervals free of critical
  points, `ε_s`, and the finiteness of `D_s` of `thm:critical-set-finite`.
* `FixedDimension.Laws`: the singularity of the image-measure and compact-image laws for
  parameters with distinct means.
-/
import BrownianImages.Defs
import BrownianImages.Occupation
import BrownianImages.Empirical
import BrownianImages.Frostman
import BrownianImages.Kernel
import BrownianImages.Periodic
import BrownianImages.SelfSimilar
import BrownianImages.Renewal
import BrownianImages.RenewalBridge
import BrownianImages.Homometric
import BrownianImages.FourPoint
import BrownianImages.Multiplier
import BrownianImages.GaussianFourPoint
import BrownianImages.WeakBorel
import BrownianImages.Profile
import BrownianImages.Recursion
import BrownianImages.Asymptotics
import BrownianImages.FourierMultiplier
import BrownianImages.Smoothing
import BrownianImages.UniformContinuity
import BrownianImages.JointMeasurability
import BrownianImages.Reduction
import BrownianImages.AhlforsRegular
import BrownianImages.OpenSet
import BrownianImages.Schief
import BrownianImages.IntervalColoring
import BrownianImages.StoppingGeometry
import BrownianImages.CrossPiece
import BrownianImages.Hutchinson
import BrownianImages.PairDifference
import BrownianImages.HomogeneousNonconstancy
import BrownianImages.ExceptionalParameters
import BrownianImages.Rescaling
import BrownianImages.FourPointBound
import BrownianImages.BlockMass
import BrownianImages.FourPointIntegral
import BrownianImages.Concentration
import BrownianImages.Endpoints
import BrownianImages.VarianceCovariance
import BrownianImages.MainTheorem
import BrownianImages.BaseFive
import BrownianImages.HomometricMeasures
import BrownianImages.ProfileAsymptotics
import BrownianImages.Separation
import BrownianImages.CantorApplication
import BrownianImages.KeyRenewalFourier
import BrownianImages.NonLattice
import BrownianImages.CompactImage
import BrownianImages.Minkowski.System
import BrownianImages.Minkowski.Tube
import BrownianImages.Minkowski.TubeAlgebra
import BrownianImages.Minkowski.Profile
import BrownianImages.Minkowski.CorrelationLower
import BrownianImages.Minkowski.BrownianScaling
import BrownianImages.Minkowski.BrownianPieces
import BrownianImages.Minkowski.BrownianCompactPieces
import BrownianImages.Minkowski.Localization
import BrownianImages.Minkowski.Cylinder
import BrownianImages.Minkowski.CylinderConvergence
import BrownianImages.Minkowski.OverlapTranslation
import BrownianImages.Minkowski.GaussianIncrement
import BrownianImages.Minkowski.OverlapProbability
import BrownianImages.Minkowski.BrownianOverlapGeometry
import BrownianImages.Minkowski.DefectExpectation
import BrownianImages.Minkowski.TubeMeanLower
import BrownianImages.Minkowski.TubeUpper
import BrownianImages.Minkowski.BrownianMaximalReduction
import BrownianImages.Minkowski.BrownianMaximalMoment
import BrownianImages.Minkowski.Stopping
import BrownianImages.Minkowski.StoppingTubeUpper
import BrownianImages.Minkowski.TubeMeanContinuity
import BrownianImages.Minkowski.TubeMomentAssembly
import BrownianImages.Minkowski.TubeRenewal
import BrownianImages.Minkowski.StoppingOverlap
import BrownianImages.Minkowski.TubeRenewalLimit
import BrownianImages.Minkowski.TubeRenewalAssembly
import BrownianImages.Minkowski.L2Recurrence
import BrownianImages.Minkowski.DefectL2
import BrownianImages.Minkowski.ProfileL2
import BrownianImages.Minkowski.AlmostSure
import BrownianImages.Minkowski.StoppingConcentration
import BrownianImages.Minkowski.Ratio
import BrownianImages.Minkowski.TubeEndpointAssembly
import BrownianImages.Minkowski.TubeArithmeticRenewal
import BrownianImages.Minkowski.TubeDiscreteRenewal
import BrownianImages.Minkowski.Limit
import BrownianImages.Minkowski.LimitClassifier
import BrownianImages.Minkowski.TubeConvergence
import BrownianImages.Minkowski.Reconstruction
import BrownianImages.Minkowski.Generation
import BrownianImages.Minkowski.GenerationScaling
import BrownianImages.Minkowski.GenerationRatio
import BrownianImages.Minkowski.ReconstructionAssembly
import BrownianImages.Minkowski.HomogeneousReconstruction
import BrownianImages.Minkowski.FullEndpointAssembly
import BrownianImages.Minkowski.CantorSetApplication
import BrownianImages.Minkowski.BaseFiveApplication
import BrownianImages.LatticeProfile
import BrownianImages.TwoContraction.Cesaro
import BrownianImages.TwoContraction.Formula
import BrownianImages.TwoContraction.Coding
import BrownianImages.TwoContraction.Moment
import BrownianImages.TwoContraction.Parameter
import BrownianImages.TwoContraction.Digamma
import BrownianImages.TwoContraction.Prefactor
import BrownianImages.TwoContraction.Local
import BrownianImages.TwoContraction.Distinction
import BrownianImages.TwoContraction.Periodic
import BrownianImages.FixedDimension.System
import BrownianImages.FixedDimension.Natural
import BrownianImages.FixedDimension.Entropy
import BrownianImages.FixedDimension.RiemannSum
import BrownianImages.FixedDimension.MainTermF
import BrownianImages.FixedDimension.MainTermIntegrals
import BrownianImages.FixedDimension.MainTerm
import BrownianImages.FixedDimension.ComplexCoding
import BrownianImages.FixedDimension.LevelSums
import BrownianImages.FixedDimension.Kernel
import BrownianImages.FixedDimension.Decomposition
import BrownianImages.FixedDimension.RemainderBound
import BrownianImages.FixedDimension.RemainderSup
import BrownianImages.FixedDimension.Remainder
import BrownianImages.FixedDimension.SecondDerivative
import BrownianImages.FixedDimension.Symmetry
import BrownianImages.FixedDimension.Monotone
import BrownianImages.FixedDimension.RealLevelSums
import BrownianImages.FixedDimension.SymmetryAll
import BrownianImages.FixedDimension.LevelSumsDomain
import BrownianImages.FixedDimension.ParameterLipschitz
import BrownianImages.FixedDimension.Analyticity
import BrownianImages.FixedDimension.Range
import BrownianImages.FixedDimension.Separation
import BrownianImages.FixedDimension.Profiles
import BrownianImages.FixedDimension.ProfilesLattice
import BrownianImages.FixedDimension.Correlation
import BrownianImages.FixedDimension.Laws
