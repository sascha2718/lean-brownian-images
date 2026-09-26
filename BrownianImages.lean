/-
A Lean formalisation of "Pair-distance profiles and Minkowski reconstruction of planar
Brownian images" (`BrownianImagesComplete.tex`).

The library is organised along the paper.  `Solution.lean` carries the formal statement
of every numbered result of the document, and `Challenge.lean` restates the headline
theorems for the comparator audit; the modules below carry what is proved.  `README.md`
gives the build and audit instructions, and `docs/` the correspondence with the paper.

The objects, and `sec:setup`:

* `Defs`: the objects the paper is phrased in, from `eq:correlation-functional` to
  `eq:variance-scale`, together with self-similar systems, their natural measures, and
  the two systems of the application, placed here so `Challenge.lean` can copy them
  from one module.
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
  and the two conclusions of `thm:profile-asymptotics` about the correlation integral.
* `UniformContinuity`: `thm:profile-uniform-continuity`, on the substitution `η = e^x`
  and the `L¹` continuity of translation for the kernel.

`sec:renewal`:

* `SelfSimilar`: strongly separated self-similar systems, the dimensions and gaps of the
  two named systems, the ratio `c` of `eq:c-definition`, and the renewal data of
  `thm:non-lattice-limit`.
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
  multiplicity bound, the partition into `M` families, and Ahlfors regularity under
  the open set condition.
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
* `Asymptotics`: `thm:profile-asymptotics`, both branches.
* `ProfileAsymptotics`: the `μ_B` conclusion of `thm:profile-asymptotics` with its
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
* `NonLattice`: those two, `eq:gb-limit` and `thm:profile-asymptotics`, discharged
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
  `Minkowski.BrownianCompactPieces`: Brownian rescaling, and the law and independence of
  compact images of disjoint time pieces, in the arbitrary compact-cylinder form.
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
