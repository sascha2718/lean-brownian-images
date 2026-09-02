/-
A Lean formalisation of `BrownianImagesComplete.tex`, "Pair-distance profiles and
Minkowski reconstruction of planar Brownian images".

The library is organised along the paper.  `Solution.lean` carries the formal
statement of every numbered result of the document, and `Challenge.lean` restates the
headline theorems for the comparator audit; the modules below carry what is proved.
`PLAN.md` records the state, the build setup, and the fidelity boundary.

* `Defs`: the objects the paper is phrased in, from `eq:correlation-functional` to
  `eq:variance-scale`, together with self-similar systems, their natural measures, and
  the two systems of the application, placed here so `Challenge.lean` can copy them
  from one module.
* `Occupation`: the occupation measure as a random point of `𝒫(ℝ²)`, and the almost
  sure facts that make it one.
* `Empirical`: the empirical profile `eq:y-definition` and the grid monotonicity
  `eq:monotone-fill`.
* `Frostman`: the Frostman condition, the two ball conventions, atomlessness, and the
  pair-distance bound `eq:phi-frostman`.
* `Kernel`: the smoothing kernel `φ` of `eq:h-definition`, its logarithmic form, and
  the two-sided domination that puts it in `L¹(ℝ)`.
* `SelfSimilar`: the theory of strongly separated self-similar systems: separation,
  dimensions and gaps of the named systems, the ratio `c` of `eq:c-definition`, and
  the renewal data of `thm:non-lattice-limit`.
* `Cantor`: the constants of `thm:cantor-values` and the non-constancy of the periodic
  profile of the middle-thirds measure.
* `Homometric`: the finite content of `thm:homometric-example`, the homometry of the
  two digit sets and the common dimension `log 6 / log 30`.
* `FourPoint`: the covariance determinants of the two overlapping pairings,
  `eq:crossing-determinant` and `eq:nested-determinant`, with their dyadic block bounds.
* `Multiplier`: the Fourier multipliers `eq:gamma-multiplier` and their non-vanishing,
  the engine of `thm:smoothing-injective`.
* `Renewal`: the key renewal theorem, vendored from Benny Avelin's `AbsorptionCutoff`
  under the Apache License 2.0; see `BrownianImages/Renewal.lean` for provenance.
* `RenewalBridge`: the hypotheses of that theorem, discharged for the renewal measure
  `ϑ = ∑ p_i δ_{a_i}` of a self-similar system.  The only module that mentions the
  vendored namespace.
* `GaussianFourPoint`: the mass half of `thm:endpoint-block-mass`, the independence of
  disjoint planar increments, and the planar return probability of
  `eq:gaussian-reduction`.
* `WeakBorel`: the Borel σ-algebra of the weak topology on `𝒫(ℝ²)` is the Giry one.
* `Profile`: elementary bounds on `G`, and its measurability without regularity.
* `Asymptotics`: `thm:profile-asymptotics`, both branches.
* `FourierMultiplier`: `eq:fourier-multiplier` and, with it, `thm:smoothing-injective`
  unconditionally.
* `Recursion`: `thm:renewal-recursion`, the self-similar recursion of `Φ` and of `G`.
* `Smoothing`: the extrema of a continuous periodic function, the continuity and
  linearity of the smoothing operator, the strict positivity of `Φ`, and
  `thm:smoothing-injective` reduced to the two multiplier facts.
* `UniformContinuity`: `thm:profile-uniform-continuity`, on the substitution `η = e^x`
  and the `L¹` continuity of translation for the kernel.
* `JointMeasurability`: joint measurability of the process, and the measurability of
  the occupation law that follows from it.
* `Reduction`: `thm:gaussian-reduction`, the Fubini interchange and the Gaussian
  transform of the pair-distance law.
* `AhlforsRegular`: Ahlfors regularity of the natural measure of a strongly separated
  system, used internally to obtain the Frostman bound at every centre.
* `Hutchinson`: the coding map on `ℕ → ι`, Hutchinson's theorem for a general system,
  and the two natural measures of `sec:renewal`.
* `CantorValues`: `thm:cantor-values`, the three exact values of `eq:cantor-values`.
* `Rescaling`: `eq:smoothing`, the layer cake identity and the substitution `δ = r²η`,
  and the two conclusions of `thm:profile-asymptotics` about the correlation integral.
* `FourPointBound`: `eq:joint-return-bound`, through the regression decomposition of the
  second increment and the disc bound for a planar Gaussian.
* `BlockMass`: `thm:endpoint-block-mass`, both halves, on the two overlapping pairings.
* `FourPointIntegral`: `thm:four-point-integral`, the dyadic summation and the
  permutation invariance of `μ⁴`, and `thm:variance` on the block bound.
* `Concentration`: `sec:concentration`, from `eq:y-variance` through
  `thm:uniform-concentration` to `thm:main`.
* `Endpoints`: the results the paper states that no single module proves, each a
  composition of two or more of the above in the shape `Challenge.lean` states it.
* `VarianceCovariance`: `eq:variance`, the second moment of the correlation functional
  as a `μ⁴`-mass, and the covariance killed off the overlap set.
* `MainTheorem`: `sec:concentration` run to its end, from `eq:y-variance` to `thm:main`.
* `HomometricMeasures`: `thm:homometric-example`, the two natural measures and the
  equality of their signed convolutions, through the difference system.
* `KeyRenewal`: `thm:non-lattice-limit` reduced to convergence of `G` alone, by cutting
  the renewal equation at a finite threshold, together with Choquet-Deny for finitely
  supported laws.
* `TailHarmonic`: a bounded function harmonic on a tail for a step law with dense group
  converges, and `thm:non-lattice-limit` with it.
* `KeyRenewalFourier`: `thm:non-lattice-limit` again, by the paper's own route.  The
  vendored key renewal theorem asks for `Nonlattice`, which `ϑ` fails; `FellerNonlattice`
  is what its proof actually consumes and what `eq:non-lattice` supplies.
* `ProfileAsymptotics`, `Separation`, `CantorApplication`: the conditional forms of
  `eq:gb-limit`, `thm:profile-asymptotics`, `thm:non-lattice-separation` and
  `thm:cantor-application`.
* `NonLattice`: those four, and `thm:cantor-application` for `μ_B`, discharged.
* `CompactImage`: compact Brownian images as measurable random variables in the
  Hausdorff hyperspace.
* `MinkowskiIntervalGap`: the symmetric first-level separation hypothesis converted
  to one of the two oriented temporal-gap configurations used by the overlap proof.
* `MinkowskiTube`, `MinkowskiTubeAlgebra`, `MinkowskiProfile`: the smoothed tube
  probability, its continuity, and the deterministic union, scaling, and overlap
  algebra from `sec:reconstruction`.
* `MinkowskiCorrelationLower`: the deterministic ball-mass/Fubini argument which
  bounds tube area below by disc area divided by the correlation integral.
* `MinkowskiBrownianScaling`, `MinkowskiBrownianPieces`: Brownian rescaling and the
  law and independence of compact images of disjoint time pieces;
  `MinkowskiBrownianCompactPieces` supplies the arbitrary compact-cylinder form and
  its exact tube-mass law.
* `MinkowskiLocalization`, `MinkowskiCylinder`, `MinkowskiCylinderConvergence`:
  bounded-Lipschitz localization, the finite-cylinder approximation estimates, and
  the abstract passage from cylinder ratios to weak convergence.
* `MinkowskiOverlapTranslation`: the convolution/Fubini identity and bounded-density
  inequality behind the separated-cylinder overlap estimate.
* `MinkowskiGaussianIncrement`: the exact planar Gaussian density of a non-degenerate
  Brownian increment and its uniform bound by the density at the origin.
* `MinkowskiDefectExpectation`, `MinkowskiOverlapAssembly`, `MinkowskiOverlapSystem`:
  pairwise overlap integrability and its finite-family assembly into the complete
  pair-and-defect estimate.
* `MinkowskiStopping`, `MinkowskiStoppingTubeUpper`, `MinkowskiBrownianMaximalMoment`,
  `MinkowskiTubeMomentAssembly`: stopping-antichain covers, every Brownian maximal
  moment, all tube moments, and the positive lower mean.
* `MinkowskiTubeRenewal`, `MinkowskiTubeRenewalLimit`,
  `MinkowskiTubeArithmeticRenewal`, `MinkowskiTubeDiscreteRenewal`: the exact mean
  renewal recurrence, exponentially decaying forcing, the non-arithmetic limit,
  finite-delay renewal convergence, and the unconditional arithmetic periodic limit.
* `MinkowskiL2Recurrence`, `MinkowskiDefectL2`, `MinkowskiContraction`,
  `MinkowskiTubeConcentrationAssembly`: the centered-variance recurrence, interpolated
  defect `L²` bound, delayed contraction, and exponential profile concentration.
* `MinkowskiAlmostSure`: the Borel--Cantelli passage from summable (in particular,
  exponentially bounded) deviations to almost-sure convergence along a fixed phase.
* `MinkowskiRatio`: the scalar passage from centered profile convergence and a positive
  renewal mean to the limiting cylinder-mass ratios.
* `MinkowskiLimit`, `MinkowskiLimitClassifier`, `MinkowskiTubeConvergence`: measurable
  weak limits of the tube sequence and Borel classifiers read directly from that
  sequence.
* `MinkowskiTransfer`, `MinkowskiReconstruction`: the rigorous passage from pathwise
  tube reconstruction to Borel recovery of the occupation measure and to mutual
  singularity of the compact-image laws.
* `MinkowskiGeneration`, `MinkowskiGenerationScaling`, `MinkowskiGenerationRatio`:
  finite self-similar generations, their exact Brownian tube scaling, and the
  almost-sure fixed-generation quotient argument.
* `MinkowskiReconstructionAssembly`, `MinkowskiHomogeneousReconstruction`,
  `MinkowskiFullEndpointAssembly`, `MinkowskiCantorSetApplication`: reconstruction
  in both renewal regimes, direct homogeneous reconstruction from the one-delay
  recurrence, and the final mutual singularity of the two compact Brownian image laws.
* `AxCheck`: `#print axioms` on every endpoint of the library, the vendored key renewal
  theorem included.
-/
import BrownianImages.Defs
import BrownianImages.Occupation
import BrownianImages.Empirical
import BrownianImages.Frostman
import BrownianImages.Kernel
import BrownianImages.Periodic
import BrownianImages.Cantor
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
import BrownianImages.Hutchinson
import BrownianImages.CantorValues
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
import BrownianImages.HomometricMeasures
import BrownianImages.ProfileAsymptotics
import BrownianImages.Separation
import BrownianImages.CantorApplication
import BrownianImages.KeyRenewal
import BrownianImages.TailHarmonic
import BrownianImages.KeyRenewalFourier
import BrownianImages.NonLattice
import BrownianImages.CompactImage
import BrownianImages.MinkowskiSystem
import BrownianImages.MinkowskiIntervalGap
import BrownianImages.MinkowskiTube
import BrownianImages.MinkowskiTubeAlgebra
import BrownianImages.MinkowskiProfile
import BrownianImages.MinkowskiCorrelationLower
import BrownianImages.MinkowskiBrownianScaling
import BrownianImages.MinkowskiBrownianPieces
import BrownianImages.MinkowskiBrownianCompactPieces
import BrownianImages.MinkowskiLocalization
import BrownianImages.MinkowskiCylinder
import BrownianImages.MinkowskiCylinderConvergence
import BrownianImages.MinkowskiOverlapTranslation
import BrownianImages.MinkowskiGaussianIncrement
import BrownianImages.MinkowskiOverlapProbability
import BrownianImages.MinkowskiBrownianOverlapGeometry
import BrownianImages.MinkowskiDefectExpectation
import BrownianImages.MinkowskiOverlapAssembly
import BrownianImages.MinkowskiTubeMeanLower
import BrownianImages.MinkowskiTubeUpper
import BrownianImages.MinkowskiBrownianMaximalReduction
import BrownianImages.MinkowskiBrownianMaximalMoment
import BrownianImages.MinkowskiStopping
import BrownianImages.MinkowskiStoppingTubeUpper
import BrownianImages.MinkowskiTubeMeanContinuity
import BrownianImages.MinkowskiTubeMomentAssembly
import BrownianImages.MinkowskiTubeRenewal
import BrownianImages.MinkowskiOverlapSystem
import BrownianImages.MinkowskiTubeRenewalLimit
import BrownianImages.MinkowskiTubeRenewalAssembly
import BrownianImages.MinkowskiL2Recurrence
import BrownianImages.MinkowskiDefectL2
import BrownianImages.MinkowskiContraction
import BrownianImages.MinkowskiAlmostSure
import BrownianImages.MinkowskiRatio
import BrownianImages.MinkowskiTubeConcentrationAssembly
import BrownianImages.MinkowskiTubeEndpointAssembly
import BrownianImages.MinkowskiTubeArithmeticRenewal
import BrownianImages.MinkowskiTubeDiscreteRenewal
import BrownianImages.MinkowskiLimit
import BrownianImages.MinkowskiLimitClassifier
import BrownianImages.MinkowskiTubeConvergence
import BrownianImages.MinkowskiTransfer
import BrownianImages.MinkowskiReconstruction
import BrownianImages.MinkowskiGeneration
import BrownianImages.MinkowskiGenerationScaling
import BrownianImages.MinkowskiGenerationRatio
import BrownianImages.MinkowskiReconstructionAssembly
import BrownianImages.MinkowskiHomogeneousReconstruction
import BrownianImages.MinkowskiFullEndpointAssembly
import BrownianImages.MinkowskiCantorSetApplication
import BrownianImages.AxCheck
