# Correspondence with the paper

This document argues the correspondence between the formal statements and the LaTeX
source `BrownianImagesComplete.tex`: what `Solution.lean` and `Challenge.lean` state,
how each result of the paper maps to an endpoint, and where a formal statement could
quietly diverge from the prose. Paper references use readable mathematical names;
LaTeX labels remain internal lookup keys in the machine-readable correspondence.
The comparator compares `Challenge.lean` with `Solution.lean` and never with
the paper, so this correspondence is a human obligation, and this document is where
it is argued. [`../paper-correspondence.yaml`](../paper-correspondence.yaml) is the
structured statement mapping used alongside the Palomar metadata. Its source hashes
detect drift and do not establish mathematical equivalence.

The paper is [arXiv:2610.16339](https://arxiv.org/abs/2610.16339). Its uploaded v1 source is
the parent research repository's `saved/arxiv-v1` branch at
`93b440fb68e1ebc74b8df1b4998923eb0f11857e`. On 14 October 2026, all 32 numbered statements
and all 30 proof environments were compared with the current manuscript through commit
`9decb5f` and found textually identical. The revised introduction adds background on correlation
dimension and local density ratios, and comparisons with dynamical reconstruction and
hitting-time statistics. These passages are outside the formalisation and have explicit
prose entries in the manifest. The attribution, acknowledgements, AI disclosure and
bibliography changes do not alter the nine headline claims.

All nine headline results have complete proofs with the paper's hypotheses and conclusions,
and all 32 numbered statements are formalised, Proposition 3.3 and Lemma 3.4 for the
explicit periodisation `G̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t+kℓ)` defined before Proposition 3.3,
represented by `System.latticePeriodisation`. The remaining differences are proof routes
and the generality of the quoted renewal theorem; see
[Omissions and proof differences](#omissions-and-proof-differences) below.

The build `lake build BrownianImages Challenge Solution` passed on 14 October 2026.
Lean's `#print axioms` reported exactly `propext`, `Classical.choice` and `Quot.sound`
for each of the 145 `Solution` audit declarations. The nine `sorry` declarations in
`Challenge` are intentional problem statements; none occurs in the library or `Solution`.
These checks verify Lean proofs and dependencies, not the interpretation of the paper.

A separate statement review on 14 October 2026 compared all 32 numbered statements
in `saved/arxiv-v1` with the current Lean declarations and the definitions they use.
It checked the hypotheses and quantifiers, parameter ranges, normalisations, constants,
and conversions between the paper's objects and their Lean representations. No further
weakening of a numbered result was found. In particular, the new periodisation has
the paper's factor `ℓ/m`, integer translates of its defect, and a proved convergent
series; its positivity, non-constancy and limiting properties are proved for that function.
The general renewal theorem and its shift consequence are both classified as partially
formalised: the shift consequence inherits the paper's arbitrary finite interarrival
law, whereas its Lean statement restricts the weights to `p_i = exp(-s * α_i)`.
This review is an agent assessment of mathematical correspondence, not a machine proof
that the LaTeX and Lean have the same meaning.

The paper uses `C_δ(μ)` for the correlation integral of the time measure as well as
`C_r(ν)` for a planar measure. The library retains the internal names `Phi μ δ` and
`corr ν r`, respectively. `Phi` uses a closed distance inequality, which agrees with
the paper's strict inequality for the atomless time measures in *Frostman measures and Gaussian reduction*
(`pairLaw_measure_singleton`). Likewise, `crossPhi` represents the paper's cross
contribution `C^×_δ(μ)`, and `expCorr` represents `𝔼 C_r(W_*μ)` directly. References to
`Φ`, `Φ_×`, or `S_μ` below use these internal notational conventions. The smoothing
kernel `φ` is a separate function and keeps the same notation in the paper.
The internal name `pairLaw μ` denotes the associated Stieltjes measure `dC_δ(μ)`,
the law of `|X - Y|` for independent points with law `μ`.

The real argument of the correlation profile `G` and inhomogeneous term `z` is written
`t` in the paper, while `w` indexes words. Bound real variables called `w` in the
library correspond to this `t`; the functions and their scaling are unchanged.
In these renewal equations, `ϑ` is the interarrival distribution; the renewal measure
is the sum `∑_{n≥0} ϑ^{*n}` of its convolution powers.
The paper consistently denotes the lattice span and logarithmic period by `ℓ`,
with period `ℓ/2` after Brownian smoothing. Internal period parameters called `h`
in renewal modules and `p` in smoothing modules represent this `ℓ`.

The paper writes `C^×_δ(μ)` directly as the sum of
`p_i p_j (μ × μ){(x,y) : |S_i(x) - S_j(y)| ≤ δ}` over `i ≠ j`, without naming the
individual pushforwards. This is the same quantity as the library's `crossPhi`.
The boundary-mass estimate is likewise written after pulling back by
`S_i`, as `μ{x ∈ K : dist(S_i(x), S_j K) ≤ δ} ≤ C δ^η`.
The fixed-block exclusion argument is `IsFeasible.measure_preimage_cthickening_le_pow`,
followed by `exists_rpow_bound_of_geometric` to obtain the bound at every scale.

The library defines `H` by the kernel integral, and `smoothing` identifies it with the
expected profile. In the paper, the expectation defines the profile and its kernel
representation is derived. Code comments on smoothing refer to the rescaled form of
this identity.

The empirical profile in *Uniform concentration and mutual singularity* is defined directly by
`Y_μ(t) = e^{2st} C_{e^{-t}}(W_*μ)`. The library's `Yprofile s ν t` is the normalised
correlation integral of a planar measure `ν`, so `Yprofile s (occupation W μ ω) t`
is the paper's `Y_μ(t)` on the Brownian path `ω`.

The paper uses `⟨F⟩_r` throughout for the open neighbourhood `Metric.thickening r F`.
In *Minkowski reconstruction from the image set*, it writes the normalising exponent `2 - 2s` explicitly;
the library retains `tubeExponent s`, also denoted by `α` in internal comments.
The logarithmic contractions are `α_i = log(1/r_i)` and `α_w = log(1/r_w)` throughout
the paper. The library's `halfLogRatio`, `generationHalfLogRatio` and
`stoppingHalfLogRatio` represent the Brownian shifts `α_i/2` and `α_w/2`. The
interarrival distribution for the neighbourhood mean is `∑ p_i δ_{α_i/2}`. If the
original logarithmic contractions have lattice span `ℓ`, then `TubeArithmetic (ℓ/2)`
expresses arithmeticity for this law. Internal variables called `beta` in
cylinder-shift arguments denote `α_w/2`.

The fixed-dimension family and its separation results form the single section
*A two-contraction family of fixed dimension*. Its subsections are *Correlation
profiles*, *Separation of image laws*, and *Monotonicity for small dimension*. The paper uses
`λ₁ = p^{1/s}` and `λ₂ = (1-p)^{1/s}` for the contractions, represented by
`fixedA s p` and `fixedB s p`. Their principal complex branches `λ₁(z)` and `λ₂(z)`
are `ca s z` and `cb s z`. Internal variables and comments using `a` and `b` for
these contractions follow the same correspondence.
The entropy is `h(p) = -p log p - (1-p) log(1-p)`, represented by `entropy p`.
In the proof of *Analyticity in the two-contraction family*, the paper uses its principal-logarithm
extension `h(z)` and identifies the local holomorphic extensions on overlapping discs by
the identity theorem. This gives extensions of the cross-term integral and mean to a
complex neighbourhood of `(0,1)`. The formal endpoint records their real-analytic consequence;
the local holomorphic cross-term extension is `differentiableOn_crossLimit_disc`.

The holomorphic kernels in *Separation of image laws* are `ψ` and `ψ_n`;
`crossKernelC` and `kernelN` are their concrete implementations, and the generic
kernel argument `φ` of `levelSum` represents `ψ`. The Gaussian smoothing kernel
retains `φ`. In *Monotonicity for small dimension*, `alphaP s p` and `betaP s p` represent
`λ_{1,max} = sup_U |λ₁|` and `λ_{2,max} = sup_U |λ₂|`. The paper writes
`ξ = 1 - λ_{2,max} B²` for the positive contraction gap. The library uses the
majorant `discB p = 1 + p/5` for `B`, so `1 - discR s p` is a lower bound for `ξ`.

The three derivative lemmas and their full calculations are stated separately in the paper.
`Section9Estimates.lean` also collects their consequences: `entropy_bounds`,
`derivative_bounds` (combining the first two derivative estimates and restating the third),
and `small_parameter_margin`. The optional `Section9Computations.nb` displays the same
symbolic differentiations, integral comparisons, sums and constants as worked calculations.
The paper uses the small-parameter error bound `0.62`; the Lean proof uses the sufficient
bound `0.754 < 0.88`. Both give the strict comparison `|J'(p)| < κ(p)`.

The paper consistently uses `S` for similarities. In *A two-contraction family of fixed dimension*,
`S₁(x) = λ₁x` and `S₂(x) = λ₂x + 1 - λ₂`, with coding alphabet `{1,2}`.
The library's `Fin 2` symbols `0`, `1` correspond to the paper's `1`, `2`.
In particular, `N₁`, `N₂` count the paper's symbols `1`, `2`, and the internal
leading-ones decomposition counts the symbols `2` before the first `1` in the paper's
*Initial-symbol decomposition*. In *Two base-five missing-digit sets with different structure* and *Identical correlation integrals*,
`S_d` is indexed by the actual digit `d` of the specified digit set.

The formulas in *Correlation profiles* use the existing cross term directly.
Its Stieltjes measure is `2pq` times the law of `S₂(Y) - S₁(X)` for independent
`X,Y ∼ μ_p`, by `fixedSystem_crossPhi`. Thus
`∫₀¹ f(δ) dC^×_δ(μ_p) = 2pq 𝔼 f(S₂(Y) - S₁(X))` whenever the integral exists.
In particular, `fixedMoment s p = (2pq)^{-1} ∫₀¹ δ^{-s} dC^×_δ(μ_p)` by
`fixedMoment_eq_natural`. The paper introduces this normalised integral as `J(p)` in
*Separation of image laws*, alongside its main approximation `J₀(p)` in
*Main approximation to the cross-term moment*, represented by `mainTerm s p`. Both functions and their parameter
derivatives are used in *Monotonicity for small dimension*. The paper retains the argument in
`T(p) = log(1/q)/s` throughout and differentiates with respect to `p`, displaying
`T'(p) = 1/(sq)`. The library evaluates its generic logarithmic variable at
`fixedT s p` and applies the chain rule in `hasDerivAt_mainTerm`.
Internal code comments using `Z_p` and `M_p(s)` denote the distance `fixedCross`
and this normalised integral, respectively. The paper writes the distance out and
introduces no moment with a general complex exponent. The correlation series absorbs
its factor `2pq` into the cross-term measure, and the mean formula is
`H̄_s(p) = 2^{-s} Γ(1-s) (∫₀¹ δ^{-s} dC^×_δ(μ_p))/h(p)`.

The source measures in *Identical correlation integrals* are `μ_{D_A}` and `μ_{D_B}`, named for
their digit sets before *Homometric non-isometric attractors*. The internal measures `σ_A`, `σ_B`
of `HomometricMeasures.lean` and digit maps `digitFunA`, `digitFunB` represent them.

The neighbourhood mean is `Q(t) = e^{(2-2s)t} 𝔼 M_{e^{-t}}(E)`, represented by
`meanBrownianTubeProfile`; local function aliases `m` in the renewal proofs denote `Q`.
The paper writes the random normalised mass explicitly;
`brownianTubeProfile` retains it as an internal definition. The statement
*Renewal asymptotics for the mean neighbourhood profile* consists of positive uniform bounds and the real-time shift
relation, represented exactly by
`System.IsNatural.tubeRenewal_bounds_shift` and `audit_tube_renewal`. The stronger constant
and periodic alternatives remain internal in `System.IsNatural.tubeRenewal`. Their
periodic profile `PK` and cutoff do not introduce notation in Section 7 of the paper.
The cylinder neighbourhood scaling identity is written as equality
in law of the mass processes indexed by radius. The concentration proof uses the cylinder
masses directly, and introduces the word shift `α_w/2` only when applying concentration
in the reconstruction proof. Internal normalised cylinder profiles express these same
masses and shifts. Both the paper and `GenerationRatio.lean` pass from concentration and
mean shift invariance to cylinder-mass ratios.

The first bound in *Concentration of the neighbourhood profile* uses variance. Its proof
writes the stopping sum and the total defect `∑_{v∈𝒯(r)} D_{v,r}` directly, with the
normalising powers of `r` outside the moments and variance. It introduces no `Y_r` or
`F_r`. The fourth moment is bounded by weighted Jensen, and Hölder bounds the second
moment using the first and fourth moments. The internal proof in
`StoppingConcentration.lean` retains names for the stopping sum and leaf defect, its
centred norms, and third-moment interpolation;
it proves the same existence of a positive exponential rate. The exact conversion to the
paper's variance statement is `System.IsNatural.tubeVarianceConcentration`, using
`MinkowskiL2Recurrence.centeredL2Norm_sq`. The Lean statements include square integrability,
and each fixed grid has its own almost-sure event.

The bounded overlap estimate and interval partition appear in
*Open set condition estimates*, where the paper cites
Hutchinson (1981), proof of Theorem 5.3(1). The library retains proofs of both facts.

The library proves the self-similar correlation recursion, its rescaled form and the
cross-term bounds. The paper records these directly in prose. The subsection
*Renewal and asymptotics* states the
shared signed-forcing renewal theorem from Falconer (1997), Proposition 7.1 and
Theorem 7.2, for an arbitrary finitely supported law, and derives the shift consequence
*Renewal shift limit* for bounded half-line solutions by a cutoff argument.
`RenewalTheorem.lean` proves both for the laws `ϑ = ∑ p_i δ_{α_i}` of a system at its
similarity dimension, which is the generality in which the paper applies them, with a
signed defect `|z(t)| ≤ C e^{-c|t|}`. The non-lattice limit and the renewal series come
from the vendored theorem. The lattice uniform convergence on one period comes from the
discrete renewal theorem and Tannery's theorem (`TubeArithmeticRenewal.lean`,
`TubeDiscreteRenewal.lean`) applied to the cutoff `min{t,1} f(t)`, where the paper uses
uniform continuity of the solution, and the limit is identified with the periodisation
by `eq_periodisation_of_periodic_limit`. The shift consequence follows the paper's cutoff
argument, with `tendsto_sub_shift_sub_of_tendsto_atTop` and
`tendsto_sub_period_sub_of_uniform_lattice` in `GenerationRatio.lean` for its two cases.
The renewal series in the lattice case and the uniform continuity of the solution are
not formalised. The lattice application uses the span-one statement after rescaling, so
its prefactor is `ℓ/m`. Feller is cited in prose for another account of the renewal
theorem.

The paper groups the constant and periodic limits in *Lattice and non-lattice renewal limits*, in the
subsection *Renewal and asymptotics*. The non-lattice result named separately in the
library is its non-lattice conclusion; the Lean declaration names are unchanged.
The lattice conclusion is stated for the paper's periodisation
`G̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t+kℓ)`, `System.latticePeriodisation`, with `renewalMean` for `m`
and `renewalDefect` for `z`. The existence form `System.lattice_G_limit` comes from the
finite-delay renewal theorem, and `LatticePeriodisation.lean` identifies its limit with
`G̃`: along a lattice `t + ℓℤ` the renewal equation telescopes, so the symmetric partial
sums of `z(t+kℓ)` converge to `g(t) m/ℓ` for every periodic limit `g` of `G`, and the
exponential tails of `z` make the series summable.
The preliminary lemma *Left-tail bounds for the renewal defect* collects continuity from the finite-sum
definition of `renewalDefect`, non-negativity from `renewalDefect_nonneg`, and the exact
negative-time calculation in the proof of `renewalDefect_pos_of_nonpos`, using
`renewalDefect_eq` and `phi_eq_one_of_one_le`. The positive-time consequence appended to
*Cross-piece mass decay* is the calculation in `exists_abs_renewalDefect_le_exp`.

The Gaussian return and endpoint-mass estimates in *The four-point variance bound*
are proved directly inside the *Four-point integral bound*. The library treats
these estimates separately, with independence on disjoint intervals used in the
proof of the *Variance bound and its little-o consequence*. `FourPoint.lean` contains the separate algebraic
calculations for the crossing-pair and nested-pair determinants.
The paper uses their common bound, with `a = |I ∩ I'|` and `b = |I △ I'|`.
After sorting the endpoints, these are the middle gap and the sum of the outer gaps,
respectively. The paper states the joint sublevel mass bound directly and integrates it
in the length variables `a,b` to reduce the estimate to two elementary integrals.
The library uses dyadic blocks and the corresponding geometric sums for the
same bound and the same three regimes of `V_s`.

## The statement layer

`Solution.lean` is the formal statement of the paper: 145 endpoints named
`audit_<slug>`, in document order, proved from the library declarations. Adding a
result to the paper means adding its statement there first; the
design work is in the statement.

`Challenge.lean` contains exactly the nine numbered results of Section 1, with
identical statement text in `Solution.lean` and `sorry` in place of each proof.
It imports only Mathlib and contains no proved helper theorems or literature axioms.
The Comparator configuration selects these nine endpoints. The results are identified
here by human-readable mathematical names, independently of the manuscript's internal labels:

| Section 1 result | Endpoint |
| --- | --- |
| 1. *Separation by expected profiles* | `audit_main` |
| 2. *Lattice and non-lattice profile asymptotics* | `audit_profile_asymptotics` |
| 3. *Lattice/non-lattice occupation-law separation* | `audit_lattice_nonlattice_measures` |
| 4. *Finite exceptions in the two-contraction family* | `audit_finite_exceptions` |
| 5. *Small-dimension monotonicity* | `audit_small_dimension` |
| 6. *Finiteness of the critical set* | `audit_finite_critical_set` |
| 7. *Minkowski reconstruction* | `audit_reconstruction` |
| 8. *Lattice/non-lattice compact-image separation* | `audit_lattice_nonlattice_sets` |
| 9. *Two-contraction compact-image separation* | `audit_two_contraction_sets` |

The expected profile is defined by `e^{2st} 𝔼 C_{e^{-t}}(W_*μ)`.
`expectedProfile_eq_H` identifies it with the internal smoothing formula in Solution.
The two-contraction pair `(K_p, μ_p)` is selected by its attractor and measure invariance
equations in `IsTwoContractionNatural`. Hutchinson's theorem, proved in the library,
supplies the pair, and `twoContraction_natural` identifies it with the library's natural
measure. `meanProfile` is the limit of the expected-profile averages, not a closed-form
substitute. `audit_finite_exceptions` proves convergence to that limit. Derivatives
are transported using equality on a neighbourhood of each interior parameter.

`levelSet_finite` strengthens the internal countability result: positivity at the chosen
parameter and the limit zero at p=0 bound the level set away from zero. Compactness
and the absence of interior accumulation points then give finiteness. The challenge
states monotonicity on every open interval without critical points, which includes
each component of the complement of the critical set.

Compact images are points of the Hausdorff hyperspace with its Borel sigma-algebra.
The cut-off probability is defined by its normalised triangular density. Its probability
fallback is irrelevant for positive radii, as `cutoffProbability_eq` proves. The
reconstruction endpoint states both almost-sure weak convergence and Borel recovery.
The small-dimension set endpoint supplies a threshold for both strict monotonicity
and compact-image separation; strict monotonicity also gives the occupation conclusion.

The older homogeneous, paired-example and countability endpoints remain proved in
Solution as special cases and internal results. They are no longer Challenge endpoints.
Run `./comparator-audit.sh` on Linux for the sandboxed audit, or pass
`--local-unsandboxed` for a macOS development check. Both use the project toolchain's
Comparator and replay through Lean, NanoDa and con-ron. The separate Palomar preflight
workflow uses the registry verifier on an immutable repository commit.

**The correspondence is not one endpoint per theorem.** Several results appear both
as a bundled endpoint carrying the paper's conclusion and as individual endpoints
used by their proofs and consumers. Internal proof estimates and special cases are
also retained. The general smoothing lemma is represented by
`audit_smoothing_injective` and `audit_smoothing_nonconstant`;
`audit_thm_smoothing_injective` is a homogeneous special case.
The nine `audit_thm_*` bundles are `audit_thm_smoothing_injective`, `audit_thm_profile_asymptotics`,
`audit_thm_gaussian_four_point`, `audit_thm_variance`,
`audit_thm_fixed_dimension_profiles`, `audit_thm_fixed_dimension_profiles_lattice`,
`audit_thm_fixed_dimension_separation`,
`audit_thm_small_dimension_monotone` and `audit_thm_critical_set_finite`.
Two further endpoints restate a general Lean result in the narrower shape the tex uses:
`audit_ahlfors_named` (the internal regularity endpoint for `μ_A` and `μ_B`),
`audit_endpoint_block_mass_dyadic` (the tex needs only dyadic `β, η`,
and uses both the mass and return estimates in the proof of *Four-point integral bound*).
The library also retains the homogeneous exponential-error refinement, with its bound
and big-`O` endpoints. The paper uses only
the general convergence in *Lattice and non-lattice profile asymptotics* for *Lattice/non-lattice occupation-law separation*.
Where an endpoint is strictly more general than the tex, the
tex-shaped wrapper is the one to check the correspondence against.

Two pairs separate what the paper asserts from what its proof produces:
`audit_smoothing_injective` is injectivity of `T`, which is the literal claim, and
`audit_smoothing_kernel_trivial` is the kernel form the Fourier argument gives;
`audit_gaussian_four_point` is the pointwise bound under `Δ > 0`, and
`audit_gaussian_four_point_ae` is the almost everywhere form used internally, with
unconditional determinant positivity as recorded below.

## State

Results and displayed claims of `BrownianImagesComplete.tex`, in document order, against
the `Solution.lean` endpoint and what stands behind it. All 145 endpoints are proved.
`Challenge.lean` retains `sorry` only as the independent statement file for the nine
headline endpoints; no library or solution declaration uses `sorry`.

| Result | Endpoint | Proved by |
| --- | --- | --- |
| *Separation by expected profiles* | `audit_main` | `main`, after identifying the expected profile with `H` through `smoothing` |
| Homogeneous special case of *Lattice/non-lattice occupation-law separation* | `audit_cantor_application` | `homogeneous_application`, the general system under the open set condition, with the homogeneous measure specified by its invariance equation |
| Internal paired example, named `μ_B` | `audit_cantor_application_pair` | `homogeneous_application_pair`, with both named measures specified by their invariance equations and the paired ratio bounds derived in the proof |
| countability of exceptional homogeneous parameters | `audit_exceptional_parameters_countable` | `exceptionalParameters_countable` |
| *Minkowski reconstruction* | `audit_minkowski_reconstruction` | `System.IsNatural.minkowskiReconstruction`, under the open set condition; the non-lattice key-renewal limit and the lattice finite-delay periodic limit both feed the generation-cylinder quotient argument, giving pathwise recovery and a measurable reconstruction map from the compact Brownian image |
| Borel recovery from the pathwise tube limit | `audit_borel_reconstruction_of_pathwise` | `MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise` |
| transfer from occupation-law singularity to compact-image-law singularity | `audit_brownianImageLaw_mutuallySingular_of_pathwise` | `MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction`; `brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio` gives the direct self-similar generation-ratio form |
| Homogeneous special case of *Lattice/non-lattice compact-image separation* | `audit_cantor_set_application` | `MinkowskiReconstruction.homogeneous_brownianImage_application`: the homogeneous source is reconstructed directly from its one-delay renewal equation, the non-lattice source, under the open set condition, by the general reconstruction theorem, and occupation-law singularity descends to mutual singularity of the compact-image laws |
| Internal paired-set example, named `K_B` | `audit_cantor_set_application_pair` | `MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional` |
| *Neighbourhood union and scaling identities* | `audit_tube_union_scaling` | `tubeCutoff_compactUnion`, `tubeMass_translate_dilate` |
| *Elementary neighbourhood-defect bounds* | `audit_tube_defect_elementary` | `tubeDefect_nonneg`, `tubeDefect_le_pairwiseTubeOverlapAreaSum` |
| *Moments of Brownian neighbourhood area and mass* | `audit_tube_moments` | `System.IsNatural.tubeMoments`, under the open set condition; discrete-martingale maximal estimates give every unit Brownian-radius moment, the stopping cover supplies the stated upper moments, and classical Ahlfors regularity under the open set condition the positive lower mean |
| *Neighbourhood overlap and defect bounds* | `audit_tube_overlap` | `System.IsNatural.tubeOverlap_of_crossPhi_bound`, under the open set condition, taking the prescribed cross-correlation exponent `η ∈ (0,1-s)` as input and retaining it in the bound `C r^{2-2s+2η}`; the Gaussian-gap estimate for the stopping cylinders at temporal scale `r²`, *Brownian overlap bound for stopping cylinders*, counted through *Count of nearby stopping-cylinder pairs* and summed dyadically, gives the pairwise overlap bound, and `Minkowski.DefectExpectation` the defect bound with integrability |
| *Renewal asymptotics for the mean neighbourhood profile* and its shift relation | `audit_tube_renewal` | `System.IsNatural.tubeRenewal_bounds_shift`; positive uniform mean bounds and invariance under every half-logarithmic shift as the real argument tends to infinity, deduced from the internal constant and uniform periodic limits |
| *Concentration of the neighbourhood profile* | `audit_tube_concentration` | `System.IsNatural.tubeVarianceConcentration`, under the open set condition; the square of the internal centred-norm bound from `tubeConcentration` is the variance bound, with constants `C²` and `2γ`, and Borel--Cantelli gives each fixed grid |
| the ambient σ-algebra on `𝒫(ℝ²)` | `audit_borel_eq_giry` | `borel_probabilityMeasure_eq_giry` |
| occupation has full mass | `audit_isProbabilityMeasure_occupation` | `IsPlanarBrownian.ae_isProbabilityMeasure_occupation` |
| `Law(W_*μ)` has total mass one | `audit_isProbabilityMeasure_occupationLaw` | `isProbabilityMeasure_occupationLaw`, for every process `W`: the push-forward of a probability measure is a probability measure |
| the law of the compact Brownian image has total mass one | `audit_isProbabilityMeasure_brownianImageLaw` | `isProbabilityMeasure_brownianImageLaw`, for every process `W` |
| occupation is measurable | `audit_aemeasurable_occupation` | `IsPlanarBrownian.aemeasurable_occupationProb` |
| Ahlfors regularity, cited from Falconer | `audit_ahlfors` | `System.OpenSetCondition.exists_isAhlforsClosed`, under the open set condition; proved internally rather than assumed as an axiom |
| the two Ahlfors ball conventions | `audit_ahlfors_conventions` | `IsAhlforsClosed.isAhlfors` |
| internal Ahlfors regularity for `μ_A`, `μ_B` | `audit_ahlfors_named` | `exists_isAhlfors_homogeneous_pair` |
| *Gaussian reduction of the expected correlation integral* | `audit_gaussian_reduction` | `gaussian_reduction` |
| *Frostman measures and Gaussian reduction*, atomlessness of `μ` | `audit_measure_singleton` | `IsFrostman.measure_singleton` |
| *Frostman measures and Gaussian reduction*, atomlessness of `dΦ` | `audit_pairLaw_noAtoms` | `pairLaw_measure_singleton` |
| *Frostman measures and Gaussian reduction*, continuity of `Φ` | `audit_phi_continuous` | `continuous_phi` |
| *Frostman condition*, the two ball conventions | `audit_frostman_conventions` | `IsFrostman.isFrostmanOpen`, `IsFrostmanOpen.isFrostman` |
| *Frostman bound for the correlation integral* | `audit_phi_le` | `phi_le` |
| *Kernel representation of the expected profile*, rescaled with `r = exp(-t)` | `audit_smoothing` | `smoothing` |
| *Frostman measures and Gaussian reduction*, `φ` integrable and `∫φ > 0` | `audit_kern_integrable` | `kern_integrableOn`, `integral_kern_pos` |
| Uniform continuity of the expected profile, following its kernel representation | `audit_profile_uniform_continuity` | `profile_uniformContinuous` |
| *Self-similar correlation recursion* | `audit_renewal_recursion` | `phi_recursion_cross`, with the cross term `Φ_×` of *Self-similar correlation recursion* |
| *Rescaled correlation recursion* | `audit_g_recursion` | `g_recursion_cross` |
| *Cross-piece mass decay* | `audit_crossPhi_bound` | `System.StrongOpenSetCondition.exists_crossPhi_bound`: `0 ≤ Φ_×(δ) ≤ C δ^{s+η}` for `0 < δ ≤ 1`, with `0 < η < 1 - s` |
| *Renewal and asymptotics*, the strongly separated case | `audit_crossPhi_separated` | `crossPhi_eq_zero_of_stronglySeparated`: the cross term vanishes below the separation gap |
| Bounded overlap and interval partition in *Open set condition estimates*, citing Hutchinson (1981), proof of Theorem 5.3(1) | `audit_stopping_overlap` | `System.IsFeasible.exists_point_multiplicity_bound` and `System.IsFeasible.exists_stopping_coloring`, under the open set condition: one integer `M` bounds the multiplicity of the stopping family at every threshold `0 < u ≤ 1`, and the family is coloured with `M` colours so that intervals of one colour have disjoint interiors |
| The boundary-mass estimate and its pairwise consequence within the proof of *Cross-piece mass decay* | `audit_cross_piece_mass` | `System.StrongOpenSetCondition.exists_cross_piece_bound`: the boundary estimate and the stronger individual bound `(μ_i × μ_j){|x-y| ≤ δ} ≤ C δ^{s+η}`, for `i ≠ j`, with one exponent `0 < η < 1 - s`. Summing with weights `p_i p_j` gives the paper's aggregate bound *Cross-correlation decay estimate* |
| Schief's theorem, cited in *Introduction* | `audit_schief` | `System.openSetCondition_iff_strongOpenSetCondition`: the open set condition is equivalent to the existence of a feasible open set meeting the attractor, by the maximal neighbour count of `Schief.lean` |
| *Non-lattice renewal limit*, the renewal inputs | `audit_renewalLaw` | `isProbabilityMeasure_renewalLaw`, `integral_id_renewalLaw` |
| *Non-lattice renewal limit*, exponential moment | `audit_exists_expTransform_lt_one` | `exists_expTransform_lt_one` |
| The key renewal theorem quoted in *Renewal and asymptotics*, the renewal series | `audit_renewal_series` | `System.nonlattice_renewal_series`: `f = ∑ ϑ^{*n} * z` for a bounded continuous solution vanishing at `-∞` with a signed defect `|z(t)| ≤ C e^{-c|t|}`, in the non-lattice case, from `KeyRenewalFourier.eq_tsum_integral_comp_sub_of_bounded` |
| The key renewal theorem quoted in *Renewal and asymptotics*, non-lattice case | `audit_renewal_theorem_nonlattice` | `System.nonlattice_renewal_limit`: `f(t) → m⁻¹ ∫ z`, through `System.tendsto_of_renewalEquation` and the vendored theorem |
| The key renewal theorem quoted in *Renewal and asymptotics*, lattice case | `audit_renewal_theorem_lattice` | `System.lattice_renewal_limit`: `sup_{t∈[0,ℓ]} |f(t+nℓ) - f̃(t)| → 0` for the continuous `ℓ`-periodic periodisation `f̃ = System.periodisation`, by the signed arithmetic renewal theorem `System.exists_uniform_periodic_limit_of_tubeArithmetic` at `f(2v)` and the identification `System.eq_periodisation_of_periodic_limit` |
| The key renewal theorem quoted in *Renewal and asymptotics*, bundled | `audit_key_renewal_theorem` | `System.key_renewal_theorem` |
| *Renewal shift limit* | `audit_renewal_shift` | `System.renewal_shift`: the paper's cutoff argument, with the two cases of the key renewal theorem |
| *Non-lattice renewal limit* | `audit_non_lattice_limit` | `non_lattice_limit`, under the open set condition; the exponential tail of the renewal defect `z` is the cross-term bound in *Renewal and asymptotics* |
| The displayed periodisation `G̃(t) = (ℓ/m) ∑_{k∈ℤ} z(t+kℓ)` before *Lattice and non-lattice renewal limits*, as a convergent series | `audit_lattice_periodisation_hasSum` | `System.IsNatural.hasSum_latticePeriodisation`: `∑_{k∈ℤ} z(t+kℓ)` converges to `(m/ℓ) G̃(t)`, by the exponential tails of `z`; this is what makes the `tsum` in `System.latticePeriodisation` the paper's sum |
| *Lattice and non-lattice renewal limits*, lattice case | `audit_lattice_periodisation_limit` | `System.IsNatural.lattice_periodisation_limit`: `G̃` is continuous, strictly positive and `ℓ`-periodic, and `G - G̃ → 0`. The periodic limit of `System.lattice_G_limit` is identified with `G̃` by `System.IsNatural.eq_latticePeriodisation_of_periodic_limit`, which telescopes the renewal equation along the lattice (`tendsto_sum_renewalDefect_of_periodic`) |
| *Lattice and non-lattice renewal limits*, bundled | `audit_thm_renewal_limits` | `non_lattice_limit` and `System.IsNatural.lattice_periodisation_limit` |
| The unnumbered definition `c^s = 1 - 2^{-s}` in the introductory paragraph “A two-contraction example” | `audit_pairRatio` | `pairRatio_rpow`, `pairRatio_lt_half` |
| *Renewal of correlation profiles*, the homogeneous system | `audit_homogeneousSystem_facts` | `homogeneousSystem_isDimension`, `homogeneousSystem_stronglySeparated` |
| *Renewal of correlation profiles*, the paired system | `audit_pairSystem_facts` | `pairSystem_isDimension`, `pairSystem_stronglySeparated` |
| *Renewal of correlation profiles*, existence of `μ_A` | `audit_exists_cantor_measure` | `exists_unique_isNatural_homogeneousSystem` |
| *Renewal of correlation profiles*, existence of `μ_B` | `audit_exists_pair_measure` | `exists_unique_isNatural_pairSystem` |
| *Non-lattice condition* is non-lattice type | `audit_pairSystem_nonArithmetic_iff` | `pairSystem_nonArithmetic_iff` |
| Internal homogeneous periodic extension | `audit_exists_periodic_extension` | `exists_periodic_extension_of_shift` |
| Internal homogeneous profile `G̃_A` | `audit_exists_periodic_profile` | `homogeneous_periodic_profile` |
| *Renewal of correlation profiles*, non-constancy of the homogeneous periodic profile as a consequence of *Non-convergence of the lattice correlation profile* | `audit_cantor_nonconstant` | `HomogeneousNonconstancy.homogeneous_G_nonconstant_on_tail`, an independent density proof retained in the library |
| *Non-convergence of the lattice correlation profile* | `audit_lattice_nonconvergence` | `System.IsNatural.latticePeriodisation_nonconstant`: the periodisation `G̃` is non-constant. The paper compares two phases directly, using the translated word maps `S_{ij}` and `S_{ji}` and the Ahlfors lower bound. The library argues by contradiction: a constant `G̃` makes `G` converge, since `G - G̃ → 0`; a limit of `G` gives constant symmetric partial sums of `z` (`tendsto_sum_renewalDefect`) and a Lipschitz bound on `Φ_×` (`crossPhi_sub_le_of_tendsto_G`); `IsFeasible.map_comp_ne` and `sq_mul_phi_le_crossPhi_sub` then give `Φ(δ) = O(δ)`, contradicting Ahlfors regularity for `s < 1` (`System.IsNatural.not_tendsto_G_of_lattice`) |
| *Gaussian smoothing and distributional separation*, the lattice limit `H̃_μ^s = T G̃` | `audit_smoothed_lattice_periodisation` | `System.IsNatural.smoothed_latticePeriodisation`: `T G̃` is continuous, `ℓ/2`-periodic, strictly positive, non-constant by *Non-convergence of the lattice correlation profile* and *Injectivity of Gaussian smoothing*, and `H_μ^s - T G̃ → 0` |
| The periodic smoothing operator in *Gaussian smoothing and distributional separation*, `Tg` is `ℓ/2`-periodic | `audit_smoothOp_periodic` | `smoothOp_periodic` |
| The periodic smoothing operator in *Gaussian smoothing and distributional separation*, `Tg` continuous and `ℓ/2`-periodic | `audit_smoothOp_continuous_periodic` | `continuous_smoothOp` |
| *Gaussian smoothing and distributional separation*, the coefficient is Mathlib's | `audit_fourierCoeffP_eq_fourierCoeffOn` | `fourierCoeffP_eq_fourierCoeffOn` |
| *Fourier multiplier identity*, the Fourier identity | `audit_fourier_multiplier` | `fourierCoeffP_smoothOp` |
| *Gamma multiplier formula*, the evaluation | `audit_gamma_multiplier` | `multInt_eq_gammaMult` |
| *Gamma multiplier formula*, non-vanishing | `audit_gammaMult_ne_zero` | `gammaMult_ne_zero` |
| *Injectivity of Gaussian smoothing*, multiplier | `audit_multInt_ne_zero` | `multInt_ne_zero` |
| *Injectivity of Gaussian smoothing*, Fourier uniqueness | `audit_fourier_uniqueness` | `eq_zero_of_fourierCoeffP_eq_zero` |
| *Injectivity of Gaussian smoothing* | `audit_smoothing_injective` | `smoothOp_injective` |
| *Injectivity of Gaussian smoothing*, kernel form | `audit_smoothing_kernel_trivial` | `smoothOp_eq_zero` |
| *Injectivity of Gaussian smoothing*, consequence | `audit_smoothing_nonconstant` | `smoothOp_nonconstant` |
| Homogeneous special case of *Injectivity of Gaussian smoothing*, bundled | `audit_thm_smoothing_injective` | `thm_smoothing_injective_homogeneous` |
| *Gaussian smoothing and distributional separation*, positivity of `H̃_A^s` | `audit_smoothOp_pos` | `smoothOp_pos` |
| *Lattice and non-lattice renewal limits*, the non-lattice limit *Non-lattice renewal limit*, applied to the two-map system of `μ_B` | `audit_gb_limit` | `homogeneous_gb_limit` |
| *Lattice and non-lattice profile asymptotics*, non-lattice case, as applied to a non-lattice `μ` in the proof of *Lattice/non-lattice occupation-law separation* | `audit_profile_asymptotics_non_lattice` | `profile_asymptotics_nonLattice` |
| *Lattice and non-lattice profile asymptotics*, non-lattice case, with the expected profile written as the normalised correlation integral of *Normalised expected correlation profile* | `audit_non_lattice_correlation_limit` | `non_lattice_correlation_limit` |
| Internal homogeneous exponential-error bound | `audit_profile_asymptotics_lattice` | `exists_lattice_bound` |
| Internal homogeneous exponential error in big-`O` shape | `audit_profile_asymptotics_lattice_bigO` | `exists_lattice_bound` |
| *Lattice/non-lattice occupation-law separation*, homogeneous correlation oscillation | `audit_lattice_correlation_oscillation` | `homogeneous_lattice_correlation_oscillation`; the paper obtains this directly from *Lattice and non-lattice profile asymptotics* |
| *Lattice and non-lattice profile asymptotics*, general dichotomy | `audit_thm_profile_asymptotics` | `lattice_profile_asymptotics_nonconstant`, `non_lattice_limit`, `profile_asymptotics_nonLattice`: the lattice limit is `T G̃` for the periodisation `G̃` of `audit_lattice_periodisation_limit`, non-constant by *Non-convergence of the lattice correlation profile*, with *Injectivity of Gaussian smoothing* carrying non-constancy through `T` |
| Internal homogeneous refinement and *Lattice and non-lattice profile asymptotics* for the non-lattice two-map system of `μ_B`, bundled two-map consequences | `audit_homogeneous_profile_asymptotics` | `homogeneous_thm_profile_asymptotics` |
| *Separation by expected profiles* for two non-lattice measures whose limits in *Lattice and non-lattice profile asymptotics* differ, the step taken in the proof of *Finite exceptions in the two-contraction family* | `audit_non_lattice_separation` | `non_lattice_separation`, both systems under the open set condition |
| Independence in the proof of *Variance bound and its little-o consequence* | `audit_disjoint_increments_indep` | `disjoint_increments_indep` |
| Gaussian return bound used in the proof of *Four-point integral bound* | `audit_gaussian_four_point` | `gaussian_four_point` |
| Internal almost everywhere Gaussian return bound | `audit_gaussian_four_point_ae` | `gaussian_four_point_ae` |
| Internal Gaussian bounds and independence, bundled | `audit_thm_gaussian_four_point` | `gaussian_four_point_bundled` |
| Block mass and return estimates in the proof of *Four-point integral bound* | `audit_endpoint_block_mass` | `endpoint_block_mass` |
| Dyadic form of the mass and return estimates for *Four-point integral bound* | `audit_endpoint_block_mass_dyadic` | `endpoint_block_mass_dyadic` |
| *Four-point integral bound* | `audit_four_point_integral` | `four_point_integral_uniform`: one constant depending only on `s,A`, chosen before the measure, probability space and Brownian process |
| *Variance bound and its little-o consequence* | `audit_variance` | `variance_four_point_uniform`, with the same uniform quantifier order |
| *Variance bound and its little-o consequence*, final assertion | `audit_varScale_isLittleO` | `varScale_div_tendsto_zero` |
| *Variance bound and its little-o consequence*, bundled | `audit_thm_variance` | `variance_bundled_uniform`, including the little-o consequence |
| *Variance of the normalised empirical profile* | `audit_y_variance` | `y_variance` |
| *Almost-sure convergence on rational grids* | `audit_grid_convergence` | `grid_convergence` |
| *Monotone interpolation between grid points* | `audit_monotone_fill` | `monotone_fill` |
| *Uniform almost-sure concentration* | `audit_uniform_concentration` | `uniform_concentration` |
| *Uniform concentration and mutual singularity*, the oscillation `d_A` | `audit_lattice_gap` | `smoothOp_gap` |
| *Base-five correlation profiles* | `audit_base_five_profiles` | `baseFive_profiles`: the values *Base-five correlation values* at every scale `5⁻ⁿ`, proved in the paper by counting touching cylinders and in Lean by equivalent first-digit recursions; profile separation follows from the distinct continuous periodic limits, with `g₁(0) = 3/2 ≠ 1 = g₂(0)`, and *Injectivity of Gaussian smoothing*. The paper cites *Lattice and non-lattice renewal limits* and the smoothing step of *Lattice and non-lattice profile asymptotics*; the library computes the limits explicitly and applies dominated convergence in *Kernel representation of the expected profile*. |
| *Base-five correlation profiles*, the first display after it | `audit_base_five_occupation_laws` | `MinkowskiReconstruction.baseFive_occupationLaw_mutuallySingular`: *Separation by expected profiles* for the two natural measures, Frostman by the open set condition |
| *Base-five correlation profiles*, the second display after it | `audit_base_five_image_laws` | `MinkowskiReconstruction.baseFive_brownianImageLaw_mutuallySingular`: *Minkowski reconstruction* for both systems under the open set condition, and the descent of the occupation-law singularity through the Borel reconstruction map |
| *Identical correlation integrals*, the signed convolution | `audit_conv_reflect` | `conv_reflect_eq_map_sub` |
| *Homometric non-isometric attractors* | `audit_homometric_example` | `homometric_example`, with the non-isometry of the attractors from `HomometricMeasures.isEmpty_isometryEquiv` |
| *Correlation profiles*, existence and uniqueness of `K_p` and `μ_p` | `audit_exists_fixed_dimension_measure` | `System.exists_unique_isNatural` for `fixedSystem`, the system `x ↦ λ₁x`, `x ↦ λ₂x + 1 - λ₂` with `λ₁ = p^{1/s}`, `λ₂ = q^{1/s}`, whose dimension is `s` (`fixedSystem_isDimension`) |
| *Separation of image laws*, `J(p) = (2pq)^{-1} ∫₀¹ δ^{-s} dC^×_δ(μ_p)` | `audit_fixed_moment_natural` | `fixedMoment_eq_natural`: `fixedMoment` is the double Bernoulli integral of `Z_p^{-s}` over the coding, and the law of the coded point is `μ_p` (`map_fixedCode_twoBern`, by Hutchinson uniqueness) |
| *Monotonicity for small dimension*, `J(p) ≥ 1` | `audit_fixed_moment_ge_one` | `one_le_fixedMoment`, since `Z_p ≤ 1` |
| *Derivative formula for the mean profile* | `audit_log_derivative_mean` | `hasDerivAt_entropyFactor` for `κ = (pq/E)'/(pq/E)`, and `hasDerivAt_fixedMean` for the mean, in the product form `H̄_s' = C_s (pq/E)(κ J(p) + J'(p))` with `C_s = 2^{1-s} Γ(1-s)`, wherever `J(p)` is differentiable |
| *Entropy-factor inequalities* | `audit_entropy_factor` | `kappa_pos`, `kappa_ge_of_le`, `kappa_ge_of_ge`: `Φ = q² log(1/q) - p² log(1/p)` is strictly concave on `[0, 1/2]` with `Φ(0) = Φ(1/2) = 0` (`strictConcaveOn_kappaNum`), hence positive between; `log(1/q) ≥ p` and `q log(1/q) ≤ p` give the explicit bound for `p ≤ 1/50`; and the constant `c` for `[p₁, 1/2)` is read off the chord of the concave `Φ` from `(p₁, Φ(p₁))` to `(1/2, 0)` |
| *Initial-symbol decomposition* | `audit_leading_ones` | `hasSum_leadingTerm`: the first-letter recursion `leadingAux_rec` of the Bernoulli double integral, with the remainder `qᴺ h_N` bounded |
| *Main approximation to the cross-term moment* | `audit_main_term` | `mainTerm_eq`, with `T(p) = log(1/b) = log(1/q)/s` (`fixedT`) |
| Internal combination of *Derivative bound for the main term*, *Derivative bound for the remainder*, and *Second-derivative bound for small dimension* | `audit_fixed_dimension_derivative_bounds` | `Section9Estimates.derivative_bounds`: `hasDerivAt_fixedMoment_small` combines the main-term and remainder estimates; `fixedMoment_second_derivative` proves the second bound, including existence of the derivatives. All constants and parameter ranges agree with the paper. |
| *Derivative bound for the main term* | `audit_main_term_derivative` | `exists_hasDerivAt_mainTerm`: termwise differentiation of the sum, internally `mainS` (`hasDerivAt_mainS`), the Riemann-sum comparison against the total variation of `g` (`abs_tsum_sub_integral_le`), the integrals of `f'`, `x f''`, `g`, `g'` on `(T(p), ∞)` (`MainTermIntegrals`), and `s ∫_{T(p)}^∞ f ≤ 2.3` from `f ≤ x^{-s}` on `(0, 1]` and `f ≤ (1 - e^{-1})^{-s} e^{-sx}` on `[1, ∞)`; the constant is `6` |
| *Derivative bound for the remainder* | `audit_remainder_derivative` | `exists_hasDerivAt_fixedMoment`: on the disc `|z - p| ≤ p/2` the level sums `Λ_n^{(m)}` converge uniformly to holomorphic `Λ_n` with *Holomorphic kernel-limit bound* (`norm_kernelLimit_sub_le`), `Δ = Λ - J₀` is holomorphic (`differentiableOn_complexDelta`) with `sup_U |Δ| ≤ 1296 s λ_{1,max} p^{-1-s}` (`norm_complexDelta_le`), Cauchy's estimate gives `Δ'` (`norm_deriv_complexDelta_le`), and `Δ(x) = J(x) - J₀(x)` on the real diameter by dominated convergence of the level sums (`complexDelta_ofReal`) |
| *Second-derivative bound for small dimension* | `audit_second_derivative_small_s` | `fixedMoment_second_derivative`: on `|z - p| ≤ 5·10⁻⁵` both contractions have modulus at most `γ ≤ 1/12` (`gammaQ_le`), the cross kernel is within `18 s γ` of `1` by the mean value inequality for `ζ ↦ ζ^{-s}` on `|ζ - 1| ≤ 1/2` (`norm_crossKernelC_sub_one_le`), the level sums converge to `Λ(z)` with `|Λ(z) - 1| ≤ 32 s γ` (`norm_crossLimit_sub_one_le`), `Λ(z) = J(x)` on the real diameter (`crossLimit_ofReal`), and Cauchy's estimate for the second derivative, with constants `18`, `32` and `10¹¹` as in the paper |
| the symmetry `J(p) = J(1-p)` in the proof of *Small-dimension monotonicity* | `audit_moment_symmetric_derivative` | `deriv_fixedMoment_half`: `Λ(1-z) = Λ(z)` on the disc around `1/2` (`crossLimit_one_sub`), since flipping every letter reflects the coded points up to the base point (`one_sub_cpointSeq_eq`) and the cross kernel is reflection invariant, so the level sums of `z` and `1 - z` differ by `O((γB²)^m)`; the complex derivative at `1/2` then vanishes, and the real derivative is its real part |
| *Small-dimension monotonicity* | `audit_small_dimension_monotone` | `exists_strictMonoOn_fixedMean`: `|J'(p)| < κ(p)` on `(0, 10⁻⁴]` from the entropy and first-derivative bounds and `(3p/2)^{1/s} ≤ (3p/2)⁴` (`abs_deriv_fixedMoment_lt_kappa_small`), and on `[10⁻⁴, 1/2)` from the second-derivative bound, `J'(1/2) = 0` and the mean value theorem (`abs_deriv_fixedMoment_lt_kappa_large`); `s₀ = min(2·10⁻⁵, c/10¹¹)` for the constant `c` of *Entropy-factor inequalities* at `p₁ = 10⁻⁴`, since `γ ≤ 2 s²/r²` (`gammaQ_le_sq`); then `strictMonoOn_of_deriv_pos` through *Derivative formula for the mean profile* and `J(p) ≥ 1` |
| *Finiteness of the critical set*, the strict increase on `(0, p₀]` | `audit_critical_set_finite` | `exists_strictMonoOn_fixedMean_small`: `|J'(p)| p (1 - log p) ≤ (6 + 3000 s (3/2)^{1/s}) √p (1 - log p)` for `p ≤ 1/50` (`abs_deriv_fixedMoment_mul_le`, using `1/s - 1 - s ≥ 1/2`) and `√p (1 - log p) ≤ 5 p^{1/4}` (`sqrt_mul_one_sub_log_le_rpow`), so `p₀ = min(1/50, (0.17/C)⁴)` |
| *Finiteness of the critical set*, bundled | `audit_thm_critical_set_finite` | the endpoint above and `criticalSet_finite`: `D_s ⊆ [p₀, 1/2]` by the positive derivative on `(0, p₀)` (`exists_deriv_fixedMean_pos_small`), and an infinite subset of a compact interval has an accumulation point (`Set.Infinite.exists_accPt_of_subset_isCompact`), which `not_accPt_criticalSet` forbids |
| *Small-dimension monotonicity*, bundled with its second sentence | `audit_thm_small_dimension_monotone` | `audit_small_dimension_monotone` and `audit_fixed_dimension_laws`; distinct parameters have distinct means by strict monotonicity |
| the remark after *Small-dimension monotonicity*, the maximum of the mean at `p = 1/2` alone for `s ≤ s₀` | `audit_small_dimension_maximum` | `exists_strictMonoOn_fixedMean` and `fixedMean_lt_half_of_strictMonoOn`: strict monotonicity on `(0, 1/2]` and the symmetry `fixedMean_symm` |
| *Correlation profiles in the two-contraction family*, *Two-contraction mean formula* | `audit_fixed_dimension_mean` | `fixedSystem_tendsto_avg_H`: `System.IsNatural.tendsto_avg_H` under the open set condition (`fixedSystem_openSetCondition`, from strong separation with gap `1 - λ₁ - λ₂`), with `m = h(p)/s` (`fixedSystem_renewalMean`), `Φ_× = 2pq ℙ(Z_p ≤ δ)` (`fixedSystem_crossPhi`), `∫ z = 2pq J(p)/s` (`fixedSystem_integral_renewalDefect`, by Tonelli) and `∫ φ = 2^{-s} Γ(1-s)`; the expected profile is `H` by `smoothing`. The paper computes the mean for both cases together, averaging the renewal limits and lattice periodisation and then the smoothing formula. |
| *Correlation profiles in the two-contraction family*, the non-lattice limit | `audit_fixed_dimension_non_lattice` | `fixedSystem_tendsto_H_nonLattice`, through *Non-lattice renewal limit*, with `log λ₁/log λ₂ ∉ ℚ` read as non-arithmeticity by `fixedSystem_nonArithmetic_iff` |
| Internal lattice Fourier expansion of the expected profile of `μ_p`, beyond *Correlation profiles in the two-contraction family* | `audit_fixed_dimension_periodic` | `fixedSystem_periodic`: the Fourier transform of the inhomogeneous term (`fixedSystem_integral_renewalDefect_char`, by Fubini), the coefficients of the lattice limit from the renewal average with a character (`System.IsNatural.fourierCoeffP_latticeLimit`), the multiplier *Gamma multiplier formula*, the bound `‖Γ(1-ζ)‖ ≤ Γ(2-s)/‖1-ζ‖` for absolute summability (`summable_norm_fixedDimCoeff`), and Fourier inversion |
| *Two-contraction correlation series* | `audit_fixed_dimension_correlation` | `fixedSystem_correlation`: `S_μ(r) = ∫ g_r(|x - y|) d(μ×μ)` by *Gaussian reduction formula*, Hutchinson's identity in both coordinates on `μ × μ` (`System.IsNatural.lintegral_prod_eq_double_sum`) gives the recursion `T(c) = p² T(cλ₁) + q² T(cλ₂) + 2pq 𝔼 g_r(c Z_p)` for `T(c) = ∫ g_r(c|x - y|)` (`corrScale_recursion`), iterated along the antidiagonals of `ℕ²` with Pascal's rule (`sum_antidiagonal_succ_pascal`); `0 ≤ T ≤ 1` bounds the remainder by `∑_{j+k=m} C(m,j) p^{2j} q^{2k} = (p² + q²)^m`, uniformly in `r`, and the series of non-negative terms sums to `T(1)` along the triangles `{j + k < m}` |
| Internal remainder bound `(p² + q²)^m` for *Two-contraction correlation series*, uniform in `r` | `audit_fixed_dimension_correlation_remainder` | `fixedSystem_correlation`, as in the row above |
| *Correlation profiles in the two-contraction family*, bundled | `audit_thm_fixed_dimension_profiles` | `audit_fixed_dimension_correlation`, `audit_fixed_dimension_mean` and `audit_fixed_dimension_non_lattice` |
| Internal bundle with the remainder bound and the lattice expansion | `audit_thm_fixed_dimension_profiles_lattice` | `audit_fixed_dimension_correlation_remainder`, `audit_fixed_dimension_mean`, `audit_fixed_dimension_non_lattice` and `audit_fixed_dimension_periodic`, the lattice span from `System.nonArithmetic_or_exists_lattice` |
| the mean symmetry in *Correlation profiles* and `J(p) = J(1-p)` in *Monotonicity for small dimension* | `audit_fixed_dimension_symmetry` | `fixedMoment_symm`, `fixedMean_symm`: flipping every letter in the level sums reflects the coded points up to the base point (`one_sub_cpointSeq_eq`), the kernel is Lipschitz on `[0,1]²` (`abs_rpow_fixedCross_sub_le`), so the level sums of `p` and `1-p` differ by `O(γ^m)` (`norm_levelSum_one_sub_sub_le'`), and both converge to the moments (`tendsto_levelSum_ofReal`) |
| *Holomorphic level sums and their expectation* | `audit_level_sums` | `levelSums`: for every jointly holomorphic kernel on the parameter disc and open convex coding domain, uniform convergence to a holomorphic limit, the stated uniform level-sum bound with `B` equal to the disc supremum, and the double integral against the natural measure at every real parameter; boundedness of the coding domain is not needed |
| *Analyticity in the two-contraction family* | `audit_fixed_dimension_analyticity` | `analyticAt_fixedMoment`, `analyticAt_fixedMean`: on the disc `|z - p₀| ≤ r` of `GoodRadius` the branches are Lipschitz (`norm_ca_sub_le`), the coded points move by at most `C|z - p₀|` (`norm_cpointSeq_sub_le`) and stay in a neighbourhood of `[0,1]` on which every cross distance has real part at least `g₀/2` (`re_crossBase_ge_of_mem`), the level sums converge uniformly to a holomorphic `Λ(z)` (`incrementBound_disc`, `differentiableOn_crossLimit_disc`) equal to `J(x)` on the real diameter (`crossLimit_eq_fixedMoment_of_mem`), and the restriction of a holomorphic function to the real line is real analytic (`AnalyticAt.restrictScalars`); multiplying `J(p)` by `2p(1-p)` gives the paper's cross-term integral, and `E` is analytic by `analyticAt_log` |
| *Range of the mean profile* | `audit_fixed_dimension_range` | continuity from analyticity, positivity from `J(p) ≥ 1`; the limit `0` from `J(p) ≤ 2^s J₀(p)` once `λ₁ ≤ (1-λ₂)/2` (`fixedMoment_le_mainTerm`, through *Initial-symbol decomposition*), `J₀(p) ≤ (s/q)(∫_{T(p)}^∞ f + T(p) f(T(p)))` (`mainTerm_le`) and `s ∫_{T(p)}^∞ f ≤ s/(1-s) + 1.59` (`mul_integral_mainF_le'`), so `J(p)` is bounded near `0` (`fixedMoment_le_of_small`), while `pq/h(p) ≤ 1/log(1/p)` (`entropy_ge`) |
| Internal consequence of *Finite exceptions in the two-contraction family*: an uncountable subfamily with pairwise singular laws | `audit_fixed_dimension_subfamily` | `exists_uncountable_injOn_fixedMean`, by the intermediate value theorem, uncountable because the image of the mean is an interval of positive length, and `audit_fixed_dimension_laws` |
| *Finite exceptions in the two-contraction family*, the analytic assertions | `audit_fixed_dimension_separation` | `not_accPt_criticalSet`, `strictMono_or_anti_of_ne_zero`, `not_accPt_levelSet`: the identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` on `(0,1)` for the derivative and for `H̄_s - H̄_s(p₁)`, non-constancy from the limit `0` at `0` and positivity at `1/2` (`fixedMean_not_const`), the sign of the derivative on an interval free of critical points by the intermediate value theorem |
| the paragraph after *Finite exceptions in the two-contraction family*, the interval `(1/2 - ε_s, 1/2)` | `audit_fixed_dimension_eps` | `exists_eps_strictMono`, `ε_s` from the isolated point `1/2` |
| Internal weaker consequence: countability and local finiteness of the exceptional level set | `audit_fixed_dimension_level_countable`, `audit_fixed_dimension_laws` | `levelSet_countable`, from the finiteness of a level set on each `[1/(n+2), 1/2]`; every interval bounded away from zero is contained in one such interval, and `audit_fixed_dimension_laws` gives both singularities outside the level set |
| *Finite exceptions in the two-contraction family*, the singular laws | `audit_fixed_dimension_laws` | `MinkowskiReconstruction.fixedSystem_occupationLaw_mutuallySingular`, `fixedSystem_brownianImageLaw_mutuallySingular`: distinct Cesàro means give separated profiles (`exists_ge_abs_sub_of_tendsto_avg`), *Separation by expected profiles* with Frostman from the open set condition, and the pathwise tube reconstruction of both systems through the common Borel reconstruction map |
| *Finite exceptions in the two-contraction family*, bundled | `audit_thm_fixed_dimension_separation` | the two endpoints above |

Proved outside the endpoint list, and load-bearing for it: the kernel layer
(`kern_pos`, `logKern_eq`, `logKern_le_exp_neg_mul_abs`, `logKern_integrable`), the
occupation layer (`continuous_plane_of_coord`, `IsPlanarBrownian.ae_continuous`,
`measurable_pathMap`, `IsPlanarBrownian.ae_occupationProb_toMeasure`), the empirical
layer (`corr_mono`, `Yprofile_le_of_le`, `measurable_corr`, `measurable_Yprofile`), the
period lattice
(`exists_nat_sub_mem_Ico`, `shift_add_nsmul`, `exists_periodic_extension`), the identification `phi_eq_pairLaw` of `Φ` as the
distribution function of `dΦ`, the homometric
layer (`strong_separation`, `homSystem`,
`homSystem_stronglySeparated`, `tHom_mem_Ioo`, `six_mul_rpow_tHom`), and the pairing
determinants (`crossing_det`, `nested_det`).

## Fidelity boundary

What a formal statement can quietly get wrong here is the ambient setting, not the
inequality.  Seven traps, and how each is closed.

- **The open set condition enters through Schief's theorem.**  The paper assumes the
  open set condition and, citing Schief, chooses a feasible open set meeting the
  attractor whenever a proof needs one.  The library's proofs take that set as their
  hypothesis, `System.StrongOpenSetCondition K`, and Schief's theorem is proved in
  `Schief.lean` (`audit_schief`), so every endpoint carries the paper's hypothesis
  `System.OpenSetCondition` and derives the strong form from the attractor of its natural
  measure.  `System.IsFeasible` carries the paper's definition of a feasible open set,
  including boundedness, which no proof uses.
- **Every measure of the paper lives on `[0,1]`, and `IsFrostman` says so.** The support
  condition `μ ([0,1])ᶜ = 0` is a field of `IsFrostman`, not a side hypothesis, because
  `occupation` reads the time through `Real.toNNReal`: a measure charging the negative
  half-line would have its occupation measure collapse onto `W₀`, and
  `audit_four_point_integral`, `audit_variance` and `audit_uniform_concentration` would
  all be false.  `System.IsNatural` carries the same condition through its attractor,
  and `IsNatural.support_Icc` extracts it; `IsNatural.isProbabilityMeasure` extracts the
  other instance an endpoint would otherwise ask for twice.
- **The four times of *The four-point variance bound* are non-negative by type.** `jointReturn` takes
  `ℝ≥0` arguments, so no clipping hides in `audit_gaussian_four_point`.  Where the
  quadruple is integrated against `μ⁴` the times are read through `Real.toNNReal`, which
  is the identity `μ⁴`-almost everywhere because `μ` sits on `[0,1]`; the block bound of
  `audit_endpoint_block_mass`, which quantifies over quadruples rather than integrating,
  carries `0 ≤ x₁` explicitly.
- **Frostman with `0 < s` is what removes the diagonal.** Real division by zero is `0`
  in Lean, so the integrand of the Gaussian reduction formula takes the value `0`, not `1`, on
  the diagonal.  Without atomlessness the identity fails outright at `μ = δ₀`, where the
  left-hand side is `1`.  `audit_gaussian_reduction` therefore carries the Frostman
  hypothesis, and `IsFrostman.measure_singleton` proves it gives what is needed.
- **Brownian motion means continuous paths.** `IsPlanarBrownian` is built from
  `IsBrownianReal`, not `IsPreBrownianReal`: finite-dimensional laws alone do not make
  `t ↦ W t ω` measurable, and `Measure.map` returns a junk value on a map that is not
  almost everywhere measurable, a Dirac mass at an arbitrary point, which would make
  `occupationLaw` junk and every mutual-singularity statement vacuous.  That junk value
  is a probability measure, so the total-mass endpoints
  `audit_isProbabilityMeasure_occupationLaw` and
  `audit_isProbabilityMeasure_brownianImageLaw` cannot detect it; what does is
  measurability.  Continuity gives measurability of the path
  (`IsPlanarBrownian.ae_continuous`, `measurable_pathMap`) and hence full mass of the
  occupation measure itself (`audit_isProbabilityMeasure_occupation`).  Measurability of
  `ω ↦ occupationProb W μ ω` is `audit_aemeasurable_occupation`, and it is `AEMeasurable`
  rather than `Measurable` for a reason: `occupationProb W μ` is genuinely not measurable
  in general, only equal almost everywhere to the occupation measure of a jointly
  measurable modification.
- **The law lives on `𝒫(ℝ²)`, not on the measures of `ℝ²`.** `occupationLaw` is a
  measure on `ProbabilityMeasure Plane`, which is the space the paper takes laws on.
  `occupationProb` is the reading of the occupation measure as a point there, with a
  Dirac fallback off the full-mass event; `occupationProb_toMeasure` and
  `IsPlanarBrownian.ae_occupationProb_toMeasure` say the fallback never enters a
  conclusion.

Five further points where the Lean text reads differently from the tex, deliberately.

- **The periodisation is a convergent series.**  Lean's `tsum` of a non-summable
  function is `0`, so a statement about `∑' k : ℤ, z(t + kℓ)` is vacuous without
  summability.  `audit_lattice_periodisation_hasSum` proves that the series in
  `System.latticePeriodisation` converges, with sum `(m/ℓ) G̃(t)`, from the exponential
  tails of the renewal defect, and `audit_lattice_periodisation_limit` states the lattice
  conclusion of *Lattice and non-lattice renewal limits* for that sum.
- **`𝒫(ℝ²)`: the two σ-algebras agree.** Mathlib's
  `ProbabilityMeasure Plane` is measurable through the evaluations `ν ↦ ν s`, while the
  paper uses the Borel σ-algebra of the weak topology. `borel_probabilityMeasure_eq_giry`
  identifies them. Mathlib has neither a
  `BorelSpace (ProbabilityMeasure Ω)` instance nor any `borel (ProbabilityMeasure Ω) = _`
  lemma; the proof is in `WeakBorel.lean` and needs only second countability, pseudo
  metrisability and `BorelSpace`, so it is not special to `ℝ²`.
- **Frostman is stated on closed balls with arbitrary centres.** The paper uses open
  balls and centres in `[0,1]`; `IsFrostman` uses closed balls and arbitrary centres,
  which is what the Fubini step of *Frostman bound for the correlation integral* consumes. `IsFrostmanOpen` is the
  paper's shape, and `audit_frostman_conventions` proves the two agree up to the change
  of constant the paper allows itself: `A` one way, `3^s A` the other.
- **The profile-separation condition is written out.** `limsup_{v→∞} |H₁ - H₂| > 0` appears as
  `∃ ε > 0, ∀ V, ∃ v ≥ V, ε ≤ |H₁(v) - H₂(v)|`, which is the same statement for a
  non-negative function and avoids the junk value `limsup` takes on unbounded functions.
  The same rewriting turns the homogeneous `liminf < limsup` consequence of *Lattice and non-lattice profile asymptotics*
  into `audit_lattice_correlation_oscillation`.
- **The lattice limit is asymptotic, and non-constant by *Non-convergence of the lattice correlation profile*.**
  `audit_thm_profile_asymptotics` uses the subgroup generated by the full log-ratios,
  with span `ℓ`, and gives a continuous, positive, non-constant limit of period `ℓ / 2`,
  namely `T G̃` for the periodisation `G̃` of `audit_lattice_periodisation_limit`.
  `LatticeProfile.lean` applies the finite-delay renewal theorem to `A + 1 - G(2v)`,
  converts uniform phase convergence to convergence on the half-line, and smooths
  the vanishing error; the lower regularity bound ensures positivity.
  `LatticeNonconstancy.lean` proves that `G` has no limit for a lattice system, so the
  periodic limit of `G` is non-constant, and *Injectivity of Gaussian smoothing* carries this through
  `T`. The separate homogeneous endpoints prove the sharper exponential error.
- **IFS terminology.** The paper calls the defining family of similarities an iterated
  function system (IFS). Its Lean type is `System`; this identifier denotes an IFS
  throughout the formalisation.
- **Orientation-reversing similarities are carried by a sign.** The paper's IFSs are
  finite families of contracting similarities of `ℝ` mapping `[0,1]` into itself, the
  orientation-reversing ones included, and *Minkowski reconstruction from the image set* uses time reversal of the
  increments when `S_w` reverses orientation. `System` writes each map as
  `S_i(x) = ε_i r_i x + b_i` with the modulus `r_i ∈ (0,1)` in `ratio` and the
  orientation `ε_i ∈ {1, -1}` in `sign`, so that the signed ratio ranges over
  `(-1,0) ∪ (0,1)` while `p_i = r_i^s`, `α_i = log(1/r_i)` and every renewal quantity are
  read off `ratio` exactly as in the tex. The `mapsTo` field is stated for the map itself,
  which is what keeps the attractor inside `[0,1]` for either orientation. A proof that
  needs the interval `S_w([0,1])` uses its left endpoint `min(S_w(0), S_w(1))`
  (`System.left`, `stoppingLeft`, `listLeft`, `generationLeft`), and a proof that needs
  Brownian scaling of a cylinder `S_w K` writes it as `ℓ_w + r_w · orientCompact ε_w K`,
  where the oriented copy is `K` or the reflection `1 - K`; the reflected case is the
  time reversal `IsPlanarBrownian.timeReversal`, a planar Brownian motion, so that
  `IsPlanarBrownian.map_tubeMass_affineBrownianCompactPiece_orientCompact_eq` is
  *Neighbourhood union and scaling identities* for both orientations. The two named systems, the
  base-five systems and the homometric systems have `ε_i = 1`; every endpoint stated for
  a general `System` covers the orientation-reversing case.
- **Quantifier scope in an almost everywhere statement.** `audit_gaussian_four_point_ae`
  asserts, outside one null set, that `Δ > 0` *and* that the bound holds whenever the
  intervals overlap.  The overlap hypothesis governs the bound alone: `Δ > 0` holds with
  no hypothesis, because `Δ = 0` forces either a degenerate interval or the two unoriented
  intervals to agree, and a Frostman measure with `0 < s` gives both null.  Pushing the
  overlap guard outwards, so that it governs the conjunction, type-checks, reads almost
  the same, and is strictly weaker.  `audit_gaussian_four_point_ae` and the bundle keep
  this scoping, and `FourPointBound.det_pos_of_ne_of_nondegenerate` is the
  unconditional determinant bound behind it. The proof of *Four-point integral bound*
  discards repeated endpoints and uses determinant positivity only for overlapping
  intervals, so the internal statement is stronger than this application requires.
Four statements deserve a note on what their endpoints assert.

- **The fixed-dimension family.** The endpoints are stated on `fixedMean s p`, which is
  the right-hand side of the two-contraction mean formula,
  `2^{-s} Γ(1-s) (∫₀¹ δ^{-s} dC^×_δ(μ_p))/h(p)`. The code writes this as
  `2^{1-s} Γ(1-s) pq · fixedMoment s p / h(p)`. The identification follows from
  `audit_fixed_moment_natural` and `fixedSystem_crossPhi`: `fixedMoment s p` is the
  normalised integral `J(p)` of *Monotonicity for small dimension*. `audit_exists_fixed_dimension_measure`
  shows the measure exists and is unique, and `audit_fixed_dimension_mean` identifies
  `fixedMean s p` with the Cesàro mean of the expected profile of `μ_p`, so the statements
  about the mean are statements about the paper's `H̄_s(p)`.  The parameter range is
  `p ∈ (0,1)` throughout where the tex restricts to `(0, 1/2]`; the tex's restriction is
  by the symmetry `audit_fixed_dimension_symmetry`.  The non-lattice hypothesis
  `log λ₁/log λ₂ ∉ ℚ` is `Irrational (log a / log b)`, equivalent to `System.NonArithmetic`
  by `fixedSystem_nonArithmetic_iff`.  "Strictly monotone on every component of
  `(0,1/2) ∖ D_s`" is stated for every open interval of `(0, 1/2)` free of critical
  points, which the components are; "no accumulation point in `(0, 1/2]`" is
  `¬ AccPt p (𝓟 D_s)` for every `p ∈ (0, 1/2]`, and the strict monotonicity near `1/2` is
  `StrictMonoOn ∨ StrictAntiOn` on `(1/2 - ε_s, 1/2)`, as the tex asserts.  The threshold
  `s₀` of `audit_small_dimension_monotone` is `min(2·10⁻⁵, c/10¹¹)` with `c` the
  non-constructive constant of *Entropy-factor inequalities*, which is what the tex asserts.  The
  derivatives in `audit_main_term_derivative`, `audit_remainder_derivative` and
  `audit_second_derivative_small_s` are asserted to exist (`HasDerivAt`), not read off
  `deriv`, so the bounds are never vacuous; `criticalSet` and the level sets are defined
  through `deriv` and `fixedMean`, which analyticity makes the genuine derivative and
  values.

- **The homogeneous periodic profile in *Renewal of correlation profiles*.** The paper obtains
  non-constancy directly from *Non-convergence of the lattice correlation profile*. `audit_cantor_nonconstant`
  asserts non-constancy on every tail for every `0 < λ < 1/2`, with an independent
  proof by the density argument of `HomogeneousNonconstancy`. Its intermediate
  first-difference and periodisation identities are internal to that proof.
- **Homometric non-isometric attractors.** The endpoint asserts everything the proposition does:
  the two natural measures, their distinctness, strong separation with gap `1/45`,
  Ahlfors regularity at `t = log 6 / log 30 ∈ (1/2,1)`, the non-isometry of the two
  attractors as `IsEmpty (KA ≃ᵢ KB)`, the equality of the signed convolutions `σ * σ̃`,
  and the consequent equalities of `Φ` and `H`.  All of it is proved.  For non-isometry,
  both proofs use the common extreme points `0` and `85/87`, so an isometry from
  one onto the other sends `0` to `0` or to `85/87` and is the identity or the
  reflection. The paper excludes these by comparing the digit sets `𝒜` and `17 - 𝒜`
  with `ℬ`; Lean uses fixed points in the corresponding missing first-level intervals
  `S_4([0,1])` and `S_5([0,1])` as explicit witnesses. The paper obtains convolution
  equality from random digit expansions with the same digit-difference law. Lean uses
  the equivalent observation that the difference law of a self-similar measure is
  itself self-similar, for the 36 maps indexed by ordered
  digit pairs at dimension `2t`; homometry makes the two difference systems the same
  system, and Hutchinson uniqueness finishes.  The rescaling `(x - y + 1)/2` is not
  cosmetic: the raw difference lives on `[-1,1]` and `System` is hard-wired to `[0,1]`.

- **Base-five correlation profiles.** The two systems are `baseFiveSystem` at the digit sets
  `{0,1,4}` and `{0,2,4}`, and the natural measures enter as `IsNatural` hypotheses, as
  in `audit_cantor_application`; `naturalMeasure_selfSimilar` supplies such a measure
  for every system, so the hypotheses are satisfiable.  The Frostman constants are not
  hypotheses: both systems satisfy the open set condition with `U = (0,1)`, and
  `System.OpenSetCondition.exists_isFrostman` produces them.  The second assertion,
  `limsup |H_{μ₁}^s - H_{μ₂}^s| > 0`, is stated as the separation
  `∃ ε > 0, ∀ V, ∃ t ≥ V, ε ≤ |H_{μ₁}^s(t) - H_{μ₂}^s(t)|`, the hypothesis shape of
  *Separation by expected profiles*, which is what the two displays after the proposition consume.  The
  exact correlation values follow in the paper from the `(3ⁿ - 1)/2` touching
  level-n cylinder pairs for `{0,1,4}` and the absence of such pairs for `{0,2,4}`.
  Lean instead sums the equivalent first-digit recursions using the contact mass `Ψ`.
  The periodic limits of the proof are built, not assumed: `exists_periodic_limit` turns the
  non-negative, exponentially small increments `G(t) - G(t - log 5)` into a continuous
  `log 5`-periodic function within `O(e^{-sw})` of `G`.

Two endpoints are strictly more general than the tex, and carry a tex-shaped wrapper:
`audit_ahlfors` against `audit_ahlfors_named`, and `audit_endpoint_block_mass` against
`audit_endpoint_block_mass_dyadic`. The internal homogeneous refinement
`audit_profile_asymptotics_lattice` states a uniform exponential-error bound, and
`audit_profile_asymptotics_lattice_bigO` gives its asymptotic form. This exponential-error
refinement is retained in the library but is not part of the paper. The module index
also retains three specialisations that the paper no longer writes out separately:
the non-lattice renewal limit for the paired system `μ_B`, its expected-profile limit,
and separation of two non-lattice measures with distinct limits. The last is the step
used in the proof of *Finite exceptions in the two-contraction family*.

### What the comparator does not check

Comparator compares the nine headline endpoints of `Challenge.lean` with
`Solution.lean` and replays their proofs through the kernel; the other endpoints of
`Solution.lean` rest on `lake build`, on the absence of any `axiom` declaration in the
library, and on the ban on `native_decide`.  It says nothing
about whether `Challenge.lean` or `Solution.lean` states the paper.  That
correspondence is a human obligation, and the traps above are exactly the places where a
formal statement can look right and be false, or look right and be vacuous.  Reviewing a
new endpoint means checking, in order: does every measure carry its support condition,
are all times non-negative, is the hypothesis strong enough to remove the diagonal, is
the ambient space the paper's, and is the conclusion the paper's complete conclusion or
a weaker surrogate. A definition that is *itself* the closed form the paper derives
proves nothing about the derivation: `gammaMult` is the closed Gamma formula,
`multInt` is the integral defining the Fourier multiplier, and it is `audit_gamma_multiplier` that connects them.  Likewise
`fixedMoment` is the moment `J(p)` through the Bernoulli coding and `fixedDimCoeff` is
the coefficient in the two-contraction lattice Fourier expansion written out; `audit_fixed_moment_natural`
and the endpoints of *Correlation profiles in the two-contraction family* are what connect them with the natural
measure and the expected profile.

## Omissions and proof differences

The following distinctions concern the arXiv v1 snapshot as well as the current manuscript,
except where a later introductory addition is explicitly mentioned.

| Paper statement | Lean coverage |
| --- | --- |
| Theorem/Corollary 1.1–1.9 | All nine headline conclusions, under the paper's assumptions. |
| Lemma 2.1 and Lemmas 3.1–3.2 | Gaussian reduction and renewal-defect estimates. Lemma 3.1 is distributed across library calculations rather than a single bundled endpoint. |
| Proposition 3.3 | The non-lattice limit and its integral formula; continuity, strict positivity, periodicity and the asymptotic approximation for the explicit periodisation, whose series is proved convergent. |
| Lemma 3.4 | Non-constancy of the explicit periodisation, by contradiction from the non-convergence of `G`. |
| Lemma 4.1, Proposition 5.1, Theorems 5.2 and 6.1 | Smoothing injectivity, the four-point bound, variance and almost-sure concentration. |
| Lemmas 7.1–7.4 and Propositions 8.1–8.2 | Neighbourhood estimates, renewal shifts, concentration, and both examples. |
| Proposition/Lemma 9.1–9.8 | Correlation series, mean and non-lattice limit, general holomorphic level sums, analyticity, range, and all three derivative bounds with their stated constants. |

**The lattice formula.** Immediately before Proposition 3.3, the paper defines

\[
  \widetilde G(t)=\frac{\ell}{m}\sum_{k\in\mathbb Z}z(t+k\ell).
\]

`System.latticePeriodisation` is this sum, with `renewalMean` for `m` and `renewalDefect`
for `z`. `System.lattice_G_limit` proves that there exists a continuous, positive,
`ℓ`-periodic function `g` with `G(t) - g(t) → 0`, by the finite-delay renewal theorem,
which does not name its limit. `LatticePeriodisation.lean` identifies `g` with the sum:
the renewal equation telescopes along `t + ℓℤ`, so the symmetric partial sums of
`z(t+kℓ)` converge to `g(t) ∑ p_i n_i = g(t) m/ℓ` (`tendsto_sum_renewalDefect_of_periodic`),
and the exponential tails of `z` make the series summable, so the same partial sums
converge to its sum. The paper reads the lattice limit off the renewal theorem in its
lattice form; Lean reaches the same function by existence plus identification.
Lemma 3.4 is then the non-constancy of this sum, from `audit_lattice_nonconvergence`.

**General renewal statements.** Section 3.3 quotes a renewal theorem for arbitrary finite
positive interarrival laws and possibly signed exponentially decaying defects, and derives
a shift limit for bounded half-line solutions. `RenewalTheorem.lean` proves the quoted
theorem and the shift limit for the laws `ϑ = ∑ p_i δ_{α_i}` of a system at its similarity
dimension, the generality in which the paper applies them, with the signed defect: the
non-lattice limit and renewal series, the lattice uniform convergence on one period to the
explicit periodisation, and *Renewal shift limit* by the paper's cutoff argument. Not
formalised are the statement for an arbitrary finitely supported law, the renewal series
in the lattice case, and the uniform continuity of the solution, which the paper uses to
upgrade pointwise lattice convergence; Lean obtains the uniform convergence from Tannery's
theorem instead. These are literature inputs, not headline hypotheses.
The restriction on the interarrival law also applies to the shift consequence, so both
prose entries are marked `partially_formalized` in the manifest. The weights and atom
locations of `System.renewalLaw` are linked by `p_i = exp(-s * α_i)`; the paper's general
statement allows them to be chosen independently.

**Background and speculation.** The introduction's cited results on generalised dimensions,
Salem sets and dynamical reconstruction, and the discussion following the homometric
example, are outside the formalisation. The current local manuscript adds explicit
correlation-dimension and local-density displays and hitting-time comparisons after v1;
the manifest excludes these additions too. Numerical suggestions of monotonicity for
every `s ∈ (0,1)` and of an empty critical set are not proved in either the paper or Lean.

**Different proofs with the same stated conclusions.** Lean uses dyadic sums for the
four-point estimate, third-moment interpolation for neighbourhood concentration, a
contradiction argument for the non-constancy of the lattice periodisation, and first-digit recursions for the
base-five example. The paper uses elementary integrals, first/fourth-moment interpolation,
phase comparisons and cylinder counting, respectively. In the small-parameter proof,
Lean establishes the sufficient numerical margin `0.754 < 0.88` rather than the paper's
`0.62 < 0.88`. The constants `6`, `3000` and `10¹¹` in the three numbered derivative
lemmas are retained, as are the parameter ranges and headline conclusions.

**Equivalent or stronger formulations.** Closed-ball Frostman bounds and the closed
time-correlation inequality are connected to the paper's conventions by proved conversion
and atomlessness results. `fixedMoment` is the normalised cross-term integral `J`; the
paper's integral is `2p(1-p) J`, and the mean is identified with the Brownian Cesàro mean.
Lemma 9.2 is stronger in Lean because boundedness of its open convex domain is unnecessary.
The homogeneous exponential-error estimate and the two-contraction lattice Fourier
expansion are additional formal results. None of these changes is a missing paper result.

**Proved without separate audit endpoints.** Coded-point bounds, contraction and kernel
bounds, the Fourier transform of the renewal defect, and the crossing/nested determinant
calculations already have library proofs. Their lack of an `audit_` wrapper is not a proof
gap. The small-parameter derivative margin is assembled inside the monotonicity proofs.
Likewise, the irrationality/non-lattice equivalence is proved by
`audit_pairSystem_nonArithmetic_iff`; non-lattice type remains a hypothesis precisely where
the paper assumes it.
