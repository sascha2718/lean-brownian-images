# Correspondence with the paper

This document argues the correspondence between the formal statements and the LaTeX
source `BrownianImagesComplete.tex`: what `Solution.lean` and `Challenge.lean` state,
how each result of the paper maps to an endpoint, and where a formal statement could
quietly diverge from the prose. Labels such as `thm:main` are the labels of the LaTeX
source. The comparator compares `Challenge.lean` with `Solution.lean` and never with
the paper, so this correspondence is a human obligation, and this document is where
it is argued.

The paper uses `C_δ(μ)` for the correlation integral of the time measure as well as
`C_r(ν)` for a planar measure. The library retains the internal names `Phi μ δ` and
`corr ν r`, respectively. `Phi` uses a closed distance inequality, which agrees with
the paper's strict inequality for the atomless time measures in `sec:setup`
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
The boundary estimate `eq:boundary-mass` is likewise written after pulling back by
`S_i`, as `μ{x ∈ K : dist(S_i(x), S_j K) ≤ δ} ≤ C δ^η`.
The fixed-block exclusion argument is `IsFeasible.measure_preimage_cthickening_le_pow`,
followed by `exists_rpow_bound_of_geometric` to obtain the bound at every scale.

The library defines `H` by the kernel integral, and `smoothing` identifies it with the
expected profile. This is `eq:h-definition` in the paper, where the expectation is
the definition and the integral formula is derived. The label `eq:smoothing` in code
comments denotes the rescaled form of this identity.

The empirical profile in `sec:concentration` is defined directly by
`Y_μ(t) = e^{2st} C_{e^{-t}}(W_*μ)`. The library's `Yprofile s ν t` is the normalised
correlation integral of a planar measure `ν`, so `Yprofile s (occupation W μ ω) t`
is the paper's `Y_μ(t)` on the Brownian path `ω`.

The paper uses `⟨F⟩_r` throughout for the open neighbourhood `Metric.thickening r F`.
In `sec:reconstruction`, it writes the normalising exponent `2 - 2s` explicitly;
the library retains `tubeExponent s`, also denoted by `α` in internal comments.
The logarithmic contractions are `α_i = log(1/r_i)` and `α_w = log(1/r_w)` throughout
the paper. The library's `halfLogRatio`, `generationHalfLogRatio` and
`stoppingHalfLogRatio` represent the Brownian shifts `α_i/2` and `α_w/2`. The
interarrival distribution for the neighbourhood mean is `∑ p_i δ_{α_i/2}`. If the
original logarithmic contractions have lattice span `ℓ`, then `TubeArithmetic (ℓ/2)`
expresses arithmeticity for this law. Internal variables called `beta` in
cylinder-shift arguments denote `α_w/2`.

The fixed-dimension family and its separation results form the single section
`sec:fixed-dimension`. Its subsections are `sec:fixed-dimension-family` (correlation
profiles), `sec:fixed-dimension-separation` (separation of image laws), and
`sec:small-dimension` (monotonicity for small dimension). The paper uses
`λ₁ = p^{1/s}` and `λ₂ = (1-p)^{1/s}` for the contractions, represented by
`fixedA s p` and `fixedB s p`. Their principal complex branches `λ₁(z)` and `λ₂(z)`
are `ca s z` and `cb s z`. Internal variables and comments using `a` and `b` for
these contractions follow the same correspondence.
The entropy is `h(p) = -p log p - (1-p) log(1-p)`, represented by `entropy p`.
In the proof of `thm:fixed-dimension-analyticity`, the paper uses its principal-logarithm
extension `h(z)` and identifies the local holomorphic extensions on overlapping discs by
the identity theorem. This gives extensions of the cross-term integral and mean to a
complex neighbourhood of `(0,1)`. The formal endpoint records their real-analytic consequence;
the local holomorphic cross-term extension is `differentiableOn_crossLimit_disc`.

The holomorphic kernels in `sec:fixed-dimension-separation` are `ψ` and `ψ_n`;
`crossKernelC` and `kernelN` are their concrete implementations, and the generic
kernel argument `φ` of `levelSum` represents `ψ`. The Gaussian smoothing kernel
retains `φ`. In `sec:small-dimension`, `alphaP s p` and `betaP s p` represent
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

The paper consistently uses `S` for similarities. In `sec:fixed-dimension`,
`S₁(x) = λ₁x` and `S₂(x) = λ₂x + 1 - λ₂`, with coding alphabet `{1,2}`.
The library's `Fin 2` symbols `0`, `1` correspond to the paper's `1`, `2`.
In particular, `N₁`, `N₂` count the paper's symbols `1`, `2`, and the internal
leading-ones decomposition counts the symbols `2` before the first `1` in the paper's
`eq:initial-symbol-decomposition`. In `sec:base-five` and `sec:obstruction`,
`S_d` is indexed by the actual digit `d` of the specified digit set.

The formulas in `sec:fixed-dimension-family` use the existing cross term directly.
Its Stieltjes measure is `2pq` times the law of `S₂(Y) - S₁(X)` for independent
`X,Y ∼ μ_p`, by `fixedSystem_crossPhi`. Thus
`∫₀¹ f(δ) dC^×_δ(μ_p) = 2pq 𝔼 f(S₂(Y) - S₁(X))` whenever the integral exists.
In particular, `fixedMoment s p = (2pq)^{-1} ∫₀¹ δ^{-s} dC^×_δ(μ_p)` by
`fixedMoment_eq_natural`. The paper introduces this normalised integral as `J(p)` in
`sec:fixed-dimension-separation`, alongside its main approximation `J₀(p)` in
`eq:main-term`, represented by `mainTerm s p`. Both functions and their parameter
derivatives are used in `sec:small-dimension`. The paper retains the argument in
`T(p) = log(1/q)/s` throughout and differentiates with respect to `p`, displaying
`T'(p) = 1/(sq)`. The library evaluates its generic logarithmic variable at
`fixedT s p` and applies the chain rule in `hasDerivAt_mainTerm`.
Internal code comments using `Z_p` and `M_p(s)` denote the distance `fixedCross`
and this normalised integral, respectively. The paper writes the distance out and
introduces no moment with a general complex exponent. The correlation series absorbs
its factor `2pq` into the cross-term measure, and the mean formula is
`H̄_s(p) = 2^{-s} Γ(1-s) (∫₀¹ δ^{-s} dC^×_δ(μ_p))/h(p)`.

The source measures in `sec:obstruction` are `μ_{D_A}` and `μ_{D_B}`, named for
their digit sets before `thm:homometric-example`. The internal measures `σ_A`, `σ_B`
of `HomometricMeasures.lean` and digit maps `digitFunA`, `digitFunB` represent them.

The neighbourhood mean is `Q(t) = e^{(2-2s)t} 𝔼 M_{e^{-t}}(E)`, represented by
`meanBrownianTubeProfile`; local function aliases `m` in the renewal proofs denote `Q`.
The paper writes the random normalised mass explicitly;
`brownianTubeProfile` retains it as an internal definition. The statement
`thm:neighbourhood-renewal` consists of positive uniform bounds and the real-time shift
relation `eq:neighbourhood-renewal-shift`, represented exactly by
`System.IsNatural.tubeRenewal_bounds_shift` and `audit_tube_renewal`. The stronger constant
and periodic alternatives remain internal in `System.IsNatural.tubeRenewal`. Their
periodic profile `PK` and cutoff do not introduce notation in Section 7 of the paper.
The cylinder scaling identity `eq:cylinder-neighbourhood-scaling` is written as equality
in law of the mass processes indexed by radius. The concentration proof uses the cylinder
masses directly, and introduces the word shift `α_w/2` only when applying concentration
in the reconstruction proof. Internal normalised cylinder profiles express these same
masses and shifts. Both the paper and `GenerationRatio.lean` pass from concentration and
mean shift invariance to cylinder-mass ratios.

The first bound in `thm:neighbourhood-concentration` uses variance. Its proof
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

Code comments referring to `thm:stopping-overlap` denote the bounded overlap estimate
and interval partition recorded in `sec:osc-geometry`, where the paper cites
Hutchinson (1981), proof of Theorem 5.3(1). The library retains proofs of both facts.

Code comments referring to `thm:renewal-recursion` denote the self-similarity identities
`eq:correlation-recursion`, `eq:g-recursion` and the cross-term bounds in `sec:renewal-equation`.
The paper records these directly in prose. Section `sec:renewal-equation` states the
shared signed-forcing renewal theorem from Falconer (1997), Proposition 7.1 and
Theorem 7.2. Uniform continuity of the solution upgrades lattice convergence to uniform
convergence on one period. The cutoff argument for bounded half-line solutions is also
stated there, with its shift consequence `eq:renewal-shift`. The constant and periodic
cases of that consequence are `tendsto_sub_shift_sub_of_tendsto_atTop` and
`tendsto_sub_period_sub_of_uniform_lattice` in `GenerationRatio.lean`. The renewal
applications are proved by the vendored non-arithmetic theorem and the discrete lattice
argument in `TubeDiscreteRenewal.lean`; the library retains this direct proof of uniform
lattice convergence. The general literature statement and its arbitrary finite-law
half-line consequence are not separate bundled endpoints. The lattice application uses
the span-one statement after rescaling, so its prefactor is `ℓ/m`. Feller is cited in
prose for another account of the renewal theorem.

The paper groups the constant and periodic limits in `thm:renewal-limits`, in
`sec:renewal-equation`. References to `thm:non-lattice-limit` in code comments and the
other library documentation denote its non-lattice conclusion. The internal declaration
names are unchanged. The lattice conclusion is `System.lattice_G_limit`, with the
qualification about its explicit periodisation formula recorded below.
The preliminary `thm:renewal-defect-left-tail` collects continuity from the finite-sum
definition of `renewalDefect`, non-negativity from `renewalDefect_nonneg`, and the exact
negative-time calculation in the proof of `renewalDefect_pos_of_nonpos`, using
`renewalDefect_eq` and `phi_eq_one_of_one_le`. The positive-time consequence appended to
`thm:cross-piece-mass` is the calculation in `exists_abs_renewalDefect_le_exp`.

The Gaussian return and endpoint mass estimates in `sec:variance` are proved directly
inside `thm:four-point-integral`. Code comments using the internal labels
`thm:gaussian-four-point`, `eq:joint-return-bound` and `thm:endpoint-block-mass`
refer to these estimates, with independence on disjoint intervals used in the proof of
`thm:variance`. The internal labels `eq:crossing-determinant` and
`eq:nested-determinant` refer to the separate algebraic calculations in `FourPoint.lean`.
The paper uses their common bound, with `a = |I ∩ I'|` and `b = |I △ I'|`.
After sorting the endpoints, these are the middle gap and the sum of the outer gaps,
respectively. The paper states the joint sublevel mass bound directly and integrates it
in the length variables `a,b` to reduce the estimate to two elementary integrals.
The library uses dyadic blocks and the corresponding geometric sums for the
same bound and the same three regimes of `V_s`.

## The statement layer

`Solution.lean` is the formal statement of the paper: 127 endpoints named
`audit_<slug>`, in document order, proved from the library declarations. Adding a
result to the paper means adding its statement there first; the
design work is in the statement.

`Challenge.lean` is the human-facing problem statement and carries only the headline
theorems, with statement text identical to `Solution.lean` and `sorry` in place of the
proofs, on Mathlib-only copies of the definitions the statements need: `thm:main` as
`audit_main`; `thm:cantor-application` as `audit_cantor_application` with
`audit_cantor_application_pair` and `audit_exceptional_parameters_countable` covering
its final sentence. It is not part of the library and not a default target, which is
what lets it carry `sorry` while the library stays clean. The comparator configuration
kernel-checks exactly these four; the other endpoints are checked by
`lake build Solution`, and the library declares no axiom.

The main theorem uses `expectedProfile`, defined directly by
`e^{2st} 𝔼 C_{e^{-t}}(W_*μ)` as in `eq:expected-profile`. The smoothing kernel, time
correlation integral and normalised profile `G` do not occur in `Challenge.lean`.
In `Solution.lean`,
`expectedProfile_eq_H` derives the equality with the library's smoothing formula
from `smoothing`.

The scalar formulas `homogeneousDimension` and `pairedRatio` are defined directly
in both statement files. They are definitionally equal to the library's
`homogeneousDim` and `pairRatio`. Separate declaration names keep compiler-generated
numeral proofs from making the challenge depend on the smoothing kernel's
declarations; comparator still checks the complete definitions, without exceptions.

The named measures are specified by `IsHomogeneousMeasure` and `IsPairMeasure`:
probability measures on `[0,1]` satisfying the two explicit invariance equations of
`sec:introduction`. Their definitions need no bundled system constructors or proofs.
The equivalences `isHomogeneousMeasure_iff_exists_isNatural` and
`isPairMeasure_iff_exists_isNatural` in `Solution.lean` identify them with the
library's natural measures, using Hutchinson uniqueness. In particular, the paired
headline has no extra ratio-bound hypotheses: `pairRatio_pos` and
`pairRatio_lt_half` supply the bounds inside its proof. The general-system headline
retains arbitrary orientations and the open set condition.

All four theorem bodies in `Challenge.lean` are holes. Its other declarations are
definitions or structures used by those statements, with no helper theorems,
constructor tactic proofs or literature axioms. Comparator compares the transitive
dependencies of the statements with their counterparts in `Solution.lean`, including
the copied definitions, audits the permitted axioms, and replays the proofs through
the kernel. Run `./comparator-audit.sh` from `lean/`; the local runner and its platform
requirements are documented in `README.md`.

**The correspondence is not one endpoint per theorem.** A theorem with several
assertions appears twice: once as a bundled `audit_thm_*` endpoint carrying the paper's
complete conclusion, and once as the individual endpoints its proof and its consumers
use. Internal proof estimates are also retained, including the Gaussian bundle.
The eight bundles are `audit_thm_smoothing_injective`, `audit_thm_profile_asymptotics`,
`audit_thm_gaussian_four_point`, `audit_thm_variance`,
`audit_thm_fixed_dimension_profiles`, `audit_thm_fixed_dimension_separation`,
`audit_thm_small_dimension_monotone` and `audit_thm_critical_set_finite`.
Two further endpoints restate a general Lean result in the narrower shape the tex uses:
`audit_ahlfors_named` (the internal regularity endpoint for `μ_A` and `μ_B`),
`audit_endpoint_block_mass_dyadic` (the tex needs only dyadic `β, η`,
and uses both the mass and return estimates in the proof of `thm:four-point-integral`).
The library also retains the homogeneous exponential-error refinement, with its bound
and big-`O` endpoints. The paper uses only
the general convergence in `thm:profile-asymptotics` for `thm:cantor-application`.
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
the `Solution.lean` endpoint and what stands behind it. All 127 endpoints are proved.
`Challenge.lean` retains `sorry` only as the independent statement file for the four
headline endpoints; no library or solution declaration uses `sorry`.

| Result | Endpoint | Proved by |
| --- | --- | --- |
| `thm:main` | `audit_main` | `main`, after identifying the expected profile with `H` through `smoothing` |
| `thm:cantor-application` | `audit_cantor_application` | `homogeneous_application`, the general system under the open set condition, with the homogeneous measure specified by its invariance equation |
| `thm:cantor-application`, named `μ_B` | `audit_cantor_application_pair` | `homogeneous_application_pair`, with both named measures specified by their invariance equations and the paired ratio bounds derived in the proof |
| countability of exceptional homogeneous parameters | `audit_exceptional_parameters_countable` | `exceptionalParameters_countable` |
| `thm:minkowski-reconstruction` | `audit_minkowski_reconstruction` | `System.IsNatural.minkowskiReconstruction`, under the open set condition; the non-lattice key-renewal limit and the lattice finite-delay periodic limit both feed the generation-cylinder quotient argument, giving pathwise recovery and a measurable reconstruction map from the compact Brownian image |
| Borel recovery from the pathwise tube limit | `audit_borel_reconstruction_of_pathwise` | `MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise` |
| transfer from occupation-law singularity to compact-image-law singularity | `audit_brownianImageLaw_mutuallySingular_of_pathwise` | `MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction`; `brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio` gives the direct self-similar generation-ratio form |
| `thm:cantor-set-application` | `audit_cantor_set_application` | `MinkowskiReconstruction.homogeneous_brownianImage_application`: the homogeneous source is reconstructed directly from its one-delay renewal equation, the non-lattice source, under the open set condition, by the general reconstruction theorem, and occupation-law singularity descends to mutual singularity of the compact-image laws |
| `thm:cantor-set-application`, named `K_B` | `audit_cantor_set_application_pair` | `MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional` |
| `eq:neighbourhood-union-scaling` | `audit_tube_union_scaling` | `tubeCutoff_compactUnion`, `tubeMass_translate_dilate` |
| `eq:neighbourhood-defect-elementary` | `audit_tube_defect_elementary` | `tubeDefect_nonneg`, `tubeDefect_le_pairwiseTubeOverlapAreaSum` |
| `thm:neighbourhood-moments` | `audit_tube_moments` | `System.IsNatural.tubeMoments`, under the open set condition; discrete-martingale maximal estimates give every unit Brownian-radius moment, the stopping cover supplies the stated upper moments, and classical Ahlfors regularity under the open set condition the positive lower mean |
| `thm:neighbourhood-overlap` | `audit_tube_overlap` | `System.IsNatural.tubeOverlap`, under the open set condition, with the bound `C r^{2-2s+2η}` for the exponent `η` of `thm:cross-piece-mass`; the Gaussian-gap estimate for the stopping cylinders at temporal scale `r²`, `eq:stopping-brownian-overlap`, counted through `eq:stopping-close-pairs` and summed dyadically, gives the pairwise overlap bound, and `Minkowski.DefectExpectation` the defect bound with integrability |
| `thm:neighbourhood-renewal`, `eq:neighbourhood-renewal-shift` | `audit_tube_renewal` | `System.IsNatural.tubeRenewal_bounds_shift`; positive uniform mean bounds and invariance under every half-logarithmic shift as the real argument tends to infinity, deduced from the internal constant and uniform periodic limits |
| `thm:neighbourhood-concentration` | `audit_tube_concentration` | `System.IsNatural.tubeVarianceConcentration`, under the open set condition; the square of the internal centred-norm bound from `tubeConcentration` is the variance bound, with constants `C²` and `2γ`, and Borel--Cantelli gives each fixed grid |
| the ambient σ-algebra on `𝒫(ℝ²)` | `audit_borel_eq_giry` | `borel_probabilityMeasure_eq_giry` |
| occupation has full mass | `audit_isProbabilityMeasure_occupation` | `IsPlanarBrownian.ae_isProbabilityMeasure_occupation` |
| `Law(W_*μ)` has total mass one | `audit_isProbabilityMeasure_occupationLaw` | `isProbabilityMeasure_occupationLaw`, for every process `W`: the push-forward of a probability measure is a probability measure |
| the law of the compact Brownian image has total mass one | `audit_isProbabilityMeasure_brownianImageLaw` | `isProbabilityMeasure_brownianImageLaw`, for every process `W` |
| occupation is measurable | `audit_aemeasurable_occupation` | `IsPlanarBrownian.aemeasurable_occupationProb` |
| Ahlfors regularity, cited from Falconer | `audit_ahlfors` | `System.OpenSetCondition.exists_isAhlforsClosed`, under the open set condition; proved internally rather than assumed as an axiom |
| the two Ahlfors ball conventions | `audit_ahlfors_conventions` | `IsAhlforsClosed.isAhlfors` |
| internal Ahlfors regularity for `μ_A`, `μ_B` | `audit_ahlfors_named` | `exists_isAhlfors_homogeneous_pair` |
| `thm:gaussian-reduction` | `audit_gaussian_reduction` | `gaussian_reduction` |
| `sec:setup`, atomlessness of `μ` | `audit_measure_singleton` | `IsFrostman.measure_singleton` |
| `sec:setup`, atomlessness of `dΦ` | `audit_pairLaw_noAtoms` | `pairLaw_measure_singleton` |
| `sec:setup`, continuity of `Φ` | `audit_phi_continuous` | `continuous_phi` |
| `eq:frostman`, the two ball conventions | `audit_frostman_conventions` | `IsFrostman.isFrostmanOpen`, `IsFrostmanOpen.isFrostman` |
| `eq:correlation-frostman` | `audit_phi_le` | `phi_le` |
| `eq:h-definition`, rescaled with `r = exp(-t)` | `audit_smoothing` | `smoothing` |
| `sec:setup`, `φ` integrable and `∫φ > 0` | `audit_kern_integrable` | `kern_integrableOn`, `integral_kern_pos` |
| `sec:setup`, uniform continuity following `eq:h-definition` (the internal label `thm:profile-uniform-continuity`) | `audit_profile_uniform_continuity` | `profile_uniformContinuous` |
| `eq:correlation-recursion` | `audit_renewal_recursion` | `phi_recursion_cross`, with the cross term `Φ_×` of `eq:correlation-recursion` |
| `eq:g-recursion` | `audit_g_recursion` | `g_recursion_cross` |
| `thm:cross-piece-mass`, `eq:cross-piece-mass` | `audit_crossPhi_bound` | `System.StrongOpenSetCondition.exists_crossPhi_bound`: `0 ≤ Φ_×(δ) ≤ C δ^{s+η}` for `0 < δ ≤ 1`, with `0 < η < 1 - s` |
| `sec:renewal-equation`, the strongly separated case | `audit_crossPhi_separated` | `crossPhi_eq_zero_of_stronglySeparated`: the cross term vanishes below the separation gap |
| Bounded overlap and interval partition in `sec:osc-geometry`, citing Hutchinson (1981), proof of Theorem 5.3(1) | `audit_stopping_overlap` | `System.IsFeasible.exists_point_multiplicity_bound` and `System.IsFeasible.exists_stopping_coloring`, under the open set condition: one integer `M` bounds the multiplicity of the stopping family at every threshold `0 < u ≤ 1`, and the family is coloured with `M` colours so that intervals of one colour have disjoint interiors |
| The boundary estimate `eq:boundary-mass` and its pairwise consequence within the proof of `thm:cross-piece-mass` | `audit_cross_piece_mass` | `System.StrongOpenSetCondition.exists_cross_piece_bound`: the boundary estimate and the stronger individual bound `(μ_i × μ_j){|x-y| ≤ δ} ≤ C δ^{s+η}`, for `i ≠ j`, with one exponent `0 < η < 1 - s`. Summing with weights `p_i p_j` gives the paper's aggregate bound `eq:cross-piece-mass` |
| Schief's theorem, cited in `sec:introduction` | `audit_schief` | `System.openSetCondition_iff_strongOpenSetCondition`: the open set condition is equivalent to the existence of a feasible open set meeting the attractor, by the maximal neighbour count of `Schief.lean` |
| `thm:non-lattice-limit`, the renewal inputs | `audit_renewalLaw` | `isProbabilityMeasure_renewalLaw`, `integral_id_renewalLaw` |
| `thm:non-lattice-limit`, exponential moment | `audit_exists_expTransform_lt_one` | `exists_expTransform_lt_one` |
| `thm:non-lattice-limit` | `audit_non_lattice_limit` | `non_lattice_limit`, under the open set condition; the exponential tail of the renewal defect `z` is the cross-term bound in `sec:renewal-equation` |
| The unnumbered definition `c^s = 1 - 2^{-s}` in the introductory paragraph “A two-contraction example” | `audit_pairRatio` | `pairRatio_rpow`, `pairRatio_lt_half` |
| `sec:renewal`, the homogeneous system | `audit_homogeneousSystem_facts` | `homogeneousSystem_isDimension`, `homogeneousSystem_stronglySeparated` |
| `sec:renewal`, the paired system | `audit_pairSystem_facts` | `pairSystem_isDimension`, `pairSystem_stronglySeparated` |
| `sec:renewal`, existence of `μ_A` | `audit_exists_cantor_measure` | `exists_unique_isNatural_homogeneousSystem` |
| `sec:renewal`, existence of `μ_B` | `audit_exists_pair_measure` | `exists_unique_isNatural_pairSystem` |
| `eq:non-lattice` is non-lattice type | `audit_pairSystem_nonArithmetic_iff` | `pairSystem_nonArithmetic_iff` |
| Internal homogeneous periodic extension | `audit_exists_periodic_extension` | `exists_periodic_extension_of_shift` |
| Internal homogeneous profile `G̃_A` | `audit_exists_periodic_profile` | `homogeneous_periodic_profile` |
| `sec:renewal`, non-constancy of the homogeneous periodic profile as a consequence of `thm:lattice-nonconvergence` | `audit_cantor_nonconstant` | `HomogeneousNonconstancy.homogeneous_G_nonconstant_on_tail`, an independent density proof retained in the library |
| `thm:lattice-nonconvergence`, non-constancy of `G̃` | `audit_lattice_nonconvergence` | `System.IsNatural.not_tendsto_G_of_lattice`, together with `System.lattice_G_limit`: existence of a continuous periodic limit makes its non-constancy equivalent to the absence of a limit for `G`. The paper compares two phases directly, using the translated word maps `S_{ij}` and `S_{ji}` and the Ahlfors lower bound. The library retains the equivalent contradiction argument: a limit of `G` gives constant periodisation (`tendsto_sum_renewalDefect`) and a Lipschitz bound on `Φ_×` (`crossPhi_sub_le_of_tendsto_G`); `IsFeasible.map_comp_ne` and `sq_mul_phi_le_crossPhi_sub` then give `Φ(δ) = O(δ)`, contradicting Ahlfors regularity for `s < 1` |
| The smoothing operator at the start of `sec:smoothing` (the internal label `eq:periodic-smoothing`), `Tg` is `ℓ/2`-periodic | `audit_smoothOp_periodic` | `smoothOp_periodic` |
| The smoothing operator at the start of `sec:smoothing` (the internal label `eq:periodic-smoothing`), `Tg` continuous and `ℓ/2`-periodic | `audit_smoothOp_continuous_periodic` | `continuous_smoothOp` |
| `sec:smoothing`, the coefficient is Mathlib's | `audit_fourierCoeffP_eq_fourierCoeffOn` | `fourierCoeffP_eq_fourierCoeffOn` |
| `eq:fourier-multiplier`, the Fourier identity | `audit_fourier_multiplier` | `fourierCoeffP_smoothOp` |
| `eq:gamma-multiplier`, the evaluation | `audit_gamma_multiplier` | `multInt_eq_gammaMult` |
| `eq:gamma-multiplier`, non-vanishing | `audit_gammaMult_ne_zero` | `gammaMult_ne_zero` |
| `thm:smoothing-injective`, multiplier | `audit_multInt_ne_zero` | `multInt_ne_zero` |
| `thm:smoothing-injective`, Fourier uniqueness | `audit_fourier_uniqueness` | `eq_zero_of_fourierCoeffP_eq_zero` |
| `thm:smoothing-injective` | `audit_smoothing_injective` | `smoothOp_injective` |
| `thm:smoothing-injective`, kernel form | `audit_smoothing_kernel_trivial` | `smoothOp_eq_zero` |
| `thm:smoothing-injective`, consequence | `audit_smoothing_nonconstant` | `smoothOp_nonconstant` |
| `thm:smoothing-injective`, bundled | `audit_thm_smoothing_injective` | `thm_smoothing_injective_homogeneous` |
| `sec:smoothing`, positivity of `H̃_A^s` | `audit_smoothOp_pos` | `smoothOp_pos` |
| `thm:renewal-limits`, the non-lattice limit `eq:g-non-lattice-limit`, applied to the two-map system of `μ_B` | `audit_gb_limit` | `homogeneous_gb_limit` |
| `thm:profile-asymptotics`, non-lattice case, as applied to a non-lattice `μ` in the proof of `thm:cantor-application` | `audit_profile_asymptotics_non_lattice` | `profile_asymptotics_nonLattice` |
| `thm:profile-asymptotics`, non-lattice case, with the expected profile written as the normalised correlation integral of `eq:expected-profile` | `audit_non_lattice_correlation_limit` | `non_lattice_correlation_limit` |
| Internal homogeneous exponential-error bound | `audit_profile_asymptotics_lattice` | `exists_lattice_bound` |
| Internal homogeneous exponential error in big-`O` shape | `audit_profile_asymptotics_lattice_bigO` | `exists_lattice_bound` |
| `thm:cantor-application`, homogeneous correlation oscillation | `audit_lattice_correlation_oscillation` | `homogeneous_lattice_correlation_oscillation`; the paper obtains this directly from `thm:profile-asymptotics` |
| `thm:profile-asymptotics`, general dichotomy | `audit_thm_profile_asymptotics` | `lattice_profile_asymptotics_nonconstant`, `non_lattice_limit`, `profile_asymptotics_nonLattice`: the lattice limit is `T G̃` for the periodic limit `G̃` of `G` from the finite-delay renewal theorem, non-constant because a constant `G̃` would make `G` converge, against `thm:lattice-nonconvergence`, and `thm:smoothing-injective` carries non-constancy through `T` |
| Internal homogeneous refinement and `thm:profile-asymptotics` for the non-lattice two-map system of `μ_B`, bundled two-map consequences | `audit_homogeneous_profile_asymptotics` | `homogeneous_thm_profile_asymptotics` |
| `thm:main` for two non-lattice measures whose limits in `thm:profile-asymptotics` differ, the step taken in the proof of `thm:fixed-dimension-separation` | `audit_non_lattice_separation` | `non_lattice_separation`, both systems under the open set condition |
| Independence in the proof of `thm:variance` | `audit_disjoint_increments_indep` | `disjoint_increments_indep` |
| Gaussian return bound used in the proof of `thm:four-point-integral` | `audit_gaussian_four_point` | `gaussian_four_point` |
| Internal almost everywhere Gaussian return bound | `audit_gaussian_four_point_ae` | `gaussian_four_point_ae` |
| Internal Gaussian bounds and independence, bundled | `audit_thm_gaussian_four_point` | `gaussian_four_point_bundled` |
| Block mass and return estimates in the proof of `thm:four-point-integral` | `audit_endpoint_block_mass` | `endpoint_block_mass` |
| Dyadic form of the mass and return estimates for `thm:four-point-integral` | `audit_endpoint_block_mass_dyadic` | `endpoint_block_mass_dyadic` |
| `thm:four-point-integral` | `audit_four_point_integral` | `four_point_integral` |
| `thm:variance` | `audit_variance` | `variance_four_point` |
| `thm:variance`, final assertion | `audit_varScale_isLittleO` | `varScale_div_tendsto_zero` |
| `thm:variance`, bundled | `audit_thm_variance` | `variance_bundled` |
| `eq:y-variance` | `audit_y_variance` | `y_variance` |
| `eq:grid-convergence` | `audit_grid_convergence` | `grid_convergence` |
| `eq:monotone-fill` | `audit_monotone_fill` | `monotone_fill` |
| `thm:uniform-concentration` | `audit_uniform_concentration` | `uniform_concentration` |
| `sec:concentration`, the oscillation `d_A` | `audit_lattice_gap` | `smoothOp_gap` |
| `thm:base-five-profiles` | `audit_base_five_profiles` | `baseFive_profiles`: the values `eq:base-five-correlation` at every scale `5⁻ⁿ`, proved in the paper by counting touching cylinders and in Lean by equivalent first-digit recursions; profile separation follows from the distinct continuous periodic limits, with `g₁(0) = 3/2 ≠ 1 = g₂(0)`, and `thm:smoothing-injective`. The paper cites `thm:renewal-limits` and the smoothing step of `thm:profile-asymptotics`; the library computes the limits explicitly and applies dominated convergence in `eq:h-definition`. |
| `thm:base-five-profiles`, the first display after it | `audit_base_five_occupation_laws` | `MinkowskiReconstruction.baseFive_occupationLaw_mutuallySingular`: `thm:main` for the two natural measures, Frostman by the open set condition |
| `thm:base-five-profiles`, the second display after it | `audit_base_five_image_laws` | `MinkowskiReconstruction.baseFive_brownianImageLaw_mutuallySingular`: `thm:minkowski-reconstruction` for both systems under the open set condition, and the descent of the occupation-law singularity through the Borel reconstruction map |
| `sec:obstruction`, the signed convolution | `audit_conv_reflect` | `conv_reflect_eq_map_sub` |
| `thm:homometric-example` | `audit_homometric_example` | `homometric_example`, with the non-isometry of the attractors from `HomometricMeasures.isEmpty_isometryEquiv` |
| `sec:fixed-dimension-family`, existence and uniqueness of `K_p` and `μ_p` | `audit_exists_fixed_dimension_measure` | `System.exists_unique_isNatural` for `fixedSystem`, the system `x ↦ λ₁x`, `x ↦ λ₂x + 1 - λ₂` with `λ₁ = p^{1/s}`, `λ₂ = q^{1/s}`, whose dimension is `s` (`fixedSystem_isDimension`) |
| `sec:fixed-dimension-separation`, `J(p) = (2pq)^{-1} ∫₀¹ δ^{-s} dC^×_δ(μ_p)` | `audit_fixed_moment_natural` | `fixedMoment_eq_natural`: `fixedMoment` is the double Bernoulli integral of `Z_p^{-s}` over the coding, and the law of the coded point is `μ_p` (`map_fixedCode_twoBern`, by Hutchinson uniqueness) |
| `sec:small-dimension`, `J(p) ≥ 1` | `audit_fixed_moment_ge_one` | `one_le_fixedMoment`, since `Z_p ≤ 1` |
| `eq:log-derivative-mean` | `audit_log_derivative_mean` | `hasDerivAt_entropyFactor` for `κ = (pq/E)'/(pq/E)`, and `hasDerivAt_fixedMean` for the mean, in the product form `H̄_s' = C_s (pq/E)(κ J(p) + J'(p))` with `C_s = 2^{1-s} Γ(1-s)`, wherever `J(p)` is differentiable |
| `thm:entropy-factor` | `audit_entropy_factor` | `kappa_pos`, `kappa_ge_of_le`, `kappa_ge_of_ge`: `Φ = q² log(1/q) - p² log(1/p)` is strictly concave on `[0, 1/2]` with `Φ(0) = Φ(1/2) = 0` (`strictConcaveOn_kappaNum`), hence positive between; `log(1/q) ≥ p` and `q log(1/q) ≤ p` give the explicit bound for `p ≤ 1/50`; and the constant `c` for `[p₁, 1/2)` is read off the chord of the concave `Φ` from `(p₁, Φ(p₁))` to `(1/2, 0)` |
| `eq:initial-symbol-decomposition` | `audit_leading_ones` | `hasSum_leadingTerm`: the first-letter recursion `leadingAux_rec` of the Bernoulli double integral, with the remainder `qᴺ h_N` bounded |
| `eq:main-term` | `audit_main_term` | `mainTerm_eq`, with `T(p) = log(1/b) = log(1/q)/s` (`fixedT`) |
| Internal combination of `thm:main-term-derivative`, `thm:remainder-derivative`, and `thm:second-derivative-small-s` | `audit_fixed_dimension_derivative_bounds` | `Section9Estimates.derivative_bounds`: `hasDerivAt_fixedMoment_small` combines the main-term and remainder estimates; `fixedMoment_second_derivative` proves the second bound, including existence of the derivatives. All constants and parameter ranges agree with the paper. |
| `thm:main-term-derivative` | `audit_main_term_derivative` | `exists_hasDerivAt_mainTerm`: termwise differentiation of the sum, internally `mainS` (`hasDerivAt_mainS`), the Riemann-sum comparison against the total variation of `g` (`abs_tsum_sub_integral_le`), the integrals of `f'`, `x f''`, `g`, `g'` on `(T(p), ∞)` (`MainTermIntegrals`), and `s ∫_{T(p)}^∞ f ≤ 2.3` from `f ≤ x^{-s}` on `(0, 1]` and `f ≤ (1 - e^{-1})^{-s} e^{-sx}` on `[1, ∞)`; the constant is `6` |
| `thm:remainder-derivative` | `audit_remainder_derivative` | `exists_hasDerivAt_fixedMoment`: on the disc `|z - p| ≤ p/2` the level sums `Λ_n^{(m)}` converge uniformly to holomorphic `Λ_n` with `eq:lambda-bound` (`norm_kernelLimit_sub_le`), `Δ = Λ - J₀` is holomorphic (`differentiableOn_complexDelta`) with `sup_U |Δ| ≤ 1296 s λ_{1,max} p^{-1-s}` (`norm_complexDelta_le`), Cauchy's estimate gives `Δ'` (`norm_deriv_complexDelta_le`), and `Δ(x) = J(x) - J₀(x)` on the real diameter by dominated convergence of the level sums (`complexDelta_ofReal`) |
| `thm:second-derivative-small-s` | `audit_second_derivative_small_s` | `fixedMoment_second_derivative`: on `|z - p| ≤ 5·10⁻⁵` both contractions have modulus at most `γ ≤ 1/12` (`gammaQ_le`), the cross kernel is within `18 s γ` of `1` by the mean value inequality for `ζ ↦ ζ^{-s}` on `|ζ - 1| ≤ 1/2` (`norm_crossKernelC_sub_one_le`), the level sums converge to `Λ(z)` with `|Λ(z) - 1| ≤ 32 s γ` (`norm_crossLimit_sub_one_le`), `Λ(z) = J(x)` on the real diameter (`crossLimit_ofReal`), and Cauchy's estimate for the second derivative, with constants `18`, `32` and `10¹¹` as in the paper |
| the symmetry `J(p) = J(1-p)` in the proof of `thm:small-dimension-monotone` | `audit_moment_symmetric_derivative` | `deriv_fixedMoment_half`: `Λ(1-z) = Λ(z)` on the disc around `1/2` (`crossLimit_one_sub`), since flipping every letter reflects the coded points up to the base point (`one_sub_cpointSeq_eq`) and the cross kernel is reflection invariant, so the level sums of `z` and `1 - z` differ by `O((γB²)^m)`; the complex derivative at `1/2` then vanishes, and the real derivative is its real part |
| `thm:small-dimension-monotone` | `audit_small_dimension_monotone` | `exists_strictMonoOn_fixedMean`: `|J'(p)| < κ(p)` on `(0, 10⁻⁴]` from the entropy and first-derivative bounds and `(3p/2)^{1/s} ≤ (3p/2)⁴` (`abs_deriv_fixedMoment_lt_kappa_small`), and on `[10⁻⁴, 1/2)` from the second-derivative bound, `J'(1/2) = 0` and the mean value theorem (`abs_deriv_fixedMoment_lt_kappa_large`); `s₀ = min(2·10⁻⁵, c/10¹¹)` for the constant `c` of `thm:entropy-factor` at `p₁ = 10⁻⁴`, since `γ ≤ 2 s²/r²` (`gammaQ_le_sq`); then `strictMonoOn_of_deriv_pos` through `eq:log-derivative-mean` and `J(p) ≥ 1` |
| `thm:critical-set-finite`, the strict increase on `(0, p₀]` | `audit_critical_set_finite` | `exists_strictMonoOn_fixedMean_small`: `|J'(p)| p (1 - log p) ≤ (6 + 3000 s (3/2)^{1/s}) √p (1 - log p)` for `p ≤ 1/50` (`abs_deriv_fixedMoment_mul_le`, using `1/s - 1 - s ≥ 1/2`) and `√p (1 - log p) ≤ 5 p^{1/4}` (`sqrt_mul_one_sub_log_le_rpow`), so `p₀ = min(1/50, (0.17/C)⁴)` |
| `thm:critical-set-finite`, bundled | `audit_thm_critical_set_finite` | the endpoint above and `criticalSet_finite`: `D_s ⊆ [p₀, 1/2]` by the positive derivative on `(0, p₀)` (`exists_deriv_fixedMean_pos_small`), and an infinite subset of a compact interval has an accumulation point (`Set.Infinite.exists_accPt_of_subset_isCompact`), which `not_accPt_criticalSet` forbids |
| `thm:small-dimension-monotone`, bundled with its second sentence | `audit_thm_small_dimension_monotone` | `audit_small_dimension_monotone` and `audit_fixed_dimension_laws`; distinct parameters have distinct means by strict monotonicity |
| the remark after `thm:small-dimension-monotone`, the maximum of the mean at `p = 1/2` alone for `s ≤ s₀` | `audit_small_dimension_maximum` | `exists_strictMonoOn_fixedMean` and `fixedMean_lt_half_of_strictMonoOn`: strict monotonicity on `(0, 1/2]` and the symmetry `fixedMean_symm` |
| `thm:fixed-dimension-profiles`, `eq:fixed-dimension-mean` | `audit_fixed_dimension_mean` | `fixedSystem_tendsto_avg_H`: `System.IsNatural.tendsto_avg_H` under the open set condition (`fixedSystem_openSetCondition`, from strong separation with gap `1 - λ₁ - λ₂`), with `m = h(p)/s` (`fixedSystem_renewalMean`), `Φ_× = 2pq ℙ(Z_p ≤ δ)` (`fixedSystem_crossPhi`), `∫ z = 2pq J(p)/s` (`fixedSystem_integral_renewalDefect`, by Tonelli) and `∫ φ = 2^{-s} Γ(1-s)`; the expected profile is `H` by `smoothing`. The paper computes the mean for both cases together, averaging the renewal limits and lattice periodisation and then the smoothing formula. |
| `thm:fixed-dimension-profiles`, the non-lattice limit | `audit_fixed_dimension_non_lattice` | `fixedSystem_tendsto_H_nonLattice`, through `thm:non-lattice-limit`, with `log λ₁/log λ₂ ∉ ℚ` read as non-arithmeticity by `fixedSystem_nonArithmetic_iff` |
| Internal lattice Fourier expansion of the expected profile of `μ_p`, beyond `thm:fixed-dimension-profiles` | `audit_fixed_dimension_periodic` | `fixedSystem_periodic`: the Fourier transform of the inhomogeneous term (`fixedSystem_integral_renewalDefect_char`, by Fubini), the coefficients of the lattice limit from the renewal average with a character (`System.IsNatural.fourierCoeffP_latticeLimit`), the multiplier `eq:gamma-multiplier`, the bound `‖Γ(1-ζ)‖ ≤ Γ(2-s)/‖1-ζ‖` for absolute summability (`summable_norm_fixedDimCoeff`), and Fourier inversion |
| `eq:fixed-dimension-correlation` | `audit_fixed_dimension_correlation` | `fixedSystem_correlation`: `S_μ(r) = ∫ g_r(|x - y|) d(μ×μ)` by `eq:gaussian-reduction`, Hutchinson's identity in both coordinates on `μ × μ` (`System.IsNatural.lintegral_prod_eq_double_sum`) gives the recursion `T(c) = p² T(cλ₁) + q² T(cλ₂) + 2pq 𝔼 g_r(c Z_p)` for `T(c) = ∫ g_r(c|x - y|)` (`corrScale_recursion`), iterated along the antidiagonals of `ℕ²` with Pascal's rule (`sum_antidiagonal_succ_pascal`); `0 ≤ T ≤ 1` bounds the remainder by `∑_{j+k=m} C(m,j) p^{2j} q^{2k} = (p² + q²)^m`, uniformly in `r`, and the series of non-negative terms sums to `T(1)` along the triangles `{j + k < m}` |
| Internal remainder bound `(p² + q²)^m` for `eq:fixed-dimension-correlation`, uniform in `r` | `audit_fixed_dimension_correlation_remainder` | `fixedSystem_correlation`, as in the row above |
| `thm:fixed-dimension-profiles`, bundled | `audit_thm_fixed_dimension_profiles` | `audit_fixed_dimension_correlation`, `audit_fixed_dimension_mean` and `audit_fixed_dimension_non_lattice` |
| Internal bundle with the remainder bound and the lattice expansion | `audit_thm_fixed_dimension_profiles_lattice` | `audit_fixed_dimension_correlation_remainder`, `audit_fixed_dimension_mean`, `audit_fixed_dimension_non_lattice` and `audit_fixed_dimension_periodic`, the lattice span from `System.nonArithmetic_or_exists_lattice` |
| the mean symmetry in `sec:fixed-dimension-family` and `J(p) = J(1-p)` in `sec:small-dimension` | `audit_fixed_dimension_symmetry` | `fixedMoment_symm`, `fixedMean_symm`: flipping every letter in the level sums reflects the coded points up to the base point (`one_sub_cpointSeq_eq`), the kernel is Lipschitz on `[0,1]²` (`abs_rpow_fixedCross_sub_le`), so the level sums of `p` and `1-p` differ by `O(γ^m)` (`norm_levelSum_one_sub_sub_le'`), and both converge to the moments (`tendsto_levelSum_ofReal`) |
| `thm:fixed-dimension-analyticity` | `audit_fixed_dimension_analyticity` | `analyticAt_fixedMoment`, `analyticAt_fixedMean`: on the disc `|z - p₀| ≤ r` of `GoodRadius` the branches are Lipschitz (`norm_ca_sub_le`), the coded points move by at most `C|z - p₀|` (`norm_cpointSeq_sub_le`) and stay in a neighbourhood of `[0,1]` on which every cross distance has real part at least `g₀/2` (`re_crossBase_ge_of_mem`), the level sums converge uniformly to a holomorphic `Λ(z)` (`incrementBound_disc`, `differentiableOn_crossLimit_disc`) equal to `J(x)` on the real diameter (`crossLimit_eq_fixedMoment_of_mem`), and the restriction of a holomorphic function to the real line is real analytic (`AnalyticAt.restrictScalars`); multiplying `J(p)` by `2p(1-p)` gives the paper's cross-term integral, and `E` is analytic by `analyticAt_log` |
| `thm:fixed-dimension-range` | `audit_fixed_dimension_range` | continuity from analyticity, positivity from `J(p) ≥ 1`; the limit `0` from `J(p) ≤ 2^s J₀(p)` once `λ₁ ≤ (1-λ₂)/2` (`fixedMoment_le_mainTerm`, through `eq:initial-symbol-decomposition`), `J₀(p) ≤ (s/q)(∫_{T(p)}^∞ f + T(p) f(T(p)))` (`mainTerm_le`) and `s ∫_{T(p)}^∞ f ≤ s/(1-s) + 1.59` (`mul_integral_mainF_le'`), so `J(p)` is bounded near `0` (`fixedMoment_le_of_small`), while `pq/h(p) ≤ 1/log(1/p)` (`entropy_ge`) |
| Internal consequence of `thm:fixed-dimension-separation`: an uncountable subfamily with pairwise singular laws | `audit_fixed_dimension_subfamily` | `exists_uncountable_injOn_fixedMean`, by the intermediate value theorem, uncountable because the image of the mean is an interval of positive length, and `audit_fixed_dimension_laws` |
| `thm:fixed-dimension-separation`, the analytic assertions | `audit_fixed_dimension_separation` | `not_accPt_criticalSet`, `strictMono_or_anti_of_ne_zero`, `not_accPt_levelSet`: the identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` on `(0,1)` for the derivative and for `H̄_s - H̄_s(p₁)`, non-constancy from the limit `0` at `0` and positivity at `1/2` (`fixedMean_not_const`), the sign of the derivative on an interval free of critical points by the intermediate value theorem |
| the paragraph after `thm:fixed-dimension-separation`, the interval `(1/2 - ε_s, 1/2)` | `audit_fixed_dimension_eps` | `exists_eps_strictMono`, `ε_s` from the isolated point `1/2` |
| the paragraph after `thm:fixed-dimension-separation`: for each fixed parameter, at most countably many possible exceptions to singularity, finitely many in every interval bounded away from zero | `audit_fixed_dimension_level_countable`, `audit_fixed_dimension_laws` | `levelSet_countable`, from the finiteness of a level set on each `[1/(n+2), 1/2]`; every interval bounded away from zero is contained in one such interval, and `audit_fixed_dimension_laws` gives both singularities outside the level set |
| `thm:fixed-dimension-separation`, the singular laws | `audit_fixed_dimension_laws` | `MinkowskiReconstruction.fixedSystem_occupationLaw_mutuallySingular`, `fixedSystem_brownianImageLaw_mutuallySingular`: distinct Cesàro means give separated profiles (`exists_ge_abs_sub_of_tendsto_avg`), `thm:main` with Frostman from the open set condition, and the pathwise tube reconstruction of both systems through the common Borel reconstruction map |
| `thm:fixed-dimension-separation`, bundled | `audit_thm_fixed_dimension_separation` | the two endpoints above |

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
inequality.  Six traps, and how each is closed.

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
- **The four times of `sec:variance` are non-negative by type.** `jointReturn` takes
  `ℝ≥0` arguments, so no clipping hides in `audit_gaussian_four_point`.  Where the
  quadruple is integrated against `μ⁴` the times are read through `Real.toNNReal`, which
  is the identity `μ⁴`-almost everywhere because `μ` sits on `[0,1]`; the block bound of
  `audit_endpoint_block_mass`, which quantifies over quadruples rather than integrating,
  carries `0 ≤ x₁` explicitly.
- **Frostman with `0 < s` is what removes the diagonal.** Real division by zero is `0`
  in Lean, so the integrand of `eq:gaussian-reduction` takes the value `0`, not `1`, on
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

- **`𝒫(ℝ²)`: the two σ-algebras agree.** Mathlib's
  `ProbabilityMeasure Plane` is measurable through the evaluations `ν ↦ ν s`, while the
  paper uses the Borel σ-algebra of the weak topology. `borel_probabilityMeasure_eq_giry`
  identifies them. Mathlib has neither a
  `BorelSpace (ProbabilityMeasure Ω)` instance nor any `borel (ProbabilityMeasure Ω) = _`
  lemma; the proof is in `WeakBorel.lean` and needs only second countability, pseudo
  metrisability and `BorelSpace`, so it is not special to `ℝ²`.
- **Frostman is stated on closed balls with arbitrary centres.** `eq:frostman` uses open
  balls and centres in `[0,1]`; `IsFrostman` uses closed balls and arbitrary centres,
  which is what the Fubini step of `eq:correlation-frostman` consumes. `IsFrostmanOpen` is the
  paper's shape, and `audit_frostman_conventions` proves the two agree up to the change
  of constant the paper allows itself: `A` one way, `3^s A` the other.
- **`eq:profile-separation` is written out.** `limsup_{v→∞} |H₁ - H₂| > 0` appears as
  `∃ ε > 0, ∀ V, ∃ v ≥ V, ε ≤ |H₁(v) - H₂(v)|`, which is the same statement for a
  non-negative function and avoids the junk value `limsup` takes on unbounded functions.
  The same rewriting turns the homogeneous `liminf < limsup` consequence of `thm:profile-asymptotics`
  into `audit_lattice_correlation_oscillation`.
- **The lattice limit is asymptotic, and non-constant by `thm:lattice-nonconvergence`.**
  `audit_thm_profile_asymptotics` uses the subgroup generated by the full log-ratios,
  with span `ℓ`, and gives a continuous, positive, non-constant limit of period `ℓ / 2`.
  `LatticeProfile.lean` applies the finite-delay renewal theorem to `A + 1 - G(2v)`,
  converts uniform phase convergence to convergence on the half-line, and smooths
  the vanishing error; the lower regularity bound ensures positivity.
  `LatticeNonconstancy.lean` proves that `G` has no limit for a lattice system, so the
  periodic limit of `G` is non-constant, and `thm:smoothing-injective` carries this through
  `T`. The separate homogeneous endpoints prove the sharper exponential error.
- **IFS terminology.** The paper calls the defining family of similarities an iterated
  function system (IFS). Its Lean type is `System`; this identifier denotes an IFS
  throughout the formalisation.
- **Orientation-reversing similarities are carried by a sign.** The paper's IFSs are
  finite families of contracting similarities of `ℝ` mapping `[0,1]` into itself, the
  orientation-reversing ones included, and `sec:reconstruction` uses time reversal of the
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
  `eq:neighbourhood-union-scaling` for both orientations. The two named systems, the
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
  unconditional determinant bound behind it. The proof of `thm:four-point-integral`
  discards repeated endpoints and uses determinant positivity only for overlapping
  intervals, so the internal statement is stronger than this application requires.
Four statements deserve a note on what their endpoints assert.

- **The fixed-dimension family.** The endpoints are stated on `fixedMean s p`, which is
  the right-hand side of `eq:fixed-dimension-mean`,
  `2^{-s} Γ(1-s) (∫₀¹ δ^{-s} dC^×_δ(μ_p))/h(p)`. The code writes this as
  `2^{1-s} Γ(1-s) pq · fixedMoment s p / h(p)`. The identification follows from
  `audit_fixed_moment_natural` and `fixedSystem_crossPhi`: `fixedMoment s p` is the
  normalised integral `J(p)` of `sec:small-dimension`. `audit_exists_fixed_dimension_measure`
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
  non-constructive constant of `thm:entropy-factor`, which is what the tex asserts.  The
  derivatives in `audit_main_term_derivative`, `audit_remainder_derivative` and
  `audit_second_derivative_small_s` are asserted to exist (`HasDerivAt`), not read off
  `deriv`, so the bounds are never vacuous; `criticalSet` and the level sets are defined
  through `deriv` and `fixedMean`, which analyticity makes the genuine derivative and
  values.

- **The homogeneous periodic profile in `sec:renewal`.** The paper obtains
  non-constancy directly from `thm:lattice-nonconvergence`. `audit_cantor_nonconstant`
  asserts non-constancy on every tail for every `0 < λ < 1/2`, with an independent
  proof by the density argument of `HomogeneousNonconstancy`. Its intermediate
  first-difference and periodisation identities are internal to that proof.
- **`thm:homometric-example`.** The endpoint asserts everything the proposition does:
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

- **`thm:base-five-profiles`.** The two systems are `baseFiveSystem` at the digit sets
  `{0,1,4}` and `{0,2,4}`, and the natural measures enter as `IsNatural` hypotheses, as
  in `audit_cantor_application`; `naturalMeasure_selfSimilar` supplies such a measure
  for every system, so the hypotheses are satisfiable.  The Frostman constants are not
  hypotheses: both systems satisfy the open set condition with `U = (0,1)`, and
  `System.OpenSetCondition.exists_isFrostman` produces them.  The second assertion,
  `limsup |H_{μ₁}^s - H_{μ₂}^s| > 0`, is stated as the separation
  `∃ ε > 0, ∀ V, ∃ t ≥ V, ε ≤ |H_{μ₁}^s(t) - H_{μ₂}^s(t)|`, the hypothesis shape of
  `thm:main`, which is what the two displays after the proposition consume.  The
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
`audit_profile_asymptotics_lattice_bigO` gives its asymptotic form. References to
`eq:ha-asymptotic` in code comments denote this retained library refinement, which
is not part of the paper. Likewise, `eq:gb-limit`, `eq:hb-asymptotic` and
`thm:non-lattice-separation` in code comments and in the module index are internal
labels for three statements the paper no longer writes out: the non-lattice limit of
`thm:renewal-limits` read at the two-map system of `μ_B`, `thm:profile-asymptotics` in
the non-lattice case read at `μ_B`, and `thm:main` for two non-lattice measures whose
limits in `thm:profile-asymptotics` differ, the step taken in the proof of
`thm:fixed-dimension-separation`.

### What the comparator does not check

Comparator compares the four headline endpoints of `Challenge.lean` with
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
proves nothing about the derivation: `gammaMult` is the closed form
`eq:gamma-multiplier`, `multInt` is the integral `eq:fourier-multiplier` defining the
multiplier, and it is `audit_gamma_multiplier` that connects them.  Likewise
`fixedMoment` is the moment `J(p)` through the Bernoulli coding and `fixedDimCoeff` is
the coefficient of `eq:fixed-dimension-periodic` written out; `audit_fixed_moment_natural`
and the endpoints of `thm:fixed-dimension-profiles` are what connect them with the natural
measure and the expected profile.

## Not formalised

The discussion after `thm:homometric-example` and the introduction's account of the
literature carry no statement and no endpoint. `thm:level-sums` has no endpoint
of its own: its increment bound, uniform limit and `eq:level-sum-bound` are the generic
`norm_levelSum_succ_sub_le`, `tendsto_levelSum`, `norm_limitSum_sub_le` and
`differentiableOn_limitSum` of `LevelSums.lean`, while the holomorphy of the level sums and
the identification of the limit at a real parameter are proved for each kernel the paper
applies the lemma to (`Analyticity.lean`, `Kernel.lean` with `Decomposition.lean`, and
`SecondDerivative.lean`); `eq:coded-point-bounds` is `cpointSeq_succ_eq` with
`norm_cratioSeq_le` and `norm_cpointSeq_le`. `eq:small-p-margin` is assembled inside the
proofs of `thm:small-dimension-monotone` and `thm:critical-set-finite` and has no endpoint
of its own.
The Fourier transform of the inhomogeneous term in the proof of
`thm:fixed-dimension-profiles`, which the tex states at frequency zero only, is proved as
`fixedSystem_integral_renewalDefect_char` without an endpoint of its own, as are the displays inside the proofs of `sec:small-dimension`:
`eq:contraction-modulus-bounds` (`five_alphaP_le`), `eq:contraction-disc` (`discR_le`, `one_sub_discR_ge`),
`eq:kernel-bounds` (`norm_kernelN_le`, `norm_kernelN_sub_le`) and `eq:lambda-bound`
(`norm_kernelLimit_sub_le`). The periodic-limit existence and uniform asymptotics in
`thm:renewal-limits` are proved by `System.lattice_G_limit`; the explicit
periodisation formula is not separately formalised. The library's proof of
`thm:lattice-nonconvergence` retains the constant-periodisation identity
(`System.IsNatural.tendsto_sum_renewalDefect`, internally called `eq:lattice-periodisation`)
and the cross-term Lipschitz bound (`System.IsNatural.crossPhi_sub_le_of_tendsto_G`,
internally called `eq:cross-lipschitz`), without endpoints of their own. The paper's direct
phase comparison and the library's contradiction argument prove the same non-constancy
statement. The elementary integral calculations in `thm:four-point-integral` have no separate
endpoints; the same bound is proved by dyadic summation in the library. The separate crossing
and nested determinant calculations are proved
in `FourPoint.lean` without endpoints of their own; they imply the common lower bound
used in the paper.
The claim the project makes is coverage of every numbered result, plus the displayed
claims that a later result cites or that carry a hypothesis of their own; it is not
coverage of every display.
`eq:non-lattice`, the rational independence of `log(1/c)/log 2`, is an open lattice
assertion in the paper. It appears in two forms: as `System.NonArithmetic` in the
statements about a general system, and literally, as `Irrational (log (1/c) / log 2)`,
in the endpoints about `μ_B`. `audit_pairSystem_nonArithmetic_iff` is the equivalence
between them.
