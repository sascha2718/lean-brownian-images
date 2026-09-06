# Correspondence with the paper

This document argues the correspondence between the formal statements and the LaTeX
source `BrownianImagesComplete.tex`: what `Solution.lean` and `Challenge.lean` state,
how each result of the paper maps to an endpoint, and where a formal statement could
quietly diverge from the prose. Labels such as `thm:main` are the labels of the LaTeX
source. The comparator compares `Challenge.lean` with `Solution.lean` and never with
the paper, so this correspondence is a human obligation, and this document is where
it is argued.

## The statement layer

`Solution.lean` is the formal statement of the paper: 84 endpoints named
`audit_<slug>`, in document order, each proved by a direct application of a library
declaration. Adding a result to the paper means adding its statement there first; the
design work is in the statement.

`Challenge.lean` is the comparator's challenge file and carries only the headline
theorems, with statement text identical to `Solution.lean` and `sorry` in place of the
proofs, on Mathlib-only copies of the definitions the statements need: `thm:main` as
`audit_main`, and `thm:cantor-application` as `audit_cantor_application` with
`audit_cantor_application_pair` and `audit_exceptional_parameters_countable` covering
its final sentence. It is not part of the library and not a default target, which is
what lets it carry `sorry` while the library stays clean. The comparator configuration
kernel-checks exactly these four; the other endpoints are checked by
`lake build Solution`, and the library declares no axiom. The pair endpoint takes
the ratio bounds `0 < c < 1/2` of `eq:c-definition` as hypotheses rather than citing
`pairRatio_pos` and `pairRatio_lt_half`, so that no proof term appears in a statement
and no lemma has to live in `Challenge.lean`; the hypotheses are provable, so nothing
is vacuous.

**The correspondence is not one endpoint per theorem.** A theorem with several
assertions appears twice: once as a bundled `audit_thm_*` endpoint carrying the paper's
complete conclusion, and once as the individual endpoints its proof and its consumers
use. The four bundles are `audit_thm_smoothing_injective`, `audit_thm_profile_asymptotics`,
`audit_thm_gaussian_four_point`, `audit_thm_variance`.
Three further endpoints restate a general Lean result in the narrower shape the tex uses:
`audit_ahlfors_named` (the internal regularity endpoint for `μ_A` and `μ_B`),
`audit_endpoint_block_mass_dyadic` (the tex needs only dyadic `β, η`,
and carries both halves of the lemma), and `audit_profile_asymptotics_lattice_bigO`
(the `O(e^{-2(1-s)t})` shape `eq:ha-asymptotic` is written in, against the uniform bound
the proof produces). Where an endpoint is strictly more general than the tex, the
tex-shaped wrapper is the one to check the correspondence against.

Two pairs separate what the paper asserts from what its proof produces:
`audit_smoothing_injective` is injectivity of `T`, which is the literal claim, and
`audit_smoothing_kernel_trivial` is the kernel form the Fourier argument gives;
`audit_gaussian_four_point` is the pointwise bound under `Δ > 0`, and
`audit_gaussian_four_point_ae` is the almost everywhere statement the paper makes.

## State

Results and displayed claims of `BrownianImagesComplete.tex`, in document order, against
the `Solution.lean` endpoint and what stands behind it. All 84 endpoints are proved.
`Challenge.lean` retains `sorry` only as the independent statement file for the four
headline endpoints; no library or solution declaration uses `sorry`.

| Result | Endpoint | Proved by |
| --- | --- | --- |
| `thm:main` | `audit_main` | `main` |
| `thm:cantor-application` | `audit_cantor_application` | `homogeneous_application` |
| `thm:cantor-application`, named `μ_B` | `audit_cantor_application_pair` | `homogeneous_application_pair` |
| countability of exceptional homogeneous parameters | `audit_exceptional_parameters_countable` | `exceptionalParameters_countable` |
| `thm:minkowski-reconstruction` | `audit_minkowski_reconstruction` | `System.IsNatural.minkowskiReconstruction`; the non-arithmetic key-renewal limit and the arithmetic finite-delay periodic limit both feed the generation-cylinder quotient argument, giving pathwise recovery and a measurable reconstruction map from the compact Brownian image |
| Borel recovery from the pathwise tube limit | `audit_borel_reconstruction_of_pathwise` | `MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise` |
| transfer from occupation-law singularity to compact-image-law singularity | `audit_brownianImageLaw_mutuallySingular_of_pathwise` | `MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction`; `brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio` gives the direct self-similar generation-ratio form |
| `thm:cantor-set-application` | `audit_cantor_set_application` | `MinkowskiReconstruction.homogeneous_brownianImage_application`: the homogeneous source is reconstructed directly from its one-delay renewal equation, the non-arithmetic interval-separated source by the general reconstruction theorem, and occupation-law singularity descends to mutual singularity of the compact-image laws |
| `thm:cantor-set-application`, named `K_B` | `audit_cantor_set_application_pair` | `MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional` |
| `eq:neighbourhood-union-scaling` | `audit_tube_union_scaling` | `tubeCutoff_compactUnion`, `tubeMass_translate_dilate` |
| `eq:neighbourhood-defect-elementary` | `audit_tube_defect_elementary` | `tubeDefect_nonneg`, `tubeDefect_le_pairwiseTubeOverlapAreaSum` |
| `thm:neighbourhood-moments` | `audit_tube_moments` | `System.IsNatural.tubeMoments`; discrete-martingale maximal estimates give every unit Brownian-radius moment, and the stopping cover supplies the stated upper moments and positive lower mean |
| `thm:neighbourhood-overlap` | `audit_tube_overlap` | `System.IsNatural.tubeOverlap`; the separated-cylinder Gaussian-density estimate and the tube moment bound give uniform pairwise overlap and total defect estimates with integrability |
| `thm:neighbourhood-renewal` | `audit_tube_renewal` | `System.IsNatural.tubeRenewal`; the finite-delay law at the maximal lattice span has gcd one, its renewal masses converge, and the exact convolution identity yields uniform convergence on each arithmetic period |
| `thm:neighbourhood-concentration` | `audit_tube_concentration` | `System.IsNatural.tubeConcentration`; interpolation between first and third moments controls the normalized defect in `L²`, delayed contraction gives exponential decay, and Borel--Cantelli gives every fixed phase |
| the ambient σ-algebra on `𝒫(ℝ²)` | `audit_borel_eq_giry` | `borel_probabilityMeasure_eq_giry` |
| occupation has full mass | `audit_isProbabilityMeasure_occupation` | `IsPlanarBrownian.ae_isProbabilityMeasure_occupation` |
| `Law(W_*μ)` has total mass one | `audit_isProbabilityMeasure_occupationLaw` | `IsPlanarBrownian.isProbabilityMeasure_occupationLaw` |
| the law of the compact Brownian image has total mass one | `audit_isProbabilityMeasure_brownianImageLaw` | `IsPlanarBrownian.isProbabilityMeasure_brownianImageLaw` |
| occupation is measurable | `audit_aemeasurable_occupation` | `IsPlanarBrownian.aemeasurable_occupationProb` |
| internal Ahlfors regularity | `audit_ahlfors` | `exists_isAhlforsClosed` |
| the two Ahlfors ball conventions | `audit_ahlfors_conventions` | `IsAhlforsClosed.isAhlfors` |
| internal Ahlfors regularity for `μ_A`, `μ_B` | `audit_ahlfors_named` | `exists_isAhlfors_homogeneous_pair` |
| `thm:gaussian-reduction` | `audit_gaussian_reduction` | `gaussian_reduction` |
| `sec:setup`, atomlessness of `μ` | `audit_measure_singleton` | `IsFrostman.measure_singleton` |
| `sec:setup`, atomlessness of `dΦ` | `audit_pairLaw_noAtoms` | `pairLaw_measure_singleton` |
| `sec:setup`, continuity of `Φ` | `audit_phi_continuous` | `continuous_phi` |
| `eq:frostman`, the two ball conventions | `audit_frostman_conventions` | `IsFrostman.isFrostmanOpen`, `IsFrostmanOpen.isFrostman` |
| `eq:phi-frostman` | `audit_phi_le` | `phi_le` |
| `eq:smoothing` | `audit_smoothing` | `smoothing` |
| `sec:setup`, `φ` integrable and `∫φ > 0` | `audit_kern_integrable` | `kern_integrableOn`, `integral_kern_pos` |
| `thm:profile-uniform-continuity` | `audit_profile_uniform_continuity` | `profile_uniformContinuous` |
| `thm:renewal-recursion` (Φ) | `audit_renewal_recursion` | `phi_recursion` |
| `thm:renewal-recursion` (G) | `audit_g_recursion` | `g_recursion` |
| `thm:non-lattice-limit`, the renewal inputs | `audit_renewalLaw` | `isProbabilityMeasure_renewalLaw`, `integral_id_renewalLaw` |
| `thm:non-lattice-limit`, exponential moment | `audit_exists_expTransform_lt_one` | `exists_expTransform_lt_one` |
| `thm:non-lattice-limit` | `audit_non_lattice_limit` | `non_lattice_limit` |
| `eq:c-definition` | `audit_pairRatio` | `pairRatio_rpow`, `pairRatio_lt_half` |
| `sec:renewal`, the homogeneous system | `audit_homogeneousSystem_facts` | `homogeneousSystem_isDimension`, `homogeneousSystem_stronglySeparated` |
| `sec:renewal`, the paired system | `audit_pairSystem_facts` | `pairSystem_isDimension`, `pairSystem_stronglySeparated` |
| `sec:renewal`, existence of `μ_A` | `audit_exists_cantor_measure` | `exists_unique_isNatural_homogeneousSystem` |
| `sec:renewal`, existence of `μ_B` | `audit_exists_pair_measure` | `exists_unique_isNatural_pairSystem` |
| `eq:non-lattice` is non-arithmeticity | `audit_pairSystem_nonArithmetic_iff` | `pairSystem_nonArithmetic_iff` |
| `sec:renewal`, the periodic extension | `audit_exists_periodic_extension` | `exists_periodic_extension_of_shift` |
| `sec:renewal`, `G̃_A` itself | `audit_exists_periodic_profile` | `homogeneous_periodic_profile` |
| `thm:homogeneous-nonconstancy` | `audit_cantor_nonconstant` | `HomogeneousNonconstancy.homogeneous_G_nonconstant_on_tail` |
| `eq:periodic-smoothing`, `Tg` is `p/2`-periodic | `audit_smoothOp_periodic` | `smoothOp_periodic` |
| `eq:periodic-smoothing`, `Tg` continuous and `p/2`-periodic | `audit_smoothOp_continuous_periodic` | `continuous_smoothOp` |
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
| `sec:smoothing`, positivity of `H̃_A` | `audit_smoothOp_pos` | `smoothOp_pos` |
| `eq:gb-limit` | `audit_gb_limit` | `homogeneous_gb_limit` |
| `thm:profile-asymptotics`, `eq:hb-asymptotic` | `audit_profile_asymptotics_non_lattice` | `profile_asymptotics_nonLattice` |
| `thm:profile-asymptotics`, `μ_B` conclusion | `audit_non_lattice_correlation_limit` | `non_lattice_correlation_limit` |
| `thm:profile-asymptotics`, `eq:ha-asymptotic` | `audit_profile_asymptotics_lattice` | `exists_lattice_bound` |
| `eq:ha-asymptotic` in big-`O` shape | `audit_profile_asymptotics_lattice_bigO` | `exists_lattice_bound` |
| `thm:profile-asymptotics`, `μ_A` conclusion | `audit_lattice_correlation_oscillation` | `homogeneous_lattice_correlation_oscillation` |
| `thm:profile-asymptotics`, bundled | `audit_thm_profile_asymptotics` | `homogeneous_thm_profile_asymptotics` |
| `thm:non-lattice-separation` | `audit_non_lattice_separation` | `non_lattice_separation` |
| `thm:gaussian-four-point`, independence | `audit_disjoint_increments_indep` | `disjoint_increments_indep` |
| `thm:gaussian-four-point`, `eq:joint-return-bound` | `audit_gaussian_four_point` | `gaussian_four_point` |
| `eq:joint-return-bound` almost everywhere | `audit_gaussian_four_point_ae` | `gaussian_four_point_ae` |
| `thm:gaussian-four-point`, bundled | `audit_thm_gaussian_four_point` | `gaussian_four_point_bundled` |
| `thm:endpoint-block-mass` | `audit_endpoint_block_mass` | `endpoint_block_mass` |
| `thm:endpoint-block-mass`, dyadic | `audit_endpoint_block_mass_dyadic` | `endpoint_block_mass_dyadic` |
| `thm:four-point-integral` | `audit_four_point_integral` | `four_point_integral` |
| `thm:variance` | `audit_variance` | `variance_four_point` |
| `thm:variance`, final assertion | `audit_varScale_isLittleO` | `varScale_div_tendsto_zero` |
| `thm:variance`, bundled | `audit_thm_variance` | `variance_bundled` |
| `eq:y-variance` | `audit_y_variance` | `y_variance` |
| `eq:grid-convergence` | `audit_grid_convergence` | `grid_convergence` |
| `eq:monotone-fill` | `audit_monotone_fill` | `monotone_fill` |
| `thm:uniform-concentration` | `audit_uniform_concentration` | `uniform_concentration` |
| `sec:concentration`, the oscillation `d_A` | `audit_lattice_gap` | `smoothOp_gap` |
| `sec:obstruction`, the signed convolution | `audit_conv_reflect` | `conv_reflect_eq_map_sub` |
| `thm:homometric-example` | `audit_homometric_example` | `homometric_example`, with the non-isometry of the attractors from `HomometricMeasures.isEmpty_isometryEquiv` |

Proved outside the endpoint list, and load-bearing for it: the kernel layer
(`kern_pos`, `logKern_eq`, `logKern_le_exp_neg_mul_abs`, `logKern_integrable`), the
occupation layer (`continuous_plane_of_coord`, `IsPlanarBrownian.ae_continuous`,
`measurable_pathMap`, `IsPlanarBrownian.ae_occupationProb_toMeasure`), the empirical
layer (`corr_mono`, `Yprofile_le_of_le`, `measurable_corr`, `measurable_Yprofile`), the
period arithmetic
(`exists_nat_sub_mem_Ico`, `shift_add_nsmul`, `exists_periodic_extension`), the identification `phi_eq_pairLaw` of `Φ` as the
distribution function of `dΦ`, the homometric
layer (`diffMultiset_eq`, `diffCount_eq`, `strong_separation`, `homSystem`,
`homSystem_stronglySeparated`, `tHom_mem_Ioo`, `six_mul_rpow_tHom`), and the pairing
determinants (`crossing_det`, `nested_det`).

## Fidelity boundary

What a formal statement can quietly get wrong here is the ambient setting, not the
inequality.  Five traps, and how each is closed.

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
  `t ↦ W t ω` measurable, and `Measure.map` returns the zero measure on a
  non-measurable map, which would make `occupationLaw` junk and every mutual-singularity
  statement vacuous.  Continuity gives measurability of the path
  (`IsPlanarBrownian.ae_continuous`, `measurable_pathMap`) and hence full mass
  (`audit_isProbabilityMeasure_occupation`).  Measurability of `ω ↦ occupationProb W μ ω`
  is `audit_aemeasurable_occupation`, and it is `AEMeasurable` rather than `Measurable`
  for a reason: `occupationProb W μ` is genuinely not measurable in general, only equal
  almost everywhere to the occupation measure of a jointly measurable modification.
- **The law lives on `𝒫(ℝ²)`, not on the measures of `ℝ²`.** `occupationLaw` is a
  measure on `ProbabilityMeasure Plane`, which is the space the paper takes laws on.
  `occupationProb` is the reading of the occupation measure as a point there, with a
  Dirac fallback off the full-mass event; `occupationProb_toMeasure` and
  `IsPlanarBrownian.ae_occupationProb_toMeasure` say the fallback never enters a
  conclusion.

Four further points where the Lean text reads differently from the tex, deliberately.

- **`𝒫(ℝ²)`: the two σ-algebras agree.** Mathlib's
  `ProbabilityMeasure Plane` is measurable through the evaluations `ν ↦ ν s`, while the
  paper uses the Borel σ-algebra of the weak topology. `borel_probabilityMeasure_eq_giry`
  identifies them. Mathlib has neither a
  `BorelSpace (ProbabilityMeasure Ω)` instance nor any `borel (ProbabilityMeasure Ω) = _`
  lemma; the proof is in `WeakBorel.lean` and needs only second countability, pseudo
  metrisability and `BorelSpace`, so it is not special to `ℝ²`.
- **Frostman is stated on closed balls with arbitrary centres.** `eq:frostman` uses open
  balls and centres in `[0,1]`; `IsFrostman` uses closed balls and arbitrary centres,
  which is what the Fubini step of `eq:phi-frostman` consumes. `IsFrostmanOpen` is the
  paper's shape, and `audit_frostman_conventions` proves the two agree up to the change
  of constant the paper allows itself: `A` one way, `3^s A` the other.
- **`eq:profile-separation` is written out.** `limsup_{v→∞} |H₁ - H₂| > 0` appears as
  `∃ ε > 0, ∀ V, ∃ v ≥ V, ε ≤ |H₁(v) - H₂(v)|`, which is the same statement for a
  non-negative function and avoids the junk value `limsup` takes on unbounded functions.
  The same rewriting turns the `liminf < limsup` conclusion of `thm:profile-asymptotics`
  into `audit_lattice_correlation_oscillation`.
- **Quantifier scope in an almost everywhere statement.** `thm:gaussian-four-point`
  asserts, outside one null set, that `Δ > 0` *and* that the bound holds whenever the
  intervals overlap.  The overlap hypothesis governs the bound alone: `Δ > 0` holds with
  no hypothesis, because `Δ = 0` forces either a degenerate interval or the two unoriented
  intervals to agree, and a Frostman measure with `0 < s` gives both null.  Pushing the
  overlap guard outwards, so that it governs the conjunction, type-checks, reads almost
  the same, and is strictly weaker.  `audit_gaussian_four_point_ae` and the bundle keep
  the paper's scoping, and `FourPointBound.det_pos_of_ne_of_nondegenerate` is the
  unconditional determinant bound behind it.
Two statements deserve a note on what their endpoints assert.

- **`thm:homogeneous-nonconstancy`.** `audit_cantor_nonconstant` is non-constancy of the
  eventual periodic profile on every tail, for every `0 < λ < 1/2`, by the density
  argument of `HomogeneousNonconstancy`.
- **`thm:homometric-example`.** The endpoint asserts everything the proposition does:
  the two natural measures, their distinctness, strong separation with gap `1/45`,
  Ahlfors regularity at `t = log 6 / log 30 ∈ (1/2,1)`, the non-isometry of the two
  attractors as `IsEmpty (KA ≃ᵢ KB)`, the equality of the signed convolutions `σ * σ̃`,
  and the consequent equalities of `Φ` and `H`.  All of it is proved.  The non-isometry
  is the paper's argument: both attractors run from `0` to `85/87`, so an isometry from
  one onto the other sends `0` to `0` or to `85/87` and is the identity or the
  reflection, and each is excluded by a first-level interval, `S_4([0,1])` or
  `S_5([0,1])`, that the attractor of `𝒜` reaches and the attractor of `ℬ` misses.  The convolution equality goes through the observation that the difference law
  of a self-similar measure is itself self-similar, for the 36 maps indexed by ordered
  digit pairs at dimension `2t`; homometry makes the two difference systems the same
  system, and Hutchinson uniqueness finishes.  The rescaling `(x - y + 1)/2` is not
  cosmetic: the raw difference lives on `[-1,1]` and `System` is hard-wired to `[0,1]`.

Two endpoints are strictly more general than the tex, and carry a tex-shaped wrapper:
`audit_ahlfors` against `audit_ahlfors_named`, and `audit_endpoint_block_mass` against
`audit_endpoint_block_mass_dyadic`. A third, `audit_profile_asymptotics_lattice`, states
the uniform bound the proof produces, with `audit_profile_asymptotics_lattice_bigO` in
the asymptotic shape `eq:ha-asymptotic` uses.

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
multiplier, and it is `audit_gamma_multiplier` that connects them.

## Not formalised

The discussion after `thm:homometric-example` and the introduction's account of the
literature carry no statement and no endpoint. Nor do the purely arithmetic displays
inside proofs: the four dyadic sums of `thm:four-point-integral` are covered by that
endpoint alone, and `eq:crossing-determinant` and `eq:nested-determinant` are proved in
`FourPoint.lean` without an endpoint of their own.
The claim the project makes is coverage of every numbered result, plus the displayed
claims that a later result cites or that carry a hypothesis of their own; it is not
coverage of every display.
`eq:non-lattice`, the rational independence of `log(1/c)/log 2`, is an open arithmetic
assertion in the paper. It appears in two forms: as `System.NonArithmetic` in the
statements about a general system, and literally, as `Irrational (log (1/c) / log 2)`,
in the endpoints about `μ_B`. `audit_pairSystem_nonArithmetic_iff` is the equivalence
between them.
