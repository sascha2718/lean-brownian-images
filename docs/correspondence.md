# Correspondence with the paper

This document argues the correspondence between the formal statements and the LaTeX
source `BrownianImagesComplete.tex`: what `Solution.lean` and `Challenge.lean` state,
how each result of the paper maps to an endpoint, and where a formal statement could
quietly diverge from the prose. Labels such as `thm:main` are the labels of the LaTeX
source. The comparator compares `Challenge.lean` with `Solution.lean` and never with
the paper, so this correspondence is a human obligation, and this document is where
it is argued.

## The statement layer

`Solution.lean` is the formal statement of the paper: 131 endpoints named
`audit_<slug>`, in document order, proved from the library declarations. Adding a
result to the paper means adding its statement there first; the
design work is in the statement.

`Challenge.lean` is the human-facing problem statement and carries only the headline
theorems, with statement text identical to `Solution.lean` and `sorry` in place of the
proofs, on Mathlib-only copies of the definitions the statements need: `thm:main` as
`audit_main`; `thm:cantor-application` as `audit_cantor_application` with
`audit_cantor_application_pair` and `audit_exceptional_parameters_countable` covering
its final sentence; and `thm:two-contraction-distinction` as
`audit_two_contraction_distinction` with `audit_two_contraction_separation` covering its
final assertion. It is not part of the library and not a default target, which is
what lets it carry `sorry` while the library stays clean. The comparator configuration
kernel-checks exactly these six; the other endpoints are checked by
`lake build Solution`, and the library declares no axiom.

The main theorem uses `expectedProfile`, defined directly by
`e^{2st} 𝔼 C_{e^{-t}}(W_*μ)` as in `eq:expected-profile`. The smoothing kernel and
pair-distance functions do not occur in `Challenge.lean`. In `Solution.lean`,
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

The two-contraction family is specified the same way. `IsTwoContractionMeasure c s μ`
is a probability measure on `[0,1]` satisfying the invariance equation for
`x ↦ x/2`, `x ↦ cx + 1 - c` with weights `(1/2)^s` and `c^s`, and the dimension `s(c)`
enters as a variable `s` with the hypothesis `2^{-s} + c^s = 1`. `dimension_facts` shows
that this hypothesis forces `0 < s < 1` and `c = pairRatio s`, and
`isTwoContractionMeasure_iff_exists_isNatural` identifies the measure with the natural
measure of `pairSystem c`. `audit_two_contraction_family` proves that for every
`0 < c < 1/2` the dimension and the measure exist and are unique, so the statements
about the family are not vacuous.

All six theorem bodies in `Challenge.lean` are holes. Its other declarations are
definitions or structures used by those statements, with no helper theorems,
constructor tactic proofs or literature axioms. Comparator compares the transitive
dependencies of the statements with their counterparts in `Solution.lean`, including
the copied definitions, audits the permitted axioms, and replays the proofs through
the kernel. Run `./comparator-audit.sh` from `lean/`; the local runner and its platform
requirements are documented in `README.md`.

**The correspondence is not one endpoint per theorem.** A theorem with several
assertions appears twice: once as a bundled `audit_thm_*` endpoint carrying the paper's
complete conclusion, and once as the individual endpoints its proof and its consumers
use. The ten bundles are `audit_thm_smoothing_injective`, `audit_thm_profile_asymptotics`,
`audit_thm_gaussian_four_point`, `audit_thm_variance`, `audit_thm_two_contraction_formula`,
`audit_thm_fixed_dimension_profiles`, `audit_thm_fixed_dimension_range`,
`audit_thm_fixed_dimension_separation`, `audit_thm_small_dimension_monotone` and
`audit_thm_critical_set_finite`.
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
the `Solution.lean` endpoint and what stands behind it. All 131 endpoints are proved.
`Challenge.lean` retains `sorry` only as the independent statement file for the six
headline endpoints; no library or solution declaration uses `sorry`.

| Result | Endpoint | Proved by |
| --- | --- | --- |
| `thm:main` | `audit_main` | `main`, after identifying the expected profile with `H` through `smoothing` |
| `thm:cantor-application` | `audit_cantor_application` | `homogeneous_application`, the general system under the open set condition, with the homogeneous measure specified by its invariance equation |
| `thm:cantor-application`, named `μ_B` | `audit_cantor_application_pair` | `homogeneous_application_pair`, with both named measures specified by their invariance equations and the paired ratio bounds derived in the proof |
| countability of exceptional homogeneous parameters | `audit_exceptional_parameters_countable` | `exceptionalParameters_countable` |
| the family before `thm:two-contraction-distinction`: `s(c)` and `μ_c` exist and are unique | `audit_two_contraction_family` | `exists_unique_twoContractionDim`, `System.exists_unique_isNatural`, `Hutchinson.eq_of_selfSimilar` |
| the mean `H̄(c)` before `thm:two-contraction-distinction`, with `eq:two-contraction-mean` | `audit_two_contraction_mean` | `pairSystem_tendsto_avg_H`, through `System.IsNatural.tendsto_avg_H`: the Cesàro mean of `H_μ^s` for any natural measure under the open set condition, read off the renewal equation by `tendsto_avg_of_renewal`, lattice or not |
| `thm:two-contraction-distinction` | `audit_two_contraction_distinction` | `twoContractionMean_lt`: `H̄ = F(s) M(s)` (`twoContractionMean_eq`), and `log F + log M` is strictly increasing on `(0,1)` (`strictMonoOn_logMean`) by one-sided finite differences of `M` (`momentM_right`, `momentM_left`) against the derivative of `log F` (`logPrefactorDeriv_sub_momentLoss_pos`) |
| `thm:two-contraction-distinction`, final assertion | `audit_two_contraction_separation` | `exists_ge_abs_sub_of_tendsto_avg`: distinct Cesàro means force the separation `eq:profile-separation` of the two profiles |
| `thm:minkowski-reconstruction` | `audit_minkowski_reconstruction` | `System.IsNatural.minkowskiReconstruction`, under the open set condition; the non-lattice key-renewal limit and the lattice finite-delay periodic limit both feed the generation-cylinder quotient argument, giving pathwise recovery and a measurable reconstruction map from the compact Brownian image |
| Borel recovery from the pathwise tube limit | `audit_borel_reconstruction_of_pathwise` | `MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise` |
| transfer from occupation-law singularity to compact-image-law singularity | `audit_brownianImageLaw_mutuallySingular_of_pathwise` | `MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction`; `brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio` gives the direct self-similar generation-ratio form |
| `thm:cantor-set-application` | `audit_cantor_set_application` | `MinkowskiReconstruction.homogeneous_brownianImage_application`: the homogeneous source is reconstructed directly from its one-delay renewal equation, the non-lattice source, under the open set condition, by the general reconstruction theorem, and occupation-law singularity descends to mutual singularity of the compact-image laws |
| `thm:cantor-set-application`, named `K_B` | `audit_cantor_set_application_pair` | `MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional` |
| `eq:neighbourhood-union-scaling` | `audit_tube_union_scaling` | `tubeCutoff_compactUnion`, `tubeMass_translate_dilate` |
| `eq:neighbourhood-defect-elementary` | `audit_tube_defect_elementary` | `tubeDefect_nonneg`, `tubeDefect_le_pairwiseTubeOverlapAreaSum` |
| `thm:neighbourhood-moments` | `audit_tube_moments` | `System.IsNatural.tubeMoments`, under the open set condition; discrete-martingale maximal estimates give every unit Brownian-radius moment, the stopping cover supplies the stated upper moments, and classical Ahlfors regularity under the open set condition the positive lower mean |
| `thm:neighbourhood-overlap` | `audit_tube_overlap` | `System.IsNatural.tubeOverlap`, under the open set condition, with the bound `C r^{α+2η}` for the exponent `η` of `thm:cross-piece-mass`; the Gaussian-gap estimate for the stopping cylinders at temporal scale `r²`, `eq:stopping-brownian-overlap`, counted through `eq:stopping-close-pairs` and summed dyadically, gives the pairwise overlap bound, and `Minkowski.DefectExpectation` the defect bound with integrability |
| `thm:neighbourhood-renewal` | `audit_tube_renewal` | `System.IsNatural.tubeRenewal`; the finite-delay law at the maximal lattice span has gcd one, its renewal masses converge, and the exact convolution identity yields uniform convergence on each lattice period |
| `thm:neighbourhood-concentration` | `audit_tube_concentration` | `System.IsNatural.tubeConcentration`, under the open set condition, by `Minkowski.StoppingConcentration`: the sum `Y_{r,u}` over the stopping cylinders at scale `u = r` has variance `O(u^s)` through the `M` independent classes of `thm:stopping-overlap`, `eq:stopping-neighbourhood-variance`; the error `F_{r,u}` telescopes over the stopping tree, its expectation is `O(r^{η}(1 + t))` by `eq:neighbourhood-defect-mean` node by node, `eq:stopping-neighbourhood-defect`, and its third moment is bounded, so interpolation gives the `L²` bound; Borel--Cantelli gives every fixed phase |
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
| `eq:phi-frostman` | `audit_phi_le` | `phi_le` |
| `eq:smoothing` | `audit_smoothing` | `smoothing` |
| `sec:setup`, `φ` integrable and `∫φ > 0` | `audit_kern_integrable` | `kern_integrableOn`, `integral_kern_pos` |
| `thm:profile-uniform-continuity` | `audit_profile_uniform_continuity` | `profile_uniformContinuous` |
| `thm:renewal-recursion` (Φ) | `audit_renewal_recursion` | `phi_recursion_cross`, with the cross term `Φ_×` of `eq:phi-recursion` |
| `thm:renewal-recursion` (G) | `audit_g_recursion` | `g_recursion_cross` |
| `thm:renewal-recursion`, the bound on the cross term | `audit_crossPhi_bound` | `System.StrongOpenSetCondition.exists_crossPhi_bound`: `0 ≤ Φ_×(δ) ≤ C δ^{s+η}` for `0 < δ ≤ 1`, with the exponent `η` of `thm:cross-piece-mass` |
| `thm:renewal-recursion`, the strongly separated case | `audit_crossPhi_separated` | `crossPhi_eq_zero_of_stronglySeparated`: the cross term vanishes below the separation gap |
| `thm:stopping-overlap` | `audit_stopping_overlap` | `System.IsFeasible.exists_point_multiplicity_bound` and `System.IsFeasible.exists_stopping_coloring`, under the open set condition: one integer `M` bounds the multiplicity of the stopping family at every threshold `0 < u ≤ 1`, and the family is coloured with `M` colours so that intervals of one colour have disjoint interiors |
| `thm:cross-piece-mass` | `audit_cross_piece_mass` | `System.StrongOpenSetCondition.exists_cross_piece_bound`: `eq:boundary-mass` and `eq:cross-piece-mass` with one exponent `0 < η < 1 - s` |
| Schief's theorem, cited in `sec:introduction` | `audit_schief` | `System.openSetCondition_iff_strongOpenSetCondition`: the open set condition is equivalent to the existence of a feasible open set meeting the attractor, by the maximal neighbour count of `Schief.lean` |
| `thm:non-lattice-limit`, the renewal inputs | `audit_renewalLaw` | `isProbabilityMeasure_renewalLaw`, `integral_id_renewalLaw` |
| `thm:non-lattice-limit`, exponential moment | `audit_exists_expTransform_lt_one` | `exists_expTransform_lt_one` |
| `thm:non-lattice-limit` | `audit_non_lattice_limit` | `non_lattice_limit`, under the open set condition; the exponential tail of the renewal defect `z` is the cross-term bound of `thm:renewal-recursion` |
| `eq:c-definition` | `audit_pairRatio` | `pairRatio_rpow`, `pairRatio_lt_half` |
| `sec:renewal`, the homogeneous system | `audit_homogeneousSystem_facts` | `homogeneousSystem_isDimension`, `homogeneousSystem_stronglySeparated` |
| `sec:renewal`, the paired system | `audit_pairSystem_facts` | `pairSystem_isDimension`, `pairSystem_stronglySeparated` |
| `sec:renewal`, existence of `μ_A` | `audit_exists_cantor_measure` | `exists_unique_isNatural_homogeneousSystem` |
| `sec:renewal`, existence of `μ_B` | `audit_exists_pair_measure` | `exists_unique_isNatural_pairSystem` |
| `eq:non-lattice` is non-lattice type | `audit_pairSystem_nonArithmetic_iff` | `pairSystem_nonArithmetic_iff` |
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
| `sec:smoothing`, positivity of `H̃_A^s` | `audit_smoothOp_pos` | `smoothOp_pos` |
| `eq:gb-limit` | `audit_gb_limit` | `homogeneous_gb_limit` |
| `thm:profile-asymptotics`, `eq:hb-asymptotic` | `audit_profile_asymptotics_non_lattice` | `profile_asymptotics_nonLattice` |
| `eq:hb-asymptotic`, normalised correlation integral | `audit_non_lattice_correlation_limit` | `non_lattice_correlation_limit` |
| `eq:ha-asymptotic` | `audit_profile_asymptotics_lattice` | `exists_lattice_bound` |
| `eq:ha-asymptotic` in big-`O` shape | `audit_profile_asymptotics_lattice_bigO` | `exists_lattice_bound` |
| `eq:ha-asymptotic`, homogeneous correlation oscillation | `audit_lattice_correlation_oscillation` | `homogeneous_lattice_correlation_oscillation` |
| `thm:profile-asymptotics`, general dichotomy | `audit_thm_profile_asymptotics` | `lattice_profile_asymptotics`, `non_lattice_limit`, `profile_asymptotics_nonLattice` |
| `eq:ha-asymptotic`, `eq:hb-asymptotic`, bundled two-map consequences | `audit_homogeneous_profile_asymptotics` | `homogeneous_thm_profile_asymptotics` |
| `thm:non-lattice-separation` | `audit_non_lattice_separation` | `non_lattice_separation`, both systems under the open set condition |
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
| `thm:base-five-profiles` | `audit_base_five_profiles` | `baseFive_profiles`: the values `eq:base-five-distances` at every scale `5⁻ⁿ`, from the recursions `eq:base-five-recursion` and `Ψ(5⁻ᵐ) = ½ 9⁻ᵐ`, and the profile separation, through the continuous `log 5`-periodic limits of the two profiles in logarithmic coordinates with `g₁(0) = 3/2 ≠ 1 = g₂(0)`, dominated convergence in `eq:h-definition` and `thm:smoothing-injective` |
| `thm:base-five-profiles`, the first display after it | `audit_base_five_occupation_laws` | `MinkowskiReconstruction.baseFive_occupationLaw_mutuallySingular`: `thm:main` for the two natural measures, Frostman by the open set condition |
| `thm:base-five-profiles`, the second display after it | `audit_base_five_image_laws` | `MinkowskiReconstruction.baseFive_brownianImageLaw_mutuallySingular`: `thm:minkowski-reconstruction` for both systems under the open set condition, and the descent of the occupation-law singularity through the Borel reconstruction map |
| `sec:obstruction`, the signed convolution | `audit_conv_reflect` | `conv_reflect_eq_map_sub` |
| `thm:homometric-example` | `audit_homometric_example` | `homometric_example`, with the non-isometry of the attractors from `HomometricMeasures.isEmpty_isometryEquiv` |
| `thm:renewal-average` | `audit_renewal_average` | `System.IsNatural.tendsto_avg_G_char` (`eq:renewal-average`) and `System.IsNatural.tendsto_avg_H` (`eq:mean-profile`), through the renewal average `tendsto_avg_of_renewal` |
| `eq:two-contraction-constant` | `audit_two_contraction_constant` | `pairSystem_tendsto_H_nonLattice`: `thm:non-lattice-limit` with `∫ z = 2pq M_c(s)/s` (`pairSystem_integral_renewalDefect`, from `Φ_× = 2pq ℙ(Z_c ≤ δ)`) and `∫ φ = 2^{-s} Γ(1-s)` (`integral_kern_eq_Gamma`) |
| `eq:two-contraction-periodic` | `audit_two_contraction_periodic` | `pairSystem_periodic`: the coefficients of the lattice limit from the renewal average with a character (`System.IsNatural.fourierCoeffP_latticeLimit`), the forcing transform `eq:two-contraction-forcing-transform` (`pairSystem_integral_renewalDefect_char`), the multiplier `eq:gamma-multiplier`, the bound `‖Γ(1-ζ)‖ ≤ Γ(2-s)/‖1-ζ‖` (`norm_Gamma_le`) for absolute summability, and Fourier inversion (`hasSum_fourierCoeffP`) |
| `thm:two-contraction-formula`, bundled | `audit_thm_two_contraction_formula` | the three endpoints above, the lattice span from `System.nonArithmetic_or_exists_lattice` |
| `sec:two-contraction-formula`, the coding: `M_{c(s)}(s) = J(s, c(s), q(s))` | `audit_moment_coding` | `crossMoment_eq_momentM`, through `map_twoCode_twoBern` and Hutchinson uniqueness |
| `thm:parameter-steps` | `audit_parameter_steps` | `crossJ_mono_exponent` (`eq:exponent-step`), `crossJ_mono_contraction` (`eq:contraction-step`), `crossJ_weight_ge` (`eq:weight-step`) |
| `thm:local-monotonicity` | `audit_local_monotonicity` | `strictMonoOn_of_local`, on any interval |
| `sec:fixed-dimension-family`, existence and uniqueness of `K_p` and `μ_p` | `audit_exists_fixed_dimension_measure` | `System.exists_unique_isNatural` for `fixedSystem`, the system `x ↦ ax`, `x ↦ bx + 1 - b` with `a = p^{1/s}`, `b = q^{1/s}`, whose dimension is `s` (`fixedSystem_isDimension`) |
| `sec:small-dimension`, `M_p(s) = 𝔼 Z_p^{-s}` with `X`, `Y` of law `μ_p` | `audit_fixed_moment_natural` | `fixedMoment_eq_natural`: `fixedMoment` is the double Bernoulli integral of `Z_p^{-s}` over the coding, and the law of the coded point is `μ_p` (`map_fixedCode_twoBern`, by Hutchinson uniqueness) |
| `sec:small-dimension`, `M_p ≥ 1` | `audit_fixed_moment_ge_one` | `one_le_fixedMoment`, since `Z_p ≤ 1` |
| `eq:log-derivative-mean` | `audit_log_derivative_mean` | `hasDerivAt_entropyFactor` for `κ = (pq/E)'/(pq/E)`, and `hasDerivAt_fixedMean` for the mean, in the product form `H̄_s' = C_s (pq/E)(κ M_p + M_p')` with `C_s = 2^{1-s} Γ(1-s)`, wherever `M_p` is differentiable |
| `thm:entropy-factor` | `audit_entropy_factor` | `kappa_pos`, `kappa_ge_of_le`, `kappa_ge_of_ge`: `Φ = q² log(1/q) - p² log(1/p)` is strictly concave on `[0, 1/2]` with `Φ(0) = Φ(1/2) = 0` (`strictConcaveOn_kappaNum`), hence positive between; `log(1/q) ≥ p` and `q log(1/q) ≤ p` give the explicit bound for `p ≤ 1/50`; and the constant `c` for `[p₁, 1/2)` is read off the chord of the concave `Φ` from `(p₁, Φ(p₁))` to `(1/2, 0)` |
| `eq:leading-ones` | `audit_leading_ones` | `hasSum_leadingTerm`: the first-letter recursion `leadingAux_rec` of the Bernoulli double integral, with the remainder `qᴺ h_N` bounded |
| `eq:main-term` | `audit_main_term` | `mainTerm_eq`, with `T = log(1/b) = log(1/q)/s` (`fixedT`) |
| `thm:main-term-derivative` | `audit_main_term_derivative` | `exists_hasDerivAt_mainTerm`: termwise differentiation of `S` (`hasDerivAt_mainS`), the Riemann-sum comparison against the total variation of `g` (`abs_tsum_sub_integral_le`), the integrals of `f'`, `x f''`, `g`, `g'` on `(T, ∞)` (`MainTermIntegrals`), and `s ∫_T^∞ f ≤ 2.3` from `f ≤ x^{-s}` on `(0, 1]` and `f ≤ (1 - e^{-1})^{-s} e^{-sx}` on `[1, ∞)`; the constant is `6` |
| `thm:remainder-derivative` | `audit_remainder_derivative` | `exists_hasDerivAt_fixedMoment`: on the disc `|z - p| ≤ p/2` the level sums `Λ_n^{(m)}` converge uniformly to holomorphic `Λ_n` with `eq:lambda-bound` (`norm_kernelLimit_sub_le`), `Δ = M - Σ` is holomorphic (`differentiableOn_complexDelta`) with `sup_U |Δ| ≤ 1296 s α p^{-1-s}` (`norm_complexDelta_le`), Cauchy's estimate gives `Δ'` (`norm_deriv_complexDelta_le`), and `Δ(x) = M_x - Σ(x)` on the real diameter by dominated convergence of the level sums (`complexDelta_ofReal`) |
| `thm:second-derivative-small-s` | `audit_second_derivative_small_s` | `fixedMoment_second_derivative`: on `|z - p| ≤ 5·10⁻⁵` both contractions have modulus at most `γ ≤ 1/12` (`gammaQ_le`), the cross kernel is within `18 s γ` of `1` by the mean value inequality for `ζ ↦ ζ^{-s}` on `|ζ - 1| ≤ 1/2` (`norm_crossKernelC_sub_one_le`), the level sums converge to `M_z` with `|M_z - 1| ≤ 32 s γ` (`norm_crossLimit_sub_one_le`), `M_z = M_x(s)` on the real diameter (`crossLimit_ofReal`), and Cauchy's estimate for the second derivative; the tex's constants `33` and `47` become `18` and `32`, with the same `10¹¹` |
| the symmetry `M_p = M_{1-p}` in the proof of `thm:small-dimension-monotone` | `audit_moment_symmetric_derivative` | `deriv_fixedMoment_half`: `M_{1-z} = M_z` on the disc around `1/2` (`crossLimit_one_sub`), since flipping every letter reflects the coded points up to the base point (`one_sub_cpointSeq_eq`) and the cross kernel is reflection invariant, so the level sums of `z` and `1 - z` differ by `O((γB²)^m)`; the complex derivative at `1/2` then vanishes, and the real derivative is its real part |
| `thm:small-dimension-monotone` | `audit_small_dimension_monotone` | `exists_strictMonoOn_fixedMean`: `|M_p'| < κ(p)` on `(0, 10⁻⁴]` from the three lemmas and `(3p/2)^{1/s} ≤ (3p/2)⁴` (`abs_deriv_fixedMoment_lt_kappa_small`), and on `[10⁻⁴, 1/2)` from the second-derivative bound, `M_{1/2}' = 0` and the mean value theorem (`abs_deriv_fixedMoment_lt_kappa_large`); `s₀ = min(2·10⁻⁵, c/10¹¹)` for the constant `c` of `thm:entropy-factor` at `p₁ = 10⁻⁴`, since `γ ≤ 2 s²/r²` (`gammaQ_le_sq`); then `strictMonoOn_of_deriv_pos` through `eq:log-derivative-mean` and `M_p ≥ 1` |
| `thm:critical-set-finite`, the strict increase on `(0, p₀]` | `audit_critical_set_finite` | `exists_strictMonoOn_fixedMean_small`: `|M_p'| p log(e/p) ≤ (6 + 3000 s (3/2)^{1/s}) √p log(e/p)` for `p ≤ 1/50` (`abs_deriv_fixedMoment_mul_le`, using `1/s - 1 - s ≥ 1/2`) and `√p log(e/p) ≤ 5 p^{1/4}` (`sqrt_mul_one_sub_log_le_rpow`), so `p₀ = min(1/50, (0.17/C)⁴)` |
| `thm:critical-set-finite`, bundled | `audit_thm_critical_set_finite` | the endpoint above and `criticalSet_finite`: `D_s ⊆ [p₀, 1/2]` by the positive derivative on `(0, p₀)` (`exists_deriv_fixedMean_pos_small`), and an infinite subset of a compact interval has an accumulation point (`Set.Infinite.exists_accPt_of_subset_isCompact`), which `not_accPt_criticalSet` forbids |
| `thm:small-dimension-monotone`, bundled with its second sentence | `audit_thm_small_dimension_monotone` | `audit_small_dimension_monotone` and `audit_fixed_dimension_laws`; distinct parameters have distinct means by strict monotonicity |
| `thm:fixed-dimension-profiles`, `eq:fixed-dimension-mean` | `audit_fixed_dimension_mean` | `fixedSystem_tendsto_avg_H`: `System.IsNatural.tendsto_avg_H` under the open set condition (`fixedSystem_openSetCondition`, from strong separation with gap `1 - a - b`), with `m = E(p)/s` (`fixedSystem_renewalMean`), `Φ_× = 2pq ℙ(Z_p ≤ δ)` (`fixedSystem_crossPhi`), `∫ z = 2pq M_p(s)/s` (`fixedSystem_integral_renewalDefect`, by Tonelli) and `∫ φ = 2^{-s} Γ(1-s)`; the expected profile is `H` by `smoothing` |
| `thm:fixed-dimension-profiles`, the non-lattice limit | `audit_fixed_dimension_non_lattice` | `fixedSystem_tendsto_H_nonLattice`, through `thm:non-lattice-limit`, with `log a/log b ∉ ℚ` read as non-arithmeticity by `fixedSystem_nonArithmetic_iff` |
| `eq:fixed-dimension-periodic` | `audit_fixed_dimension_periodic` | `fixedSystem_periodic`: `eq:fixed-dimension-forcing` (`fixedSystem_integral_renewalDefect_char`, by Fubini), the coefficients of the lattice limit from the renewal average with a character (`System.IsNatural.fourierCoeffP_latticeLimit`), the multiplier `eq:gamma-multiplier`, the bound `‖Γ(1-ζ)‖ ≤ Γ(2-s)/‖1-ζ‖` for absolute summability (`summable_norm_fixedDimCoeff`), and Fourier inversion |
| `eq:fixed-dimension-correlation` | `audit_fixed_dimension_correlation` | `fixedSystem_correlation`: `S_μ(r) = ∫ g_r(|x - y|) d(μ×μ)` by `eq:gaussian-reduction`, Hutchinson's identity in both coordinates on `μ × μ` (`System.IsNatural.lintegral_prod_eq_double_sum`) gives the recursion `T(c) = p² T(ca) + q² T(cb) + 2pq 𝔼 g_r(c Z_p)` for `T(c) = ∫ g_r(c|x - y|)` (`corrScale_recursion`), iterated along the antidiagonals of `ℕ²` with Pascal's rule (`sum_antidiagonal_succ_pascal`); `0 ≤ T ≤ 1` bounds the remainder by `∑_{j+k=m} C(m,j) p^{2j} q^{2k} = (p² + q²)^m`, uniformly in `r`, and the series of non-negative terms sums to `T(1)` along the triangles `{j + k < m}` |
| `thm:fixed-dimension-profiles`, bundled | `audit_thm_fixed_dimension_profiles` | the four endpoints above, the lattice span from `System.nonArithmetic_or_exists_lattice` |
| the display before `thm:fixed-dimension-analyticity`, `H̄_s(p) = H̄_s(1-p)` | `audit_fixed_dimension_symmetry` | `fixedMoment_symm`, `fixedMean_symm`: flipping every letter in the level sums reflects the coded points up to the base point (`one_sub_cpointSeq_eq`), the kernel is Lipschitz on `[0,1]²` (`abs_rpow_fixedCross_sub_le`), so the level sums of `p` and `1-p` differ by `O(γ^m)` (`norm_levelSum_one_sub_sub_le'`), and both converge to the moments (`tendsto_levelSum_ofReal`) |
| `thm:fixed-dimension-analyticity` | `audit_fixed_dimension_analyticity` | `analyticAt_fixedMoment`, `analyticAt_fixedMean`: on the disc `|z - p₀| ≤ r` of `GoodRadius` the branches are Lipschitz (`norm_ca_sub_le`), the coded points move by at most `C|z - p₀|` (`norm_cpointSeq_sub_le`) and stay in a neighbourhood of `[0,1]` on which every cross distance has real part at least `g₀/2` (`re_crossBase_ge_of_mem`), the level sums converge uniformly to a holomorphic `M_z` (`incrementBound_disc`, `differentiableOn_crossLimit_disc`) equal to `M_x(s)` on the real diameter (`crossLimit_eq_fixedMoment_of_mem`), and the restriction of a holomorphic function to the real line is real analytic (`AnalyticAt.restrictScalars`); `E` is analytic by `analyticAt_log` |
| `thm:fixed-dimension-range` | `audit_fixed_dimension_range` | continuity from analyticity, positivity from `M_p ≥ 1`; the limit `0` from `M_p ≤ 2^s Σ(p)` once `a ≤ (1-b)/2` (`fixedMoment_le_mainTerm`, through `eq:leading-ones`), `Σ ≤ (s/q)(∫_T^∞ f + T f(T))` (`mainTerm_le`) and `s ∫_T^∞ f ≤ s/(1-s) + 1.59` (`mul_integral_mainF_le'`), so `M_p` is bounded near `0` (`fixedMoment_le_of_small`), while `pq/E(p) ≤ 1/log(1/p)` (`entropy_ge`); the uncountable subfamily by the intermediate value theorem (`exists_uncountable_injOn_fixedMean`), uncountable because its image is an interval of positive length |
| `thm:fixed-dimension-range`, bundled with the singular laws of the subfamily | `audit_thm_fixed_dimension_range` | the endpoint above and `audit_fixed_dimension_laws` |
| `thm:fixed-dimension-separation`, the analytic assertions | `audit_fixed_dimension_separation` | `not_accPt_criticalSet`, `strictMono_or_anti_of_ne_zero`, `exists_eps_strictMono`, `not_accPt_levelSet`, `levelSet_countable`: the identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` on `(0,1)` for the derivative and for `H̄_s - H̄_s(p₁)`, non-constancy from the limit `0` at `0` and positivity at `1/2` (`fixedMean_not_const`), the sign of the derivative on an interval free of critical points by the intermediate value theorem, `ε_s` from the isolated point `1/2`, and countability of a level set from its finiteness on each `[1/(n+2), 1/2]` |
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
  which is what the Fubini step of `eq:phi-frostman` consumes. `IsFrostmanOpen` is the
  paper's shape, and `audit_frostman_conventions` proves the two agree up to the change
  of constant the paper allows itself: `A` one way, `3^s A` the other.
- **`eq:profile-separation` is written out.** `limsup_{v→∞} |H₁ - H₂| > 0` appears as
  `∃ ε > 0, ∀ V, ∃ v ≥ V, ε ≤ |H₁(v) - H₂(v)|`, which is the same statement for a
  non-negative function and avoids the junk value `limsup` takes on unbounded functions.
  The same rewriting turns the `liminf < limsup` consequence of `eq:ha-asymptotic`
  into `audit_lattice_correlation_oscillation`.
- **The lattice limit is asymptotic and need not be non-constant in general.**
  `audit_thm_profile_asymptotics` uses the subgroup generated by the full log-ratios,
  with span `h`, and gives a continuous positive limit of period `h / 2`.
  `LatticeProfile.lean` applies the finite-delay renewal theorem to `A + 1 - G(2v)`,
  converts uniform phase convergence to convergence on the half-line, and smooths
  the vanishing error. The lower regularity bound ensures positivity. The separate
  homogeneous endpoints prove non-constancy and the sharper exponential error.
- **IFS terminology.** The paper calls the defining family of similarities an iterated
  function system (IFS). Its Lean type is `System`; this identifier denotes an IFS
  throughout the formalisation.
- **Orientation-reversing similarities are carried by a sign.** The paper's IFSs are
  finite families of contracting similarities of `ℝ` mapping `[0,1]` into itself, the
  orientation-reversing ones included, and `sec:reconstruction` uses time reversal of the
  increments when `S_w` reverses orientation. `System` writes each map as
  `S_i(x) = ε_i r_i x + b_i` with the modulus `r_i ∈ (0,1)` in `ratio` and the
  orientation `ε_i ∈ {1, -1}` in `sign`, so that the signed ratio ranges over
  `(-1,0) ∪ (0,1)` while `p_i = r_i^s`, `a_i = log(1/r_i)` and every renewal quantity are
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
- **Quantifier scope in an almost everywhere statement.** `thm:gaussian-four-point`
  asserts, outside one null set, that `Δ > 0` *and* that the bound holds whenever the
  intervals overlap.  The overlap hypothesis governs the bound alone: `Δ > 0` holds with
  no hypothesis, because `Δ = 0` forces either a degenerate interval or the two unoriented
  intervals to agree, and a Frostman measure with `0 < s` gives both null.  Pushing the
  overlap guard outwards, so that it governs the conjunction, type-checks, reads almost
  the same, and is strictly weaker.  `audit_gaussian_four_point_ae` and the bundle keep
  the paper's scoping, and `FourPointBound.det_pos_of_ne_of_nondegenerate` is the
  unconditional determinant bound behind it.
Five statements deserve a note on what their endpoints assert.

- **The fixed-dimension family.** The endpoints are stated on `fixedMean s p`, which is
  the right-hand side of `eq:fixed-dimension-mean`, `2^{1-s} Γ(1-s) pq M_p(s)/E(p)`, with
  `fixedMoment s p` the moment `M_p(s)` through the Bernoulli coding of `μ_p`.
  `audit_fixed_moment_natural` identifies `fixedMoment` with `𝔼 Z_p^{-s}` for `X`, `Y`
  independent of law `μ_p`, the paper's definition, `audit_exists_fixed_dimension_measure`
  shows the measure exists and is unique, and `audit_fixed_dimension_mean` identifies
  `fixedMean s p` with the Cesàro mean of the expected profile of `μ_p`, so the statements
  about the mean are statements about the paper's `H̄_s(p)`.  The parameter range is
  `p ∈ (0,1)` throughout where the tex restricts to `(0, 1/2]`; the tex's restriction is
  by the symmetry `audit_fixed_dimension_symmetry`.  The non-lattice hypothesis
  `log a/log b ∉ ℚ` is `Irrational (log a / log b)`, equivalent to `System.NonArithmetic`
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

- **`thm:base-five-profiles`.** The two systems are `baseFiveSystem` at the digit sets
  `{0,1,4}` and `{0,2,4}`, and the natural measures enter as `IsNatural` hypotheses, as
  in `audit_cantor_application`; `naturalMeasure_selfSimilar` supplies such a measure
  for every system, so the hypotheses are satisfiable.  The Frostman constants are not
  hypotheses: both systems satisfy the open set condition with `U = (0,1)`, and
  `System.OpenSetCondition.exists_isFrostman` produces them.  The second assertion,
  `limsup |H_{μ₁}^s - H_{μ₂}^s| > 0`, is stated as the separation
  `∃ ε > 0, ∀ V, ∃ t ≥ V, ε ≤ |H_{μ₁}^s(t) - H_{μ₂}^s(t)|`, the hypothesis shape of
  `thm:main`, which is what the two displays after the proposition consume.  The
  periodic limits of the proof are built, not assumed: `exists_periodic_limit` turns the
  non-negative, exponentially small increments `G(w) - G(w - log 5)` into a continuous
  `log 5`-periodic function within `O(e^{-sw})` of `G`.

- **`thm:two-contraction-distinction`.** The theorem says that `c ↦ H̄(c)` is strictly
  increasing, where `H̄(c) = lim T⁻¹ ∫₀ᵀ H_{μ_c}^{s(c)}`.  The endpoint takes
  `0 < c₁ < c₂ < 1/2`, their dimensions and natural measures, and asserts that both
  Cesàro limits exist and are strictly ordered.  This is the theorem: the limit is
  unique when it exists, it exists for every `c` (`audit_two_contraction_mean`), and
  `s(c)` and `μ_c` exist and are unique (`audit_two_contraction_family`).  A function
  `H̄` defined by `limUnder` would take a junk value where the limit fails, so the
  statement asserts the convergence.  The proof is the tex's, step for step: the
  one-sided bounds of `thm:parameter-steps` give `eq:moment-above` and `eq:moment-below`
  (`momentM_right`, `momentM_left`), the digamma bound comes from the convexity of
  `log Γ` (`neg_logGammaDeriv_one_sub_ge`), and `thm:local-monotonicity` turns local
  strict increase of `log F + log M` into strict monotonicity, with no continuity of
  `M`.

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
multiplier, and it is `audit_gamma_multiplier` that connects them.  Likewise
`crossMoment` and `crossMomentC` are the moment `M_c(α) = 𝔼 Z_c^{-α}` with
`Z_c = 1 - c + cY - X/2`, and `twoContractionCoeff` is the coefficient of
`eq:two-contraction-periodic` written out; the endpoints of `thm:two-contraction-formula`
are what connect them with the expected profile.

## Not formalised

The discussion after `thm:homometric-example` and the introduction's account of the
literature carry no statement and no endpoint. In `sec:fixed-dimension-family`, the
displays of the subsection on the moment computation, the recursions for the ordinary
moments and the binomial series for `M_p(s)`, carry no endpoint: they are the numerical
recipe for `eq:fixed-dimension-mean`, cited by no result.
`eq:fixed-dimension-forcing` is proved as `fixedSystem_integral_renewalDefect_char` without
an endpoint of its own, as are the displays inside the proofs of `sec:small-dimension`:
`eq:alpha-beta` (`five_alphaP_le`), `eq:contraction-disc` (`discR_le`, `one_sub_discR_ge`),
`eq:phi-bounds` (`norm_kernelN_le`, `norm_kernelN_sub_le`) and `eq:lambda-bound`
(`norm_kernelLimit_sub_le`).  The displays inside the proof of
`thm:two-contraction-distinction` are proved as library declarations without endpoints
of their own: `eq:two-contraction-mean-factorisation` (`twoContractionMean_eq`),
`eq:natural-weight-bound` (`pairWeight_mul_lt_one`), `eq:moment-above` and
`eq:moment-below` (`momentM_right`, `momentM_left`), `eq:loss-rate-bound`
(`momentLoss_lt`, `pairWeight_deriv_mul_lossRate`) and `eq:rate-comparison`
(`logPrefactorDeriv_sub_momentLoss_pos`), and so is
`eq:two-contraction-forcing-transform` (`pairSystem_integral_renewalDefect_char`). Nor do the purely lattice displays
inside proofs: the four dyadic sums of `thm:four-point-integral` are covered by that
endpoint alone, and `eq:crossing-determinant` and `eq:nested-determinant` are proved in
`FourPoint.lean` without an endpoint of their own.
The claim the project makes is coverage of every numbered result, plus the displayed
claims that a later result cites or that carry a hypothesis of their own; it is not
coverage of every display.
`eq:non-lattice`, the rational independence of `log(1/c)/log 2`, is an open lattice
assertion in the paper. It appears in two forms: as `System.NonArithmetic` in the
statements about a general system, and literally, as `Irrational (log (1/c) / log 2)`,
in the endpoints about `μ_B`. `audit_pairSystem_nonArithmetic_iff` is the equivalence
between them.
