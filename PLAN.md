# `BrownianImages`: the formalisation of `BrownianImagesComplete.tex`

Mirrors "Pair-distance profiles and Minkowski reconstruction of planar Brownian images".
The library is sorry-free and axiom-clean. `Solution.lean` carries 84 formal endpoints,
all proved: the numbered results of the paper together with displayed claims that a
later result cites or that carry a hypothesis of their own. `Challenge.lean` restates
the headline theorems, `thm:main` and `thm:cantor-application`, with `sorry`, on
Mathlib-only copies of the definitions their statements need, and the comparator audits
those endpoints against `Solution.lean`. The axiom check `BrownianImages/AxCheck.lean`
covers the library endpoints, all reporting `propext`, `Classical.choice`, `Quot.sound`
or a subset.

The module index is the root module `BrownianImages.lean`. This file carries what that
does not: the build setup, the statement layer, the state, the fidelity boundary, and
the technique notes worth not re-deriving.

Convention: state, not history. Edit in place, append nothing; `git log` has the rest.

## 0. Build setup

The project **reuses the already-built Mathlib** in `~/Documents/lean/mathematics_in_lean`,
via `packagesDir` in `lakefile.toml`:

```toml
packagesDir = "/Users/sascha/Documents/lean/mathematics_in_lean/.lake/packages"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.32.2"
```

`packagesDir`, rather than a path-require on Mathlib alone, is what makes this work: it
also resolves Mathlib's transitive dependencies (batteries, aesop, Qq, proofwidgets),
which are already built there. No download and no Mathlib recompilation; our own
`.lake` holds only this library.

Consequences, accepted deliberately:

- `lean-toolchain` is pinned to `v4.32.2`, dictated by that Mathlib; Mathlib is pinned
  to rev `905b9581` (tag `v4.32.2`).
- The project is **not self-contained**. It moves in lockstep with the shared tree:
  `rev` here must equal what `mathematics_in_lean` resolves, and the shared tree has to
  be updated first, since resolving this project drags the shared checkouts to whatever
  `rev` says.
- `lake update` here is safe only when the shared tree already sits at the target
  revisions, in which case it merely rewrites `lake-manifest.json`.
- Editing `lean-toolchain` or `lakefile.toml` is itself the start of an upgrade: the
  editor's Lean server re-resolves on save.
- Escape hatch if the project leaves this machine: drop `packagesDir` and use
  `lake exe cache get`. Removing `packagesDir` makes Lake **move** the shared packages
  directory into this project rather than fetch a new one, which leaves
  `mathematics_in_lean` without dependencies until the directory is moved back.

The same setup serves `~/Documents/ActiveResearch/JA-ST/lean`, and the two projects have
to be upgraded together.

```
cd lean
lake build                # the library, including the axiom check
lake build Challenge Solution
./comparator-audit.sh
```

### Comparator audit

An independent check beside `AxCheck.lean`: `Challenge.lean` states the headline
theorems with `sorry` on Mathlib-only copies of the definitions, `Solution.lean` proves
them by the library declarations, and `comparator-audit.sh` runs
`leanprover/comparator` on the pair (names in `comparator-config.json`): statement
comparison and axiom audit on the raw `lean4export` output, then a kernel replay of the
solution's dependency closure, none of it trusting the elaborator or `#print axioms`.
The point of the Mathlib-only import is the trusted surface: the comparator's guarantee
covers the import closure of `Challenge.lean`, so the audit trusts that one file and
Mathlib, never the library.  Comparator compares the transitive closure of every
constant a listed statement uses, definition bodies included, by syntactic equality of
the exports, which forces the copies in `Challenge.lean` to elaborate to exactly the
library's terms.  Two consequences, both load-bearing:

- Any drift between a copied definition and the library original fails the audit, so
  the duplication is machine-checked, not a maintenance hazard.
- Auxiliary `_proof` constants (abstracted nested proofs, e.g. the `Nat.AtLeastTwo`
  instance proof behind a numeral) are deduplicated per module and named after the
  first declaration in the module that needs them.  Every definition copied into
  `Challenge.lean` must therefore be declared in one library module, `Defs.lean`, in
  the same relative order as in `Challenge.lean`; splitting them across modules makes
  identical bodies reference differently named auxiliaries and the audit fails on a
  definition as innocent as `homogeneousDim`.

Tooling: `~/Documents/lean/comparator` (own toolchain and packages) and
`~/Documents/lean/lean4export` at tag `v4.32.2`, which must move with `lean-toolchain`.
`landrun` is Linux-only, so on macOS the audit runs through comparator's unsandboxed
shim; nanoda (second kernel, Rust) is not built, `enable_nanoda` is false. For the
audited endpoints the statement text must stay character-for-character identical
between the two files.

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
kernel-checks exactly these four; the other 80 endpoints are checked by
`lake build Solution` together with the library's axiom check. The pair endpoint takes
the ratio bounds `0 < c < 1/2` of `eq:c-definition` as hypotheses rather than citing
`pairRatio_pos` and `pairRatio_lt_half`, so that no proof term appears in a statement
and no lemma has to live in `Challenge.lean`; the hypotheses are provable, so nothing
is vacuous.

**The correspondence is not one endpoint per theorem.** A theorem with several
assertions appears twice: once as a bundled `audit_thm_*` endpoint carrying the paper's
complete conclusion, and once as the individual endpoints its proof and its consumers
use. The five bundles are `audit_thm_cantor_values`, `audit_thm_smoothing_injective`,
`audit_thm_profile_asymptotics`, `audit_thm_gaussian_four_point`, `audit_thm_variance`.
Three further endpoints restate a general Lean result in the narrower shape the tex uses:
`audit_ahlfors_named` (the tex states `thm:ahlfors` for `μ_A` and `μ_B` only, on the
balls `B(x,ρ)`), `audit_endpoint_block_mass_dyadic` (the tex needs only dyadic `β, η`,
and carries both halves of the lemma), and `audit_profile_asymptotics_lattice_bigO`
(the `O(e^{-2(1-s)v})` shape `eq:ha-asymptotic` is written in, against the uniform bound
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

| Result | Endpoint | State |
| --- | --- | --- |
| `thm:main` | `audit_main` | **done**, `main` |
| `thm:cantor-application` | `audit_cantor_application` | **done**, `cantor_application` |
| `thm:cantor-application`, named `μ_B` | `audit_cantor_application_pair` | **done**, `cantor_application_pair` |
| countability of exceptional homogeneous parameters | `audit_exceptional_parameters_countable` | **done**, `exceptionalParameters_countable` |
| `thm:minkowski-reconstruction` | `audit_minkowski_reconstruction` | **done**, `System.IsNatural.minkowskiReconstruction`; the non-arithmetic key-renewal limit and the arithmetic finite-delay periodic limit both feed the generation-cylinder quotient argument, giving pathwise recovery and a measurable reconstruction map from the compact Brownian image |
| Borel recovery from the pathwise tube limit | `audit_borel_reconstruction_of_pathwise` | **done**, `MinkowskiReconstruction.exists_borel_reconstruction_of_pathwise` |
| transfer from occupation-law singularity to compact-image-law singularity | `audit_brownianImageLaw_mutuallySingular_of_pathwise` | **done**, `MinkowskiReconstruction.brownianImageLaw_mutuallySingular_of_pathwise_tubeReconstruction`; `brownianImageLaw_mutuallySingular_of_generation_tubeMassRatio` gives the direct self-similar generation-ratio form |
| `thm:cantor-set-application` | `audit_cantor_set_application` | **done**, `MinkowskiReconstruction.homogeneous_brownianImage_application_pair_unconditional`: the homogeneous source is reconstructed directly from its one-delay renewal equation, the paired source by the non-arithmetic theorem, and occupation-law singularity descends to mutual singularity of the compact-image laws |
| `eq:tube-union-scaling` | `audit_tube_union_scaling` | **done**, `tubeCutoff_compactUnion`, `tubeMass_translate_dilate` |
| `eq:tube-defect-elementary` | `audit_tube_defect_elementary` | **done**, `tubeDefect_nonneg`, `tubeDefect_le_pairwiseTubeOverlapAreaSum` |
| `thm:tube-moments` | `audit_tube_moments` | **done**, `System.IsNatural.tubeMoments`; discrete-martingale maximal estimates give every unit Brownian-radius moment, and the stopping cover supplies the stated upper moments and positive lower mean |
| `thm:tube-overlap` | `audit_tube_overlap` | **done**, `System.IsNatural.tubeOverlap`; the separated-cylinder Gaussian-density estimate and the tube moment bound give uniform pairwise overlap and total defect estimates with integrability |
| `thm:tube-renewal` | `audit_tube_renewal` | **done**, `System.IsNatural.tubeRenewal`; the finite-delay law at the maximal lattice span has gcd one, its renewal masses converge, and the exact convolution identity yields uniform convergence on each arithmetic period |
| `thm:tube-concentration` | `audit_tube_concentration` | **done**, `System.IsNatural.tubeConcentration`; interpolation between first and third moments controls the normalized defect in `L²`, delayed contraction gives exponential decay, and Borel--Cantelli gives every fixed phase |
| the ambient σ-algebra on `𝒫(ℝ²)` | `audit_borel_eq_giry` | **done**, `borel_probabilityMeasure_eq_giry` |
| occupation has full mass | `audit_isProbabilityMeasure_occupation` | **done**, `IsPlanarBrownian.ae_isProbabilityMeasure_occupation` |
| `Law(W_*μ)` has total mass one | `audit_isProbabilityMeasure_occupationLaw` | **done**, `IsPlanarBrownian.isProbabilityMeasure_occupationLaw` |
| occupation is measurable | `audit_aemeasurable_occupation` | **done**, `IsPlanarBrownian.aemeasurable_occupationProb` |
| `thm:ahlfors` | `audit_ahlfors` | **done**, `exists_isAhlforsClosed` |
| `eq:ahlfors`, the two ball conventions | `audit_ahlfors_conventions` | **done**, `IsAhlforsClosed.isAhlfors` |
| `thm:ahlfors` for `μ_A`, `μ_B` | `audit_ahlfors_named` | **done**, `exists_isAhlfors_cantor_pair` |
| `thm:gaussian-reduction` | `audit_gaussian_reduction` | **done**, `gaussian_reduction` |
| `sec:setup`, atomlessness of `μ` | `audit_measure_singleton` | **done**, `IsFrostman.measure_singleton` |
| `sec:setup`, atomlessness of `dΦ` | `audit_pairLaw_noAtoms` | **done**, `pairLaw_measure_singleton` |
| `sec:setup`, continuity of `Φ` | `audit_phi_continuous` | **done**, `continuous_phi` |
| `eq:frostman`, the two ball conventions | `audit_frostman_conventions` | **done**, `IsFrostman.isFrostmanOpen`, `IsFrostmanOpen.isFrostman` |
| `eq:phi-frostman` | `audit_phi_le` | **done**, `phi_le` |
| `eq:smoothing` | `audit_smoothing` | **done**, `smoothing` |
| `sec:setup`, `K` integrable and `∫K > 0` | `audit_kern_integrable` | **done**, `kern_integrableOn`, `integral_kern_pos` |
| `thm:profile-uniform-continuity` | `audit_profile_uniform_continuity` | **done**, `profile_uniformContinuous` |
| `thm:renewal-recursion` (Φ) | `audit_renewal_recursion` | **done**, `phi_recursion` |
| `thm:renewal-recursion` (G) | `audit_g_recursion` | **done**, `g_recursion` |
| `thm:non-lattice-limit`, the renewal inputs | `audit_renewalLaw` | **done**, `isProbabilityMeasure_renewalLaw`, `integral_id_renewalLaw` |
| `thm:non-lattice-limit`, exponential moment | `audit_exists_expTransform_lt_one` | **done**, `exists_expTransform_lt_one` |
| `thm:non-lattice-limit` | `audit_non_lattice_limit` | **done**, `nonLatticeLimit` |
| `eq:c-definition` | `audit_pairRatio` | **done**, `pairRatio_rpow`, `pairRatio_lt_half` |
| `sec:setup`, the middle-thirds system | `audit_cantorSystem_facts` | **done**, `cantorSystem_isDimension`, `cantorSystem_stronglySeparated` |
| `sec:setup`, the paired system | `audit_pairSystem_facts` | **done**, `pairSystem_isDimension`, `pairSystem_stronglySeparated` |
| `sec:setup`, existence of `μ_A` | `audit_exists_cantor_measure` | **done**, `exists_unique_isNatural_cantorSystem` |
| `sec:setup`, existence of `μ_B` | `audit_exists_pair_measure` | **done**, `exists_unique_isNatural_pairSystem` |
| `eq:non-lattice` is non-arithmeticity | `audit_pairSystem_nonArithmetic_iff` | **done**, `pairSystem_nonArithmetic_iff` |
| `sec:renewal`, the periodic extension | `audit_exists_periodic_extension` | **done**, `exists_periodic_extension_of_shift` |
| `sec:renewal`, `G̃_A` itself | `audit_exists_periodic_profile` | **done**, `exists_periodic_profile` |
| `thm:cantor-values` | `audit_cantor_values` | **done**, `cantor_values` |
| `thm:cantor-values`, non-constancy | `audit_cantor_nonconstant` | **done**, `G_nonconstant_on_period` |
| `thm:cantor-values`, bundled | `audit_thm_cantor_values` | **done**, `thm_cantor_values` |
| `eq:periodic-smoothing`, `Tg` is `p/2`-periodic | `audit_smoothOp_periodic` | **done**, `smoothOp_periodic` |
| `eq:periodic-smoothing`, `Tg` continuous and `p/2`-periodic | `audit_smoothOp_continuous_periodic` | **done**, `continuous_smoothOp` |
| `sec:smoothing`, the coefficient is Mathlib's | `audit_fourierCoeffP_eq_fourierCoeffOn` | **done**, `fourierCoeffP_eq_fourierCoeffOn` |
| `eq:fourier-multiplier`, the Fourier identity | `audit_fourier_multiplier` | **done**, `fourierCoeffP_smoothOp` |
| `eq:gamma-multiplier`, the evaluation | `audit_gamma_multiplier` | **done**, `multInt_eq_gammaMult` |
| `eq:gamma-multiplier`, non-vanishing | `audit_gammaMult_ne_zero` | **done**, `gammaMult_ne_zero` |
| `thm:smoothing-injective`, multiplier | `audit_multInt_ne_zero` | **done**, `multInt_ne_zero` |
| `thm:smoothing-injective`, Fourier uniqueness | `audit_fourier_uniqueness` | **done**, `eq_zero_of_fourierCoeffP_eq_zero` |
| `thm:smoothing-injective` | `audit_smoothing_injective` | **done**, `smoothOp_injective` |
| `thm:smoothing-injective`, kernel form | `audit_smoothing_kernel_trivial` | **done**, `smoothOp_eq_zero` |
| `thm:smoothing-injective`, consequence | `audit_smoothing_nonconstant` | **done**, `smoothOp_nonconstant` |
| `thm:smoothing-injective`, bundled | `audit_thm_smoothing_injective` | **done**, `thm_smoothing_injective` |
| `sec:smoothing`, positivity of `H̃_A` | `audit_smoothOp_pos` | **done**, `smoothOp_pos` |
| `eq:gb-limit` | `audit_gb_limit` | **done**, `gb_limit` |
| `thm:profile-asymptotics`, `eq:hb-asymptotic` | `audit_profile_asymptotics_non_lattice` | **done**, `profile_asymptotics_nonLattice` |
| `thm:profile-asymptotics`, `μ_B` conclusion | `audit_non_lattice_correlation_limit` | **done**, `non_lattice_correlation_limit` |
| `thm:profile-asymptotics`, `eq:ha-asymptotic` | `audit_profile_asymptotics_lattice` | **done**, `profile_asymptotics_lattice` |
| `eq:ha-asymptotic` in big-`O` shape | `audit_profile_asymptotics_lattice_bigO` | **done**, `profile_asymptotics_lattice_bigO` |
| `thm:profile-asymptotics`, `μ_A` conclusion | `audit_lattice_correlation_oscillation` | **done**, `lattice_correlation_oscillation` |
| `thm:profile-asymptotics`, bundled | `audit_thm_profile_asymptotics` | **done**, `thm_profile_asymptotics` |
| `thm:non-lattice-separation` | `audit_non_lattice_separation` | **done**, `non_lattice_separation` |
| `thm:gaussian-four-point`, independence | `audit_disjoint_increments_indep` | **done**, `disjoint_increments_indep` |
| `thm:gaussian-four-point`, `eq:joint-return-bound` | `audit_gaussian_four_point` | **done**, `gaussian_four_point` |
| `eq:joint-return-bound` almost everywhere | `audit_gaussian_four_point_ae` | **done**, `gaussian_four_point_ae` |
| `thm:gaussian-four-point`, bundled | `audit_thm_gaussian_four_point` | **done**, `gaussian_four_point_bundled` |
| `thm:endpoint-block-mass` | `audit_endpoint_block_mass` | **done**, `endpoint_block_mass` |
| `thm:endpoint-block-mass`, dyadic | `audit_endpoint_block_mass_dyadic` | **done**, `endpoint_block_mass_dyadic` |
| `thm:four-point-integral` | `audit_four_point_integral` | **done**, `four_point_integral` |
| `thm:variance` | `audit_variance` | **done**, `variance_four_point` |
| `thm:variance`, final assertion | `audit_varScale_isLittleO` | **done**, `varScale_div_tendsto_zero` |
| `thm:variance`, bundled | `audit_thm_variance` | **done**, `variance_bundled` |
| `eq:y-variance` | `audit_y_variance` | **done**, `y_variance` |
| `eq:grid-convergence` | `audit_grid_convergence` | **done**, `grid_convergence` |
| `eq:monotone-fill` | `audit_monotone_fill` | **done**, `monotone_fill` |
| `thm:uniform-concentration` | `audit_uniform_concentration` | **done**, `uniform_concentration` |
| `eq:lattice-gap` | `audit_lattice_gap` | **done**, `smoothOp_gap` |
| `sec:obstruction`, the signed convolution | `audit_conv_reflect` | **done**, `conv_reflect_eq_map_sub` |
| `thm:homometric-example` | `audit_homometric_example` | **done**, `homometric_example` |

Proved outside the endpoint list, and load-bearing for it: the kernel layer
(`kern_pos`, `logKern_eq`, `logKern_le_exp_neg_mul_abs`, `logKern_integrable`), the
occupation layer (`continuous_plane_of_coord`, `IsPlanarBrownian.ae_continuous`,
`measurable_pathMap`, `IsPlanarBrownian.ae_occupationProb_toMeasure`), the empirical
layer (`corr_mono`, `Yprofile_le_of_le`, `measurable_corr`, `measurable_Yprofile`), the
period arithmetic
(`exists_period_representative`, `exists_nat_sub_mem_Ico`, `shift_add_nsmul`,
`exists_periodic_extension`), the identification `phi_eq_pairLaw` of `Φ` as the
distribution function of `dΦ`, the Cantor constants (`rpow_three_sCantor`,
`three_fifths_two_rpow_lt_one`, `halfMass_eq`, `G_add_nsmul_period`), the homometric
layer (`diffMultiset_eq`, `diffCount_eq`, `strong_separation`, `homSystem`,
`homSystem_stronglySeparated`, `tHom_mem_Ioo`, `six_mul_rpow_tHom`), and the pairing
determinants (`crossing_det`, `nested_det`).

## What Mathlib does not have

Five gaps, each one a piece of the paper that has to be built here.

- **No iterated function systems and no self-similar measures anywhere in Lean.** A
  search of public Lean repositories for iterated function systems, Hutchinson, Hausdorff
  dimension and self-similar measures returns nothing; this is the one gap with no
  external work to reuse, and it is built here. `System.IsNatural`
  takes Hutchinson's identity `μ = ∑ r_i^s (S_i)_*μ` as the definition, together with
  an attractor `K` carrying the measure, and `System.exists_unique_isNatural` is
  Hutchinson's theorem for it: the pair `(K, μ)` exists and is unique.  `Hutchinson.lean`
  builds it off the code space `ℕ → ι`, not off a metric on measures, since Mathlib
  carries no completeness for Lévy-Prokhorov: the attractor is the range of the coding
  map, the measure is the pushforward of the Bernoulli law with weights `r_i^s`, and
  uniqueness of the measure needs only uniform continuity, through the adjoint
  `T f = ∑ p_i f ∘ S_i` on `ℝ →ᵇ ℝ` and Heine-Cantor on `[0,1]`. Strong separation is a condition on the pieces `S_i K` of the attractor,
  as in `sec:renewal`, not on the first-level intervals `S_i([0,1])`, which would be
  strictly stronger; `homSystem_stronglySeparated` derives the attractor version from
  the interval version for the homometric systems.
- **No key renewal theorem for a lattice-supported non-arithmetic law: closed, and not
  where it was expected.** Mathlib carries no renewal theory at all, and the vendored
  `AbsorptionCutoff` theorem does not apply to `F` as stated
  (`not_nonlattice_renewalLaw`).  `thm:non-lattice-limit` turns out not to need a key
  renewal theorem: cutting the renewal equation at any finite threshold `T` past the gap
  gives the exact identity `∫ z = ∑ᵢ pᵢ ∫_{T-aᵢ}^{T} G`, so if `G` converges the limit is
  forced to be `m⁻¹ ∫ z`, with positivity separate and unconditional
  (`renewalConstant_pos`).  What is left is bare convergence of `G`, and that is
  Choquet-Deny: `IsDimension` says `∑ pᵢ = 1`, so `eq:g-recursion` makes `G` a bounded
  harmonic function for the walk with steps `log(1/rᵢ)`, and `NonArithmetic` says that
  walk's step group is dense.  See *Reusing the external renewal library* below for the
  route not taken and why it is still worth knowing.
- **The planar return probability: closed, through polar coordinates.**
  `IsPlanarBrownian.return_prob` proves
  `P(|W_u - W_t| < r) = 1 - exp(-r²/(2|u-t|))`. The `χ²` route is **not** available: a
  search confirms Mathlib has no chi-squared distribution and no result on the squared
  norm of a Gaussian vector, so the identification in
  `AbsorptionCutoff.Supercritical.GaussianRadial` has no Mathlib counterpart and that
  module is not a Mathlib-only leaf. The proof here goes through
  `lintegral_comp_polarCoord_symm`, `prod_withDensity`, Tonelli and the fundamental
  theorem of calculus.
- **Joint measurability of the process: closed.** Mathlib's `IsPreBrownianReal` gives
  only `AEMeasurable (B t) P` at a fixed time, so `W` itself is not jointly measurable
  and cannot be made so.  What is available is a modification:
  `IsPlanarBrownian.exists_jointlyMeasurable` and
  `Reduction.exists_jointly_measurable_modification` produce a `V` with every path
  continuous, every `V t` measurable, and `V = W` off one measurable null set.  Joint
  measurability is then `measurable_uncurry_of_continuous_of_measurable`, with no dyadic
  approximation.  Keep the form that exposes the null set: transporting a fixed-time
  identity such as `return_prob` across it needs `measure_congr` on a set that is only
  outer measurable.  `audit_aemeasurable_occupation` and `audit_gaussian_reduction` are
  built on this, as is the completed variance expansion of `audit_variance`.
- **Fourier theory: closed.** `eq:fourier-multiplier`, the Gamma evaluation and
  uniqueness are all proved, so `thm:smoothing-injective` is unconditional. The Gamma
  evaluation went through Mathlib's Mellin transform (`mellin_comp_mul_left`,
  `mellin_comp_inv`, `Complex.GammaIntegral_eq_mellin`) rather than a hand-rolled change
  of variables; the paper's substitution `x = 1/(2η)` is exactly that composite, and no
  integrability side condition arises because each step is an unconditional identity.
- **Fourier uniqueness: closed.** Mathlib has no uniqueness theorem for Fourier
  coefficients of periodic functions on the line, but it has `fourierBasis`, a Hilbert
  basis of `L²(AddCircle T)`. `eq_zero_of_fourierCoeffP_eq_zero` builds the bridge and
  runs it: lift `g` to `AddCircle q` by `Function.Periodic.lift`, match the coefficients
  through `fourierCoeff_eq_intervalIntegral`, apply `fourierBasis.repr` injectivity, and
  come back from almost-everywhere-zero by continuity.  The multiplier identity and
  its non-vanishing are also proved, so `audit_smoothing_kernel_trivial` is closed.
- **The dense-or-cyclic dichotomy: closed.** Mathlib's `AddSubgroup.dense_or_cyclic`
  plus `AddSubgroup.mem_closure_singleton` is the raw material;
  `pairSystem_nonArithmetic_iff` turns it into "the group generated by `log 2` and
  `log(1/c)` is dense iff their ratio is irrational", which is what makes `eq:non-lattice`
  exactly the hypothesis of `thm:non-lattice-limit`.
- **Minkowski reconstruction: closed.** Compact Brownian images are measurable in the
  Hausdorff hyperspace, their affine cylinder laws and finite-family independence are
  proved, and the cut-off, union, scaling, defect, localization, finite-cylinder, and
  translation-overlap algebra is exact. `tendsto_tubeProbability_of_cylinder_approximation` performs the
  two-scale bounded-Lipschitz limit, while
  `tubeReconstructsOccupation_of_ae_cylinder_approximation` packages its almost-sure
  use. Prokhorov compactness supplies a Borel limit map, and a direct Borel classifier
  transfers occupation-law singularity to the laws of the compact image sets. The
  Brownian stopping-cover moments, separated-cylinder overlaps, sharp centered-variance
  recurrence, delayed exponential contraction, and fixed-generation almost-sure quotient
  limits are now formalised.  The homogeneous source is reconstructed directly from its
  one-delay recurrence and the paired source from the non-arithmetic renewal theorem, so
  their compact Brownian image laws are proved mutually singular.  For an arbitrary
  arithmetic system, the induced finite-delay law has gcd one at the maximal span;
  convergence of its renewal masses and the exact convolution identity give uniform
  convergence to a positive periodic mean profile and hence complete reconstruction.

## Reusing the external renewal library

`thm:non-lattice-limit` does not need a key renewal theorem proved from scratch.
`AbsorptionCutoff` (Benny Avelin, Apache-2.0) contains one, and the relevant part is a
**Mathlib-only leaf**: six modules, about 5,200 lines, importing nothing from the rest of
that project.

```
Renewal.lean (1594)  →  RenewalAbel.lean (1572)  ┐
RenewalKernel.lean (365)                         ├→  RenewalSinc.lean (323)
                                                 ┘        ↓
                          RenewalEquation.lean (447) ←  RenewalApprox.lean (855)
```

### What it gives, and what it does not

The library's headline is
`AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm`:

```
theorem tendsto_tsum_integral_comp_sub_of_driNorm {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℂ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      atTop (𝓝 ((∫ x, z x) / ((∫ x, x ∂μ : ℝ) : ℂ)))
```

which reads as `eq:g-non-lattice-limit` verbatim. **It does not apply to `F` as stated**,
and `not_nonlattice_renewalLaw` is the machine-checked reason. It is, however, usable
after weakening its hypothesis: see the ledger below.

What is usable, and is what the vendoring is worth keeping for, is everything not gated
on `Nonlattice`. In particular the reduction that occupies the first half of the proof of
`thm:non-lattice-limit`:

* `convPow`, `renewalMeasure`, `driNorm`, `cellSup`, `expTransform` and their algebra;
* `eq_tsum_integral_comp_sub_of_renewalEquation` — the renewal equation `h = h⋆μ + ψ`
  iterated to `h y = ∑ₙ ∫ ψ(y − s) dμ^{*n}(s)`, which is exactly the paper's
  "`G = z + F*G` iterates to `G = ∑_{n≥0} F^{*n}*z`". It needs the exponential moment,
  which `exists_expTransform_lt_one` supplies, and **no** non-lattice hypothesis;
* `tendsto_integral_comp_sub_convPow_zero` — the terminal term `F^{*(N+1)}*G` vanishing.

For the pair-distance part of the paper, this reduction is closed in two ways below:
the vendored theorem has been restated under Feller non-arithmeticity, and an independent
Choquet--Deny argument proves the same endpoint without the key renewal theorem.

### The `Nonlattice` ledger

**`Nonlattice (S.renewalLaw s)` is false, for every self-similar system.**
`AbsorptionCutoff.Renewal.Nonlattice μ` asks that `μ` charge no affine lattice `a + rℤ`.
A measure carried by two atoms always charges one, taking `a` the first atom and `r` the
gap, so `F` never satisfies it. `not_nonlattice_renewalLaw` proves this, and
`System.exists_norm_charFun_renewalLaw_eq_one` sharpens it to the analytic level: at
`t = 2π/(a₁ − a₀)` the atom phases align and `‖charFun F t‖ = 1`. So no route asking for
`‖charFun‖ < 1` pointwise can work.

**But the vendored theorem is stated far stronger than its proof uses, and `F` does
satisfy what the proof needs.** Of the 24 vendored declarations carrying `Nonlattice`,
all but three merely forward it. It is consumed at two leaves only:
`charFun_ne_one_of_nonlattice`, which needs `charFun μ t ≠ 1` for `t ≠ 0`, and that *is*
Feller's hypothesis (`System.nonArithmetic_iff_charFun_ne_one` proves `eq:non-lattice` is
exactly it, in both directions); and `norm_charFun_lt_one_of_nonlattice`, whose one live
use sits inside a `filter_upwards`, so an almost everywhere statement suffices, and for
`F` the set `{t : ‖charFun F t‖ = 1}` is contained in a lattice, hence countable and
null. Swapping `Nonlattice` for those two weaker conditions and re-running the chain
does close `thm:non-lattice-limit` by the Fourier route; this was carried out and
compiled, at the cost of restating and re-proving about 760 lines of vendored proof body,
which is why it is not the proof of record.

**Do not conclude from `not_nonlattice_renewalLaw` that the vendored theorem is
unusable.** That inference is wrong, and it stood in this file for a while. The right
long-term fix is to weaken the hypothesis in the vendored copy, or upstream, rather than
to duplicate the chain.

**Both routes are in the library, and the endpoint is proved twice.**
`KeyRenewalFourier.lean` is the paper's own route and is what `Solution.lean` cites: it
restates the vendored chain under `FellerNonlattice` and runs it, so
`thm:non-lattice-limit` is certified by the key renewal theorem the paper appeals to.
`KeyRenewal.lean` and `TailHarmonic.lean` are an independent second proof that needs no
key renewal theorem at all: cutting the renewal equation at a finite threshold pins the
constant, and Choquet-Deny run against the tail on which `eq:g-recursion` holds supplies
convergence of `G`. They are about 1200 lines and depend on no vendored declaration.
Keeping both is deliberate: the first certifies the paper's argument, the second is
elementary and survives any change to the vendoring.

**The duplication is removable, and the patch is measured.** `KeyRenewalFourier.lean`
carries 935 lines restating the vendored chain, purely because `Nonlattice` sits in the
*statements* of 24 vendored declarations. Weakening it in the vendored copy instead was
tried and compiles: 80 changed or added lines across five files (`Kernel.lean` untouched),
namely the `FellerNonlattice` definition with one almost everywhere lemma, the 24
hypothesis swaps, and three proof sites, of which only one is substantive, a six line
block becoming two. **The patch is applied**, so the vendored chain carries
`FellerNonlattice` directly and `KeyRenewalFourier.lean` states no vendored declaration
a second time. The price is recorded under *The leaf is vendored*: the tree is no longer
pristine, and re-syncing gained a step.

Do not try to discharge `Nonlattice` for `F`, and do not weaken `System.NonArithmetic`
to try to meet it. What is needed is a different theorem: the key renewal theorem for
non-arithmetic distributions that may be carried by a lattice. Feller vol. II §XI.1
(1.10)–(1.17), or Gut, *Stopped Random Walks*, Thm. 6.6.

### The leaf is vendored

Route chosen: the six modules are copied into `BrownianImages/Renewal/` under the Apache
License 2.0, with `Renewal/LICENSE`, a top-level `NOTICE`, and a provenance header in each
file. Upstream commit `41c45c6d72e979419e46224bb7b4be5cee31f2b5`. Only the `import` lines were rewritten;
`Kernel.lean` is byte-identical to the original, and the other five carry, besides the
import rewrite, the `Nonlattice` to `FellerNonlattice` weakening described in the ledger
above: 80 changed or added lines, stated in each file's header and in the top-level
`NOTICE` as the Apache License requires. The declarations keep
their upstream namespace `AbsorptionCutoff.Renewal`, so nothing there is confusable with a
declaration of this project, and `RenewalBridge.lean` is the only module of the library
that mentions that namespace.

It compiles against our Mathlib `v4.32.2` unchanged, in about 20 s. `AxCheck.lean` audits
`tendsto_tsum_integral_comp_sub_of_driNorm` and its real variant here rather than taking
the upstream README on trust: both report `propext`, `Classical.choice`, `Quot.sound`.

Re-syncing with upstream means refetching the six files at a newer commit, redoing the
import rewrite, and reapplying the hypothesis weakening. The last step is the one that
can rot: if upstream changes where `Nonlattice` is consumed, the three proof sites have to
be re-traced. `git diff` against a pristine checkout of the commit above is the way to see
the whole patch at once.

The two routes not taken: a Lake dependency on the whole project, which would have pinned
Mathlib `v4.32.0` against our `v4.32.2` and the shared `packagesDir` tree of section 0 and
compiled 72,000 lines; and upstreaming to Mathlib, which is the right long-run home for
renewal theory but is slow and not under this project's control.

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

- **`𝒫(ℝ²)`: the two σ-algebras agree, and that is now proved.** Mathlib's
  `ProbabilityMeasure Plane` is measurable through the evaluations `ν ↦ ν s`, while the
  paper uses the Borel σ-algebra of the weak topology. `borel_probabilityMeasure_eq_giry`
  identifies them, so this is no longer a fidelity gap. Mathlib has neither a
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
One statement is split between a probabilistic half and a finite half, and both are now
proved.

- **`thm:cantor-values`.** `audit_cantor_values` is the three exact values.
  `audit_cantor_nonconstant` is non-constancy on every period, and it takes
  `Φ_A(1/3) = 1/2`, `Φ_A(1/6) = 3/10` and the shift identity `eq:g-recursion` as
  hypotheses; `cantor_values` and `cantor_g_period` discharge all three.
- **`thm:homometric-example`.** The endpoint asserts everything the proposition does:
  the two natural measures, their distinctness, strong separation with gap `1/45`,
  Ahlfors regularity at `t = log 6 / log 30 ∈ (1/2,1)`, the equality of the signed
  convolutions `σ * σ̃`, and the consequent equalities of `Φ` and `H`.  All of it is
  proved.  The convolution equality goes through the observation that the difference law
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
`Solution.lean` and replays their proofs through the kernel; the other 80 endpoints of
`Solution.lean` rest on `lake build` and the library's axiom check.  It says nothing
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

## Technique notes

- **`decide` handles the difference multiset.** The 36-element signed difference
  multiset of a six-element digit set reduces in the kernel without trouble.
  `native_decide` is banned: it drags in `Lean.ofReduceBool` and breaks the axiom check.
- **rpow numerics: raise to an integer power, do not substitute.** `2^{2/3} < 5/3`
  becomes `4 < 125/27` through `Real.rpow_natCast`, `Real.rpow_mul` and
  `lt_of_pow_lt_pow_left₀`. The same shape proves `s < 2/3` from `log 8 < log 9`.
- **`Real.rpow_def_of_pos` is the workhorse** for identities of the form `3^s = 2`:
  rewrite to `exp (log 3 * s)`, cancel `log 3`, and apply `Real.exp_log`.
- **The kernel's `L¹` bound is two one-sided bounds.** `e^{-t} ≤ 1` gives
  `k(x) ≤ ½e^{(s-1)x}`, and `e^{-t} ≤ 1/t` gives `k(x) ≤ e^{sx}`; together they are
  `k(x) ≤ e^{-min(s,1-s)|x|}`, and that is exactly where `0 < s < 1` enters.
- **The reflection idiom for `Iic`** is
  `(Measure.measurePreserving_neg volume).integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding`,
  copied from Mathlib's `integrable_rpow_mul_exp_neg_mul_sq`. There is no lemma for
  `x ↦ e^{-c|x|}` on the line; `integrable_exp_neg_mul_abs` supplies it.
- **`AddCircle` is how a periodic extension is built.** `AddCircle.liftIco_continuous`
  turns "continuous on `[a, a+p]` with equal endpoint values" into a continuous function
  on the circle, and composing with the quotient map gives the periodic extension on the
  line. `exists_periodic_extension_of_shift` then pushes the agreement from one period to
  the whole half line with `exists_nat_sub_mem_Ico` and `shift_add_nsmul`. Do not try to
  build the extension by hand out of `Int.fract`: it is discontinuous at the endpoints
  and the gluing has to be redone.
- **Names that moved at v4.32.2**: `inv_anti₀` (was `inv_le_inv_of_le`),
  `lt_of_pow_lt_pow_left₀`, `div_lt_iff₀`, `pow_lt_pow_left₀`. `div_lt_div_iff` is gone
  in the form the older sources use; go through `div_lt_iff₀` instead.
- **Implicit arguments in `Integrable.mono'`.** The dominating function's parameters
  unify against the wrong hypothesis if left implicit; pass `(c := ...)` explicitly.
- **`positivity` does not see hypothesis-carried positivity.** Feed `0 < 2 * exp x` as
  a term where `Continuous.inv₀` asks for it.

- **`thm:ahlfors` needs no antichain.** Below the separation gap a closed ball meets at
  most one piece `S_i K`, and a piece it misses pulls back into `Kᶜ`, hence to a null
  set, so Hutchinson's identity collapses to the single term
  `μ(B̄(x,r)) = r_i^s μ(B̄(S_i⁻¹x, r/r_i))`.  Iterating that step *is* the antichain: an
  induction on `ρ/2 ≤ r q^n`, with `q = (max_i r_i)⁻¹`, runs the cut to the stopping
  scale, where the upper bound is just `μ ≤ 1`.  The hull counting of the paper, and the
  whole word and cylinder layer a literal formalisation would need, never appear.  The
  lower bound needs a mass bound uniform in the centre at the stopping scale, and that is
  compactness of the support, not Hutchinson uniqueness.
- **`eq:ahlfors` is not `eq:frostman`.** `IsAhlfors` quantifies its upper bound over
  support points only.  The recursion above gives the upper bound at every centre and
  every radius, so `AhlforsRegular.exists_isFrostman_of_isNatural` is what the later
  endpoints should read the Frostman hypothesis of `μ_A` and `μ_B` off.
- **`eq:smoothing` is the layer cake formula, not an integration by parts.** Write
  `1 - e^{-r²/(2δ)} = ∫₀^{δ⁻¹} (r²/2) e^{-r²u/2} du`, which holds at every real `δ`
  because Lean's `0⁻¹ = 0` makes both sides vanish at `δ = 0`, matching `Φ(0) = 0`.  Then
  `lintegral_comp_eq_lintegral_meas_lt_mul` gives the result with no boundary terms.  The
  substitution `δ = r²η` is `integral_comp_rpow_Ioi` at `p = -1` followed by
  `integral_comp_mul_left_Ioi`, both unconditional, so no integrability side condition
  arises.
- **`eq:joint-return-bound` through the regression decomposition.** Write `Z' = ρZ + N`
  with `ρ = crossCov/δ` and `Var N = Δ/δ`; the joint bound is then two applications of
  "a disc of radius `r` has mass at most `r²/(2v)` under a centred planar Gaussian",
  whose proof is the pointwise density bound `(2πv)⁻¹` times the area `πr²`.  Work in
  `ℝ × ℝ` with `Complex.volume_ball`, not in `EuclideanSpace`, whose ball volume carries
  a `Γ` factor.  Independence of `Z` and `N` is
  `HasGaussianLaw.indepFun_of_covariance_eval` fed by `iIndepFun.hasGaussianLaw`; Mathlib's
  Gaussian API is richer here than the missing `χ²` suggests.  Using the signed covariance
  rather than `overlap`, which is its absolute value, removes every case split on the
  orientation of the two intervals.
- **The four dyadic sums factor.**
  `min{1, λ/(β+η), λ²/(βη)} ≤ min{1,λ/β} · min{1,λ/η}` turns `eq:dyadic-master-sum` into a
  product of two one-dimensional sums, so `eq:dyadic-elementary` and `eq:dyadic-critical`
  are one lemma `∑_j β^θ min(1, λ/β)` in three regimes, applied at `θ = s` and `θ = 2s`.
  Bound partial sums in `ℝ` and lift with `ENNReal.tsum_eq_iSup_sum'`, which avoids
  summability side conditions and truncated subtraction.
- **`μ⁴` permutation invariance in one lemma.** Transport through `ℝ⁴ ≃ᵐ (Fin 4 → ℝ)` and
  precomposition `x ↦ x ∘ σ`, each step by `Measure.pi_eq` on boxes.  Do not compose
  adjacent `Prod.swap` transpositions.  Supply concrete permutations as
  `Equiv.ofBijective ![0,2,1,3] (by decide)`, which reduces by `rfl` where products of
  `Equiv.swap` do not.
- **Chebyshev and Borel-Cantelli, in the shapes that avoid work.**
  `ProbabilityTheory.meas_ge_le_variance_div_sq` is the real-valued Chebyshev and skips
  `evariance` entirely; `MeasureTheory.ae_eventually_notMem` is the Borel-Cantelli the
  grid argument wants, not `measure_limsup_atTop_eq_zero`.  The three regimes of
  `eq:y-variance` collapse to `φ(v) ≤ 2e^{-av}` with `a = min(2s, 2(1-s), 1/2)`, which
  makes every grid sum geometric uniformly in the regime.
- **`set_option ... in` and `omit ... in` go before the doc comment**, not between it and
  the declaration, where they are a parse error.
- **Names that moved, second batch**: `Measure.finsetSum_apply` and `Measure.coe_finsetSum`
  (the `finset_sum` spellings are deprecated), `ProbabilityTheory.variance_const_mul` (was
  `variance_mul`), `Set.eq_empty_iff_forall_notMem`, `Set.notMem_empty`,
  `Set.piecewise_eq_of_notMem`, `mul_le_mul_right` (was `mul_le_mul_left'`),
  `pow_le_one₀`, `pow_le_pow_of_le_one`, `Summable.sum_le_tsum`,
  `Measure.isProbabilityMeasure_map`, `lt_or_ge` (`lt_or_le` no longer resolves).
  `div_le_div_of_nonneg_left` is the way to shrink a denominator: `gcongr` splits a
  product denominator pointwise and fails.

- **A convex average cannot increase a modulus of continuity.** `IsDimension` says
  `∑ᵢ rᵢ^s = 1`, so `eq:g-recursion` writes `G(w)` as a convex average of its own earlier
  values; `|G(w+h) - G(w)| ≤ maxᵢ |G(w+h-aᵢ) - G(w-aᵢ)|`, and descending by one plain
  `Nat` induction lands any tail point in the compact window `[log ρ⁻¹ - a_max,
  log ρ⁻¹ + a_min]`, where Heine-Cantor applies.  So a continuous tail-harmonic function
  is automatically uniformly continuous on the tail: no equicontinuity hypothesis, no
  Arzelà-Ascoli, no locally uniform limit of translates.  Keeping the descending pair
  within `a_min/2` is what stops it falling below the threshold.
- **Choquet-Deny against a threshold needs slack.** Running the maximum principle on a
  tail needs the defect non-negative everywhere the descent visits *and* near maximisers
  arbitrarily far to the right.  `sSup (range f)` gives the first and not the second, a
  tail supremum gives the second and is not a fixed number.  Use
  `d = limsup f + ε₀ - f`, or equivalently `M = ⨅ n : ℕ, sSup (f '' Set.Ici (T + n))`,
  which sidesteps `Filter.limsup` and its `IsBoundedUnder` autoparams; those autoparams
  never fire over `ℝ` and have to be supplied by hand as `Filter.isBoundedUnder_of` and
  `Filter.isCoboundedUnder_le_of_le`.
- **Arzelà-Ascoli is a dead end here**, even with equicontinuity: a locally uniform limit
  of translates is harmonic and constant, but constancy of the limit does not by itself
  relate `limsup G` to `liminf G`.  The threshold version of the maximum principle has no
  such gap.
- **The difference law of a self-similar measure is self-similar.** For `σ` under
  `S_i(x) = x/30 + d_i/18`, the law of `(X - X' + 1)/2` satisfies Hutchinson's identity
  for the 36 maps `u ↦ u/30 + ((d_i - d_j)/36 + 29/60)` at dimension `2t`.  Homometry of
  the digit sets is then literal equality of the two systems, and uniqueness finishes.
  `Finset.sum_eq_multiset_sum` plus `Multiset.map_map` reduces homometry to a `decide`
  over `Fin 6 × Fin 6`, with no explicit permutation.
- **`overlap = 0` does not mean the intervals are separated.** A degenerate pair `t = u`
  has zero overlap while sitting strictly inside the other interval, so
  `disjoint_increments_indep` does not apply to it.  Case-split on degeneracy first, where
  the return event is everything and independence is trivial, and test it on the
  `Real.toNNReal`-ed times: two distinct negative times collapse to the same `ℝ≥0`.
- **A second moment can be a mass, with no indicator anywhere.** `C_r(ν_ω)` is `(μ×μ)` of
  a section of one measurable set, and `C_r(ν_ω)²` is `μ⁴` of a section of another whose
  section at `ω` is the *square* of the first, which holds by `rfl`.  That single `rfl` is
  the whole second-moment computation, and it keeps the variance expansion in `ℝ≥0∞` with
  no nested Fubini.  `Measure.prodAssoc_prod` identifies `(μ×μ)×(μ×μ)` with `μ⁴`, and is
  much cheaper than transporting through `Fin 4 → ℝ`.
- **`Type*` in a hypothesis binder is unusable.** It binds a universe parameter of the
  declaration rather than a metavariable, so the hypothesis can never be applied at a
  concrete alphabet.  Lean does not report a universe error: it burns the full heartbeat
  budget in `isDefEq` and reports a timeout at whichever argument is under the cursor,
  which points nowhere near the cause.  Write `Type`, or reuse the ambient index type.
  Two separate developments lost time to this.
- **Compose an endpoint into a `∀`-shaped hypothesis by its bare name.** Wrapping it in a
  `fun` binds the intervening implicit arguments positionally and everything shifts;
  passing the name alone lets Lean match implicit to implicit and instantiate the index
  type itself.
- **Do not create dotted names that shadow a root namespace.** Declaring
  `AbsorptionCutoff.Renewal.foo` inside `namespace BrownianImages` creates
  `BrownianImages.AbsorptionCutoff.Renewal`, after which `open AbsorptionCutoff.Renewal`
  silently opens the empty one.  Use `open _root_.AbsorptionCutoff.Renewal`.

## Not formalised

`rem:conditionality`, the discussion after `thm:homometric-example`, and the
introduction's account of the literature carry no statement and no endpoint. Nor do the
purely arithmetic displays inside proofs: `eq:dyadic-master-sum`, `eq:dyadic-elementary`
and `eq:dyadic-critical` are the four dyadic sums of `thm:four-point-integral` and are
covered by that endpoint alone, and `eq:crossing-determinant` and
`eq:nested-determinant` are proved in `FourPoint.lean` without an endpoint of their own.
The claim the project makes is coverage of every numbered result, plus the displayed
claims that a later result cites or that carry a hypothesis of their own; it is not
coverage of every display.
`eq:non-lattice`, the rational independence of `log(1/c)/log 2`, is an open arithmetic
assertion in the paper. It appears in two forms: as `System.NonArithmetic` in the
statements about a general system, and literally, as `Irrational (log (1/c) / log 2)`,
in the endpoints about `μ_B`. `audit_pairSystem_nonArithmetic_iff` is the equivalence
between them.
