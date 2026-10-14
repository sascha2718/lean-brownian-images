# The vendored renewal library

The non-lattice conclusion of *Lattice and non-lattice renewal limits* and
*Renewal asymptotics for the mean neighbourhood profile* use the non-arithmetic key
renewal theorem for directly Riemann integrable functions on the line (Feller, vol. II,
§XI). Mathlib carries no renewal theory. Benny Avelin's
[AbsorptionCutoff](https://github.com/BennyAvelin/AbsorptionCutoff) (Apache License
2.0) contains one. The retained subset consists of six modules importing only
Mathlib and one another, with no dependency on the rest of that project. They live in
`BrownianImages/Renewal/`, based on upstream commit
`41c45c6d72e979419e46224bb7b4be5cee31f2b5`, with `Renewal/LICENSE`, the top-level
`NOTICE`, and a provenance header in each file.

The vendored sources use Lean's module system. Public imports and exposed public
definitions preserve the interfaces used by this project.

```
Basic.lean  →  Abel.lean  ┐
Kernel.lean               ├→  Sinc.lean  →  Approx.lean  →  Equation.lean
                          ┘
```

The declarations keep their upstream namespace `AbsorptionCutoff.Renewal`, so nothing
there is confusable with a declaration of this project. `RenewalBridge`,
`KeyRenewalFourier` and `Minkowski.TubeRenewalLimit` are the modules of the library
that mention that namespace.

## What it gives

The library's headline, in the vendored form, is

```
theorem tendsto_tsum_integral_comp_sub_of_driNorm {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : FellerNonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℂ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      atTop (𝓝 ((∫ x, z x) / ((∫ x, x ∂μ : ℝ) : ℂ)))
```

This supplies the analytic renewal-series limit used to prove the paper's
*Non-lattice renewal limit*. The retained library also supplies the algebra of
`convPow`, `renewalMeasure`, `driNorm`, `cellSup` and `expTransform`, and the iterated
renewal equation `eq_tsum_integral_comp_sub_of_renewalEquation`: `h = h⋆μ + ψ` iterates
to `h y = ∑ₙ ∫ ψ(y − s) dμ^{*n}(s)`, which is the paper's "`G = z + ϑ*G` iterates to
`G = ∑_{n≥0} ϑ^{*n}*z`". This identity assumes the integrability and growth
conditions needed to make the terminal term vanish, as well as the exponential
moment supplied by `System.exists_expTransform_lt_one`. It needs no non-lattice
hypothesis.

## The non-lattice hypothesis

Upstream, the theorem asks for `Nonlattice μ`: `μ` is not concentrated on any
affine lattice `a + rℤ`. That hypothesis is false for every two-map IFS. A measure
carried by two atoms is concentrated on such a lattice, with `a` the first atom and
`r` the gap, so the renewal
law `ϑ = ∑ p_i δ_{α_i}` never satisfies it. `System.not_nonlattice_renewalLaw`
is the machine-checked statement, and `System.exists_norm_charFun_renewalLaw_eq_one`
sharpens it to the analytic level: for distinct log-ratios, the atom phases align
at `t = 2π/(α₁ − α₀)` and `‖charFun ϑ t‖ = 1`. Thus a pointwise strict bound on
the modulus at every nonzero frequency cannot hold.

The upstream statement is stronger than its renewal-limit proof uses. That proof
needs two characteristic-function facts: `charFun μ t ≠ 1` for `t ≠ 0`, which is
Feller's non-arithmetic condition (`System.nonArithmetic_iff_charFun_ne_one` proves that the paper's
*Non-lattice condition* is exactly it, in both directions), and `‖charFun μ t‖ < 1`
inside one `filter_upwards`, where an almost everywhere statement suffices; for `ϑ` the set `{t : ‖charFun ϑ t‖ = 1}`
is contained in a lattice, hence countable and null
(`System.countable_norm_charFun_renewalLaw_eq_one`).

`FellerNonlattice`, defined in `Renewal/Basic.lean`, records these two conditions.
The renewal-limit chain uses it in place of `Nonlattice`, with an almost everywhere
lemma and three adjusted proof sites. `fellerNonlattice_of_nonlattice` proves that
the vendored hypothesis is weaker than the upstream one. The original `Nonlattice`
definition and its bounds `charFun_ne_one_of_nonlattice` and
`norm_charFun_lt_one_of_nonlattice` remain unchanged; the two-atom refutations remain
proved in the project library.

The subset retains the proved key renewal theorem, the renewal-equation series
identity and their dependencies. It omits unused convolution identities, the
separate discounted renewal-measure API, auxiliary comparison and pole-correction
lemmas, the characteristic-function power-limit wrapper, the upstream scalar-limit
and angular-reconstruction wrappers, and two redundant smoothing-kernel helpers.
The Fourier proof's Abel regularisation is retained in `Abel.lean`. Provenance
headers and `NOTICE` record the modifications, as required by the Apache License.

## The paper's non-lattice renewal limit

`KeyRenewalFourier` proves the endpoint `audit_non_lattice_limit`. The paper's
*Non-lattice condition* supplies `FellerNonlattice`. Under the open set condition,
the cross-term estimates in *Renewal and asymptotics* give the exponential tail of
the renewal defect `z = G - F*G`. These inputs feed the vendored key renewal theorem.
The consequences in `NonLattice`, including the occupation-law separation results,
use this limit. `Minkowski.TubeRenewalLimit` applies the same vendored theorem to
*Renewal asymptotics for the mean neighbourhood profile*. The *Rescaled correlation
recursion* includes a cross term under the open set condition, so the proof needs
the renewal theorem for the defect rather than tail harmonicity of `G`.

## What the audit covers

The vendored theorem is a proved dependency of the general non-lattice profile and
Minkowski reconstruction results. These occur among the nine Section 1 Challenge
endpoints selected by Comparator, including `audit_profile_asymptotics`,
`audit_reconstruction` and the general lattice/non-lattice corollaries. It is not an
assumed literature input. The library's axiom discipline applies throughout the vendored
code: no `axiom`, no proof holes and no `native_decide`.

## Re-syncing with upstream

Refetch the six files at the target commit, redo the import rewrite, reapply the
hypothesis weakening, and retain the subset needed by the project proofs and
documented interfaces, including the non-lattice counterexamples. If upstream
changes where `Nonlattice` is consumed, re-trace the three adjusted proof sites.
`git diff` against a pristine checkout of the commit above shows the whole patch at once. Two routes were
not taken: a Lake dependency on the whole upstream project, which pins a different
Mathlib and compiles about 72,000 lines, and upstreaming to Mathlib, the right long-run
home for renewal theory.
