# The vendored renewal library

`thm:non-lattice-limit` and `thm:neighbourhood-renewal` rest on the non-arithmetic key
renewal theorem for directly Riemann integrable functions on the line (Feller, vol. II,
§XI). Mathlib carries no renewal theory. Benny Avelin's
[AbsorptionCutoff](https://github.com/BennyAvelin/AbsorptionCutoff) (Apache License
2.0) contains one, and the relevant part is a Mathlib-only leaf: six modules, about
5,300 lines, importing nothing from the rest of that project. They are copied into
`BrownianImages/Renewal/` from upstream commit
`41c45c6d72e979419e46224bb7b4be5cee31f2b5`, with `Renewal/LICENSE`, the top-level
`NOTICE`, and a provenance header in each file.

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

which reads as `eq:g-non-lattice-limit` verbatim, together with the algebra of
`convPow`, `renewalMeasure`, `driNorm`, `cellSup` and `expTransform`, and the iterated
renewal equation `eq_tsum_integral_comp_sub_of_renewalEquation`: `h = h⋆μ + ψ` iterates
to `h y = ∑ₙ ∫ ψ(y − s) dμ^{*n}(s)`, which is the paper's "`G = z + ϑ*G` iterates to
`G = ∑_{n≥0} ϑ^{*n}*z`". The iteration needs the exponential moment, which
`RenewalBridge.exists_expTransform_lt_one` supplies, and no non-lattice hypothesis.

## The non-lattice hypothesis

Upstream, the theorem asks for `Nonlattice μ`: `μ` charges no affine lattice `a + rℤ`.
That hypothesis is false for every self-similar system. A measure carried by two atoms
always charges such a lattice, with `a` the first atom and `r` the gap, so the renewal
law `ϑ = ∑ p_i δ_{a_i}` never satisfies it. `RenewalBridge.not_nonlattice_renewalLaw`
is the machine-checked statement, and `System.exists_norm_charFun_renewalLaw_eq_one`
sharpens it to the analytic level: at `t = 2π/(a₁ − a₀)` the atom phases align and
`‖charFun ϑ t‖ = 1`, so no route asking for `‖charFun‖ < 1` pointwise can work.

The upstream statement is far stronger than its proof uses. Of the vendored
declarations carrying `Nonlattice`, all but three merely forward it, and it is consumed
in two forms only: `charFun μ t ≠ 1` for `t ≠ 0`, which is Feller's non-arithmetic
condition (`System.nonArithmetic_iff_charFun_ne_one` proves that `eq:non-lattice` is
exactly it, in both directions), and `‖charFun μ t‖ < 1` inside one `filter_upwards`,
where an almost everywhere statement suffices; for `ϑ` the set `{t : ‖charFun ϑ t‖ = 1}`
is contained in a lattice, hence countable and null
(`System.countable_norm_charFun_renewalLaw_eq_one`).

`FellerNonlattice`, defined in `Renewal/Basic.lean`, is exactly those two conditions,
and the vendored chain carries it in place of `Nonlattice`: 80 changed or added lines
across five files (`Kernel.lean` is byte-identical to upstream), namely the definition
with one almost everywhere lemma, the hypothesis swaps, and three proof sites, of which
one is substantive, a six-line block becoming two. `fellerNonlattice_of_nonlattice`
records that the vendored hypothesis is weaker than the upstream one, and `Nonlattice`
with its three lemmas is kept unchanged. Each file's header and the top-level `NOTICE`
state the modification, as the Apache License requires.

## Two proofs of `thm:non-lattice-limit`

`KeyRenewalFourier` is the paper's own route and proves the endpoint
`audit_non_lattice_limit`: it feeds `FellerNonlattice`, which `eq:non-lattice`
supplies, to the vendored key renewal theorem. `KeyRenewal` and `TailHarmonic` are an
independent second proof that needs no key renewal theorem: cutting the renewal
equation at a finite threshold pins the constant, and Choquet-Deny run against the tail
on which `eq:g-recursion` holds supplies convergence of `G`. The consequences drawn in
`NonLattice`, among them `thm:cantor-application`, rest on the second proof. Both are
kept: the first mirrors the paper's argument, the second is elementary and independent
of the vendored code. `Minkowski.TubeRenewalLimit` uses the vendored theorem for
`thm:neighbourhood-renewal`, where no elementary substitute is available.

## What the audit covers

The vendored theorem sits in the dependency closure of five endpoints of
`Solution.lean`: `audit_non_lattice_limit`, `audit_tube_renewal`,
`audit_minkowski_reconstruction`, `audit_cantor_set_application` and
`audit_cantor_set_application_pair`. It sits in the closure of none of the four
endpoints the comparator kernel-checks, whose proofs of `thm:cantor-application` go
through the Choquet-Deny route. So the vendored code is checked by `lake build
Solution`, with the library's axiom discipline (no `axiom`, no `native_decide`)
applying to it as to everything else, and it compiles against Mathlib `v4.32.2`
unchanged.

## Re-syncing with upstream

Refetch the six files at the target commit, redo the import rewrite, and reapply the
hypothesis weakening. The last step is the one that can rot: if upstream changes where
`Nonlattice` is consumed, the three proof sites have to be re-traced. `git diff` against
a pristine checkout of the commit above shows the whole patch at once. Two routes were
not taken: a Lake dependency on the whole upstream project, which pins a different
Mathlib and compiles about 72,000 lines, and upstreaming to Mathlib, the right long-run
home for renewal theory.
