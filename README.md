# Distinguishing sets and measures from their planar Brownian images: the Lean formalisation

[![Comparator audit](https://github.com/sascha2718/lean-brownian-images/actions/workflows/comparator.yml/badge.svg)](https://github.com/sascha2718/lean-brownian-images/actions/workflows/comparator.yml)

A Lean 4 formalisation, over Mathlib, of the paper

> Sascha Troscheit, *Distinguishing sets and measures from their planar Brownian images*, 2026. Manuscript.

The nine numbered results of Section 1 are stated independently in `Challenge.lean`
and proved in `Solution.lean`. Supporting statements, representations and coverage
qualifications are mapped in [`paper-correspondence.yaml`](paper-correspondence.yaml),
with proof details in [`docs/correspondence.md`](docs/correspondence.md). Schief's theorem,
which the paper cites for the open set condition, is proved in `BrownianImages/Schief.lean`.
The library is `sorry`-free, declares no axiom, and every proof uses only the three
standard axioms `propext`, `Classical.choice` and `Quot.sound`; `native_decide` is not
used.

## What is proved

The Comparator configuration selects all nine Section 1 statements:

| Section 1 result | Endpoint |
| --- | --- |
| 1. Separation by expected profiles | `audit_main` |
| 2. Lattice and non-lattice profile asymptotics | `audit_profile_asymptotics` |
| 3. Lattice/non-lattice occupation-law separation | `audit_lattice_nonlattice_measures` |
| 4. Finite exceptions in the two-contraction family | `audit_finite_exceptions` |
| 5. Small-dimension monotonicity | `audit_small_dimension` |
| 6. Finiteness of the critical set | `audit_finite_critical_set` |
| 7. Minkowski reconstruction | `audit_reconstruction` |
| 8. Lattice/non-lattice compact-image separation | `audit_lattice_nonlattice_sets` |
| 9. Two-contraction compact-image separation | `audit_two_contraction_sets` |

Beside them, `Solution.lean` states 136 endpoints in all, named `audit_<slug>` covering the manuscript, from the Gaussian reduction of the correlation integral through the renewal
analysis with the non-constancy of the lattice profile, the smoothing operator and its
Fourier multipliers, the four-point estimate and the concentration argument, to the
Minkowski reconstruction of the occupation measure from the compact Brownian image, the
transfer of singularity to compact-set laws, the base-five missing-digit comparison, the
homometric counterexample, and the fixed-dimension family: its
limiting profiles, the analyticity and the range of the mean profile, the separation of
parameters with distinct means, and the strict monotonicity of the mean for small
dimension. The table of every result against its endpoint is in
[`docs/correspondence.md`](docs/correspondence.md).

## Layout

- `BrownianImages/`: the library, 140 modules organised along the sections of the paper.
  The root module `BrownianImages.lean` is the index: it lists every module with the part
  of the paper it certifies. `BrownianImages/FixedDimension/` carries the fixed-dimension
  family, `BrownianImages/Minkowski/` carries the reconstruction
  section, and `BrownianImages/Renewal/` is vendored third-party code, see below.
- `Solution.lean`: the formal statement of the paper, every endpoint proved by a library
  declaration.
- `Challenge.lean`: the nine headline endpoints restated with `sorry`, on Mathlib-only
  definitions of the expected correlation profile and self-similar measures. It contains
  no helper proofs or bundled constructors for the named systems. It imports only Mathlib, so the audit
  trusts this file and Mathlib alone. Its statement text is character-for-character
  identical to `Solution.lean`.
- `comparator-config.json`, `comparator-audit.sh`: the audit configuration and a local
  runner for it.
- `formalization.yaml`: Palomar metadata, source and automation disclosures, and the nine headline mappings.
- `paper-correspondence.yaml`: all 32 numbered manuscript statements, their Lean correspondences and qualifications.
- `scripts/check_paper_correspondence.py`: source-drift and declaration consistency checks.
- `.github/workflows/palomar-preflight.yml`: the pinned Palomar verifier, run on demand.
- `docs/`: the [correspondence with the paper](docs/correspondence.md), including the
  fidelity boundary; [what Mathlib does not have](docs/mathlib-gaps.md); and the account
  of the [vendored renewal library](docs/renewal-library.md).

Every module opens with a comment naming the section of the paper it mirrors and the
declarations that matter, and every declaration carries a doc comment identifying the
paper result it formalises.

The concise companion for §9.3 is
[`Section9Estimates.lean`](BrownianImages/FixedDimension/Section9Estimates.lean). It states
the entropy and derivative bounds and the small-parameter comparison, all proved from
the library. The accompanying `Section9Computations.nb` in the paper directory contains
the detailed scalar calculations as executable Mathematica cells with saved outputs.

## Building

The project pins Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (`lean-toolchain`,
`lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get          # the prebuilt Mathlib
lake build                  # the library
lake build Solution Challenge
```

## The audit

[Comparator](https://github.com/leanprover/comparator) compares the statements of
`Challenge.lean` with the identically named declarations of `Solution.lean`, audits the
axioms of the solution proofs on the raw `lean4export` output, and replays the proofs
through the Lean kernel, trusting neither the elaborator nor `#print axioms`. Because
`Challenge.lean` imports only Mathlib, the guarantee covers the audited statements as
written there, with the library never trusted. The other endpoints of `Solution.lean` are
checked by `lake build Solution`: the library declares no axiom, so they rest on the same
three axioms.

The development workflow `.github/workflows/comparator.yml` runs the audit on every push, fully
sandboxed: comparator, `lean4export` and `landrun` are built at pinned commits, the
sandbox is probed, and comparator runs inside a `systemd-run` unit with network access
denied.

To run it locally, build [comparator](https://github.com/leanprover/comparator) and
[lean4export](https://github.com/leanprover/lean4export) at Lean `v4.35.0-rc2`, then

```
COMPARATOR_TOOLS=/path/to/tools ./comparator-audit.sh
```

where the tools directory contains the two checkouts; `COMPARATOR_LANDRUN` and
`COMPARATOR_LEAN4EXPORT` override the individual binaries. On macOS, where `landrun`
is unavailable, the script uses comparator's unsandboxed shim.

## Palomar upload

The repository contains the two Lean files, pinned Lake files, licence, Comparator
configuration, and [`formalization.yaml`](formalization.yaml). Submit the public
repository at an immutable commit with `comparator-config.json` as the configuration
path. [`Palomar preflight`](.github/workflows/palomar-preflight.yml) runs Palomar's
verifier on the selected commit. It is separate from the local macOS Comparator
check and does not register a submission. The toolchain and dependency pins are unchanged.

The paper is kept in the parent research directory. To check the correspondence locally:

```
python3 scripts/check_paper_correspondence.py
```

The check covers the source fingerprints, all numbered statements, the nine theorem
holes, the solution declaration names, the Comparator list and metadata alignment.
It neither elaborates Lean nor establishes mathematical equivalence. Revisit the
correspondence when source fingerprints change.

## Correspondence with the paper

Comparator never compares against the paper, so the correspondence between the formal
statements and the document is a human obligation. [`docs/correspondence.md`](docs/correspondence.md)
argues it: the statement layer, the endpoint table, and the fidelity boundary, that is
the places where a formal statement can look right and be false or vacuous, chiefly the
support condition on a measure and the clipping of negative times by `Real.toNNReal`.

## Licence

The code in this repository is licensed under the Apache License 2.0, see `LICENSE`.
`BrownianImages/Renewal/` is vendored from Benny Avelin's
[AbsorptionCutoff](https://github.com/BennyAvelin/AbsorptionCutoff), also under the
Apache License 2.0, with the modifications recorded in `NOTICE` and in each file's
header.

## Citation

See `CITATION.cff`.
